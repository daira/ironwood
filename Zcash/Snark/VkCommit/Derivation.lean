import Zcash.Bridge.VkProjection
import Zcash.Circuits.Fixtures.Layout
import Zcash.Snark.Core.Group

/-!
# Deriving the Action verifying key's commitment fields from the circuit + captured URS

This module derives the two commitment families of an Action `VerifyingKey` —
`fixedCommitment` (the 29 fixed columns) and `permutationCommonCommitment` (the 15
permutation columns) — from the derived circuit layout and a supplied monomial URS:
Lagrange-basis URS by inverse FFT
(`derivedUrsGLagrange`), dense fixed columns from the certified layout recipe
(`derivedFixedColumns`), the keygen permutation polynomials (`permPolyColumns`), and
`commit_lagrange` commitments for both families. `derivedActionVk` assembles a
`VerifyingKey` from these plus the already-certified derived scalar/gate/layout fields.

## Rust reference

* Lagrange URS: `poly/commitment.rs:75-88` (`Params::new`'s `g_lagrange`), `arithmetic.rs:192`
  (`best_fft` — bit-reversal + iterative Cooley–Tukey butterflies).
* `commit_lagrange` blind: `poly/commitment.rs:212-216` (`Blind::default () = Blind(F::ONE)`).
* Permutation commitments: `plonk/permutation/keygen.rs:102-152` (`Assembly::build_vk`).

## Certification

`Zcash.Snark.VkCommit.Certificate` certifies the whole derivation (inverse FFT +
`n⁻¹` scaling + dense column reconstruction + keygen mapping + blind convention) and
proves `vk = derivedActionVk`. It is kept in a separate module so clients can import
the derived data and key without evaluating the expensive concrete certificate.
The explicit `ZcashVkCommit` target builds both modules; it remains excluded from
`defaultTargets`.
-/

namespace Zcash.Snark.VkCommit

open Zcash.Snark
open Bridge
open Halo2
open Zcash.Circuits.Fixtures

/-! ## Lagrange URS derivation (`poly/commitment.rs:75-88`, `arithmetic.rs:192`) -/

/-- `bitreverse(n, l)` — reverse the low `l` bits of `n` (`best_fft`'s local `bitreverse`,
`arithmetic.rs:193-200`). -/
def bitreverse (n l : ℕ) : ℕ := Id.run do
  let mut r := 0
  let mut m := n
  for _ in [0:l] do
    r := (r <<< 1) ||| (m &&& 1)
    m := m >>> 1
  return r

/-- The size-`2^k` root of unity's inverse, `omega⁻¹ = omega^(2^k − 1)` (order `2^k`).
This is halo2's `alpha_inv` (`ROOT_OF_UNITY_INV` squared `S − k` times,
`poly/commitment.rs:76-79`), computed here from `omegaOf` since both are the same
primitive `2^k`-th root. -/
def omegaInvOf (k : ℕ) : Fp := powFast (omegaOf k) (2 ^ k - 1)

/-- In-place radix-2 DIT FFT over the group `G` with `Fp` twiddles, mirroring
`best_fft(a, omega, log_n)` (`arithmetic.rs:192-256`): bit-reversal permutation, precomputed
twiddle powers `[omega^0 … omega^(n/2−1)]`, then `log_n` rounds of decimation-in-time
butterflies `(a, b) ↦ (a + tw·b, a − tw·b)`. The scalar action `tw·b` is the same
`ZMod.val • point` convention `commitLagrange` uses (Rust's iterative and recursive
`best_fft` branches compute this identical result; we mirror the iterative one,
`arithmetic.rs:223-252`). -/
def bestFftG {G : Type} [AddCommGroup G] [Inhabited G]
    (a0 : Array G) (omega : Fp) (logN : ℕ) : Array G := Id.run do
  let n := a0.size
  let mut a := a0
  -- bit-reversal permutation (`arithmetic.rs:207-212`)
  for k in [0:n] do
    let rk := bitreverse k logN
    if k < rk then
      let ak := a[k]!
      let ark := a[rk]!
      a := (a.set! k ark).set! rk ak
  -- precompute twiddles `[omega^0 … omega^(n/2 − 1)]` (`arithmetic.rs:215-221`)
  let mut tw : Array Fp := Array.mkEmpty (n / 2)
  let mut w : Fp := 1
  for _ in [0:n / 2] do
    tw := tw.push w
    w := w * omega
  -- `log_n` rounds of butterflies (`arithmetic.rs:223-252`)
  let mut half := 1
  for _ in [0:logN] do
    let chunk := 2 * half
    let twiddleChunk := n / chunk
    for c in [0:n / chunk] do
      let s := c * chunk
      for j in [0:half] do
        let twdl := tw[j * twiddleChunk]!
        let aIdx := s + j
        let bIdx := s + half + j
        let aOld := a[aIdx]!
        let t := twdl.val • a[bIdx]!
        a := a.set! aIdx (aOld + t)
        a := a.set! bIdx (aOld - t)
    half := chunk
  return a

/-- The Lagrange-basis generators derived from a monomial URS by inverse FFT and
`n⁻¹` scaling, exactly as in halo2's `Params::new`. -/
def derivedUrsGLagrange {G : Type} [AddCommGroup G] [Inhabited G]
    (urs : URS G) : List G :=
  let monomial := List.ofFn urs.g
  let minv : Fp := ((2 : Fp) ^ urs.k)⁻¹
  (bestFftG monomial.toArray (omegaInvOf urs.k) urs.k).toList.map
    fun point => minv.val • point

/-! ## Generalized Lagrange commitment (`poly/commitment.rs:212-216`) -/

/-- Commit to a zero-padded Lagrange-coefficient column against an arbitrary basis with
`Blind::default () = Blind(F::ONE)` (`poly/commitment.rs:212-216`):
`(∑ᵢ coeffsᵢ • basisᵢ) + w` — the same `+ w` blind convention the existing
`commitLagrange` uses, generalized to an arbitrary basis and coefficient list (the
instance-commitment path through `commitLagrange` is deliberately left untouched). -/
def commitLagrangeWith {G : Type} [AddCommGroup G] [Inhabited G]
    (blind : G) (basis : List G) (coeffs : List Fp) : G :=
  ((List.range coeffs.length).map
    (fun i => (coeffs.getD i 0).val • basis.getD i 0)).sum + blind

/-! ## Derived fixed columns and their commitments

The sparse fixed-cell reconstruction is the Action layout recipe `TestVkLayoutAction`
certifies against the Rust dump, driven from fully-derived placements: `V1.starts`
region starts and `V1.constants` allocation (both certified equal to the fixture's in
`TestFloorPlanner`), `indexedRegions` bodies, `actionSelMapDerived` packed selectors,
and `usable = 2^actionK − (blindingFactors + 1)`. Unlike `TestVkLayoutAction` — which
reads the fixture's `constants` allocation — `constantsFixed` here consumes the DERIVED
`V1.constants` (the constants column contents ARE part of the fixed columns keygen
commits to; the layout test simply predates the planner-side constants derivation).
The dense columns are `numFixedColumns` (= 29, `actionPinnedCs.numFixedColumns`)
columns of length `2^actionK`, unassigned cells `0` (`domain.empty_lagrange`,
`plonk/keygen.rs`), assigned values coerced back from the `ZMod.val` triples. -/

/-- The Action pinned constraint system, derived without any captured fixture. -/
def actionPinnedCs : PinnedConstraintSystem Fp :=
  .derive actionCS (actionSelMapDerived (2 ^ actionK))

/-- Derived region bodies, by `assignRegion` index. -/
def actionRegions : List (ℕ × RegionOperations Fp) := (indexedRegions actionOperations 0).1

/-- Derived V1 region starts (`floor_planner/v1.rs`; `FloorPlanner.V1.starts`, certified
equal to the fixture placements in `TestFloorPlanner`). -/
def actionStarts : List ℕ := FloorPlanner.V1.starts actionOperations

/-- Derived V1 constants allocation `(value, col, row)` (`v1.rs:79-136`); orchard's single
constants column is fixed column 3 (`enable_constant`). Certified equal to the fixture's
allocation in `TestFloorPlanner`. -/
def actionConstants : List (ℕ × ℕ × ℕ) :=
  FloorPlanner.V1.constants (ZMod.val : Fp → ℕ) actionOperations [3]

/-- Usable rows `n − (blindingFactors + 1)` (= 2042) — the trailing rows carry blinders
(`keygen.rs`; the `usable = 2042` of `TestVkLayoutAction`). -/
def actionUsable : ℕ := 2 ^ actionK - (actionCS.blindingFactors + 1)

/-- The sparse fixed cells `(col, row, ZMod.val value)`: loaded tables + the constants
column + packed selector columns + region `assign_fixed`s, deduped and sorted — the exact
recipe `TestVkLayoutAction` pins against the Rust dump, from derived inputs. -/
def actionFixedSparse : List (ℕ × ℕ × ℕ) :=
  Layout.sortFixed (Layout.dedupFixed
    (Layout.tableFixed (ZMod.val : Fp → ℕ) actionUsable actionOperations
      ++ Layout.constantsFixed actionConstants
      ++ Layout.selectorFixed (actionSelMapDerived (2 ^ actionK))
          (activations actionStarts actionRegions)
      ++ Layout.regionAssignFixed (ZMod.val : Fp → ℕ) actionStarts actionRegions))

/-- Scatter sparse `(col, row, natval)` triples into `numCols` dense length-`n` columns,
default `0` (`domain.empty_lagrange`); the `natval`s are `ZMod.val`s coerced back to `Fp`. -/
def denseColumns (n numCols : ℕ) (triples : List (ℕ × ℕ × ℕ)) : List (List Fp) := Id.run do
  let mut cols : Array (Array Fp) := Array.replicate numCols (Array.replicate n 0)
  for (c, r, v) in triples do
    if c < numCols then
      cols := cols.modify c (fun col => col.set! r ((v : ℕ) : Fp))
  return cols.toList.map Array.toList

/-- The derived dense fixed columns (`numFixedColumns` columns of length `2^actionK`). -/
def derivedFixedColumns : List (List Fp) :=
  denseColumns (2 ^ actionK) actionPinnedCs.numFixedColumns actionFixedSparse

/-- The derived fixed-column commitments against the supplied URS. -/
def derivedFixedCommitments {G : Type} [AddCommGroup G] [Inhabited G]
    (urs : URS G) : List G :=
  let lagrange := derivedUrsGLagrange urs
  derivedFixedColumns.map (commitLagrangeWith urs.w lagrange)

/-! ## Derived permutation commitments (`plonk/permutation/keygen.rs:102-152`) -/

/-- The permutation columns as `ColRef`s in `enable_equality` order
(`cs.permutationColumns`, certified equal to the capture's via `permutationColumns_eq`) —
the order the keygen `Assembly` mapping and the `δ^i` scaling are indexed by, and the
column shape `V1.copyList` resolves cells against. -/
def actionPermCols : List Zcash.Circuits.Fixtures.ColRef :=
  actionCS.permutationColumns.map fun c =>
    match c.kind with
    | .advice => .advice c.index
    | .fixed => .fixed c.index
    | .instance => .instance c.index

/-- The derived keygen copy list under the V1 floor planner (`floor_planner/v1.rs`;
`Fixtures/Layout.lean` `V1.copyList`, the recipe `TestVkLayoutAction` certifies), over
derived placements and constants. -/
def actionCopyList : List (ℕ × ℕ × ℕ × ℕ) :=
  Layout.V1.copyList actionPermCols actionStarts actionOperations actionConstants

/-- The keygen permutation `mapping` (`permutation/keygen.rs` `Assembly::copy` replay,
`Layout.runAssembly`) over the derived copy list: `mapping[i][j] = (i', j')`. -/
def actionPermMapping : Array (Array (ℕ × ℕ)) :=
  Layout.runAssembly (2 ^ actionK) actionPermCols.length actionCopyList

/-- `[ω^0, ω^1, …, ω^(n−1)]` by iterated multiplication (`build_vk`'s `omega_powers`,
`permutation/keygen.rs:108-116`) — NOT `powFast` per entry. -/
def omegaPowersArr (omega : Fp) (n : ℕ) : Array Fp := Id.run do
  let mut arr : Array Fp := Array.mkEmpty n
  let mut cur : Fp := 1
  for _ in [0:n] do
    arr := arr.push cur
    cur := cur * omega
  return arr

/-- `[δ^0, δ^1, …, δ^(m−1)]` by iterated multiplication (`build_vk`'s `cur *= DELTA`,
`permutation/keygen.rs:118-133`). -/
def deltaPowersArr (delta : Fp) (m : ℕ) : Array Fp := Id.run do
  let mut arr : Array Fp := Array.mkEmpty m
  let mut cur : Fp := 1
  for _ in [0:m] do
    arr := arr.push cur
    cur := cur * delta
  return arr

/-- The per-column permutation polynomials in Lagrange form:
`p_i[j] = deltaomega[i'][j'] = δ^{i'} · ω^{j'}` where `(i', j') = mapping[i][j]`
(`build_vk`, `permutation/keygen.rs:135-146`). -/
def permPolyColumns : List (List Fp) :=
  let n := 2 ^ actionK
  let omegaPows := omegaPowersArr (omegaOf actionK) n
  let deltaPows := deltaPowersArr deltaFp actionPermCols.length
  let mapping := actionPermMapping
  (List.range actionPermCols.length).map fun i =>
    (List.range n).map fun j =>
      let pij := (mapping[i]!)[j]!
      deltaPows[pij.1]! * omegaPows[pij.2]!

/-- The derived permutation common commitments against the supplied URS. -/
def derivedPermutationCommonCommitments
    {G : Type} [AddCommGroup G] [Inhabited G]
    (urs : URS G) : List G :=
  let lagrange := derivedUrsGLagrange urs
  permPolyColumns.map (commitLagrangeWith urs.w lagrange)

/-! ## The fully-derived Action verifying key -/

/-- The Action `VerifyingKey` with EVERY field derived from the circuit (+ the captured
URS for the two commitment families): domain/permutation scalars from
`actionK`/`actionCS`/pasta constants (certified equal to the capture's in
`vk_scalars_derived`), gates and query layouts from `actionPinnedCs`
(`capturedPinnedCs_eq_derived`) carried back across the `RichExpression → Expr` boundary
by `RichExpression.toExpr`, `permutationChunks` from the derived selector map
(`vk_permutationChunks_derived`), and the commitment families from
`derivedFixedCommitments`/`derivedPermutationCommonCommitments`. The record equality
is `vk_eq_derived` below (consuming the bundled commitment certification). -/
def derivedActionVk
    {G : Type} [AddCommGroup G] [Inhabited G]
    (shape : Shape) (urs : URS G) :
    VerifyingKey shape Fp G where
  omega := omegaOf actionK
  n := 2 ^ actionK
  blindingFactors := actionCS.blindingFactors
  delta := deltaFp
  chunkLen := actionCS.chunkLen
  gates := actionPinnedCs.gates.map RichExpression.toExpr
  instanceQueryLayout := actionPinnedCs.instanceQueryLayout
  adviceQueryLayout := actionPinnedCs.adviceQueryLayout
  fixedQueryLayout := actionPinnedCs.fixedQueryLayout
  fixedCommitment := fun i => (derivedFixedCommitments urs).getD i 0
  permutationCommonCommitment := fun i =>
    (derivedPermutationCommonCommitments urs).getD i.val 0
  permutationChunks := permutationChunksOf (actionSelMapDerived (2 ^ actionK)) actionCS
  lookupInputExprs := fun l =>
    (actionPinnedCs.lookupInputExprs.getD l.val []).map RichExpression.toExpr
  lookupTableExprs := fun l =>
    (actionPinnedCs.lookupTableExprs.getD l.val []).map RichExpression.toExpr

end Zcash.Snark.VkCommit
