import Zcash.Snark.Fixtures.SingleAction.VkMatch
import Zcash.Circuits.Fixtures.Layout

/-!
# Deriving the Action verifying key's commitment fields from the circuit + captured URS

This module derives the two commitment families the Action `VerifyingKey` capture still
transcribes as opaque points — `fixedCommitment` (the 29 fixed columns) and
`permutationCommonCommitment` (the 15 permutation columns) — from the derived circuit
layout and the captured monomial URS: Lagrange-basis URS by inverse FFT
(`derivedUrsGLagrange`), dense fixed columns from the certified layout recipe
(`derivedFixedColumns`), the keygen permutation polynomials (`permPolyColumns`), and
`commit_lagrange` commitments for both families. `derivedActionVk` assembles a
`VerifyingKey` from these plus the already-certified derived scalar/gate/layout fields.

## Rust reference

* Lagrange URS: `poly/commitment.rs:75-88` (`Params::new`'s `g_lagrange`), `arithmetic.rs:192`
  (`best_fft` — bit-reversal + iterative Cooley–Tukey butterflies).
* `commit_lagrange` blind: `poly/commitment.rs:212-216` (`Blind::default () = Blind(F::ONE)`).
* Permutation commitments: `plonk/permutation/keygen.rs:102-152` (`Assembly::build_vk`).

## Certification status and cost (why this target is non-default)

`commitments_derived` below certifies the whole derivation (inverse FFT + `n⁻¹`
scaling + dense column reconstruction + keygen mapping + blind convention) by ONE
bundled `native_decide`. Measured baseline: a single-column probe cost **1291 s wall,
6.9 GB peak RSS** — dominated by the fixed cost every `native_decide` in this file pays
(native codegen of the ~2110-point fixture closure) plus the Lagrange FFT
(2^11·11 group butterflies) and one 2^11-term Vesta MSM, all under the naive
`ZMod.val • point` binary scalar multiplication with affine (inversion-per-add) point
arithmetic.

The FULL bundled certification — all 29 fixed + 15 permutation commitments + the
Lagrange-prefix cross-check in one `native_decide`, and the record theorem
`vk = derivedActionVk` — costs the fixed ≈ 21.5 min plus ~43 additional MSMs.
Maintainer-accepted as a known annoyance: this target (`ZcashVkCommit`, see
`lakefile.toml`) is excluded from `defaultTargets` so the default build stays fast, and
the acceleration path is a Pippenger bucket MSM + projective coordinates + faster
certified field arithmetic (the dominant cost today is one field inversion per affine
point-add inside the binary `ZMod.val • point` scalar multiplication).
-/

namespace Zcash.Snark.VkCommit

open Zcash.Snark
open Zcash.Snark.Fixture
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
def bestFftG (a0 : Array G) (omega : Fp) (logN : ℕ) : Array G := Id.run do
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

/-- The derived Lagrange-basis URS generators (length `2^actionK = 2048`): the monomial
generators `capturedUrsG` transformed by an inverse FFT at `omega⁻¹ = alpha_inv` and scaled
by `n⁻¹ = TWO_INV^k = (2^k)⁻¹` — halo2's `g_lagrange` (`poly/commitment.rs:75-88`).
`commitments_derived` cross-checks the captured 10-generator prefix directly and
certifies the rest through the commitments. -/
def derivedUrsGLagrange : List G :=
  let minv : Fp := ((2 : Fp) ^ actionK)⁻¹
  (bestFftG capturedUrsG.toArray (omegaInvOf actionK) actionK).toList.map fun p => minv.val • p

/-! ## Generalized Lagrange commitment (`poly/commitment.rs:212-216`) -/

/-- Commit to a zero-padded Lagrange-coefficient column against an arbitrary basis with
`Blind::default () = Blind(F::ONE)` (`poly/commitment.rs:212-216`):
`(∑ᵢ coeffsᵢ • basisᵢ) + w` — the same `+ w` blind convention the existing
`commitLagrange` uses, generalized to an arbitrary basis and coefficient list (the
instance-commitment path through `commitLagrange` is deliberately left untouched). -/
def commitLagrangeWith (basis : List G) (coeffs : List Fp) : G :=
  ((List.range coeffs.length).map
    (fun i => (coeffs.getD i 0).val • basis.getD i 0)).sum + capturedURS.w

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

/-- The derived fixed-column commitments — `commit_lagrange` of each dense fixed column
with the default blind (`plonk/keygen.rs`, `keygen_vk`'s `fixed_commitments`). All 29 are
certified equal to the capture in `commitments_derived`. -/
def derivedFixedCommitments : List G :=
  derivedFixedColumns.map (commitLagrangeWith derivedUrsGLagrange)

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

/-- The derived permutation common commitments — `commit_lagrange` of each permutation
polynomial with the default blind (`build_vk`, `permutation/keygen.rs:147-151`). Certified
against the capture in `commitments_derived`. -/
def derivedPermutationCommonCommitments : List G :=
  permPolyColumns.map (commitLagrangeWith derivedUrsGLagrange)

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
def derivedActionVk : VerifyingKey shape Fp G where
  omega := omegaOf actionK
  n := 2 ^ actionK
  blindingFactors := actionCS.blindingFactors
  delta := deltaFp
  chunkLen := actionCS.chunkLen
  gates := actionPinnedCs.gates.map RichExpression.toExpr
  instanceQueryLayout := actionPinnedCs.instanceQueryLayout
  adviceQueryLayout := actionPinnedCs.adviceQueryLayout
  fixedQueryLayout := actionPinnedCs.fixedQueryLayout
  fixedCommitment := fun i => derivedFixedCommitments.getD i 0
  permutationCommonCommitment := fun i => derivedPermutationCommonCommitments.getD i.val 0
  permutationChunks := permutationChunksOf (actionSelMapDerived (2 ^ actionK)) actionCS
  lookupInputExprs := fun l =>
    (actionPinnedCs.lookupInputExprs.getD l.val []).map RichExpression.toExpr
  lookupTableExprs := fun l =>
    (actionPinnedCs.lookupTableExprs.getD l.val []).map RichExpression.toExpr

/-! ## Certification

ONE `native_decide` sharing the FFT, fixed contents and keygen mapping across the
Lagrange-prefix cross-check and all 44 commitments, split by `Prod.mk.injEq`, feeding
the record theorem `vk = derivedActionVk` (record-wise, NOT `native_decide` — the
record has function fields). Maintainer-accepted cost (this module's build runs tens of
minutes; see the module docstring), quarantined in the non-default `ZcashVkCommit`
target. -/

/-- **The derived commitment data matches the capture**: the Lagrange URS 10-generator
prefix, the 29 fixed-column commitments, and the 15 permutation common commitments —
bundled into ONE `native_decide` so the shared Lagrange FFT, fixed contents, and keygen
mapping evaluate exactly once (rather than once per fact). -/
theorem commitments_derived :
    (derivedUrsGLagrange.take capturedUrsGLagrange.length,
     derivedFixedCommitments, derivedPermutationCommonCommitments)
    = (capturedUrsGLagrange, capturedFixedCommitments,
       capturedPermutationCommonCommitments) := by native_decide

/-- The derived Lagrange URS reproduces the captured 10-generator prefix. -/
theorem derivedUrsGLagrange_prefix_eq :
    derivedUrsGLagrange.take capturedUrsGLagrange.length = capturedUrsGLagrange := by
  have h := commitments_derived
  simp only [Prod.mk.injEq] at h
  exact h.1

/-- The derived fixed-column commitments are the captured ones. -/
theorem derivedFixedCommitments_eq :
    derivedFixedCommitments = capturedFixedCommitments := by
  have h := commitments_derived
  simp only [Prod.mk.injEq] at h
  exact h.2.1

/-- The derived permutation common commitments are the captured ones. -/
theorem derivedPermutationCommonCommitments_eq :
    derivedPermutationCommonCommitments = capturedPermutationCommonCommitments := by
  have h := commitments_derived
  simp only [Prod.mk.injEq] at h
  exact h.2.2

/-- `((List.ofFn f).map g).getD` at an in-range `Fin` index is `g (f l)`. -/
private theorem getD_map_ofFn {α β : Type} {n : ℕ} (f : Fin n → α) (g : α → β)
    (l : Fin n) (d : β) : ((List.ofFn f).map g).getD l.val d = g (f l) := by
  simp [List.getD_eq_getElem?_getD, l.isLt]

/-- **The captured Action verifying key is fully derived.** Proven record-wise (not by
`native_decide` — the record carries function fields) from the certified field
equalities: scalars (`vk_scalars_derived`), gates/queries via the pinned CS
(`vk_*_eq_derived` and `RichExpression.toExpr_ofExpr`), `permutationChunks`
(`vk_permutationChunks_derived`), and the two commitment families
(`commitments_derived`). -/
theorem vk_eq_derived : vk = derivedActionVk := by
  have hs := vk_scalars_derived
  simp only [Prod.mk.injEq] at hs
  obtain ⟨ho, hn, hb, hd, hc⟩ := hs
  have hg : actionPinnedCs.gates.map RichExpression.toExpr = vk.gates := by
    rw [← vk_gates_eq_derived, List.map_map]
    simp [Function.comp_def, RichExpression.toExpr_ofExpr]
  have hli : (fun l => (actionPinnedCs.lookupInputExprs.getD l.val []).map
      RichExpression.toExpr) = vk.lookupInputExprs := by
    funext l
    rw [← vk_lookupInputExprs_eq_derived, getD_map_ofFn, List.map_map]
    simp [Function.comp_def, RichExpression.toExpr_ofExpr]
  have hlt : (fun l => (actionPinnedCs.lookupTableExprs.getD l.val []).map
      RichExpression.toExpr) = vk.lookupTableExprs := by
    funext l
    rw [← vk_lookupTableExprs_eq_derived, getD_map_ofFn, List.map_map]
    simp [Function.comp_def, RichExpression.toExpr_ofExpr]
  have hfc : (fun i => derivedFixedCommitments.getD i 0) = vk.fixedCommitment := by
    rw [derivedFixedCommitments_eq]; rfl
  have hpp : (fun i : Fin shape.numPermutationColumns =>
      derivedPermutationCommonCommitments.getD i.val 0)
      = vk.permutationCommonCommitment := by
    rw [derivedPermutationCommonCommitments_eq]; rfl
  unfold vk derivedActionVk
  rw [VerifyingKey.mk.injEq]
  exact ⟨ho, hn, hb, hd, hc, hg.symm,
    vk_instanceQueryLayout_eq_derived, vk_adviceQueryLayout_eq_derived,
    vk_fixedQueryLayout_eq_derived, hfc.symm, hpp.symm, vk_permutationChunks_derived,
    hli.symm, hlt.symm⟩

assert_no_sorry commitments_derived
assert_no_sorry vk_eq_derived

end Zcash.Snark.VkCommit
