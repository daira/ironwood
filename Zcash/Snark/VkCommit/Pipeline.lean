import CompElliptic.Curves.Pasta
import Zcash.Bridge.VkProjection
import Zcash.Circuits.Fixtures.Layout
import Zcash.Circuits.TopLevelKeygen

/-!
# `FormalCircuit.toVerifierKey` — the circuit-side half of halo2 `keygen_vk`, assembled

The generic pipeline from a Clean `FormalCircuit` (+ a monomial URS) to the full
`VerifyingKey`: Clean's `Halo2.Keygen` derives the pinned constraint system, domain
exponent and selector map; this module adds the group-side half — the Lagrange-basis URS
by inverse FFT, the dense fixed columns from the derived layout, the keygen permutation
polynomials, and the `commit_lagrange` commitments — and assembles the record.
`VerifyingKey.ofOperations` is the `(cs, operations)` core; `FormalCircuit.toVerifierKey`
runs the bundle's `configure`/`synthesize` and delegates.

Everything here is pasta/Vesta-concrete (the group side stays ironwood-side by
maintainer ruling); the circuit-side inputs all come from the Clean package.

## Rust reference

* Lagrange URS: `poly/commitment.rs:75-88` (`Params::new`'s `g_lagrange`),
  `arithmetic.rs:192` (`best_fft` — bit-reversal + iterative Cooley–Tukey butterflies).
* `commit_lagrange` blind: `poly/commitment.rs:212-216` (`Blind::default() = Blind(F::ONE)`).
* Fixed commitments: `plonk/keygen.rs:230-240` (`keygen_vk`'s `fixed_commitments`).
* Permutation commitments: `plonk/permutation/keygen.rs:102-152` (`Assembly::build_vk`).
-/

namespace Zcash.Snark.VkCommit

open Zcash.Snark
open Bridge
open Halo2
open Zcash.Circuits.Fixtures

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Curves.Pasta in
/-- The verifier group, Vesta (`SWPoint Vesta.curve`) — the same concrete `G` the
fixtures instantiate. -/
abbrev G := SWPoint Vesta.curve

instance : Inhabited G := ⟨0⟩

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

/-- The Lagrange-basis generators of a monomial URS (length `2^k`): the monomial
generators transformed by an inverse FFT at `omega⁻¹ = alpha_inv` and scaled by
`n⁻¹ = TWO_INV^k = (2^k)⁻¹` — halo2's `g_lagrange` (`poly/commitment.rs:75-88`). -/
def _root_.Zcash.Snark.URS.gLagrange (urs : URS G) : List G :=
  let minv : Fp := ((2 : Fp) ^ urs.k)⁻¹
  (bestFftG (Array.ofFn urs.g) (omegaInvOf urs.k) urs.k).toList.map fun p => minv.val • p

/-! ## Generalized Lagrange commitment (`poly/commitment.rs:212-216`) -/

/-- Commit to a zero-padded Lagrange-coefficient column against a basis with
`Blind::default() = Blind(F::ONE)` (`poly/commitment.rs:212-216`):
`(∑ᵢ coeffsᵢ • basisᵢ) + w`. -/
def commitLagrangeWith (basis : List G) (w : G) (coeffs : List Fp) : G :=
  ((List.range coeffs.length).map
    (fun i => (coeffs.getD i 0).val • basis.getD i 0)).sum + w

/-! ## Derived fixed columns (`plonk/keygen.rs`) -/

/-- Scatter sparse `(col, row, natval)` triples into `numCols` dense length-`n` columns,
default `0` (`domain.empty_lagrange`); the `natval`s are `ZMod.val`s coerced back to `Fp`. -/
def denseColumns (n numCols : ℕ) (triples : List (ℕ × ℕ × ℕ)) : List (List Fp) := Id.run do
  let mut cols : Array (Array Fp) := Array.replicate numCols (Array.replicate n 0)
  for (c, r, v) in triples do
    if c < numCols then
      cols := cols.modify c (fun col => col.set! r ((v : ℕ) : Fp))
  return cols.toList.map Array.toList

/-- The derived V1 constants allocation `(value, col, row)` (`v1.rs:79-136`), over the
CS-recorded constants columns (`enable_constant` order). -/
def constantsOf (cs : ConstraintSystem Fp) (ops : Operations Fp) : List (ℕ × ℕ × ℕ) :=
  FloorPlanner.V1.constants (ZMod.val : Fp → ℕ) ops (cs.constants.map (·.index))

/-- The sparse fixed cells `(col, row, ZMod.val value)` at domain size `2^k`: loaded
tables + the constants column + packed selector columns + region `assign_fixed`s, deduped
and sorted — the layout recipe `TestVkLayoutAction` pins against the Rust dump, from
derived inputs. -/
def fixedSparseOf (selMap : Halo2.SelCompressMap) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List (ℕ × ℕ × ℕ) :=
  let starts := FloorPlanner.V1.starts ops
  let regions := (indexedRegions ops 0).1
  let usable := 2 ^ k - (cs.blindingFactors + 1)
  Layout.sortFixed (Layout.dedupFixed
    (Layout.tableFixed (ZMod.val : Fp → ℕ) usable ops
      ++ Layout.constantsFixed (constantsOf cs ops)
      ++ Layout.selectorFixed selMap (activations starts regions)
      ++ Layout.regionAssignFixed (ZMod.val : Fp → ℕ) starts regions))

/-- The derived fixed-column commitments — `commit_lagrange` of each dense fixed column
with the default blind (`plonk/keygen.rs:230-240`, `keygen_vk`'s `fixed_commitments`).
`numFixedColumns` is the post-compression count (the caller has the pinned CS in hand;
re-deriving it here would repeat the whole projection). -/
def fixedCommitmentsOf (basis : List G) (w : G) (selMap : Halo2.SelCompressMap)
    (numFixedColumns k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  (denseColumns (2 ^ k) numFixedColumns (fixedSparseOf selMap k cs ops)).map
    (commitLagrangeWith basis w)

/-! ## Derived permutation commitments (`plonk/permutation/keygen.rs:102-152`) -/

/-- The permutation columns as `ColRef`s in `enable_equality` order
(`cs.permutationColumns`) — the order the keygen `Assembly` mapping and the `δ^i` scaling
are indexed by, and the column shape `V1.copyList` resolves cells against. -/
def permColsOf (cs : ConstraintSystem Fp) : List Zcash.Circuits.Fixtures.ColRef :=
  cs.permutationColumns.map fun c =>
    match c.kind with
    | .advice => .advice c.index
    | .fixed => .fixed c.index
    | .instance => .instance c.index

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
(`build_vk`, `permutation/keygen.rs:135-146`), over the keygen `Assembly` mapping
(`Assembly::copy` replay, `Layout.runAssembly`) of the derived V1 copy list. -/
def permPolysOf (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    List (List Fp) :=
  let n := 2 ^ k
  let permCols := permColsOf cs
  let copyList := Layout.V1.copyList permCols (FloorPlanner.V1.starts ops) ops
    (constantsOf cs ops)
  let mapping := Layout.runAssembly n permCols.length copyList
  let omegaPows := omegaPowersArr (omegaOf k) n
  let deltaPows := deltaPowersArr deltaFp permCols.length
  (List.range permCols.length).map fun i =>
    (List.range n).map fun j =>
      let pij := (mapping[i]!)[j]!
      deltaPows[pij.1]! * omegaPows[pij.2]!

/-- The derived permutation common commitments — `commit_lagrange` of each permutation
polynomial with the default blind (`build_vk`, `permutation/keygen.rs:147-151`). -/
def permutationCommitmentsOf (basis : List G) (w : G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  (permPolysOf k cs ops).map (commitLagrangeWith basis w)

/-! ## Assembly -/

/-- The verifying key of a circuit given its keygen-view operation stream and a monomial
URS (which must be sized for the circuit, `urs.k = minimalK cs ops` — orchard's
`Params::new(K)`): the circuit-side half of halo2 `keygen_vk`. Every field is derived —
domain scalars from the minimal fitting exponent, gates/query layouts/lookups from the
pinned CS (carried across the `RichExpression → Expr` boundary), and the two commitment
families from the derived layout over the URS's Lagrange basis. -/
def _root_.Zcash.Snark.VerifyingKey.ofOperations (shape : Shape) (urs : URS G)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : VerifyingKey shape Fp G :=
  let k := minimalK cs ops
  let selMap := deriveSelCompressMap cs (2 ^ k)
    (activations (FloorPlanner.V1.starts ops) (indexedRegions ops 0).1)
  let pinned := PinnedConstraintSystem.derive cs selMap
  let basis := urs.gLagrange
  { omega := omegaOf k
    n := 2 ^ k
    blindingFactors := cs.blindingFactors
    delta := deltaFp
    chunkLen := cs.chunkLen
    gates := pinned.gates.map RichExpression.toExpr
    instanceQueryLayout := pinned.instanceQueryLayout
    adviceQueryLayout := pinned.adviceQueryLayout
    fixedQueryLayout := pinned.fixedQueryLayout
    fixedCommitment := fun i =>
      (fixedCommitmentsOf basis urs.w selMap pinned.numFixedColumns k cs ops).getD i 0
    permutationCommonCommitment := fun i =>
      (permutationCommitmentsOf basis urs.w k cs ops).getD i.val 0
    permutationChunks := permutationChunksOf selMap cs
    lookupInputExprs := fun l =>
      (pinned.lookupInputExprs.getD l.val []).map RichExpression.toExpr
    lookupTableExprs := fun l =>
      (pinned.lookupTableExprs.getD l.val []).map RichExpression.toExpr }

/-- Casting `ofOperations` along a shape equality is `ofOperations` at the other shape —
the record mentions the shape only in its `Fin`-domain types, never in a field value. -/
theorem ofOperations_cast {s₁ s₂ : Shape} (hs : s₁ = s₂) (urs : URS G)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    hs ▸ VerifyingKey.ofOperations s₁ urs cs ops
      = VerifyingKey.ofOperations s₂ urs cs ops := by
  cases hs; rfl

/-! ## The method form: `TopLevelCircuit.toVerifierKey` -/

/-- The two `Shape` counts that are genuinely proof-shape rather than circuit data: the
batch size and the multiopen point-set count. Everything else merges in derived
(`ProofParams.mergeDerived`). -/
structure ProofParams where
  numProofs : ℕ
  numPointSets : ℕ

open Zcash.Circuits in
/-- The `Shape` of a top-level circuit's proofs: the proof-shape counts merged with
everything the circuit derives — the domain exponent (`TopLevelCircuit.domainExponent`),
column/lookup/permutation counts from the configure-recorded constraint system, the
query counts from the derived pinned CS layouts (`TopLevelCircuit.pinnedCS`), the
verifier's permutation chunking `⌈columns / chunkLen⌉` (`permutation/verifier.rs:43-47`),
and the quotient split `cs.degree() − 1` (`vk.domain.get_quotient_poly_degree()`). -/
def ProofParams.mergeDerived (pp : ProofParams)
    {ConfigInput Config : Type} {Output : TypeMap} [CircuitType Output]
    (top : TopLevelCircuit Fp ConfigInput Config Output) : Shape :=
  let cs := top.constraintSystem
  let pinned := top.pinnedCS
  { k := top.domainExponent
    numProofs := pp.numProofs
    numAdviceColumns := cs.numAdviceColumns
    numLookups := cs.lookups.length
    numPermutationSets :=
      (cs.permutationColumns.length + cs.chunkLen - 1) / cs.chunkLen
    numPermutationColumns := cs.permutationColumns.length
    numQuotientPieces := csDegree cs - 1
    numInstanceQueries := pinned.instanceQueryLayout.length
    numAdviceQueries := pinned.adviceQueryLayout.length
    numFixedQueries := pinned.fixedQueryLayout.length
    numPointSets := pp.numPointSets }

/-- **The verifying key of a closed top-level circuit**: the `TopLevelCircuit` carries
its own `configInput` and unit input, so the only remaining inputs are the proof-shape
counts and the URS — `keygen_vk` at the `TopLevelCircuit` level, with the derived
`Shape` in the return type (no lawfulness side condition to discharge). -/
def _root_.Zcash.Circuits.TopLevelCircuit.toVerifierKey
    {ConfigInput Config : Type} {Output : TypeMap} [CircuitType Output]
    (top : Zcash.Circuits.TopLevelCircuit Fp ConfigInput Config Output)
    (pp : ProofParams) (urs : URS G) :
    VerifyingKey (pp.mergeDerived top) Fp G :=
  .ofOperations (pp.mergeDerived top) urs top.constraintSystem (top.operations 0)

end Zcash.Snark.VkCommit
