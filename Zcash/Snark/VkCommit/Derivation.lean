import Zcash.Snark.VkCommit.Pipeline
import Zcash.Snark.Fixtures.SingleAction.VkMatch
import Zcash.Circuits.Action.TopLevel

/-!
# The Action verifying key, fully derived: `vk = orchardActionTopLevelCircuit.toVerifierKey …`

Instantiates the generic `toVerifierKey` pipeline (`Pipeline.lean`) at the bundled
Orchard Action circuit and the captured URS, and certifies the two commitment families —
`fixedCommitment` (29 fixed columns) and `permutationCommonCommitment` (15 permutation
columns) — against the capture. Together with the already-certified scalar, gate, layout
and permutation-chunk fields (`VkMatch`, `PinnedCsMatch`), this proves the endgame
statement `vk_eq_toVerifierKey : vk = shape_eq_mergeDerived ▸
orchardActionTopLevelCircuit.toVerifierKey actionProofParams capturedURS` — every field
of the captured verifying key is derived from the circuit, with the URS and the two
proof-shape counts (`ProofParams`) as the only non-circuit inputs; the derived `Shape`
rides in the return type.

## Certification cost (why this target is non-default)

`commitments_derived` certifies the whole derivation (inverse FFT + `n⁻¹` scaling +
dense column reconstruction + keygen mapping + blind convention) by ONE bundled
`native_decide`. Measured baseline: a single-column probe cost **1291 s wall, 6.9 GB
peak RSS** — dominated by the fixed cost every `native_decide` in this file pays
(native codegen of the ~2110-point fixture closure) plus the Lagrange FFT and one
2^11-term Vesta MSM, all under the naive `ZMod.val • point` binary scalar
multiplication with affine (inversion-per-add) point arithmetic; the full bundle
(29 + 15 commitments + the Lagrange-prefix cross-check) measured **1 h 38 min wall,
7.0 GB RSS**. Maintainer-accepted as a known annoyance: this target (`ZcashVkCommit`,
see `lakefile.toml`) is excluded from `defaultTargets` so the default build stays fast,
and the acceleration path is a Pippenger bucket MSM + projective coordinates + faster
certified field arithmetic (the dominant cost today is one field inversion per affine
point-add inside the binary `ZMod.val • point` scalar multiplication).
-/

namespace Zcash.Snark.VkCommit

open Zcash.Snark
open Zcash.Snark.Fixture
open Bridge
open Halo2
open Zcash.Circuits.Fixtures
open Zcash.Circuits.Action (orchardActionTopLevelCircuit)

/-! ## The derived commitment data, at the Action circuit

Each definition is spelled as the exact instantiation of the `Pipeline.lean` generic it
mirrors, so `derivedActionVk` below is definitionally the generic pipeline core's
output (`derivedActionVk_eq_ofOperations` is `rfl`). -/

/-- The derived Lagrange-basis URS generators (length `2^actionK = 2048`), from the
captured monomial generators (`URS.gLagrange`). `commitments_derived` cross-checks the
captured 10-generator prefix directly and certifies the rest through the commitments. -/
def derivedUrsGLagrange : List G := capturedURS.gLagrange

/-- The derived fixed-column commitments (`fixedCommitmentsOf`, `plonk/keygen.rs:230-240`).
All 29 are certified equal to the capture in `commitments_derived`. -/
def derivedFixedCommitments : List G :=
  fixedCommitmentsOf derivedUrsGLagrange capturedURS.w (actionSelMapDerived (2 ^ actionK))
    actionPinnedCs.numFixedColumns actionK actionCS actionOperations

/-- The derived permutation common commitments (`permutationCommitmentsOf`,
`permutation/keygen.rs:102-152` `build_vk`). Certified against the capture in
`commitments_derived`. -/
def derivedPermutationCommonCommitments : List G :=
  permutationCommitmentsOf derivedUrsGLagrange capturedURS.w actionK actionCS
    actionOperations

/-! ## The fully-derived Action verifying key -/

/-- The Action `VerifyingKey` with EVERY field derived from the circuit (+ the captured
URS for the two commitment families): domain/permutation scalars from
`actionK`/`actionCS`/pasta constants (certified equal to the capture's in
`vk_scalars_derived`), gates and query layouts from `actionPinnedCs`
(`capturedPinnedCs_eq_derived`) carried back across the `RichExpression → Expr` boundary
by `RichExpression.toExpr`, `permutationChunks` from the derived selector map
(`vk_permutationChunks_derived`), and the commitment families from
`derivedFixedCommitments`/`derivedPermutationCommonCommitments`. Definitionally the
generic pipeline core's output at the Action circuit (`derivedActionVk_eq_ofOperations`);
the record equality with the capture is `vk_eq_derived` below. -/
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
record has function fields). Maintainer-accepted cost (this module's build runs
~1 h 40 min; see the module docstring), quarantined in the non-default `ZcashVkCommit`
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

/-! ## The method form -/

set_option maxRecDepth 1000000 in
/-- The explicit derived record is definitionally the generic pipeline core's output at
the Action circuit — every field of `derivedActionVk` is spelled as the exact
instantiation of `VerifyingKey.ofOperations`' fields. -/
theorem derivedActionVk_eq_ofOperations :
    derivedActionVk
      = VerifyingKey.ofOperations shape capturedURS actionCS actionOperations := rfl

/-- The Action circuit's proof-shape parameters — the only two `Shape` counts that are
not circuit data (orchard: one Action proof per statement, five multiopen point sets). -/
def actionProofParams : ProofParams := { numProofs := 1, numPointSets := 5 }

/-- The fixture's `Shape` is the proof-shape parameters merged with the circuit-derived
counts — certifying every derived `Shape` field (domain exponent, column/lookup/
permutation/query counts, chunking, quotient split) against the capture's. -/
theorem shape_eq_mergeDerived :
    actionProofParams.mergeDerived orchardActionTopLevelCircuit = shape := by
  native_decide

set_option maxRecDepth 1000000 in
/-- **`vk = orchardActionTopLevelCircuit.toVerifierKey actionProofParams capturedURS`**
— the captured Orchard Action verifying key IS the closed circuit's derived verifying
key at the captured URS: `keygen_vk` at the `TopLevelCircuit` level, certified end to
end, with the derived `Shape` carried in the type (cast along
`shape_eq_mergeDerived`). -/
theorem vk_eq_toVerifierKey :
    vk = shape_eq_mergeDerived
      ▸ orchardActionTopLevelCircuit.toVerifierKey actionProofParams capturedURS := by
  rw [vk_eq_derived, derivedActionVk_eq_ofOperations]
  exact (ofOperations_cast shape_eq_mergeDerived capturedURS _ _).symm

assert_no_sorry commitments_derived
assert_no_sorry vk_eq_derived
assert_no_sorry vk_eq_toVerifierKey

end Zcash.Snark.VkCommit
