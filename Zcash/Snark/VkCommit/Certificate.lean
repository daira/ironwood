import Zcash.Snark.VkCommit.Derivation
import Zcash.Snark.VkCommit.Pipeline
import Zcash.Snark.Fixtures.SingleAction.VkMatch
import Zcash.Circuits.Action.TopLevel

/-!
# Concrete certificate for the derived Action verifying key

This module contains the expensive concrete computation, separately from the
reusable derivation data. The `ZcashVkCommit` target builds it explicitly; ordinary
clients of `derivedActionVk` only need `Derivation`.
-/

namespace Zcash.Snark.VkCommit

open Zcash.Snark
open Zcash.Snark.Fixture
open Halo2

/-!
One `native_decide` shares the FFT, fixed contents, and keygen mapping across the
Lagrange-prefix cross-check and all 44 commitments. The record equality is then
proved field-wise because the verifying key contains function fields.
-/

/-- **The derived commitment data matches the capture**: the Lagrange URS prefix,
the 29 fixed-column commitments, and the 15 permutation common commitments. -/
theorem commitments_derived :
    ((derivedUrsGLagrange capturedURS).take capturedUrsGLagrange.length,
     derivedFixedCommitments capturedURS,
     derivedPermutationCommonCommitments capturedURS)
    = (capturedUrsGLagrange, capturedFixedCommitments,
       capturedPermutationCommonCommitments) := by
  native_decide

/-- The derived Lagrange URS reproduces the captured 10-generator prefix. -/
theorem derivedUrsGLagrange_prefix_eq :
    (derivedUrsGLagrange capturedURS).take capturedUrsGLagrange.length =
      capturedUrsGLagrange := by
  have h := commitments_derived
  simp only [Prod.mk.injEq] at h
  exact h.1

/-- The derived fixed-column commitments are the captured ones. -/
theorem derivedFixedCommitments_eq :
    derivedFixedCommitments capturedURS = capturedFixedCommitments := by
  have h := commitments_derived
  simp only [Prod.mk.injEq] at h
  exact h.2.1

/-- The derived permutation common commitments are the captured ones. -/
theorem derivedPermutationCommonCommitments_eq :
    derivedPermutationCommonCommitments capturedURS =
      capturedPermutationCommonCommitments := by
  have h := commitments_derived
  simp only [Prod.mk.injEq] at h
  exact h.2.2

/-- `((List.ofFn f).map g).getD` at an in-range `Fin` index is `g (f l)`. -/
private theorem getD_map_ofFn
    {α β : Type} {n : ℕ} (f : Fin n → α) (g : α → β)
    (l : Fin n) (d : β) :
    ((List.ofFn f).map g).getD l.val d = g (f l) := by
  simp [List.getD_eq_getElem?_getD, l.isLt]

/-- **The captured Action verifying key is fully derived.** -/
theorem vk_eq_derived : vk = derivedActionVk shape capturedURS := by
  have hs := vk_scalars_derived
  simp only [Prod.mk.injEq] at hs
  obtain ⟨ho, hn, hb, hd, hc⟩ := hs
  -- the `have`s are stated over `Fixture.actionPinnedCs` (what the `VkMatch` lemmas
  -- speak about); the final `exact` bridges to the definitionally-equal
  -- `VkCommit.actionPinnedCs` inside `derivedActionVk`
  have hg : Fixture.actionPinnedCs.gates.map RichExpression.toExpr = vk.gates := by
    rw [← vk_gates_eq_derived, List.map_map]
    simp [Function.comp_def, RichExpression.toExpr_ofExpr]
  have hli : (fun l =>
      (Fixture.actionPinnedCs.lookupInputExprs.getD l.val []).map
        RichExpression.toExpr) = vk.lookupInputExprs := by
    funext l
    rw [← vk_lookupInputExprs_eq_derived, getD_map_ofFn, List.map_map]
    simp [Function.comp_def, RichExpression.toExpr_ofExpr]
  have hlt : (fun l =>
      (Fixture.actionPinnedCs.lookupTableExprs.getD l.val []).map
        RichExpression.toExpr) = vk.lookupTableExprs := by
    funext l
    rw [← vk_lookupTableExprs_eq_derived, getD_map_ofFn, List.map_map]
    simp [Function.comp_def, RichExpression.toExpr_ofExpr]
  have hfc :
      (fun i => (derivedFixedCommitments capturedURS).getD i 0) =
        vk.fixedCommitment := by
    rw [derivedFixedCommitments_eq]
    rfl
  have hpp :
      (fun i : Fin shape.numPermutationColumns =>
        (derivedPermutationCommonCommitments capturedURS).getD i.val 0) =
          vk.permutationCommonCommitment := by
    rw [derivedPermutationCommonCommitments_eq]
    rfl
  unfold vk derivedActionVk
  rw [VerifyingKey.mk.injEq]
  exact ⟨ho, hn, hb, hd, hc, hg.symm,
    vk_instanceQueryLayout_eq_derived,
    vk_adviceQueryLayout_eq_derived,
    vk_fixedQueryLayout_eq_derived,
    hfc.symm, hpp.symm, vk_permutationChunks_derived,
    hli.symm, hlt.symm⟩

/-! ## The method form, certified -/

open Zcash.Circuits.Action (orchardActionTopLevelCircuit)

/-- The Action circuit's proof-shape parameters — the only two `Shape` counts that are
not circuit data (orchard: one Action proof per statement, five multiopen point sets). -/
def actionProofParams : ProofParams := { numProofs := 1, numPointSets := 5 }

/-- The fixture's `Shape` is the proof-shape parameters merged with the circuit-derived
counts — certifying every derived `Shape` field (domain exponent, column/lookup/
permutation/query counts, chunking, quotient split) against the capture's. -/
theorem shape_eq_mergeDerived :
    actionProofParams.mergeDerived orchardActionTopLevelCircuit = shape := by
  native_decide

/-- **`vk = derivedActionVk (actionProofParams.mergeDerived …) capturedURS`** — the
captured Orchard Action verifying key IS the derived verifying key at the derived
`Shape` (transported along `shape_eq_mergeDerived`) and the captured URS: every field,
including the `Shape` in the type, comes from the circuit plus the URS and the two
proof-shape counts. -/
theorem vk_eq_toVerifierKey :
    vk = shape_eq_mergeDerived
      ▸ derivedActionVk
          (actionProofParams.mergeDerived orchardActionTopLevelCircuit) capturedURS := by
  rw [vk_eq_derived]
  exact (derivedActionVk_cast shape_eq_mergeDerived capturedURS).symm

assert_no_sorry commitments_derived
assert_no_sorry vk_eq_derived
assert_no_sorry vk_eq_toVerifierKey

end Zcash.Snark.VkCommit
