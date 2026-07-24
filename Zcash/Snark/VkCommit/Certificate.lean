import Zcash.Snark.VkCommit.Derivation
import Zcash.Snark.Fixtures.SingleAction.VkMatch

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
  have hg : actionPinnedCs.gates.map RichExpression.toExpr = vk.gates := by
    rw [← vk_gates_eq_derived, List.map_map]
    simp [Function.comp_def, RichExpression.toExpr_ofExpr]
  have hli : (fun l =>
      (actionPinnedCs.lookupInputExprs.getD l.val []).map
        RichExpression.toExpr) = vk.lookupInputExprs := by
    funext l
    rw [← vk_lookupInputExprs_eq_derived, getD_map_ofFn, List.map_map]
    simp [Function.comp_def, RichExpression.toExpr_ofExpr]
  have hlt : (fun l =>
      (actionPinnedCs.lookupTableExprs.getD l.val []).map
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

assert_no_sorry commitments_derived
assert_no_sorry vk_eq_derived

end Zcash.Snark.VkCommit
