import Zcash.Snark.Fixtures.MaxShape
import Zcash.Snark.Soundness.Composition.AlgebraicRootBudget

/-!
# Concrete composite-bound inputs for the captured Orchard shape

This module specializes the pinned AGM root budget to the captured Orchard verifier
dimensions while leaving the adversary query count explicit.  The resulting term is additive;
there is no continuation threshold or fourth-root conversion in this path.
-/

namespace Zcash.Snark.FixtureMax

open Zcash.Snark
open scoped ENNReal

/-- Cross-multiplication for finite positive natural denominators, packaged for the concrete
arithmetic below. -/
private theorem ennreal_nat_div_le_one_div {a p m : ℕ} (hp : 0 < p) (hm : 0 < m)
    (h : a * m ≤ p) :
    (a : ℝ≥0∞) / p ≤ 1 / (m : ℝ≥0∞) := by
  apply (ENNReal.div_le_iff (Nat.cast_ne_zero.mpr hp.ne')
    (ENNReal.natCast_ne_top p)).2
  have hcast : (a : ℝ≥0∞) * (m : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast h
  have hdiv := (ENNReal.le_div_iff_mul_le
    (Or.inl (Nat.cast_ne_zero.mpr hm.ne'))
    (Or.inl (ENNReal.natCast_ne_top m))).2 hcast
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using hdiv

/-- The captured shape contributes fifty opening queries per action and forty-six shared queries. -/
theorem queryBudget_at_captured_shape (n : ℕ) :
    queryBudget (shape n) = 50 * n + 46 := by
  simp [queryBudget, shape]
  omega

/-! ## Pinned AGM root budget

The direct-root construction uses a conservative all-members/all-nodes union.  The wrapped
machine makes `11 + k = 22` extra reads and a one-squeeze root event costs
`Q + 22 + 1 = Q + 23` at `k = 11`.
-/

/-- The captured verifier shape has ample field capacity for the offline `x4` interpolation used by
the AGM decoder.  This is a structural fact, not a cryptographic assumption. -/
theorem interpolationCapacity_at_captured_shape (n : Nat) :
    (shape n).numPointSets + 1 <= Fintype.card Fp := by
  norm_num [shape, card_Fp, scalarFieldOrder,
    CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

/-- Exact conservative sum of all AGM root budgets at the consensus maximum. -/
theorem algebraicRootBudget_at_consensus_max :
    algebraicRootBudget (shape orchardConsensusMaxProofs) 11 =
      53_686_986_342_456 / (Fintype.card Fp : ENNReal) := by
  rw [algebraicRootBudget, queryBudget_at_captured_shape]
  norm_num [shape, orchardConsensusMaxProofs]

/-- The concrete multiopen contribution of the pinned-root theorem under `Q <= T`. -/
noncomputable def consensusPinnedRootMultiopenModel (T : Nat) : ENNReal :=
  (T + 23 : Nat) * algebraicRootBudget (shape orchardConsensusMaxProofs) 11

theorem consensusPinnedRootMultiopenModel_eq (T : Nat) :
    consensusPinnedRootMultiopenModel T =
      ((T + 23 : Nat) : ENNReal) * 53_686_986_342_456 / Fintype.card Fp := by
  rw [consensusPinnedRootMultiopenModel, algebraicRootBudget_at_consensus_max]
  simp only [div_eq_mul_inv]
  ring

/-- At `T = 2^122`, the conservative pinned-root term is still below `2^-86`.  This arithmetic
fact does not assume a generic-group formula for DLOG advantage. -/
theorem consensusPinnedRootMultiopenModel_at_2pow122 :
    consensusPinnedRootMultiopenModel (2 ^ 122) <= (1 / (2 ^ 86 : ENNReal)) := by
  rw [consensusPinnedRootMultiopenModel_eq, card_Fp]
  convert ennreal_nat_div_le_one_div
    (a := (2 ^ 122 + 23) * 53_686_986_342_456)
    (p := scalarFieldOrder) (m := 2 ^ 86)
    (by norm_num [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    (by norm_num)
    (by norm_num [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]) using 1 <;>
    norm_num

end Zcash.Snark.FixtureMax
