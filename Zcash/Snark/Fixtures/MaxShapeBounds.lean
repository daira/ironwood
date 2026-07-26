import Zcash.Snark.Fixtures.MaxShape
import Zcash.Snark.Soundness.Composition.ActionBudget
import Zcash.Snark.Soundness.Composition.AlgebraicRootBudget

/-!
# Concrete composite-bound inputs for the captured Orchard shape

The adaptive multiopen contribution in the composite soundness theorem is controlled by
`actionBudget`.  This module specializes that budget to the captured Orchard verifier dimensions
while leaving the action count explicit, then evaluates it at the consensus maximum.

These are exact symbolic values.  Turning the budget into a per-level threshold still uses the
current adaptive-coupling premise `s ≤ τ⁴`; the purpose of these lemmas is to make that concrete
loss visible at the deployed parameters.
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

/-- The exact numerator of the action budget at the captured shape. -/
theorem actionBudget_at_captured_shape (n : ℕ) :
    actionBudget (shape n) 11 =
      ((3 * (50 * n + 46) + max 2048 (50 * n + 46) + 10 : ℕ) : ℝ≥0∞) /
        Fintype.card Fp := by
  rw [actionBudget, queryBudget_at_captured_shape]
  simp [shape]
  simp only [div_eq_mul_inv]
  ring

/-- At the consensus maximum, the adaptive multiopen joint budget is exactly
`13_107_194 / |F_p|`. -/
theorem actionBudget_at_consensus_max :
    actionBudget (shape orchardConsensusMaxProofs) 11 =
      13_107_194 / (Fintype.card Fp : ℝ≥0∞) := by
  rw [actionBudget_at_captured_shape]
  norm_num [orchardConsensusMaxProofs]

/-- The current four-level coupling can use `τ = 2⁻⁵⁷` at the consensus maximum.  This is an
exact rational inequality over the deployed Vesta scalar-field order, not a floating-point
estimate. -/
theorem actionBudget_consensus_max_le_tau57_fourth :
    actionBudget (shape orchardConsensusMaxProofs) 11
      ≤ (1 / (2 ^ 57 : ℝ≥0∞)) *
          ((1 / (2 ^ 57 : ℝ≥0∞)) *
            ((1 / (2 ^ 57 : ℝ≥0∞)) * (1 / (2 ^ 57 : ℝ≥0∞)))) := by
  rw [actionBudget_at_consensus_max, card_Fp]
  have h := ennreal_nat_div_le_one_div
    (a := 13_107_194) (p := scalarFieldOrder) (m := 2 ^ 228)
    (by norm_num [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    (by norm_num)
    (by norm_num [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
  have hpow :
      (1 / (2 ^ 57 : ℝ≥0∞)) *
          ((1 / (2 ^ 57 : ℝ≥0∞)) *
            ((1 / (2 ^ 57 : ℝ≥0∞)) * (1 / (2 ^ 57 : ℝ≥0∞))))
        = 1 / (2 ^ 228 : ℝ≥0∞) := by
    simp only [one_div]
    rw [← ENNReal.mul_inv (by norm_num) (by norm_num),
      ← ENNReal.mul_inv (by norm_num) (by norm_num),
      ← ENNReal.mul_inv (by norm_num) (by norm_num)]
    norm_num
  rw [hpow]
  change (13_107_194 : ℝ≥0∞) / (scalarFieldOrder : ℝ≥0∞)
    ≤ 1 / (2 ^ 228 : ℝ≥0∞)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

/-! ## Conditional time-success comparison for the additive target

The following definitions do not assert a quantitative DLOG theorem.  They make the usual
external generic-group model explicit: an adversary of work `T` has single-instance DLOG
advantage at most `T^2 / |Fp|`.  At `k = 11`, the proved DLR-to-DLOG reduction multiplies that
advantage by `2^11 + 2 = 2050`.

The additive multiopen target uses `Q <= T` and the wrapped query overhead
`11 + k + 4 = 26`.  Its contribution is therefore at most
`(T + 26) * 13_107_194 / |Fp|` at the consensus maximum.
-/

/-- The desired additive multiopen contribution under `Q <= T`, specialized to the captured
depth and consensus-maximum action count. -/
noncomputable def consensusAdditiveMultiopenModel (T : ℕ) : ℝ≥0∞ :=
  (T + 26 : ℕ) * actionBudget (shape orchardConsensusMaxProofs) 11

/-- The DLOG contribution under the *conditional* generic model
`epsilon_DL(T) = T^2 / |Fp|`, including the proved factor `2^11 + 2 = 2050`. -/
noncomputable def genericDlogContributionModel (T : ℕ) : ℝ≥0∞ :=
  2050 * (((T : ℝ≥0∞) * T) / Fintype.card Fp)

/-- Exact closed form of the additive target at the consensus maximum. -/
theorem consensusAdditiveMultiopenModel_eq (T : ℕ) :
    consensusAdditiveMultiopenModel T =
      ((T + 26 : ℕ) : ℝ≥0∞) * 13_107_194 / Fintype.card Fp := by
  rw [consensusAdditiveMultiopenModel, actionBudget_at_consensus_max]
  simp only [div_eq_mul_inv]
  ring

/-- Beyond `2^14` work, the desired additive multiopen term is no larger than the DLOG term in
the stated generic model.  Below that crossover both terms are far below one; the next theorem
checks the security-scale endpoint directly. -/
theorem consensusAdditiveMultiopenModel_le_genericDlogContributionModel
    (T : ℕ) (hT : 2 ^ 14 ≤ T) :
    consensusAdditiveMultiopenModel T ≤ genericDlogContributionModel T := by
  have h1 : T + 26 ≤ 2 * T := by omega
  have h2 : 2 * 13_107_194 ≤ 2050 * T := by omega
  have hnum : (T + 26) * 13_107_194 ≤ 2050 * (T * T) := by
    calc
      (T + 26) * 13_107_194 ≤ (2 * T) * 13_107_194 :=
        Nat.mul_le_mul_right 13_107_194 h1
      _ = T * (2 * 13_107_194) := by ring
      _ ≤ T * (2050 * T) := Nat.mul_le_mul_left T h2
      _ = 2050 * (T * T) := by ring
  rw [consensusAdditiveMultiopenModel_eq, genericDlogContributionModel]
  have hcast : (((T + 26) * 13_107_194 : ℕ) : ℝ≥0∞)
      ≤ ((2050 * (T * T) : ℕ) : ℝ≥0∞) := by exact_mod_cast hnum
  calc
    ((T + 26 : ℕ) : ℝ≥0∞) * 13_107_194 / Fintype.card Fp
        = (((T + 26) * 13_107_194 : ℕ) : ℝ≥0∞) / Fintype.card Fp := by
            norm_num
    _ ≤ ((2050 * (T * T) : ℕ) : ℝ≥0∞) / Fintype.card Fp := by gcongr
    _ = 2050 * (((T : ℝ≥0∞) * T) / Fintype.card Fp) := by
          push_cast
          simp only [div_eq_mul_inv]
          ring

/-- At `T = 2^122`, where the modeled factor-2050 DLOG term is already order one, the desired
additive multiopen term is still below `2^-107`.  This is exact rational arithmetic over the
deployed field order; only the interpretation of the DLOG curve is conditional. -/
theorem consensusAdditiveMultiopenModel_at_dlog_scale :
    consensusAdditiveMultiopenModel (2 ^ 122) ≤ (1 / (2 ^ 107 : ℝ≥0∞)) := by
  rw [consensusAdditiveMultiopenModel_eq, card_Fp]
  convert ennreal_nat_div_le_one_div
    (a := (2 ^ 122 + 26) * 13_107_194) (p := scalarFieldOrder) (m := 2 ^ 107)
    (by norm_num [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    (by norm_num)
    (by norm_num [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]) using 1 <;>
    norm_num

/-! ## Prefix-pinned AGM root budget

The final direct-root construction uses a conservative all-members/all-nodes union.  This is
larger than the old per-member `actionBudget`, but it is paid linearly rather than through a
fourth root.  The wrapped machine makes `11 + k = 22` extra reads and a one-squeeze root event
costs `Q + 22 + 1 = Q + 23` at `k = 11`.
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

/-- The concrete multiopen contribution of the prefix-pinned root theorem under `Q <= T`. -/
noncomputable def consensusPinnedRootMultiopenModel (T : Nat) : ENNReal :=
  (T + 23 : Nat) * algebraicRootBudget (shape orchardConsensusMaxProofs) 11

theorem consensusPinnedRootMultiopenModel_eq (T : Nat) :
    consensusPinnedRootMultiopenModel T =
      ((T + 23 : Nat) : ENNReal) * 53_686_986_342_456 / Fintype.card Fp := by
  rw [consensusPinnedRootMultiopenModel, algebraicRootBudget_at_consensus_max]
  simp only [div_eq_mul_inv]
  ring

/-- Even with the conservative quadratic shape budget, DLOG dominates from `2^36` work onward
in the explicitly conditional generic model. -/
theorem consensusPinnedRootMultiopenModel_le_genericDlogContributionModel
    (T : Nat) (hT : 2 ^ 36 <= T) :
    consensusPinnedRootMultiopenModel T <= genericDlogContributionModel T := by
  have h1 : T + 23 <= 2 * T := by omega
  have h2 : 2 * 53_686_986_342_456 <= 2050 * T := by omega
  have hnum : (T + 23) * 53_686_986_342_456 <= 2050 * (T * T) := by
    calc
      (T + 23) * 53_686_986_342_456 <= (2 * T) * 53_686_986_342_456 :=
        Nat.mul_le_mul_right 53_686_986_342_456 h1
      _ = T * (2 * 53_686_986_342_456) := by ring
      _ <= T * (2050 * T) := Nat.mul_le_mul_left T h2
      _ = 2050 * (T * T) := by ring
  rw [consensusPinnedRootMultiopenModel_eq, genericDlogContributionModel]
  have hcast : ((((T + 23) * 53_686_986_342_456 : Nat)) : ENNReal)
      <= ((2050 * (T * T) : Nat) : ENNReal) := by exact_mod_cast hnum
  calc
    ((T + 23 : Nat) : ENNReal) * 53_686_986_342_456 / Fintype.card Fp
        = (((T + 23) * 53_686_986_342_456 : Nat) : ENNReal) / Fintype.card Fp := by
            norm_num
    _ <= ((2050 * (T * T) : Nat) : ENNReal) / Fintype.card Fp := by gcongr
    _ = 2050 * (((T : ENNReal) * T) / Fintype.card Fp) := by
          push_cast
          simp only [div_eq_mul_inv]
          ring

/-- At the modeled DLOG scale, the conservative pinned-root term is still below `2^-86`. -/
theorem consensusPinnedRootMultiopenModel_at_dlog_scale :
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
