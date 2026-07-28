import Zcash.Snark.Fixtures.MaxShapeBounds
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity

/-!
# Consensus-maximum concrete inputs for the straight-line AGM capstone

The DLOG advantage remains an explicit finite-security profile.  This file evaluates only the
information-theoretic terms and records the exact five-bit work-factor arithmetic.
-/

namespace Zcash.Snark.FixtureMax

open Zcash.Arithmetic (card_Fp scalarFieldOrder)
open Zcash.Snark
open Zcash.Snark.ComputedStraightLineDeployedFSFamily (straightLineDlogGroupWork)
open scoped ENNReal

/-- Cross-multiplication helper for the concrete finite-field arithmetic. -/
private theorem ennreal_nat_div_le_one_div_straightLine {a p m : Nat}
    (hp : 0 < p) (hm : 0 < m) (h : a * m <= p) :
    (a : ENNReal) / p <= 1 / (m : ENNReal) := by
  apply (ENNReal.div_le_iff (Nat.cast_ne_zero.mpr hp.ne')
    (ENNReal.natCast_ne_top p)).2
  have hcast : (a : ENNReal) * (m : ENNReal) <= (p : ENNReal) := by exact_mod_cast h
  have hdiv := (ENNReal.le_div_iff_mul_le
    (Or.inl (Nat.cast_ne_zero.mpr hm.ne'))
    (Or.inl (ENNReal.natCast_ne_top m))).2 hcast
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using hdiv

/-- All straight-line statistical terms at the consensus maximum, excluding the supplied DLOG
advantage: `z=0`, the eleven IPA quadratics, six deployed roots, programmed-slot loss, and the
captured constraint-`x` root budget. -/
noncomputable def consensusStraightLineStatisticalModel (T : Nat) : ENNReal :=
  (T + 1 : Nat) * (1 / Fintype.card Fp) +
    (T + 1 : Nat) * (11 * (2 / (Fintype.card Fp : ENNReal))) +
    consensusPinnedRootMultiopenModel T +
    1 / Fintype.card Fp +
    (T + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal))

/-- Single-fraction form used for exact arithmetic. -/
theorem consensusStraightLineStatisticalModel_eq (T : Nat) :
    consensusStraightLineStatisticalModel T =
      (((T + 1) * (1 + 11 * 2 + 20470) +
          (T + 23) * 53_686_986_342_456 + 1 : Nat) : ENNReal) /
        Fintype.card Fp := by
  rw [consensusStraightLineStatisticalModel,
    consensusPinnedRootMultiopenModel_eq]
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- At the `2^122` adversary-work target, all non-DLOG terms together are below `2^-85`.
The dominant contribution is the deliberately conservative all-members multiopen root union. -/
theorem consensusStraightLineStatisticalModel_at_2pow122 :
    consensusStraightLineStatisticalModel (2 ^ 122) <=
      1 / (2 ^ 85 : ENNReal) := by
  rw [consensusStraightLineStatisticalModel_eq, card_Fp]
  convert ennreal_nat_div_le_one_div_straightLine
    (a := ((2 ^ 122 + 1) * (1 + 11 * 2 + 20470) +
      (2 ^ 122 + 23) * 53_686_986_342_456 + 1))
    (p := scalarFieldOrder) (m := 2 ^ 85)
    (by norm_num [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    (by norm_num)
    (by norm_num [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]) using 1
  norm_num

/-- Consensus-maximum straight-line **compressed-identity** capstone with the query cap `Q <= T`.
The right side is the caller-supplied finite-security DLOG advantage plus the concrete statistical
model above; row-level semantics are the four-budget promotion
`straightLineConstraintSemanticFailure_prob_le_of_generatorRO_dlogProfile`. -/
theorem straightLineConstraintFailure_prob_le_at_consensus_max
    (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily (shape orchardConsensusMaxProofs))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily
      ((20470 : Nat) / (Fintype.card Fp : ENNReal)))
    (profile : family.StraightLineConstraintDlogProfile B)
    {T : Nat} (hQ : family.Q <= T) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (shape orchardConsensusMaxProofs).k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (shape orchardConsensusMaxProofs) family.init.length 10 +
            3 * (shape orchardConsensusMaxProofs).k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B static) <=
      profile.advantage family.straightLineDlogRandomOracleQueries
          (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
        consensusStraightLineStatisticalModel T := by
  refine le_trans
    (family.straightLineConstraintFailure_prob_le_of_dlogProfile B static schedule profile) ?_
  rw [consensusStraightLineStatisticalModel]
  change _ <= profile.advantage family.straightLineDlogRandomOracleQueries
      (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
    ((T + 1 : Nat) * (1 / Fintype.card Fp) +
      (T + 1 : Nat) * (11 * (2 / (Fintype.card Fp : ENNReal))) +
      consensusPinnedRootMultiopenModel T +
      1 / Fintype.card Fp +
      (T + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal)))
  rw [consensusPinnedRootMultiopenModel]
  simp only [show (shape orchardConsensusMaxProofs).k = 11 from rfl]
  -- Relax `Q` to `T` in the capstone's own association, then reassociate the shared DLOG term.
  calc
    _ <= (T + 1 : Nat) * (1 / (Fintype.card Fp : ENNReal)) +
          (T + 1 : Nat) * (((11 : Nat) : ENNReal) * (2 / (Fintype.card Fp : ENNReal))) +
          ((T + 23 : Nat) : ENNReal) *
            algebraicRootBudget (shape orchardConsensusMaxProofs) 11 +
          (profile.advantage family.straightLineDlogRandomOracleQueries
              (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / (Fintype.card Fp : ENNReal)) +
          (T + 1 : Nat) * (((20470 : Nat) : ENNReal) / (Fintype.card Fp : ENNReal)) := by
      gcongr
    _ = _ := by push_cast; ring

/-- Generator-random-oracle form of the consensus-maximum straight-line **compressed-identity**
endpoint. -/
theorem straightLineConstraintFailure_prob_le_at_consensus_max_generatorRO
    {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (shape orchardConsensusMaxProofs).k) -> T')
    (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily (shape orchardConsensusMaxProofs))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily
      ((20470 : Nat) / (Fintype.card Fp : ENNReal)))
    (profile : family.StraightLineConstraintDlogProfile B)
    {T : Nat} (hQ : family.Q <= T) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (shape orchardConsensusMaxProofs) family.init.length 10 +
            3 * (shape orchardConsensusMaxProofs).k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) <=
      profile.advantage family.straightLineDlogRandomOracleQueries
          (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
        consensusStraightLineStatisticalModel T := by
  refine le_trans
    (family.straightLineConstraintFailure_prob_le_of_generatorRO_dlogProfile
      B hB query hquery static schedule profile) ?_
  rw [consensusStraightLineStatisticalModel]
  change _ <= profile.advantage family.straightLineDlogRandomOracleQueries
      (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
    ((T + 1 : Nat) * (1 / Fintype.card Fp) +
      (T + 1 : Nat) * (11 * (2 / (Fintype.card Fp : ENNReal))) +
      consensusPinnedRootMultiopenModel T +
      1 / Fintype.card Fp +
      (T + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal)))
  rw [consensusPinnedRootMultiopenModel]
  simp only [show (shape orchardConsensusMaxProofs).k = 11 from rfl]
  -- Relax `Q` to `T` in the capstone's own association, then reassociate the shared DLOG term.
  calc
    _ <= (T + 1 : Nat) * (1 / (Fintype.card Fp : ENNReal)) +
          (T + 1 : Nat) * (((11 : Nat) : ENNReal) * (2 / (Fintype.card Fp : ENNReal))) +
          ((T + 23 : Nat) : ENNReal) *
            algebraicRootBudget (shape orchardConsensusMaxProofs) 11 +
          (profile.advantage family.straightLineDlogRandomOracleQueries
              (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / (Fintype.card Fp : ENNReal)) +
          (T + 1 : Nat) * (((20470 : Nat) : ENNReal) / (Fintype.card Fp : ENNReal)) := by
      gcongr
    _ = _ := by push_cast; ring

/-- Concrete 122-bit work-factor package.  It combines the probability capstone, the `2^-85`
statistical bound, and the separately checked `2^127` solver-resource ceiling.  The DLOG advantage
at that solver cost remains the explicit cryptographic premise carried by `profile`. -/
theorem straightLine_consensus_2pow122_workFactor_generatorRO
    {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (shape orchardConsensusMaxProofs).k) -> T')
    (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily (shape orchardConsensusMaxProofs))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily
      ((20470 : Nat) / (Fintype.card Fp : ENNReal)))
    (profile : family.StraightLineFiveBitDlogProfile B (2 ^ 122)) :
    ((independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype
          (BTranscript Fp VestaG
            (preIpaLen (shape orchardConsensusMaxProofs) family.init.length 10 +
              3 * (shape orchardConsensusMaxProofs).k) -> Fp))).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            family.straightLineConstraintFailureEvent static) <=
        profile.advantage (2 ^ 127) (2 ^ 127) +
          1 / (2 ^ 85 : ENNReal)) ∧
      family.straightLineDlogRandomOracleQueries <= 2 ^ 127 ∧
      straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork <= 2 ^ 127 := by
  constructor
  · have hcost := profile.solverCost_at_2pow122
    refine le_trans
      (straightLineConstraintFailure_prob_le_at_consensus_max_generatorRO
        B hB query hquery family static schedule profile.toStraightLineConstraintDlogProfile
        profile.queryBound) ?_
    exact add_le_add
      (profile.advantage_mono hcost.1 hcost.2)
      consensusStraightLineStatisticalModel_at_2pow122
  · exact profile.solverCost_at_2pow122

/-- The final work-factor arithmetic used in prose: an explicit five-bit overhead takes the
`2^122` adversary target exactly to the `2^127` DLOG-solver scale. -/
theorem consensus_five_bit_overhead_at_2pow122 :
    32 * 2 ^ 122 = 2 ^ 127 :=
  ComputedStraightLineDeployedFSFamily.five_bit_overhead_at_2pow122

end Zcash.Snark.FixtureMax
