import Zcash.Snark.Fixtures.MultiAction.StaticChecks
import Zcash.Snark.Fixtures.MultiAction.Schedule
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity

/-!
# Captured-key straight-line AGM knowledge-error endpoint

This is parallel to `MultiAction.KnowledgeError`: the existing file retains the recursive AFK
capstone, while this file selects the fixed-call straight-line relation finder.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark
open scoped ENNReal

/-- Captured-key straight-line AGM capstone.  The family supplies the staged IPA representation
trace and deployed root chronology; the captured key discharges the static checks and degree
budget.  The only computational term is the explicit finite-security Vesta DLOG profile. -/
theorem orchard_deployed_knowledge_error_captured_straightLine
    (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (hvk : forall basis, family.vk basis = vk)
    (profile : family.StraightLineConstraintDlogProfile B)
    (hpinned : forall basis
      (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
      (v : Fp),
      deployedConstraintXBadSet family.toRootFamily basis
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 4) v) =
        deployedConstraintXBadSet family.toRootFamily basis O) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B
          (deployedConstraintStaticChecks_of_captured family.toRootFamily hvk)) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (profile.advantage family.straightLineDlogRandomOracleQueries
            (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          ((20470 : Nat) / (Fintype.card Fp : ENNReal)) :=
  family.straightLineConstraintFailure_prob_le_of_dlogProfile B
    (deployedConstraintStaticChecks_of_captured family.toRootFamily hvk)
    (deployedConstraintXSqueezeSchedule_captured family.toRootFamily hvk hpinned) profile

/-- Generator-random-oracle form of the captured straight-line endpoint. -/
theorem orchard_deployed_knowledge_error_captured_straightLine_generatorRO
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (hvk : forall basis, family.vk basis = vk)
    (profile : family.StraightLineConstraintDlogProfile B)
    (hpinned : forall basis
      (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
      (v : Fp),
      deployedConstraintXBadSet family.toRootFamily basis
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 4) v) =
        deployedConstraintXBadSet family.toRootFamily basis O) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent
            (deployedConstraintStaticChecks_of_captured family.toRootFamily hvk)) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (profile.advantage family.straightLineDlogRandomOracleQueries
            (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          ((20470 : Nat) / (Fintype.card Fp : ENNReal)) :=
  family.straightLineConstraintFailure_prob_le_of_generatorRO_dlogProfile
    B hB query hquery (deployedConstraintStaticChecks_of_captured family.toRootFamily hvk)
    (deployedConstraintXSqueezeSchedule_captured family.toRootFamily hvk hpinned) profile

end Zcash.Snark.Fixture2
