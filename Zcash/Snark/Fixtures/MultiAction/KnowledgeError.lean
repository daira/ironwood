import Zcash.Snark.Fixtures.MultiAction.StaticChecks
import Zcash.Snark.Fixtures.MultiAction.Schedule
import Zcash.Snark.Soundness.AGM.DirectX4Columns

/-!
# The deployed compressed-identity extraction bound at the captured key

`snarkConstraintsDeployed_prob_le_of_root_schedule` bounds extraction failure for the verifier's
compressed constraint identity by five additive terms. This module instantiates it at the captured
Post-NU6.3 key: the static checks and the schedule's degree caps are discharged from the verifying key
(`StaticChecks`, `Schedule`), so the bad-`x` term is the concrete `(Q + 1) · 20470 / |𝔽|` and
the multiopen term is the shape's own root budget — additive, with no continuation threshold or
fourth-root conversion. What remains named: single-instance DLOG for the combined finder (`hDL`)
and exact leave-one-squeeze invariance for both the root and constraint bad sets. Reverse
unbatching may use later challenges; only the answer currently being priced is excluded.
The captured premise pins only scalar metadata, layouts, and expressions. It intentionally does
not equate the family's verifier commitments with the fixture's fixed Vesta points: public AGM
points must instead carry representations over each sampled basis.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark
open scoped ENNReal

/-- **The deployed compressed-identity extraction bound at the captured key.** The rewind-free
capstone with the captured key's static checks and degree caps discharged: extraction failure for
that identity is at most the challenge-pricing terms, the tight DLOG term, the additive root budget,
and the concrete `(Q + 1) · 20470 / |𝔽|` bad-`x` term. Row-level semantics require the four
additional budgets of `snarkConstraintsSemanticDeployed_prob_le_of_root_schedule`. -/
theorem orchard_deployed_knowledge_error_captured
    {T' : Type*} [DecidableEq T'] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T') (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape)
    (hvk : ∀ basis, CapturedVerifierKeyProfile (family.vk basis))
    {dlogBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder family
        (deployedConstraintQuotientFinder family)) dlogBound)
    (hpinnedX : DeployedConstraintXPinning family) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily
            (deployedConstraintDecodedOfOutcome family
              (deployedConstraintOutcomeProviderOfRoot family
                (deployedConstraintStaticChecks_of_captured family hvk))))
      ≤ ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          (dlogBound + 1 / Fintype.card Fp))
        + (family.Q + (11 + shape.k) + 1 : ℕ) * algebraicRootBudget shape shape.k
        + (family.Q + 1 : ℕ) * ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞)) :=
  snarkConstraintsDeployed_prob_le_of_root_schedule B hB query hquery family
    (deployedConstraintStaticChecks_of_captured family hvk)
    (deployedConstraintXSqueezeSchedule_captured family hvk hpinnedX) hDL

/-- **The captured compressed-identity bound on the interpolation-free route.** The same capstone,
with the deployed root family built by `ofCovered`: its outcome is decoded from online coverage, so
the statement rests on no field-capacity premise and no offline interpolation — only single-instance
DLOG for the combined finder and exact leave-one-squeeze invariance for both root families. -/
theorem orchard_deployed_knowledge_error_captured_direct
    {T' : Type*} [DecidableEq T'] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T') (hquery : Function.Injective query)
    (online : ComputedOnlineMemberFSFamily shape)
    (hpinned : DeployedRootSqueezeInvariance online.toFamily
      (deployedRootOutcomeOfCovered online))
    (hvk : ∀ basis, CapturedVerifierKeyProfile
      ((ComputedDeployedRootFSFamily.ofCovered online hpinned).vk basis))
    {dlogBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder (ComputedDeployedRootFSFamily.ofCovered online hpinned)
        (deployedConstraintQuotientFinder
          (ComputedDeployedRootFSFamily.ofCovered online hpinned))) dlogBound)
    (hpinnedX : DeployedConstraintXPinning
      (ComputedDeployedRootFSFamily.ofCovered online hpinned)) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (ComputedDeployedRootFSFamily.ofCovered online hpinned).toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed
            (ComputedDeployedRootFSFamily.ofCovered online hpinned).toFamily
            (deployedConstraintDecodedOfOutcome _
              (deployedConstraintOutcomeProviderOfRoot _
                (deployedConstraintStaticChecks_of_captured _ hvk))))
      ≤ (((ComputedDeployedRootFSFamily.ofCovered online hpinned).Q + shape.k) *
            (3 / Fintype.card Fp) +
          ((ComputedDeployedRootFSFamily.ofCovered online hpinned).Q + 1 : ℕ) *
            (1 / Fintype.card Fp) +
          (dlogBound + 1 / Fintype.card Fp))
        + ((ComputedDeployedRootFSFamily.ofCovered online hpinned).Q + (11 + shape.k) + 1 : ℕ) *
            algebraicRootBudget shape shape.k
        + ((ComputedDeployedRootFSFamily.ofCovered online hpinned).Q + 1 : ℕ) *
            ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞)) :=
  orchard_deployed_knowledge_error_captured B hB query hquery _ hvk hDL hpinnedX

end Zcash.Snark.Fixture2
