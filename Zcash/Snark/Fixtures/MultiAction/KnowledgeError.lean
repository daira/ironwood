import Zcash.Snark.Fixtures.MultiAction.StaticChecks
import Zcash.Snark.Fixtures.MultiAction.Schedule

/-!
# The deployed knowledge-error bound at the captured key

`snarkConstraintsDeployed_prob_le_of_root_schedule` bounds deployed extraction failure by five
additive terms. This module instantiates it at the captured Post-NU6.3 key: the static checks
and the schedule's degree caps are discharged from the captured verifying key
(`StaticChecks`, `Schedule`), so the bad-`x` term is the concrete `(Q + 1) · 20470 / |𝔽|` and
the multiopen term is the shape's own root budget — additive, with no continuation threshold or
fourth-root conversion. What remains named: single-instance DLOG for the combined finder
(`hDL`), and the `x`-squeeze pinning premise the schedule carries (`hpinned`); the family's own
root-event invariance travels inside `ComputedDeployedRootFSFamily`.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark
open scoped ENNReal

/-- **The deployed knowledge-error bound at the captured key.** The rewind-free capstone with
the captured key's static checks and degree caps discharged: extraction failure is at most the
challenge-pricing terms, the tight DLOG term, the additive root budget, and the concrete
`(Q + 1) · 20470 / |𝔽|` bad-`x` term. -/
theorem orchard_deployed_knowledge_error_captured
    {T' : Type*} [DecidableEq T'] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T') (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape)
    (hvk : ∀ basis, family.vk basis = vk)
    {dlogBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder family
        (deployedConstraintQuotientFinder family)) dlogBound)
    (hpinned : ∀ basis
      (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
      (v : Fp),
      deployedConstraintXBadSet family basis
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 4) v) =
        deployedConstraintXBadSet family basis O) :
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
    (deployedConstraintXSqueezeSchedule_captured family hvk hpinned) hDL

end Zcash.Snark.Fixture2
