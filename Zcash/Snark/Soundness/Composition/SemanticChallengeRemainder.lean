import Zcash.Snark.Soundness.ChallengePricing

/-!
# The semantic challenge remainder

The compressed-identity capstones price the multiopen and IPA events.  The Action-level statement
additionally needs the *semantic* challenge exclusions: the `y` fold split, the permutation `β`
and `γ` resolvers, and the lookup `β`, `γ` and `θ` resolvers.  `ChallengePricing` bounds each
exclusion set; this module prices the bundle-wide unions those exclusions are stated against and
adds them into one remainder.

The terms are kept separate and named because they are *not* known to fit inside the compressed
model's existing ceiling: each is a count of circuit-sized quantities over `|Fp|`, so the total
has to be evaluated at the deployed shape before any end-to-end exponent is claimed.

Each challenge is its own squeeze, so the events are priced independently and added.  That is the
same accounting the deployed capstones already use for their separate squeezes.
-/

namespace Zcash.Snark

open scoped ENNReal
open Finset

variable {shape : Shape} {G : Type*}

/-! ## Bundle-wide permutation exclusions -/

/-- The bundle-wide permutation `γ` exclusion costs the summed cell counts, doubled. -/
theorem allResolverPermutationGammaBadSet_measure_le
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ) :
    uniformChallenge.toOuterMeasure (allResolverPermutationGammaBadSet vk ch poly m) ≤
      ((∑ p : Fin shape.numProofs,
        2 * Fintype.card (ResolverPermutationCell vk poly p m) : ℕ) : ℝ≥0∞) /
        Fintype.card Fp := by
  refine le_trans (le_of_eq (uniformChallenge_badSet _)) (ENNReal.div_le_div_right ?_ _)
  exact_mod_cast le_trans (Finset.card_biUnion_le)
    (Finset.sum_le_sum fun p _ => resolverPermutationGammaBadSet_card_le vk ch poly p m)

/-- The bundle-wide permutation `β` exclusion costs the summed quadratic cell counts. -/
theorem allResolverPermutationBetaBadSet_measure_le
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ) :
    uniformChallenge.toOuterMeasure (allResolverPermutationBetaBadSet vk poly m) ≤
      ((∑ p : Fin shape.numProofs,
        (Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
          Fintype.card (ResolverPermutationCell vk poly p m) : ℕ) : ℝ≥0∞) /
        Fintype.card Fp := by
  refine le_trans (le_of_eq (uniformChallenge_badSet _)) (ENNReal.div_le_div_right ?_ _)
  exact_mod_cast le_trans (Finset.card_biUnion_le)
    (Finset.sum_le_sum fun p _ => resolverPermutationBetaBadSet_card_le vk poly p m)

/-! ## Bundle-wide lookup exclusions -/

/-- The bundle-wide lookup `γ` exclusion costs `2(u+1)` per (proof, lookup) pair. -/
theorem allResolverLookupGammaBadSet_measure_le
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (u : ℕ) :
    uniformChallenge.toOuterMeasure (allResolverLookupGammaBadSet vk ch poly u) ≤
      ((shape.numProofs * shape.numLookups * (2 * (u + 1)) : ℕ) : ℝ≥0∞) / Fintype.card Fp := by
  refine le_trans (le_of_eq (uniformChallenge_badSet _)) (ENNReal.div_le_div_right ?_ _)
  refine_lift Nat.cast_le.mpr ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  refine le_trans (Finset.sum_le_sum fun q _ =>
    resolverLookupGammaBadSet_card_le vk ch poly q.1 q.2 u) ?_
  simp [Finset.sum_const, Fintype.card_prod, Nat.mul_assoc]

/-- The bundle-wide lookup `β` exclusion costs `(u+2)(u+1) + (u+1)` per pair. -/
theorem allResolverLookupBetaBadSet_measure_le
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (u : ℕ) :
    uniformChallenge.toOuterMeasure (allResolverLookupBetaBadSet vk ch poly u) ≤
      ((shape.numProofs * shape.numLookups * ((u + 2) * (u + 1) + (u + 1)) : ℕ) : ℝ≥0∞) /
        Fintype.card Fp := by
  refine le_trans (le_of_eq (uniformChallenge_badSet _)) (ENNReal.div_le_div_right ?_ _)
  refine_lift Nat.cast_le.mpr ?_
  refine le_trans (Finset.card_biUnion_le) ?_
  refine le_trans (Finset.sum_le_sum fun q _ =>
    resolverLookupBetaBadSet_card_le vk ch poly q.1 q.2 u) ?_
  simp [Finset.sum_const, Fintype.card_prod, Nat.mul_assoc]

/-! ## The remainder -/

/-- **The Action-level semantic challenge remainder.**  The `y` fold-split term, the permutation
`β`/`γ` terms and the lookup `β`/`γ` terms, each as a count over `|Fp|`.

`θ` is not folded in here: `enabledLookupThetaBadSetFamily_card_le` prices it against an
environment family rather than a verifying key, so it is charged where that family is fixed. -/
noncomputable def semanticChallengeRemainder
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp) (constraints : List (Polynomial Fp))
    (m u : ℕ) : ℝ≥0∞ :=
  ((vk.n * constraints.length : ℕ) : ℝ≥0∞) / Fintype.card Fp +
    ((∑ p : Fin shape.numProofs,
      2 * Fintype.card (ResolverPermutationCell vk poly p m) : ℕ) : ℝ≥0∞) / Fintype.card Fp +
    ((∑ p : Fin shape.numProofs,
      (Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
        Fintype.card (ResolverPermutationCell vk poly p m) : ℕ) : ℝ≥0∞) / Fintype.card Fp +
    ((shape.numProofs * shape.numLookups * (2 * (u + 1)) : ℕ) : ℝ≥0∞) / Fintype.card Fp +
    ((shape.numProofs * shape.numLookups * ((u + 2) * (u + 1) + (u + 1)) : ℕ) : ℝ≥0∞) /
      Fintype.card Fp

/-- **Each semantic exclusion is charged once, and the four bundle-wide events sum to the
remainder.**  The `y` event is priced over its own squeeze by `goodY_failure_measure_le`; the
other three are the bundle-wide unions above.  Stated as a sum because each challenge is a
separate squeeze. -/
theorem semanticChallengeRemainder_covers
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (constraints : List (Polynomial Fp))
    (m u : ℕ) (hn : vk.n ≠ 0) :
    uniformChallenge.toOuterMeasure
        {y : Fp | ∃ j, y ∈ szBadSet (foldSplitWitness constraints vk.n j)} +
      uniformChallenge.toOuterMeasure (allResolverPermutationGammaBadSet vk ch poly m) +
      uniformChallenge.toOuterMeasure (allResolverPermutationBetaBadSet vk poly m) +
      uniformChallenge.toOuterMeasure (allResolverLookupGammaBadSet vk ch poly u) +
      uniformChallenge.toOuterMeasure (allResolverLookupBetaBadSet vk ch poly u) ≤
      semanticChallengeRemainder vk poly constraints m u := by
  unfold semanticChallengeRemainder
  gcongr
  · exact goodY_failure_measure_le constraints hn
  · exact allResolverPermutationGammaBadSet_measure_le vk ch poly m
  · exact allResolverPermutationBetaBadSet_measure_le vk poly m
  · exact allResolverLookupGammaBadSet_measure_le vk ch poly u
  · exact allResolverLookupBetaBadSet_measure_le vk ch poly u

end Zcash.Snark
