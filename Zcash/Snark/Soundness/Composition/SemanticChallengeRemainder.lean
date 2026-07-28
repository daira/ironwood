import Zcash.Snark.Soundness.ChallengePricing
import Zcash.Snark.Soundness.Composition.PrefixedSqueeze

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


/-! ## The four surfaces at their squeeze indices

`theta` is squeezed first, then `beta`, then `gamma`, then `y` — indices `0`, `1`, `2`, `3` of the
pre-IPA record.  Each surface is priced by the index-generic squeeze bound, so the four premises
the semantic endpoint takes are one application apiece.
-/

/-- The `theta` surface: index `0`. -/
abbrev thetaSurface (family : ComputedAlgebraicFSFamily shape)
    (badF : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 0 → Fp) → Set Fp) :=
  squeezeSurfaceEvent 0 family badF

/-- The `beta` surface: index `1`. -/
abbrev betaSurface (family : ComputedAlgebraicFSFamily shape)
    (badF : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 1 → Fp) → Set Fp) :=
  squeezeSurfaceEvent 1 family badF

/-- The `gamma` surface: index `2`. -/
abbrev gammaSurface (family : ComputedAlgebraicFSFamily shape)
    (badF : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 2 → Fp) → Set Fp) :=
  squeezeSurfaceEvent 2 family badF

/-- The `y` surface: index `3`. -/
abbrev ySurface (family : ComputedAlgebraicFSFamily shape)
    (badF : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 3 → Fp) → Set Fp) :=
  squeezeSurfaceEvent 3 family badF

/-- **The four semantic surfaces, priced together.**  Each costs `(Q + 1)` times its own
per-challenge bound, so the semantic endpoint's `hY`, `hBeta`, `hGamma` and `hTheta` premises are
supplied at once.  The per-challenge bounds are the bundle-wide exclusion measures above; the
stability inputs come from `hstab_of_prefixDeterminedAt` at the matching index. -/
theorem semanticSurfaces_prob_le {T' : Type*} [DecidableEq T']
    (query : AugmentedIndex (2 ^ shape.k) → T')
    (family : ComputedAlgebraicFSFamily shape)
    (badTheta : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 0 → Fp) → Set Fp)
    (badBeta : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 1 → Fp) → Set Fp)
    (badGamma : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 2 → Fp) → Set Fp)
    (badY : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 3 → Fp) → Set Fp)
    {epsTheta epsBeta epsGamma epsY : ENNReal}
    (hstabTheta : ∀ basis O v,
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 0) v)) 0 =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 0)
    (hstabBeta : ∀ basis O v,
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 1) v)) 1 =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 1)
    (hstabGamma : ∀ basis O v,
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 2) v)) 2 =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 2)
    (hstabY : ∀ basis O v,
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 3) v)) 3 =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 3)
    (hTheta : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badTheta basis t nu) ≤ epsTheta)
    (hBeta : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badBeta basis t nu) ≤ epsBeta)
    (hGamma : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badGamma basis t nu) ≤ epsGamma)
    (hY : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badY basis t nu) ≤ epsY) :
    (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          thetaSurface family badTheta) ≤ (family.Q + 1 : ℕ) * epsTheta ∧
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          betaSurface family badBeta) ≤ (family.Q + 1 : ℕ) * epsBeta ∧
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          gammaSurface family badGamma) ≤ (family.Q + 1 : ℕ) * epsGamma ∧
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          ySurface family badY) ≤ (family.Q + 1 : ℕ) * epsY :=
  ⟨squeezeSurfaceEvent_prob_le 0 query family badTheta hstabTheta hTheta,
   squeezeSurfaceEvent_prob_le 1 query family badBeta hstabBeta hBeta,
   squeezeSurfaceEvent_prob_le 2 query family badGamma hstabGamma hGamma,
   squeezeSurfaceEvent_prob_le 3 query family badY hstabY hY⟩


/-! ## Run-uniformity of the epsilons

`semanticSurfaces_prob_le` takes bounds uniform over runs, while the card bounds are stated against
a resolver `poly`.  For the permutation surfaces the dependence is only apparent: the chunk pair
list is a `map` over the key's own `permutationChunks`, so its length — and hence the cell count
the bound is stated in — is the same for every `poly`.  The lookup bounds are already stated in
the usable-row count alone.
-/

/-- The resolver's chunk pair count is the key's, not the run's. -/
theorem resolverPermutationPairs_length {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (c : ℕ) :
    (ResolverPermutationPairs vk poly p c).length = (vk.permutationChunks.getD c []).length :=
  List.length_map _

/-- Hence two runs give the same permutation cell count, so the epsilon is run-uniform. -/
theorem resolverPermutationCell_card_congr {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly poly' : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (m : ℕ) :
    Fintype.card (ResolverPermutationCell vk poly p m) =
      Fintype.card (ResolverPermutationCell vk poly' p m) := by
  unfold ResolverPermutationCell
  simp only [resolverPermutationPairs_length]

end Zcash.Snark
