import Zcash.Snark.Soundness.ChallengePricing
import Zcash.Snark.Soundness.PermutationSemantics

/-!
# Bundle-wide resolver permutation challenge pricing

This module collects the finite bad sets needed to obtain
`ResolverPermutationGoodChallenges` simultaneously for every proof in a bundle,
and bounds their uniform-challenge cost.
-/

namespace Zcash.Snark

open Halo2 Polynomial Finset
open scoped ENNReal

set_option maxHeartbeats 20000

/-- Both multisets used by a resolver permutation argument contain exactly one entry per
active chunk cell. -/
theorem card_chunkedCellPairs_eq_fintypeCard
    (nc m : ℕ) (width : ℕ → ℕ)
    (value name : ℕ → ℕ → ℕ → Fp) :
    Multiset.card (chunkedCellPairs nc m width value name) =
      Fintype.card (ChunkCell nc m width) := by
  simp [chunkedCellPairs]

/-- The finite `β` exclusion for one resolver-backed permutation argument.  There is one
coefficient root set for each potentially nonzero coefficient of `pairProdDiff`. -/
noncomputable def resolverPermutationBetaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (m : ℕ) : Finset Fp :=
  (Finset.range (Fintype.card (ResolverPermutationCell vk poly p m) + 1)).biUnion fun j =>
    szBadSet ((pairProdDiff
      (chunkedCellPairs shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p)))
      (chunkedCellPairs shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowName vk.omega vk.delta vk.chunkLen))).coeff j)

/-- Avoiding the two per-proof bad sets supplies exactly the good-challenge record consumed by
the resolver permutation endpoint. -/
theorem ResolverPermutationGoodChallenges.ofBadSets
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (m : ℕ)
    (hgamma : ch.gamma ∉ resolverPermutationGammaBadSet vk ch poly p m)
    (hbeta : ch.beta ∉ resolverPermutationBetaBadSet vk poly p m) :
    ResolverPermutationGoodChallenges vk ch poly p m where
  gamma := hgamma
  beta j := by
    let source :=
      chunkedCellPairs shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
    let target :=
      chunkedCellPairs shape.numPermutationSets m
        (fun c => (ResolverPermutationPairs vk poly p c).length)
        (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
        (chunkRowName vk.omega vk.delta vk.chunkLen)
    let d := Fintype.card (ResolverPermutationCell vk poly p m)
    change ch.beta ∉ szBadSet ((pairProdDiff source target).coeff j)
    by_cases hj : j < d + 1
    · intro hmem
      apply hbeta
      rw [resolverPermutationBetaBadSet]
      exact Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_range.mpr hj, hmem⟩
    · have hsource : Multiset.card source = d := by
        simpa only [source, d] using card_chunkedCellPairs_eq_fintypeCard
          shape.numPermutationSets m
          (fun c => (ResolverPermutationPairs vk poly p c).length)
          (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
          (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
      have htarget : Multiset.card target = d := by
        simpa only [target, d] using card_chunkedCellPairs_eq_fintypeCard
          shape.numPermutationSets m
          (fun c => (ResolverPermutationPairs vk poly p c).length)
          (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
          (chunkRowName vk.omega vk.delta vk.chunkLen)
      have hzero : (pairProdDiff source target).coeff j = 0 := by
        apply pairProdDiff_coeff_eq_zero_of_le
        simp only [hsource, htarget, max_self]
        omega
      rw [hzero]
      simp [szBadSet]

/-- The union of all resolver permutation `γ` exclusions in one proof bundle. -/
noncomputable def allResolverPermutationGammaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ) : Finset Fp :=
  (Finset.univ : Finset (Fin shape.numProofs)).biUnion fun p =>
    resolverPermutationGammaBadSet vk ch poly p m

/-- The union of all resolver permutation `β` exclusions in one proof bundle. -/
noncomputable def allResolverPermutationBetaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ) : Finset Fp :=
  (Finset.univ : Finset (Fin shape.numProofs)).biUnion fun p =>
    resolverPermutationBetaBadSet vk poly p m

/-- Bundle-wide permutation challenge exclusions at one active-row boundary.
This is the verifier-native package consumed by circuit integrations. -/
structure ResolverPermutationChallengeExclusions
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ) : Prop where
  gamma :
    ch.gamma ∉ allResolverPermutationGammaBadSet vk ch poly m
  beta :
    ch.beta ∉ allResolverPermutationBetaBadSet vk poly m

/-- Avoiding the bundle-wide permutation bad sets supplies the good-challenge record for every
proof. -/
theorem allResolverPermutationGoodChallenges_of_not_mem
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ)
    (hgamma : ch.gamma ∉ allResolverPermutationGammaBadSet vk ch poly m)
    (hbeta : ch.beta ∉ allResolverPermutationBetaBadSet vk poly m) :
    ∀ p : Fin shape.numProofs,
      ResolverPermutationGoodChallenges vk ch poly p m := by
  intro p
  apply ResolverPermutationGoodChallenges.ofBadSets
  · intro hmem
    apply hgamma
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hmem⟩
  · intro hmem
    apply hbeta
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hmem⟩

/-- A bundle exclusion package supplies the per-proof record used by the
permutation semantic endpoint. -/
theorem ResolverPermutationChallengeExclusions.good
    {shape : Shape} {G : Type*}
    {vk : VerifyingKey shape Fp G} {ch : Challenges shape.k Fp}
    {poly : CommitmentId → Polynomial Fp} {m : ℕ}
    (exclusions :
      ResolverPermutationChallengeExclusions vk ch poly m) :
    ∀ p : Fin shape.numProofs,
      ResolverPermutationGoodChallenges vk ch poly p m :=
  allResolverPermutationGoodChallenges_of_not_mem
    vk ch poly m exclusions.gamma exclusions.beta

/-- One resolver permutation `γ` exclusion costs at most two challenge values per active
permutation cell: one for multiset recovery and one for source-factor nonvanishing. -/
theorem resolverPermutationGammaBadSet_card_le
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (m : ℕ) :
    (resolverPermutationGammaBadSet vk ch poly p m).card ≤
      2 * Fintype.card (ResolverPermutationCell vk poly p m) := by
  let source :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  let target :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  let d := Fintype.card (ResolverPermutationCell vk poly p m)
  have hsource : Multiset.card source = d := by
    simpa only [source, d] using card_chunkedCellPairs_eq_fintypeCard
      shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  have htarget : Multiset.card target = d := by
    simpa only [target, d] using card_chunkedCellPairs_eq_fintypeCard
      shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  have hroot :
      (szBadSet (resolverPermutationGammaDifference vk ch poly p m)).card ≤ d := by
    apply le_trans (szBadSet_linProdDiff_card_le _ _)
    simp [source, target, hsource, htarget]
  have hzero :
      (resolverPermutationZeroFactorBadSet vk ch poly p m).card ≤ d := by
    exact additiveZeroBadSet_card_le
      (resolverPermutationFactorOffset vk ch poly p m)
  rw [resolverPermutationGammaBadSet]
  calc
    (szBadSet (resolverPermutationGammaDifference vk ch poly p m) ∪
        resolverPermutationZeroFactorBadSet vk ch poly p m).card
      ≤ (szBadSet (resolverPermutationGammaDifference vk ch poly p m)).card +
          (resolverPermutationZeroFactorBadSet vk ch poly p m).card :=
        Finset.card_union_le _ _
    _ ≤ d + d := Nat.add_le_add hroot hzero
    _ = 2 * d := by omega

/-- One resolver permutation `β` exclusion costs at most `(d + 1)·d`, where `d` is the number
of active permutation cells. -/
theorem resolverPermutationBetaBadSet_card_le
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (m : ℕ) :
    (resolverPermutationBetaBadSet vk poly p m).card ≤
      (Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
        Fintype.card (ResolverPermutationCell vk poly p m) := by
  let source :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  let target :=
    chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  let d := Fintype.card (ResolverPermutationCell vk poly p m)
  have hsource : Multiset.card source = d := by
    simpa only [source, d] using card_chunkedCellPairs_eq_fintypeCard
      shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))
  have htarget : Multiset.card target = d := by
    simpa only [target, d] using card_chunkedCellPairs_eq_fintypeCard
      shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)
  have hcoeff : ∀ j, (szBadSet ((pairProdDiff source target).coeff j)).card ≤ d := by
    intro j
    exact le_trans (szBadSet_card_le _) (by
      simpa [hsource, htarget] using natDegree_coeff_pairProdDiff_le source target j)
  rw [resolverPermutationBetaBadSet]
  calc
    ((Finset.range (d + 1)).biUnion fun j =>
        szBadSet ((pairProdDiff source target).coeff j)).card
      ≤ ∑ j ∈ Finset.range (d + 1),
          (szBadSet ((pairProdDiff source target).coeff j)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (d + 1), d :=
      Finset.sum_le_sum fun j _ => hcoeff j
    _ = (d + 1) * d := by simp

/-- The bundle-wide permutation `γ` surface is bounded by the sum of the per-proof active-cell
budgets. -/
theorem uniformChallenge_allResolverPermutationGammaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverPermutationGammaBadSet vk ch poly m)
      ≤ (∑ p : Fin shape.numProofs,
          (2 * Fintype.card (ResolverPermutationCell vk poly p m) : ℕ)) /
        (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  rw [allResolverPermutationGammaBadSet]
  calc
    ((Finset.univ : Finset (Fin shape.numProofs)).biUnion fun p =>
        resolverPermutationGammaBadSet vk ch poly p m).card
      ≤ ∑ p ∈ (Finset.univ : Finset (Fin shape.numProofs)),
          (resolverPermutationGammaBadSet vk ch poly p m).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin shape.numProofs)),
          2 * Fintype.card (ResolverPermutationCell vk poly p m) :=
        Finset.sum_le_sum fun p _ =>
          resolverPermutationGammaBadSet_card_le vk ch poly p m
    _ = ∑ p : Fin shape.numProofs,
          2 * Fintype.card (ResolverPermutationCell vk poly p m) := by simp

/-- The bundle-wide permutation `β` surface is bounded by the sum of the per-proof coefficient
budgets. -/
theorem uniformChallenge_allResolverPermutationBetaBadSet
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp) (m : ℕ) :
    uniformChallenge.toOuterMeasure
        (allResolverPermutationBetaBadSet vk poly m)
      ≤ (∑ p : Fin shape.numProofs,
          ((Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
            Fintype.card (ResolverPermutationCell vk poly p m) : ℕ)) /
        (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  gcongr
  rw [allResolverPermutationBetaBadSet]
  calc
    ((Finset.univ : Finset (Fin shape.numProofs)).biUnion fun p =>
        resolverPermutationBetaBadSet vk poly p m).card
      ≤ ∑ p ∈ (Finset.univ : Finset (Fin shape.numProofs)),
          (resolverPermutationBetaBadSet vk poly p m).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ p ∈ (Finset.univ : Finset (Fin shape.numProofs)),
          (Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
            Fintype.card (ResolverPermutationCell vk poly p m) :=
        Finset.sum_le_sum fun p _ =>
          resolverPermutationBetaBadSet_card_le vk poly p m
    _ = ∑ p : Fin shape.numProofs,
          (Fintype.card (ResolverPermutationCell vk poly p m) + 1) *
            Fintype.card (ResolverPermutationCell vk poly p m) := by simp

end Zcash.Snark
