import Zcash.Snark.Soundness.Compose67

/-!
# The unconditional decomposition of the #67 knowledge-error bound

`snarkExtraction_prob_le_of_generatorRO_textbookDL` (`Soundness.Compose67`) bounds the
SNARK-extraction failure `{deployed acceptance ∧ ¬extracted}` by the `#56` clean-opening bound
`(Q+k)·3/|Fp| + (Q+1)/|Fp| + |basis|·ε`, **conditional** on `hExtract : ∀ basis coins,
hasCleanOpening → extracted` — the assumption that *every* clean-opening run already extracts.

This module removes that assumption. The failure event splits, with no hypothesis at all, into the
clean-opening failure (already priced by `#56`) and the **clean-but-not-extracted** residual: runs
that produced a clean IPA opening yet on which the SNARK extraction predicate fails. The main result
`snarkExtraction_prob_le_of_generatorRO_textbookDL_decomposed` is the resulting *unconditional*
inequality

  `μ {accept ∧ ¬extracted} ≤ [ #56 bound ] + μ {hasCleanOpening ∧ ¬extracted}`.

So the conditionality of the #67 bound is now a single, explicit, quantified term — not an assumed
implication. `hExtract` held exactly when that residual is empty; here it is measured instead.

## What closing the residual needs (the recorded gap)

The residual `μ(cleanButNotExtracted)` is bounded by the multiopen knowledge error
`t₁ + (t₂ + t₃ + t₄)` (`Soundness.Multiopen.BudgetedExtraction.deployed_member_budget`), but only
through a coupling this file does **not** discharge, for the reason recorded at
`Soundness.VestaBudget` (the clean-opening hand-off note) and confirmed by the forking/oracle audit:

* `deployed_member_budget` prices a *per-base* accept event over `uniformOfFintype (Fp × Fp × Fp × Fp)`
  — the four fresh (reprogrammed) multiopen challenges;
* `cleanButNotExtracted` lives over the family's coin space `family.Coins`, whose Fiat–Shamir
  challenges are *functions of the coins*, not an independent fresh draw;
* the bridge is a **distributional coupling**, of the exact shape of `roChallenges_ipaRound_uniform`
  (`Soundness.Forking.Rewind`, proven for the IPA rounds): the pushforward of
  `uniformOfFintype family.Coins` under reading/reprogramming the oracle at the sealed
  `preX1Transcript` prefix and the `canonicalX{1,2,3}Run`-determined `preX2/preX3/preX4` prefixes
  equals `uniformOfFintype (Fp × Fp × Fp × Fp)` on the relevant marginal, independent of the residual
  coins. This is the explicit form of the random-oracle-uniformity convention every `hprob`/`hJ`
  floor already carries in its statement (`Soundness.Forking.Oracle`, `uniformChallenge`); it is a
  genuine probabilistic modeling step (with an adaptive multiopen rewind tree), not a composition of
  existing lemmas. It is **not** assumed here: a premise phrased as a bound on
  `μ(cleanButNotExtracted)` would mention `extracted` and restate the conclusion, so it is
  deliberately omitted. The residual term stands quantified and unproven-below, which is the honest
  state.

Everything above `hExtract` — the member witness→columns binding from a single joint accept floor,
the derived gate feed, the value shift, the extraction logic — is discharged (`Soundness.VestaBudget`,
`Soundness.Multiopen.BudgetedExtraction`). This file isolates precisely the one measure-theoretic
coupling that remains between here and a single unconditional number.
-/

namespace Zcash.Snark

open scoped ENNReal

/-- Match `Algebraic.lean`'s `Inhabited VestaG` value, named to avoid the auto-name clash and the
`whnf` timeouts that a shadowing anonymous instance causes on the composed algebraic-family terms. -/
local instance vestaInhabitedCompose67Unc : Inhabited VestaG := ⟨0⟩

namespace ComputedAlgebraicFSFamily

variable {shape : Shape}

/-- The **clean-but-not-extracted** residual: runs on which the computed family produced a clean IPA
opening (`hasCleanOpening`) yet the SNARK-extraction predicate `extracted` fails. This is the only
part of the SNARK-extraction failure not already contained in the `#56` clean-opening failure
`snarkFailureEvent`. -/
def cleanButNotExtracted (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins) :=
  {q | family.hasCleanOpening q.1 q.2 ∧ ¬ extracted q.1 q.2}

/-- **The unconditional split.** With no hypothesis, the SNARK-extraction failure is contained in the
union of the clean-opening failure (`snarkFailureEvent`, no clean opening) and the
clean-but-not-extracted residual. Case split on whether a clean opening was produced: with one it is
in the residual (its `¬extracted` is shared); without one it is in the clean-opening failure (its
acceptance is shared — both events use the same `fullAlgebraicAccept` predicate). This is the
hypothesis-free replacement for `snarkExtractionFailureEvent_subset` (which needed `hExtract`). -/
theorem snarkExtractionFailureEvent_subset_union (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop) :
    family.snarkExtractionFailureEvent extracted
      ⊆ family.snarkFailureEvent ∪ family.cleanButNotExtracted extracted := by
  rintro q ⟨hacc, hnex⟩
  by_cases hclean : family.hasCleanOpening q.1 q.2
  · exact Or.inr ⟨hclean, hnex⟩
  · exact Or.inl ⟨hacc, hclean⟩

end ComputedAlgebraicFSFamily

set_option maxHeartbeats 1000000 in
open ComputedAlgebraicFSFamily in
/-- **#67: the unconditional knowledge-error decomposition.** Without the `hExtract` hypothesis of
`snarkExtraction_prob_le_of_generatorRO_textbookDL`, the measure of "deployed acceptance but no SNARK
extraction" is at most the `#56` clean-opening bound `(Q+k)·3/|Fp| + (Q+1)/|Fp| + |basis|·ε` **plus**
the measure of the clean-but-not-extracted residual. Set containment
(`snarkExtractionFailureEvent_subset_union`) + `measure_union_le` + the `#56` bound
(`snarkFailure_prob_le_of_generatorRO_textbookDL`).

The residual term is exactly the coupling gap documented in this module: it is bounded by the
multiopen knowledge error `t₁ + (t₂ + t₃ + t₄)` under the distributional challenge-uniformity
coupling, which is a modeling step not discharged here. This theorem is the honest unconditional
form: no assumed implication, the one remaining gap standing as a measured quantity. -/
theorem snarkExtraction_prob_le_of_generatorRO_textbookDL_decomposed {shape : Shape}
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T) (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkExtractionFailureEvent extracted)
      ≤ ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound)
        + (independentProductPMF (orchardGeneratorROSetup query)
            (PMF.uniformOfFintype family.Coins)).toOuterMeasure
              ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
                family.cleanButNotExtracted extracted) := by
  -- Bind the #56 bound first, then abbreviate the (shared) outer measure `μ`, so `set` rewrites the
  -- AGM term into the same `μ` shape as the goal. The preimage map is left as the literal it is in
  -- both goal and `hAGM`, avoiding a `set f` whose binder type would thrash elaboration.
  have hAGM := snarkFailure_prob_le_of_generatorRO_textbookDL B hB query hquery family hDL
  set μ := (independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)).toOuterMeasure with hμ
  refine le_trans (μ.mono (Set.preimage_mono
    (family.snarkExtractionFailureEvent_subset_union extracted))) ?_
  rw [Set.preimage_union]
  exact le_trans (MeasureTheory.measure_union_le _ _) (add_le_add hAGM le_rfl)

end Zcash.Snark
