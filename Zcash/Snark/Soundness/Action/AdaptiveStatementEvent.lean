import Zcash.Snark.Soundness.Action.AdaptiveStatementTerminal
import Zcash.Snark.Soundness.AGM.AdaptiveComposition

/-!
# Adaptive-statement Action event composition

The relation finder combines the load-bearing pre-`theta` instance-coordinate comparison with the
complete one-run Action terminal.  Probability composition keeps the still-to-be-priced
statistical residual explicit; this prevents either silently assuming that residual away or
wrapping an already adaptive theorem in a second query factor.
-/

namespace Zcash.Snark

open Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open scoped ENNReal

local instance adaptiveStatementEventVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- One combined relation finder: first bind the selected instance coordinates at `theta`, then
run the decoded Action terminal. -/
noncomputable def relationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
    family.Coins → Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    match family.instanceRepresentationRelationFinder basis O with
    | some relation => some relation
    | none => family.terminalRelationFinder hchar basis O

/-- The exact DLOG-reduction event of the combined adaptive-statement finder. -/
def relationEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  {q | (family.relationFinder hchar q.1 q.2).isSome}

/-- False-statement acceptance not already converted into explicit relation data. -/
def statisticalResidualEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  family.acceptFalseStatementEvent \ family.relationEvent hchar

/-- The adaptive false-statement event is exhausted by the relation event and its literal
statistical residual. -/
theorem acceptFalseStatementEvent_subset {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder) :
    family.acceptFalseStatementEvent ⊆
      family.relationEvent hchar ∪ family.statisticalResidualEvent hchar := by
  intro q hq
  by_cases hrelation : q ∈ family.relationEvent hchar
  · exact Or.inl hrelation
  · exact Or.inr ⟨hq, hrelation⟩

/-- The combined adaptive-statement finder has the standard textbook-DLOG reduction. -/
theorem relation_prob_le_of_textbookDL {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B (family.relationFinder hchar) bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
        family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.relationEvent hchar) ≤
      bound + 1 / Fintype.card Fp := by
  simpa [relationEvent, relSetWithCoins] using
    (relationWithCoins_prob_le_of_textbookDL B (family.relationFinder hchar) hDL)

/-- Adaptive-statement soundness composition with the statistical residual exposed as a premise. -/
theorem acceptFalseStatement_prob_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) {dlBound residualBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B (family.relationFinder hchar) dlBound)
    (hresidual :
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
          family.Coins)).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
          family.statisticalResidualEvent hchar) ≤ residualBound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
        family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        family.acceptFalseStatementEvent) ≤
      (dlBound + 1 / Fintype.card Fp) + residualBound := by
  refine le_trans (MeasureTheory.measure_mono (Set.preimage_mono
    (family.acceptFalseStatementEvent_subset hchar))) ?_
  rw [Set.preimage_union]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add (family.relation_prob_le_of_textbookDL hchar B hDL) hresidual

/-- When the residual surfaces share the existing adaptive query accounting, statement selection
adds no second multiplicative loss: the capstone contains one `(Q + 1)` factor. -/
theorem acceptFalseStatement_prob_le_of_query_accounting {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) {dlBound epsilon : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B (family.relationFinder hchar) dlBound)
    (hresidual :
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
          family.Coins)).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
          family.statisticalResidualEvent hchar) ≤ (family.Q + 1 : Nat) * epsilon) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
        family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        family.acceptFalseStatementEvent) ≤
      (dlBound + 1 / Fintype.card Fp) + (family.Q + 1 : Nat) * epsilon :=
  family.acceptFalseStatement_prob_le hchar B hDL hresidual

end ComputedAdaptiveActionStatementFSFamily

end Zcash.Snark
