import Zcash.Snark.Soundness.Action.AdaptiveStatementModel

/-!
# Adaptive-statement query accounting

The statement-bound `theta` query is priced by the same labeled-query/fresh-fallback mechanism used
by the existing adaptive-online proof.  Completing the adversary with that one verifier-selected
query changes `Q` to `Q + 1`; it does not wrap an already adaptive theorem in another `Q` factor.
-/

namespace Zcash.Snark

open Keygen
open scoped ENNReal

namespace ComputedAdaptiveActionStatementFSFamily

/-- The output-selected first Fiat--Shamir query. -/
def thetaPoint {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    AdaptiveActionStatementTranscript pp :=
  output.prefixesPre (family.vkTranscriptRepr basis) 0

/-- Detect whether the final instance representations differ from those fixed by the first actual
query at the statement-bound `theta` prefix. A mismatch is an explicit AGM relation. -/
def instanceRepresentationRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let output := (family.adversary basis).run O
  let t := family.thetaPoint basis output
  selectedQueryRepresentationRelation? t (family.adversary basis) O
    (adaptiveStatementInstanceRepresentationList output.instanceRepresentations)
    (output.instanceRepresentations_coveredAtTheta (family.vkTranscriptRepr basis))

/-- With no instance-representation relation, the statement prefix was fresh or the final
instance coordinates were already pinned by its first pre-answer query annotation. -/
def instanceRepresentationRelationFinder_eq_none {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.instanceRepresentationRelationFinder basis O = none) :
    let output := (family.adversary basis).run O
    let t := family.thetaPoint basis output
    (family.adversary basis).findLabel O t = none ⊕'
      SelectedQueryRepresentationPinned t (family.adversary basis) O
        (adaptiveStatementInstanceRepresentationList output.instanceRepresentations) := by
  dsimp only
  apply selectedQueryRepresentationRelation?_eq_none
  exact hnone

/-- Exact `(Q + 1)` accounting for a bad set at the adaptive statement's first squeeze. -/
theorem thetaSurface_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (bad : (t : AdaptiveActionStatementTranscript pp) →
      AlgebraicTranscriptQuery (F := Fp) basis t →
      family.Coins → Set Fp)
    (fallback : AdaptiveActionStatementOutput pp basis
        (family.fixedRepresentations basis) →
      AdaptiveActionStatementTranscript pp → family.Coins → Set Fp)
    (hbadBlind : ∀ t label O v,
      bad t label (Function.update O t v) = bad t label O)
    (hfallbackBlind : ∀ output t O v,
      fallback output t (Function.update O t v) = fallback output t O)
    {epsilon : ENNReal}
    (hbad : ∀ t label O,
      (PMF.uniformOfFintype Fp).toOuterMeasure (bad t label O) ≤ epsilon)
    (hfallback : ∀ output t O,
      (PMF.uniformOfFintype Fp).toOuterMeasure (fallback output t O) ≤ epsilon) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | O (family.thetaPoint basis ((family.adversary basis).run O)) ∈
        LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
          bad fallback (family.thetaPoint basis ((family.adversary basis).run O)) O} ≤
      (family.Q + 1 : ℕ) * epsilon := by
  exact LabeledOracleComp.firstLabelOrFallbackBad_measure_le
    (family.adversary basis) (family.thetaPoint basis) bad fallback
    hbadBlind hfallbackBlind hbad hfallback (family.queryBound basis)

/-- A relation finder may cover final-output/query-label mismatches without changing the query
factor.  The remaining adaptive statement failure still costs exactly `(Q + 1) * epsilon`. -/
theorem thetaFinalBadWithoutRelation_table_le {pp : ProofParams} {Relation : Type*}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (finalBad : AdaptiveActionStatementOutput pp basis
        (family.fixedRepresentations basis) →
      AdaptiveActionStatementTranscript pp → family.Coins → Set Fp)
    (finder : family.Coins → Option Relation)
    (bad : (t : AdaptiveActionStatementTranscript pp) →
      AlgebraicTranscriptQuery (F := Fp) basis t → family.Coins → Set Fp)
    (fallback : AdaptiveActionStatementOutput pp basis
        (family.fixedRepresentations basis) →
      AdaptiveActionStatementTranscript pp → family.Coins → Set Fp)
    (hcover : ∀ O,
      let output := (family.adversary basis).run O
      let t := family.thetaPoint basis output
      O t ∈ finalBad output t O → finder O = none →
        O t ∈ LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
          bad fallback t O)
    (hbadBlind : ∀ t label O v,
      bad t label (Function.update O t v) = bad t label O)
    (hfallbackBlind : ∀ output t O v,
      fallback output t (Function.update O t v) = fallback output t O)
    {epsilon : ENNReal}
    (hbad : ∀ t label O,
      (PMF.uniformOfFintype Fp).toOuterMeasure (bad t label O) ≤ epsilon)
    (hfallback : ∀ output t O,
      (PMF.uniformOfFintype Fp).toOuterMeasure (fallback output t O) ≤ epsilon) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | let output := (family.adversary basis).run O
        let t := family.thetaPoint basis output
        O t ∈ finalBad output t O ∧ finder O = none} ≤
      (family.Q + 1 : ℕ) * epsilon := by
  exact LabeledOracleComp.finalBadWithoutRelation_measure_le
    (family.adversary basis) (family.thetaPoint basis) finalBad finder bad fallback
    hcover hbadBlind hfallbackBlind hbad hfallback (family.queryBound basis)

end ComputedAdaptiveActionStatementFSFamily

end Zcash.Snark
