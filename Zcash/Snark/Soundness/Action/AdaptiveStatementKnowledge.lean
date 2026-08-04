import Zcash.Snark.Soundness.Action.AdaptiveStatementCapstone

/-!
# Adaptive-statement Action knowledge soundness

This module defines the complete executable selected-statement witness projection and proves that
failure of that projection is covered by the same combined relation finder and statistical
surfaces as adaptive-statement false-statement soundness.
-/

namespace Zcash.Snark

open Classical Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)
open scoped ENNReal

local instance adaptiveStatementKnowledgeVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- Post-relation-finder selected-statement outcome.  Keeping the empty-finder proof as an
explicit argument avoids reducing through a dependent match when proving extractor success. -/
def adaptiveStatementKnowledgeOutcomeCore {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hrelation : family.relationFinder hchar basis O = none) :
    Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) :=
  let hprovenance := family.relationFinder_none_provenance hchar basis O hrelation
  let proof := family.runProof basis O
  let nu := family.runPreIpaReads basis O
  let rounds := family.runIpaReads basis O
  match family.accepts? basis O with
  | none => none
  | some hacceptsProof =>
    let haccepts : family.accepts basis O := hacceptsProof.down
    if hz : nu 10 ≠ 0 then
      if hattack : fullAlgebraicBindingAttackZ basis
          (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            (family.runOutput basis O).inputs)
          proof nu rounds then
        none
      else
        match family.batchOutcome basis O with
        | PSum.inr relation => some (Sum.inr
            (ComputedStraightLineIpaFSFamily.straightLineCanonicalRelation relation))
        | PSum.inl witness =>
          match family.batchGoodRoots? basis O witness with
          | none => none
          | some hroots =>
            have hshifted := family.shiftedValue_of_accept_not_attack
              basis O haccepts hz hattack
            let rawDecode := family.rawDecodeOfBatchGoodRoots basis O witness
              hroots.down hshifted
            let hacceptsFull : DeployedAccepts (AdaptiveActionStatementShape pp)
                (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
                (adaptiveActionStatementVk pp basis)
                (adaptiveActionStatementInstanceCommitment pp basis
                  (family.runOutput basis O).inputs)
                proof.proof.1 (chRecord nu rounds) := by
              simpa only [accepts, family.runRecord_eq_chRecord, proof, nu, rounds]
                using haccepts
            let hcharFull : deployedX4PairCount (adaptiveActionStatementVk pp basis)
                (adaptiveActionStatementInstanceCommitment pp basis
                  (family.runOutput basis O).inputs)
                proof.proof.1 (chRecord nu rounds) < scalarFieldOrder := by
              simpa only [family.runRecord_eq_chRecord, proof, nu, rounds] using
                hchar basis O
            let output := family.runOutput basis O
            let source := output.proofData.algebraicProof.preX1AssemblySource
              (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
                family.fixedRepresentations basis)
            let difference := adaptiveActionPreXDifference pp basis output.inputs
              output.proofData.algebraicProof.erase source (family.runRecord basis O)
            if _hsupport : difference = 0 then
              family.preXIdentityOutcome? basis O hprovenance.2.2.2.2.1 witness rawDecode
                rfl hacceptsFull hcharFull
            else
              let run : family.DecodedRun basis O :=
                { hchar := hchar basis O
                  decode := family.decodeOfBatchGoodRoots basis O witness hroots.down hshifted
                  accepts := haccepts }
              family.semanticOutcome? basis O run
    else none

/-- Complete selected-statement outcome, retaining either extracted witnesses or relation data. -/
def adaptiveStatementKnowledgeOutcome {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) :=
  match hrelation : family.relationFinder hchar basis O with
  | some relation => some (Sum.inr relation)
  | none => family.adaptiveStatementKnowledgeOutcomeCore hchar basis O hrelation

@[simp] theorem adaptiveStatementKnowledgeOutcome_eq_core_of_none {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hrelation : family.relationFinder hchar basis O = none) :
    family.adaptiveStatementKnowledgeOutcome hchar basis O =
      family.adaptiveStatementKnowledgeOutcomeCore hchar basis O hrelation := by
  unfold adaptiveStatementKnowledgeOutcome
  split
  · rename_i relation heq
    rw [hrelation] at heq
    contradiction
  · congr

/-- Witness-only projection of the complete selected-statement outcome. -/
def adaptiveStatementKnowledgeExtractor {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs) :=
  match family.adaptiveStatementKnowledgeOutcome hchar basis O with
  | some (Sum.inl witness) => some witness
  | _ => none

/-- Acceptance for a selected statement with failure of the executable witness projection. -/
def adaptiveStatementKnowledgeFailureEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  {q | family.accepts q.1 q.2 ∧
    family.adaptiveStatementKnowledgeExtractor hchar q.1 q.2 = none}

set_option maxRecDepth 10000 in
theorem adaptiveStatementKnowledgeExtractor_isSome_of_no_events {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (haccepts : family.accepts basis O)
    (hrelationEvent : (basis, O) ∉ family.relationEvent hchar)
    (hzeroEvent : (basis, O) ∉ family.zeroEvent)
    (hipaEvent : (basis, O) ∉ family.ipaEvent)
    (hrootEvent : (basis, O) ∉ family.rootEvent)
    (hsemanticEvent : (basis, O) ∉ family.semanticEvent) :
    (family.adaptiveStatementKnowledgeExtractor hchar basis O).isSome := by
  change ¬(family.relationFinder hchar basis O).isSome at hrelationEvent
  have hfinderNone := Option.not_isSome_iff_eq_none.mp hrelationEvent
  have hprovenance := family.relationFinder_none_provenance hchar basis O hfinderNone
  have hterminalNone := family.relationFinder_none_terminal hchar basis O hfinderNone
  have hidentityNone := family.relationFinder_none_identity hchar basis O hfinderNone
  have hz : family.runPreIpaReads basis O 10 ≠ 0 := by
    intro hz
    exact hzeroEvent hz
  let proof := family.runProof basis O
  let nu := family.runPreIpaReads basis O
  let rounds := family.runIpaReads basis O
  have hattack : ¬fullAlgebraicBindingAttackZ basis
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      proof nu rounds := by
    intro hattack
    cases hsplit : proof.straightLineBindingAttackZIndexedRootOrRelation
        nu rounds hattack with
    | inl root =>
        obtain ⟨j, hj⟩ := root
        apply hipaEvent
        refine ⟨j, ?_⟩
        change O (family.ipaPoint basis j (family.runOutput basis O)) ∈
            outputIpaFallbackBad family basis j (family.runOutput basis O)
              (family.ipaPoint basis j (family.runOutput basis O)) O ∧ _
        rw [outputIpaFallbackBad_actual]
        exact ⟨by simpa only [proof, nu, rounds] using hj, hprovenance.2.2.1⟩
    | inr relation =>
        have hacceptsSome := family.accepts?_isSome_of basis O haccepts
        obtain ⟨hacceptsProof, hacceptsEq⟩ := Option.isSome_iff_exists.mp hacceptsSome
        unfold terminalRelationFinder at hterminalNone
        rw [hacceptsEq] at hterminalNone
        dsimp only at hterminalNone
        rw [dif_pos (by simpa only [nu] using hz), dif_pos hattack, hsplit] at hterminalNone
        simp at hterminalNone
  let hshifted := family.shiftedValue_of_accept_not_attack basis O haccepts hz hattack
  cases hout : family.batchOutcome basis O with
  | inr relation =>
      have hacceptsSome := family.accepts?_isSome_of basis O haccepts
      obtain ⟨hacceptsProof, hacceptsEq⟩ := Option.isSome_iff_exists.mp hacceptsSome
      unfold terminalRelationFinder at hterminalNone
      rw [hacceptsEq] at hterminalNone
      dsimp only at hterminalNone
      rw [dif_pos (by simpa only [nu] using hz), dif_neg hattack, hout] at hterminalNone
      simp at hterminalNone
  | inl witness =>
      have hroots := witness.goodRoots_of_not_rootEvent family basis O hrootEvent
        hprovenance.2.1
      let rawDecode := family.rawDecodeOfBatchGoodRoots basis O witness hroots hshifted
      have hbatches : rawDecode.batches = witness.batches := by rfl
      have hacceptsFull : DeployedAccepts (AdaptiveActionStatementShape pp)
          (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
          (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            (family.runOutput basis O).inputs)
          (family.runProof basis O).proof.1
          (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)) := by
        simpa only [accepts, family.runRecord_eq_chRecord] using haccepts
      have hcharFull : deployedX4PairCount (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            (family.runOutput basis O).inputs)
          (family.runProof basis O).proof.1
          (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)) <
            scalarFieldOrder := by
        simpa only [family.runRecord_eq_chRecord] using hchar basis O
      have hsurface : ∀ n : Fin 5,
          let n11 : Fin 11 := Fin.castLE (by omega) n
          let nu := family.runPreIpaReads basis O
          nu n11 ∉ adaptiveActionSurfaceAt pp basis (family.runOutput basis O).inputs n
            (family.runProof basis O).proof.1
            (semanticRepresentationTarget (family.runOutput basis O) n ++
              family.fixedRepresentations basis)
            (fun i => nu (i.castLE (le_of_lt n11.isLt))) := by
        intro n
        dsimp only
        intro hbad
        apply hsemanticEvent
        refine ⟨n, ?_⟩
        let n11 : Fin 11 := Fin.castLE (by omega) n
        change O (family.preIpaPoint basis n11 (family.runOutput basis O)) ∈
            outputSemanticBad family basis n (family.runOutput basis O)
              (family.preIpaPoint basis n11 (family.runOutput basis O)) O ∧ _
        refine ⟨?_, hprovenance.2.2.2.1⟩
        rw [outputSemanticBad_actual]
        simpa only [outputSemanticSurface, adaptiveActionSurfaceAtOf_action,
          n11] using hbad
      have hexclusions := family.statementExclusions_of_no_surface basis O
        hprovenance.2.2.2.2.1 witness rawDecode hbatches haccepts (hchar basis O) hsurface
      have hacceptsSome := family.accepts?_isSome_of basis O haccepts
      obtain ⟨hacceptsProof, hacceptsEq⟩ := Option.isSome_iff_exists.mp hacceptsSome
      have hrootsSome := family.batchGoodRoots?_isSome_of basis O witness hroots
      obtain ⟨hrootsProof, hrootsEq⟩ := Option.isSome_iff_exists.mp hrootsSome
      let output := family.runOutput basis O
      let data := output.proofData
      let fixed := adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
        family.fixedRepresentations basis
      let source := data.algebraicProof.preX1AssemblySource fixed
      let difference := adaptiveActionPreXDifference pp basis output.inputs
        data.algebraicProof.erase source (family.runRecord basis O)
      by_cases hsupport : difference = 0
      · have houtcomeSome := family.preXIdentityOutcome_isSome_of basis O
          hprovenance.2.2.2.2.1 witness rawDecode hbatches hacceptsFull hcharFull
          (by simpa only [difference, source, fixed, data, output] using hsupport)
          hexclusions.2.1 hexclusions.2.2.1 hexclusions.2.2.2
        obtain ⟨outcome, houtcomeEq⟩ := Option.isSome_iff_exists.mp houtcomeSome
        cases outcome with
        | inr relation =>
            have hrelationSome : (family.preXIdentityRelation? basis O
                hprovenance.2.2.2.2.1 witness rawDecode hbatches hacceptsFull
                hcharFull).isSome := by
              unfold preXIdentityRelation?
              rw [houtcomeEq]
              rfl
            have hfinderSome := family.identityRelationFinder_isSome_of hchar basis O
              hprovenance.2.2.2.2.1 witness hout hroots haccepts hz hattack hrelationSome
            rw [hidentityNone] at hfinderSome
            simp at hfinderSome
        | inl extracted =>
            unfold adaptiveStatementKnowledgeExtractor
            rw [family.adaptiveStatementKnowledgeOutcome_eq_core_of_none
              hchar basis O hfinderNone]
            unfold adaptiveStatementKnowledgeOutcomeCore
            rw [hacceptsEq]
            dsimp only
            rw [dif_pos hz, dif_neg hattack, hout]
            dsimp only
            rw [hrootsEq]
            dsimp only
            rw [dif_pos (by simpa only [difference, source, fixed, data, output]
              using hsupport)]
            rw [houtcomeEq]
            rfl
      · have heval := family.statementAcceptedDifference_eval_eq_preX basis O
          hprovenance.2.2.2.2.1 hprovenance.2.2.2.2.2 witness rawDecode hbatches
          haccepts (hchar basis O)
        dsimp only at heval
        have hpreEval : difference.eval (family.runRecord basis O).x ≠ 0 :=
          (not_mem_szBadSet.mp (by
            simpa only [difference, source, fixed, data, output] using hexclusions.1)) hsupport
        let decode := rawDecode.reRound (family.runIpaReads basis O)
        let model := CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
            (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) haccepts
        let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi) haccepts
        have hactionGood : (family.runRecord basis O).x ∉ szBadSet
            (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
              model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
              (family.runRecord basis O).y model.chunkLen model.l0 model.lLast model.lBlind -
                polynomial .vanishingH * (X ^ actionCircuit.n - 1)) := by
          apply not_mem_szBadSet.mpr
          intro _
          rw [heval]
          simpa only [difference, source, fixed, data, output] using hpreEval
        let run : family.DecodedRun basis O :=
          { hchar := hchar basis O
            decode := family.decodeOfBatchGoodRoots basis O witness hroots hshifted
            accepts := haccepts }
        have hdecode : run.decode = decode := by
          simp only [run, decode, decodeOfBatchGoodRoots_eq_reRound, rawDecode]
        let good : family.SemanticExclusions basis O run :=
          { xGood := by simpa only [run, hdecode, model, polynomial] using hactionGood
            yGood := by simpa only [run, hdecode, model, polynomial] using hexclusions.2.1
            permutation := by
              simpa only [run, hdecode, model, polynomial] using hexclusions.2.2.1
            lookup := by
              simpa only [run, hdecode, model, polynomial] using hexclusions.2.2.2 }
        have houtcomeSome := family.semanticOutcome?_isSome_of basis O run good
        obtain ⟨outcome, houtcomeEq⟩ := Option.isSome_iff_exists.mp houtcomeSome
        cases outcome with
        | inr relation =>
            have hsemanticSome : (family.semanticRelation? basis O run).isSome := by
              unfold semanticRelation?
              rw [houtcomeEq]
              rfl
            have hterminalSome := family.terminalRelationFinder_isSome_of hchar basis O witness
              hout hroots haccepts hz hattack (by simpa only [run] using hsemanticSome)
            rw [hterminalNone] at hterminalSome
            simp at hterminalSome
        | inl extracted =>
            unfold adaptiveStatementKnowledgeExtractor
            rw [family.adaptiveStatementKnowledgeOutcome_eq_core_of_none
              hchar basis O hfinderNone]
            unfold adaptiveStatementKnowledgeOutcomeCore
            rw [hacceptsEq]
            dsimp only
            rw [dif_pos hz, dif_neg hattack, hout]
            dsimp only
            rw [hrootsEq]
            dsimp only
            rw [dif_neg (by simpa only [difference, source, fixed, data, output]
              using hsupport)]
            rw [show family.semanticOutcome? basis O _ = some (Sum.inl extracted) by
              simpa only [run] using houtcomeEq]
            rfl

/-- Extractor failure is covered by the combined relation event and the same four statistical
surface families used by adaptive-statement false-statement soundness. -/
theorem adaptiveStatementKnowledgeFailureEvent_subset {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder) :
    family.adaptiveStatementKnowledgeFailureEvent hchar ⊆
      family.relationEvent hchar ∪ family.statisticalSurfaceEvent := by
  rintro ⟨basis, O⟩ ⟨haccepts, hextractorNone⟩
  by_cases hrelation : (basis, O) ∈ family.relationEvent hchar
  · exact Or.inl hrelation
  · right
    by_contra hsurface
    simp only [statisticalSurfaceEvent, Set.mem_union, not_or] at hsurface
    have hextracted := family.adaptiveStatementKnowledgeExtractor_isSome_of_no_events
      hchar basis O
      haccepts hrelation hsurface.1 hsurface.2.1 hsurface.2.2.1 hsurface.2.2.2
    rw [hextractorNone] at hextracted
    contradiction

/-- Adaptive-statement knowledge soundness for the defined witness projection.  The probability
argument introduces no second statistical query factor; resource accounting for the combined
relation finder is supplied separately by the conservative finite-security profile. -/
theorem adaptiveStatementKnowledgeFailure_prob_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    (B : VestaG) {dlBound : ENNReal} (epsilon : Fin 5 → ENNReal)
    (hDL : TextbookDLWithCoinsAdvantageLE B (family.relationFinder hchar) dlBound)
    (hsurface : ∀
      (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
      (n : Fin 5)
      (instanceCommitment :
        Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
      (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ epsilon n) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
        family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        family.adaptiveStatementKnowledgeFailureEvent hchar) ≤
      (dlBound + 1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (1 / Fintype.card Fp +
            (AdaptiveActionStatementShape pp).k *
              (2 / (Fintype.card Fp : ENNReal)) +
            algebraicRootBudget (AdaptiveActionStatementShape pp)
              (AdaptiveActionStatementShape pp).k +
            ∑ n : Fin 5, epsilon n) := by
  refine le_trans (MeasureTheory.measure_mono (Set.preimage_mono
    (family.adaptiveStatementKnowledgeFailureEvent_subset hchar))) ?_
  rw [Set.preimage_union]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add (family.relation_prob_le_of_textbookDL hchar B hDL)
    (family.statisticalSurfaceEvent_prob_le B epsilon hsurface)

end ComputedAdaptiveActionStatementFSFamily
end Zcash.Snark
