import Zcash.Snark.Soundness.Action.AdaptiveStatementEvent

/-!
# Adaptive-statement Action soundness capstone

This module closes the deterministic residual cover for an adversary that selects the public
statement and proof together, then instantiates the existing one-query-accounting probability
composition without an external cover premise.
-/

namespace Zcash.Snark

open Classical Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)
open scoped ENNReal

local instance adaptiveStatementCapstoneVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem statisticalResidualEvent_subset_surfaceEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder) :
    family.statisticalResidualEvent hchar ⊆ family.statisticalSurfaceEvent := by
  rintro ⟨basis, O⟩ hresidual
  rcases hresidual with ⟨⟨haccepts, hfalse⟩, hrelationEvent⟩
  change ¬(family.relationFinder hchar basis O).isSome at hrelationEvent
  have hfinderNone := Option.not_isSome_iff_eq_none.mp hrelationEvent
  have hprovenance := family.relationFinder_none_provenance hchar basis O hfinderNone
  have hterminalNone := family.relationFinder_none_terminal hchar basis O hfinderNone
  have hidentityNone := family.relationFinder_none_identity hchar basis O hfinderNone
  by_contra hsurfaceEvent
  simp only [statisticalSurfaceEvent, Set.mem_union, not_or] at hsurfaceEvent
  rcases hsurfaceEvent with ⟨hzeroEvent, hipaEvent, hrootEvent, hsemanticEvent⟩
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
      have hacceptsFull : DeployedAccepts
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
        have hrelationSome := family.preXIdentityRelation_isSome_of_outcome basis O
          hprovenance.2.2.2.2.1 witness rawDecode hbatches hacceptsFull hcharFull
          houtcomeSome hfalse
        have hfinderSome := family.identityRelationFinder_isSome_of hchar basis O
          hprovenance.2.2.2.2.1 witness hout hroots haccepts hz hattack hrelationSome
        rw [hidentityNone] at hfinderSome
        contradiction
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
        have hsemanticSome := family.semanticRelation?_isSome_of_false basis O run good hfalse
        have hterminalSome := family.terminalRelationFinder_isSome_of hchar basis O witness
          hout hroots haccepts hz hattack (by simpa only [run] using hsemanticSome)
        rw [hterminalNone] at hterminalSome
        contradiction

/-- Adaptive-statement false-statement soundness with the deterministic residual discharged.
Statement selection introduces no second random-oracle-query loss: all statistical surfaces are
priced under the single existing `(Q + 1)` factor. -/
theorem acceptFalseStatement_prob_le_adaptive {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
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
        family.acceptFalseStatementEvent) ≤
      (dlBound + 1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (1 / Fintype.card Fp +
            (AdaptiveActionStatementShape pp).k *
              (2 / (Fintype.card Fp : ENNReal)) +
            algebraicRootBudget (AdaptiveActionStatementShape pp)
              (AdaptiveActionStatementShape pp).k +
            ∑ n : Fin 5, epsilon n) := by
  exact family.acceptFalseStatement_prob_le_of_surface_cover hchar B epsilon hDL hsurface
    (family.statisticalResidualEvent_subset_surfaceEvent hchar)

end ComputedAdaptiveActionStatementFSFamily
end Zcash.Snark
