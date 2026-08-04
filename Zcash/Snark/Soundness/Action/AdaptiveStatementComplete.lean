import Zcash.Snark.Soundness.Action.AdaptiveStatementSemantic

/-!
# Complete semantic terminal for adaptive Action statements

The complete terminal separates the identically-zero fixed pre-`x` difference from the ordinary
nonzero Schwartz--Zippel branch. Both branches operate on the statement and proof selected by the
same adaptive random-oracle run.
-/

namespace Zcash.Snark

open Classical Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)

local instance adaptiveStatementCompleteVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- Good direct roots and the shifted equality decode the selected proof at the pre-IPA record. -/
def rawDecodeOfBatchGoodRoots {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (witness : family.BatchWitness basis O)
    (hgood : family.BatchGoodRoots basis O witness)
    (hshifted : family.ShiftedValue basis O) :
    DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O)
      ((family.runProof basis O).aMulti (family.runPreIpaReads basis O))
      ((family.runProof basis O).multiU (family.runPreIpaReads basis O))
      ((family.runProof basis O).multiBlind (family.runPreIpaReads basis O)) := by
  let ch := family.runPreIpaRecord basis O
  have hvalue : commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
      ((family.runProof basis O).aMulti (family.runPreIpaReads basis O)) =
      multiopenValue (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
        (family.runProof basis O).proof.1 ch :=
    rawValue_of_shiftedValue_of_good _ _ _ _ _ _ _
      hshifted.1 hshifted.2 hgood.xi hgood.z
  have hgood1 := not_mem_deployedX1RootSet_of_not_mem_all
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 ch witness.batches hgood.x1
  exact deployedAlgebraicDecode_of_good_roots
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 ch witness.batches hvalue hgood.x4 hgood.x3 hgood.x2 hgood1

theorem decodeOfBatchGoodRoots_eq_reRound {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (witness : family.BatchWitness basis O)
    (hgood : family.BatchGoodRoots basis O witness)
    (hshifted : family.ShiftedValue basis O) :
    family.decodeOfBatchGoodRoots basis O witness hgood hshifted =
      (family.rawDecodeOfBatchGoodRoots basis O witness hgood hshifted).reRound
        (family.runIpaReads basis O) := by
  rfl

theorem accepts?_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (haccepts : family.accepts basis O) :
    (family.accepts? basis O).isSome := by
  change DeployedAccepts (AdaptiveActionStatementShape pp)
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 (family.runRecord basis O) at haccepts
  unfold DeployedAccepts at haccepts
  unfold accepts?
  split
  · rename_i hassemble
    rw [hassemble] at haccepts
    exact False.elim haccepts
  · rename_i msm hassemble
    rw [hassemble] at haccepts
    simp [haccepts]

theorem batchGoodRoots?_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (witness : family.BatchWitness basis O)
    (hgood : family.BatchGoodRoots basis O witness) :
    (family.batchGoodRoots? basis O witness).isSome := by
  let ch := family.runPreIpaRecord basis O
  let urs := ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis
  let delta := commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
      ((family.runProof basis O).aMulti (family.runPreIpaReads basis O)) -
    multiopenValue (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 ch
  let sEval := commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
    (family.runProof basis O).s
  have hx1Some := deployedX1RootAvoidance?_isSome_of urs rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 ch witness.batches hgood.x1
  have hx2Some := deployedX2RootAvoidance?_isSome_of urs rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 ch witness.batches hgood.x2
  have hx3Some := deployedX3RootAvoidance?_isSome_of urs rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 ch witness.batches hgood.x3
  have hx4Some := deployedX4RootAvoidance?_isSome_of urs rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 ch witness.batches hgood.x4
  have hxiSome := deployedXiRootAvoidance?_isSome_of delta sEval ch.xi hgood.xi
  have hzSome := deployedZRootAvoidance?_isSome_of delta
    ((family.runProof basis O).multiU (family.runPreIpaReads basis O))
    (family.runProof basis O).sU sEval ch.xi ch.z hgood.z
  obtain ⟨hx1, hhx1⟩ := Option.isSome_iff_exists.mp hx1Some
  obtain ⟨hx2, hhx2⟩ := Option.isSome_iff_exists.mp hx2Some
  obtain ⟨hx3, hhx3⟩ := Option.isSome_iff_exists.mp hx3Some
  obtain ⟨hx4, hhx4⟩ := Option.isSome_iff_exists.mp hx4Some
  obtain ⟨hxi, hhxi⟩ := Option.isSome_iff_exists.mp hxiSome
  obtain ⟨hz, hhz⟩ := Option.isSome_iff_exists.mp hzSome
  unfold batchGoodRoots?
  dsimp only
  rw [hhx1, hhx2, hhx3, hhx4, hhxi, hhz]
  rfl

/-- The identically-zero pre-`x` branch yields an Action witness or an explicit relation. -/
def preXIdentityOutcome? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hsource : family.semanticSourceMismatchRelationFinder basis O = none)
    (witness : family.BatchWitness basis O)
    (rawDecode : DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O)
      ((family.runProof basis O).aMulti (family.runPreIpaReads basis O))
      ((family.runProof basis O).multiU (family.runPreIpaReads basis O))
      ((family.runProof basis O).multiBlind (family.runPreIpaReads basis O)))
    (hbatches : rawDecode.batches = witness.batches)
    (haccepts : DeployedAccepts (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1
      (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)))
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1
      (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)) <
        scalarFieldOrder) :
    Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) := by
  let output := family.runOutput basis O
  let data := output.proofData
  let proof := family.runProof basis O
  let ch := family.runRecord basis O
  let fixed := adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
    family.fixedRepresentations basis
  let source := data.algebraicProof.preX1AssemblySource fixed
  let piecePoly := fun i => onlinePointPolynomial source (data.algebraicProof.hPieces i).point
  let difference := adaptiveActionPreXDifference pp basis output.inputs
    data.algebraicProof.erase source ch
  if hsupport : difference = 0 then
    let decode := rawDecode.reRound (family.runIpaReads basis O)
    let model := CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
      (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) haccepts
    let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts
    let preXPoly := committedPreXQuotient (adaptiveActionStatementVk pp basis) piecePoly
    have hpolyStage : ∀ id, id ≠ .vanishingH → id ≠ .randomPoly →
        polynomial id = adaptiveActionCommitmentPolynomial pp basis output.inputs
          data.algebraicProof.erase
          (semanticRepresentationTarget output (4 : Fin 5) ++
            family.fixedRepresentations basis) ch id := by
      intro id hvanishing hrandom
      have havailable : adaptiveActionCommitmentActive (AdaptiveActionStatementShape pp) (adaptiveActionStatementVk pp basis) id →
          adaptiveActionCommitmentAvailable (4 : Fin 5) id := by
        intro hactive
        cases id <;> simp_all [adaptiveActionCommitmentAvailable]
      have hraw := adaptiveStatementAcceptedPolynomial_eq_stage_nonterminal
        family basis O hsource (4 : Fin 5) id havailable ⟨hvanishing, hrandom⟩
        witness rawDecode hbatches hchar haccepts
      simpa only [polynomial, decode, output, data, ch,
        family.runRecord_eq_chRecord] using hraw
    have hmodelStage : model = adaptiveActionCommittedModel pp basis output.inputs
        data.algebraicProof.erase
        (semanticRepresentationTarget output (4 : Fin 5) ++
          family.fixedRepresentations basis) ch := by
      unfold model adaptiveActionCommittedModel adaptiveActionCommittedModelOf
      exact VerifyingKey.constraintModel_congr_nonterminal _
        (adaptiveActionStatementVk pp basis) ch _ _ _ hpolyStage
    have hsource4 : semanticRepresentationTarget output (4 : Fin 5) ++
        family.fixedRepresentations basis = source := by
      unfold semanticRepresentationTarget source fixed
      rw [List.append_assoc]
      exact data.algebraicProof.actionRepresentationsBefore_four_append
        (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
          family.fixedRepresentations basis)
    have hmodel : model = adaptiveActionCommittedModel pp basis output.inputs
        data.algebraicProof.erase source ch := by
      rw [← hsource4]
      exact hmodelStage
    have hidentity :
        let committedModel := adaptiveActionCommittedModel pp basis output.inputs
          data.algebraicProof.erase source ch
        combineConstraints committedModel.fixedCols committedModel.adviceCols
            committedModel.instanceCols committedModel.gates committedModel.sets
            committedModel.chunks committedModel.lookups committedModel.beta
            committedModel.gamma committedModel.delta committedModel.theta ch.y
            committedModel.chunkLen committedModel.l0 committedModel.lLast
            committedModel.lBlind =
          preXPoly * (X ^ (adaptiveActionStatementVk pp basis).n - 1) := by
      have hzero := hsupport
      unfold difference at hzero
      rw [adaptiveActionPreXDifference_eq] at hzero
      exact sub_eq_zero.mp (by
        simpa only [preXPoly, piecePoly, adaptiveActionStatementVk] using hzero)
    have hsatisfiedRaw : model.CircuitSat ch.y preXPoly
        (adaptiveActionStatementVk pp basis).n
        (proof.aMulti (family.runPreIpaReads basis O)) := by
      rw [hmodel]
      simpa only [proof, runProof, output] using hidentity
    have hsatisfied : model.CircuitSat ch.y preXPoly actionCircuit.n
        (proof.aMulti (family.runPreIpaReads basis O)) := by
      simpa only [adaptiveActionStatementVk, actionCircuit.toVerifierKey_n] using hsatisfiedRaw
    let hn : actionCircuit.n ≠ 0 := by
      change 2 ^ actionCircuit.domainExponent ≠ 0
      positivity
    exact match hgoodY : foldSplitAvoidance? model.constraints actionCircuit.n hn ch.y with
    | none => none
    | some hgoodYProof =>
      match hpermutation : resolverPermutationChallengeExclusions?
          pp.numProofs (adaptiveActionStatementVk pp basis) ch polynomial actionActiveRows with
      | none => none
      | some hpermutationProof =>
        match hlookup : TopLevelLookup.topLevelLookupChallengeExclusions?
            actionCircuit pp
            (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) ch polynomial with
        | none => none
        | some hlookupProof =>
          match ActionTerminal.action_bundleWitness_or_relation_of_decode_circuitSat pp
              (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl output.inputs
              proof.proof.1 ch
              (proof.multiU (family.runPreIpaReads basis O))
              (proof.multiBlind (family.runPreIpaReads basis O))
              (proof.aMulti (family.runPreIpaReads basis O)) decode hchar haccepts
              preXPoly hsatisfied hgoodYProof.down hpermutationProof.down
              hlookupProof.down with
          | PSum.inl extracted => some (Sum.inl extracted)
          | PSum.inr relation => some (Sum.inr
              (augmentedBasis_ursOfAugmentedBasis
                (AdaptiveActionStatementShape pp).k basis ▸
                  AugmentedRelationWitness.toAlgebraicRelationWitness relation))
  else
    exact none

/-- Relation-only projection of the pre-`x` identity outcome. -/
def preXIdentityRelation? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hsource : family.semanticSourceMismatchRelationFinder basis O = none)
    (witness : family.BatchWitness basis O)
    (rawDecode : DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O)
      ((family.runProof basis O).aMulti (family.runPreIpaReads basis O))
      ((family.runProof basis O).multiU (family.runPreIpaReads basis O))
      ((family.runProof basis O).multiBlind (family.runPreIpaReads basis O)))
    (hbatches : rawDecode.batches = witness.batches)
    (haccepts : DeployedAccepts (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1
      (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)))
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1
      (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)) <
        scalarFieldOrder) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match family.preXIdentityOutcome? basis O hsource witness rawDecode hbatches
      haccepts hchar with
  | some (Sum.inr relation) => some relation
  | _ => none

theorem preXIdentityRelation_isSome_of_outcome {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hsource) (witness) (rawDecode) (hbatches) (haccepts) (hchar)
    (hcomplete : (family.preXIdentityOutcome? basis O hsource witness rawDecode
      hbatches haccepts hchar).isSome)
    (hfalse : ¬BundleStatement (family.runOutput basis O).inputs) :
    (family.preXIdentityRelation? basis O hsource witness rawDecode hbatches
      haccepts hchar).isSome := by
  obtain ⟨outcome, houtcome⟩ := Option.isSome_iff_exists.mp hcomplete
  cases outcome with
  | inl extracted => exact False.elim (hfalse extracted.statement)
  | inr relation =>
      unfold preXIdentityRelation?
      rw [houtcome]
      rfl

theorem preXIdentityOutcome_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hsource : family.semanticSourceMismatchRelationFinder basis O = none)
    (witness : family.BatchWitness basis O)
    (rawDecode : DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O)
      ((family.runProof basis O).aMulti (family.runPreIpaReads basis O))
      ((family.runProof basis O).multiU (family.runPreIpaReads basis O))
      ((family.runProof basis O).multiBlind (family.runPreIpaReads basis O)))
    (hbatches : rawDecode.batches = witness.batches)
    (haccepts : DeployedAccepts (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1
      (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)))
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1
      (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)) <
        scalarFieldOrder)
    (hsupport :
      let output := family.runOutput basis O
      let source := output.proofData.algebraicProof.preX1AssemblySource
        (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
          family.fixedRepresentations basis)
      adaptiveActionPreXDifference pp basis output.inputs
        output.proofData.algebraicProof.erase source (family.runRecord basis O) = 0)
    (hgoodY :
      let decode := rawDecode.reRound (family.runIpaReads basis O)
      let model := CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
        (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) haccepts
      ∀ j, (family.runRecord basis O).y ∉
        szBadSet (foldSplitWitness model.constraints actionCircuit.n j))
    (hpermutation :
      let decode := rawDecode.reRound (family.runIpaReads basis O)
      ResolverPermutationChallengeExclusions pp.numProofs (adaptiveActionStatementVk pp basis)
        (family.runRecord basis O)
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
        actionActiveRows)
    (hlookup :
      let decode := rawDecode.reRound (family.runIpaReads basis O)
      TopLevelLookup.ChallengeExclusions actionCircuit pp
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
        (family.runRecord basis O)
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)) :
    (family.preXIdentityOutcome? basis O hsource witness rawDecode hbatches
      haccepts hchar).isSome := by
  let decode := rawDecode.reRound (family.runIpaReads basis O)
  let model := CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
    (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) haccepts
  let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts
  dsimp only at hsupport hgoodY hpermutation hlookup
  have hn : actionCircuit.n ≠ 0 := by
    change 2 ^ actionCircuit.domainExponent ≠ 0
    positivity
  have hySome := foldSplitAvoidance?_isSome_of model.constraints _ hn _ hgoodY
  have hpSome := resolverPermutationChallengeExclusions?_isSome_of _ _ _ _ _ hpermutation
  have hlSome := TopLevelLookup.topLevelLookupChallengeExclusions?_isSome_of
    actionCircuit pp (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
      _ _ hlookup
  obtain ⟨hgoodYProof, hgoodYEq⟩ := Option.isSome_iff_exists.mp hySome
  obtain ⟨hpermutationProof, hpermutationEq⟩ := Option.isSome_iff_exists.mp hpSome
  obtain ⟨hlookupProof, hlookupEq⟩ := Option.isSome_iff_exists.mp hlSome
  unfold preXIdentityOutcome?
  rw [dif_pos hsupport]
  dsimp only
  rw [hgoodYEq, hpermutationEq, hlookupEq]
  dsimp only
  split <;> rfl

/-- Execute just the identically-zero pre-`x` relation branch for one selected statement. -/
def identityRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
    family.Coins → Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    match hsource : family.semanticSourceMismatchRelationFinder basis O with
    | some relation => some relation
    | none =>
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
              | PSum.inr relation =>
                  some (ComputedStraightLineIpaFSFamily.straightLineCanonicalRelation relation)
              | PSum.inl witness =>
                  match family.batchGoodRoots? basis O witness with
                  | none => none
                  | some hroots =>
                      let hshifted := family.shiftedValue_of_accept_not_attack
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
                      family.preXIdentityRelation? basis O hsource witness rawDecode rfl
                        hacceptsFull hcharFull
          else none

theorem identityRelationFinder_none_source {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.identityRelationFinder hchar basis O = none) :
    family.semanticSourceMismatchRelationFinder basis O = none := by
  unfold identityRelationFinder at hnone
  split at hnone
  · simp_all
  · assumption

theorem identityRelationFinder_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hsource : family.semanticSourceMismatchRelationFinder basis O = none)
    (witness : family.BatchWitness basis O)
    (hout : family.batchOutcome basis O = PSum.inl witness)
    (hroots : family.BatchGoodRoots basis O witness)
    (haccepts : family.accepts basis O)
    (hz : family.runPreIpaReads basis O 10 ≠ 0)
    (hattack : ¬fullAlgebraicBindingAttackZ basis
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O) (family.runPreIpaReads basis O)
      (family.runIpaReads basis O))
    (hidentity :
      let hshifted := family.shiftedValue_of_accept_not_attack
        basis O haccepts hz hattack
      let rawDecode := family.rawDecodeOfBatchGoodRoots basis O witness hroots hshifted
      let hacceptsFull : DeployedAccepts (AdaptiveActionStatementShape pp)
          (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
          (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            (family.runOutput basis O).inputs)
          (family.runProof basis O).proof.1
          (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)) := by
        simpa only [accepts, family.runRecord_eq_chRecord] using haccepts
      let hcharFull : deployedX4PairCount (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            (family.runOutput basis O).inputs)
          (family.runProof basis O).proof.1
          (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)) <
            scalarFieldOrder := by
        simpa only [family.runRecord_eq_chRecord] using hchar basis O
      (family.preXIdentityRelation? basis O hsource witness rawDecode rfl
        hacceptsFull hcharFull).isSome) :
    (family.identityRelationFinder hchar basis O).isSome := by
  let hshifted := family.shiftedValue_of_accept_not_attack basis O haccepts hz hattack
  let rawDecode := family.rawDecodeOfBatchGoodRoots basis O witness hroots hshifted
  let hacceptsFull : DeployedAccepts (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1
      (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)) := by
    simpa only [accepts, family.runRecord_eq_chRecord] using haccepts
  let hcharFull : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1
      (chRecord (family.runPreIpaReads basis O) (family.runIpaReads basis O)) <
        scalarFieldOrder := by
    simpa only [family.runRecord_eq_chRecord] using hchar basis O
  have hacceptsSome := family.accepts?_isSome_of basis O haccepts
  obtain ⟨hacceptsProof, hacceptsEq⟩ := Option.isSome_iff_exists.mp hacceptsSome
  have hrootsSome := family.batchGoodRoots?_isSome_of basis O witness hroots
  obtain ⟨hrootsProof, hrootsEq⟩ := Option.isSome_iff_exists.mp hrootsSome
  obtain ⟨relation, hrelationEq⟩ := Option.isSome_iff_exists.mp hidentity
  unfold identityRelationFinder
  split
  · simp_all
  · rename_i hsource'
    have hsourceEq : hsource' = hsource := Subsingleton.elim _ _
    cases hsourceEq
    rw [hacceptsEq]
    dsimp only
    rw [dif_pos hz, dif_neg hattack, hout]
    dsimp only
    rw [hrootsEq]
    dsimp only
    rw [hrelationEq]
    rfl

/-- The existing nonzero semantic terminal returns relation data once its computed semantic
projection does. -/
theorem terminalRelationFinder_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (witness : family.BatchWitness basis O)
    (hout : family.batchOutcome basis O = PSum.inl witness)
    (hroots : family.BatchGoodRoots basis O witness)
    (haccepts : family.accepts basis O)
    (hz : family.runPreIpaReads basis O 10 ≠ 0)
    (hattack : ¬fullAlgebraicBindingAttackZ basis
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O) (family.runPreIpaReads basis O)
      (family.runIpaReads basis O))
    (hsemantic :
      let hshifted := family.shiftedValue_of_accept_not_attack
        basis O haccepts hz hattack
      let run : family.DecodedRun basis O :=
        { hchar := hchar basis O
          decode := family.decodeOfBatchGoodRoots basis O witness hroots hshifted
          accepts := haccepts }
      (family.semanticRelation? basis O run).isSome) :
    (family.terminalRelationFinder hchar basis O).isSome := by
  let hshifted := family.shiftedValue_of_accept_not_attack basis O haccepts hz hattack
  let run : family.DecodedRun basis O :=
    { hchar := hchar basis O
      decode := family.decodeOfBatchGoodRoots basis O witness hroots hshifted
      accepts := haccepts }
  have hacceptsSome := family.accepts?_isSome_of basis O haccepts
  obtain ⟨hacceptsProof, hacceptsEq⟩ := Option.isSome_iff_exists.mp hacceptsSome
  have hrootsSome := family.batchGoodRoots?_isSome_of basis O witness hroots
  obtain ⟨hrootsProof, hrootsEq⟩ := Option.isSome_iff_exists.mp hrootsSome
  obtain ⟨relation, hrelationEq⟩ := Option.isSome_iff_exists.mp hsemantic
  unfold terminalRelationFinder
  rw [hacceptsEq]
  dsimp only
  rw [dif_pos hz, dif_neg hattack, hout]
  dsimp only
  rw [hrootsEq]
  dsimp only
  rw [hrelationEq]
  rfl

end ComputedAdaptiveActionStatementFSFamily
end Zcash.Snark
