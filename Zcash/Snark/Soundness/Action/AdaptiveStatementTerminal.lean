import Zcash.Snark.Soundness.Action.AdaptiveStatementAccounting
import Zcash.Snark.Soundness.Action.AdaptiveTerminal

/-!
# Pointwise terminal for adaptive Action statements

This module feeds the statement and proof selected by one adaptive-statement run into the shared
Action semantic terminal.  In particular, every terminal type is indexed by the selected public
inputs rather than by an input fixed outside the random-oracle experiment.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)

local instance adaptiveStatementTerminalVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- The represented proof selected by one adaptive-statement run. -/
abbrev runProof {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :=
  (family.runOutput basis O).toAlgebraicWfProof

/-- The eleven pre-IPA answers read at the selected statement's canonical prefixes. -/
def runPreIpaReads {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Fin 11 → Fp :=
  fun i => O ((family.runOutput basis O).prefixesPre (family.vkTranscriptRepr basis) i)

@[simp] theorem runRecord_eq_chRecord {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.runRecord basis O = chRecord (family.runPreIpaReads basis O)
      (fun j => O ((family.runOutput basis O).prefixes
        (family.vkTranscriptRepr basis) j)) := by
  rfl

/-- The pre-IPA challenge record used by the direct multiopen decoder. -/
def runPreIpaRecord {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Challenges (AdaptiveActionStatementShape pp).k Fp :=
  chRecord (family.runPreIpaReads basis O) (fun _ => 0)

/-- The IPA-round answers used to transport a pre-IPA decode to the full verifier record. -/
def runIpaReads {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Fin (AdaptiveActionStatementShape pp).k → Fp :=
  fun j => O ((family.runOutput basis O).prefixes (family.vkTranscriptRepr basis) j)

/-- The selected proof's exact direct `x₄` online-coordinate source. -/
abbrev batchX4Source {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :=
  deployedX4ColumnRepresentationsOfCovered
    (family.runProof basis O)
    (adaptiveStatementInstanceRepresentationList
        (family.runOutput basis O).instanceRepresentations ++
      family.fixedRepresentations basis)
    (family.runOutput basis O).proofData.membersCovered
    (family.runPreIpaReads basis O)

/-- The direct unbatcher's successful branch, retaining the online-coordinate equalities needed
to identify both the six root surfaces and the later semantic resolver with the selected proof.
Unlike `DeployedBatchWitness`, this record is indexed directly by the adaptive statement output,
so its instance commitment may vary with the oracle table. -/
structure BatchWitness {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) where
  batches : DeployedAlgebraicBatches
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O)
    ((family.runProof basis O).aMulti (family.runPreIpaReads basis O))
    ((family.runProof basis O).multiU (family.runPreIpaReads basis O))
    ((family.runProof basis O).multiBlind (family.runPreIpaReads basis O))
  x4Coeffs : batches.x4.coeffs = (family.batchX4Source basis O).coeffs
  x4U : batches.x4.uComp = (family.batchX4Source basis O).uComp
  x4W : batches.x4.wComp = (family.batchX4Source basis O).wComp
  memberCoeffs : ∀ i
      (hi : i < deployedX4PairCount (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
        (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O)),
    (batches.x1 i hi).coeffs =
      (deployedMemberRepresentationsOfCovered (family.runProof basis O)
        (adaptiveStatementInstanceRepresentationList
            (family.runOutput basis O).instanceRepresentations ++
          family.fixedRepresentations basis)
        (family.runOutput basis O).proofData.membersCovered
        (family.runPreIpaReads basis O) i hi).coeffs
  memberU : ∀ i
      (hi : i < deployedX4PairCount (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
        (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O)),
    (batches.x1 i hi).uComp =
      (deployedMemberRepresentationsOfCovered (family.runProof basis O)
        (adaptiveStatementInstanceRepresentationList
            (family.runOutput basis O).instanceRepresentations ++
          family.fixedRepresentations basis)
        (family.runOutput basis O).proofData.membersCovered
        (family.runPreIpaReads basis O) i hi).uComp
  memberW : ∀ i
      (hi : i < deployedX4PairCount (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
        (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O)),
    (batches.x1 i hi).wComp =
      (deployedMemberRepresentationsOfCovered (family.runProof basis O)
        (adaptiveStatementInstanceRepresentationList
            (family.runOutput basis O).instanceRepresentations ++
          family.fixedRepresentations basis)
        (family.runOutput basis O).proofData.membersCovered
        (family.runPreIpaReads basis O) i hi).wComp

/-- The retained direct `x₄` columns reconstruct the selected proof's canonical aggregate. -/
theorem BatchWitness.x4Source_reconstruct {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {O : family.Coins} (witness : family.BatchWitness basis O) :
    (∑ j : Fin (deployedX4PairCount (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
        (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O) + 1),
      (family.runPreIpaRecord basis O).x4 ^ (j : Nat) •
        (family.batchX4Source basis O).coeffs j) =
      (family.runProof basis O).aMulti (family.runPreIpaReads basis O) := by
  rw [← witness.x4Coeffs]
  exact witness.batches.x4.reconstruct.symm

/-- The same retained columns reconstruct the aggregate `u` coordinate. -/
theorem BatchWitness.x4Source_reconstructU {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {O : family.Coins} (witness : family.BatchWitness basis O) :
    (∑ j : Fin (deployedX4PairCount (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
        (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O) + 1),
      (family.runPreIpaRecord basis O).x4 ^ (j : Nat) *
        (family.batchX4Source basis O).uComp j) =
      (family.runProof basis O).multiU (family.runPreIpaReads basis O) := by
  rw [← witness.x4U]
  exact witness.batches.x4.reconstructU.symm

set_option maxHeartbeats 3200000 in
/-- Construct the direct deployed batches for the selected statement, or expose the first
nontrivial AGM relation encountered while unbatching. -/
def batchOutcome {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.BatchWitness basis O ⊕'
      AugmentedRelationWitness (F := Fp)
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).g
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).u
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w :=
  let output := family.runOutput basis O
  let proof := family.runProof basis O
  let nu := family.runPreIpaReads basis O
  let fixed := adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
    family.fixedRepresentations basis
  match deployedX4BatchOfCoveredWithSourceOrRelation proof fixed
      output.proofData.membersCovered nu with
  | PSum.inr relation => PSum.inr relation
  | PSum.inl x4Result =>
      let x4Batch := x4Result.batch
      match finForallOrRelationWitness (fun i :
          Fin (deployedX4PairCount (adaptiveActionStatementVk pp basis)
            (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
            proof.proof.1 (family.runPreIpaRecord basis O)) =>
          deployedX1BatchOfCoveredWithSourceOrRelation proof fixed
            output.proofData.membersCovered nu x4Batch i i.isLt) with
      | PSum.inr relation => PSum.inr relation
      | PSum.inl results => PSum.inl
          { batches :=
              { x4 := x4Batch
                x1 := fun i hi => (results ⟨i, hi⟩).batch }
            x4Coeffs := x4Result.coeffs_eq
            x4U := x4Result.uComp_eq
            x4W := x4Result.wComp_eq
            memberCoeffs := fun i hi => (results ⟨i, hi⟩).coeffs_eq
            memberU := fun i hi => (results ⟨i, hi⟩).uComp_eq
            memberW := fun i hi => (results ⟨i, hi⟩).wComp_eq }

/-- The six direct root exclusions for one successfully constructed batch set. -/
structure BatchGoodRoots {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (witness : family.BatchWitness basis O) : Prop where
  x1 : (family.runPreIpaRecord basis O).x1 ∉ deployedX1AllRootSet
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O) witness.batches
  x2 : (family.runPreIpaRecord basis O).x2 ∉ deployedX2RootSet
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O) witness.batches
  x3 : (family.runPreIpaRecord basis O).x3 ∉ deployedX3RootSet
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O) witness.batches
  x4 : (family.runPreIpaRecord basis O).x4 ∉ deployedX4RootSet
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O) witness.batches
  xi : (family.runPreIpaRecord basis O).xi ∉ szBadSet (ipaShiftXiPolynomial
    (commitGen (evalVector (AdaptiveActionStatementShape pp).k
        (family.runPreIpaRecord basis O).x3)
      ((family.runProof basis O).aMulti (family.runPreIpaReads basis O)) -
        multiopenValue (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            (family.runOutput basis O).inputs)
          (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O))
    (commitGen (evalVector (AdaptiveActionStatementShape pp).k
      (family.runPreIpaRecord basis O).x3) (family.runProof basis O).s))
  z : (family.runPreIpaRecord basis O).z ∉ szBadSet (ipaShiftZPolynomial
    (commitGen (evalVector (AdaptiveActionStatementShape pp).k
        (family.runPreIpaRecord basis O).x3)
      ((family.runProof basis O).aMulti (family.runPreIpaReads basis O)) -
        multiopenValue (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            (family.runOutput basis O).inputs)
          (family.runProof basis O).proof.1 (family.runPreIpaRecord basis O))
    ((family.runProof basis O).multiU (family.runPreIpaReads basis O))
    (family.runProof basis O).sU
    (commitGen (evalVector (AdaptiveActionStatementShape pp).k
      (family.runPreIpaRecord basis O).x3) (family.runProof basis O).s)
    (family.runPreIpaRecord basis O).xi)

/-- The shifted aggregate equality obtained from acceptance outside the IPA binding event. -/
def ShiftedValue {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Prop :=
  let ch := family.runPreIpaRecord basis O
  ch.z ≠ 0 ∧
    commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
        ((family.runProof basis O).aMulti (family.runPreIpaReads basis O)) =
      multiopenValue (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            (family.runOutput basis O).inputs)
          (family.runProof basis O).proof.1 ch +
        ch.z⁻¹ * ((family.runProof basis O).multiU (family.runPreIpaReads basis O) +
          ch.xi * (family.runProof basis O).sU) -
        ch.xi * commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
          (family.runProof basis O).s

set_option maxHeartbeats 800000 in
/-- Good direct roots and the shifted verifier equality decode the selected proof, then transport
the decode across the actual IPA-round challenges. -/
def decodeOfBatchGoodRoots {pp : ProofParams}
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
      (family.runProof basis O).proof.1 (family.runRecord basis O)
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
  exact (deployedAlgebraicDecode_of_good_roots
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 ch witness.batches hvalue hgood.x4 hgood.x3 hgood.x2 hgood1).reRound
      (family.runIpaReads basis O)

/-- Executable deployed-acceptance certificate for the selected statement and proof. -/
def accepts? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (PLift (family.accepts basis O)) :=
  match hassemble : assemble? (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) with
  | none => none
  | some msm =>
      if hzero : msm.eval
          (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) = 0 then
        some ⟨by
          unfold accepts
          dsimp only
          unfold DeployedAccepts
          rw [hassemble]
          exact hzero⟩
      else none

/-- Run all six finite deployed-root checks for one selected batch set. -/
def batchGoodRoots? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (witness : family.BatchWitness basis O) :
    Option (PLift (family.BatchGoodRoots basis O witness)) :=
  let ch := family.runPreIpaRecord basis O
  let urs := ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis
  let delta := commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
      ((family.runProof basis O).aMulti (family.runPreIpaReads basis O)) -
    multiopenValue (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 ch
  let sEval := commitGen (evalVector (AdaptiveActionStatementShape pp).k ch.x3)
    (family.runProof basis O).s
  match deployedX1RootAvoidance? urs rfl (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 ch witness.batches with
  | none => none
  | some hx1 =>
      match deployedX2RootAvoidance? urs rfl (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis
            (family.runOutput basis O).inputs)
          (family.runProof basis O).proof.1 ch witness.batches with
      | none => none
      | some hx2 =>
          match deployedX3RootAvoidance? urs rfl (adaptiveActionStatementVk pp basis)
              (adaptiveActionStatementInstanceCommitment pp basis
                (family.runOutput basis O).inputs)
              (family.runProof basis O).proof.1 ch witness.batches with
          | none => none
          | some hx3 =>
              match deployedX4RootAvoidance? urs rfl (adaptiveActionStatementVk pp basis)
                  (adaptiveActionStatementInstanceCommitment pp basis
                    (family.runOutput basis O).inputs)
                  (family.runProof basis O).proof.1 ch witness.batches with
              | none => none
              | some hx4 =>
                  match deployedXiRootAvoidance? delta sEval ch.xi with
                  | none => none
                  | some hxi =>
                      match deployedZRootAvoidance? delta
                          ((family.runProof basis O).multiU (family.runPreIpaReads basis O))
                          (family.runProof basis O).sU sEval ch.xi ch.z with
                      | none => none
                      | some hz => some ⟨{
                          x1 := by simpa only using hx1.down
                          x2 := by simpa only using hx2.down
                          x3 := by simpa only using hx3.down
                          x4 := by simpa only using hx4.down
                          xi := by simpa only using hxi.down
                          z := by simpa only using hz.down }⟩

set_option maxHeartbeats 800000 in
/-- Acceptance and absence of the guarded IPA binding attack imply the shifted decoder equality. -/
theorem shiftedValue_of_accept_not_attack {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (haccept : family.accepts basis O)
    (hz : family.runPreIpaReads basis O 10 ≠ 0)
    (hnot : ¬fullAlgebraicBindingAttackZ basis (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O) (family.runPreIpaReads basis O)
      (family.runIpaReads basis O)) :
    family.ShiftedValue basis O := by
  let proof := family.runProof basis O
  let nu := family.runPreIpaReads basis O
  let rounds := family.runIpaReads basis O
  have hdeployed : DeployedAccepts (AdaptiveActionStatementShape pp)
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
      (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      proof.proof.1 (chRecord nu rounds) := by
    simpa only [accepts, runRecord, nu, rounds, proof] using haccept
  have hacceptFull : fullAlgebraicAccept basis (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      proof nu rounds :=
    fullAlgebraicAccept_of_deployed basis (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      proof nu rounds hdeployed
  have heq : innerProduct (proof.aMulti nu)
      (evalVector (AdaptiveActionStatementShape pp).k (nu 7)) =
      multiopenValue (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
        proof.proof.1 (chRecord nu (fun _ => 0)) +
      (nu 10)⁻¹ * (proof.multiU nu + nu 9 * proof.sU) -
        nu 9 * innerProduct proof.s
          (evalVector (AdaptiveActionStatementShape pp).k (nu 7)) := by
    by_contra hmismatch
    exact hnot ⟨⟨hacceptFull, hmismatch⟩, hz⟩
  constructor
  · simpa only [ShiftedValue, runPreIpaRecord, chRecord, nu, proof] using hz
  · simpa only [ShiftedValue, runPreIpaRecord, chRecord, nu, proof, commitGen,
      innerProduct] using heq

/-- Decode and acceptance evidence for the exact statement selected by one run. -/
structure DecodedRun {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) where
  hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder
  decode : DeployedAlgebraicDecode (AdaptiveActionStatementShape pp)
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 (family.runRecord basis O)
    ((family.runProof basis O).aMulti (family.runPreIpaReads basis O))
    ((family.runProof basis O).multiU (family.runPreIpaReads basis O))
    ((family.runProof basis O).multiBlind (family.runPreIpaReads basis O))
  accepts : family.accepts basis O

/-- The four finite semantic exclusions consumed by the shared Action terminal. -/
structure SemanticExclusions {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (run : family.DecodedRun basis O) where
  xGood :
    let model := CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := fun i hi => run.decode.toMemberDecode run.hchar i hi)
      (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) run.accepts
    let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := fun i hi => run.decode.toMemberDecode run.hchar i hi) run.accepts
    (family.runRecord basis O).x ∉ szBadSet
      (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
        model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
        (family.runRecord basis O).y model.chunkLen model.l0 model.lLast model.lBlind -
          polynomial .vanishingH * (X ^ actionCircuit.n - 1))
  yGood :
    let model := CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := fun i hi => run.decode.toMemberDecode run.hchar i hi)
      (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)) run.accepts
    ∀ j, (family.runRecord basis O).y ∉
      szBadSet (foldSplitWitness model.constraints actionCircuit.n j)
  permutation : ResolverPermutationChallengeExclusions pp.numProofs
    (adaptiveActionStatementVk pp basis) (family.runRecord basis O)
    (CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := fun i hi => run.decode.toMemberDecode run.hchar i hi) run.accepts)
    actionActiveRows
  lookup : TopLevelLookup.ChallengeExclusions actionCircuit pp
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)
    (family.runRecord basis O)
    (CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := fun i hi => run.decode.toMemberDecode run.hchar i hi) run.accepts)

/-- Execute the semantic terminal at the adversary-selected statement. -/
def semanticOutcome? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (run : family.DecodedRun basis O) :
    Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) :=
  ActionTerminal.actionWitnessOrRelationOfDecode? pp basis
    (family.runOutput basis O).inputs (family.runProof basis O).proof.1
    ((family.runProof basis O).aMulti (family.runPreIpaReads basis O))
    ((family.runProof basis O).multiU (family.runPreIpaReads basis O))
    ((family.runProof basis O).multiBlind (family.runPreIpaReads basis O))
    (family.runRecord basis O) run.hchar run.decode run.accepts

/-- Project explicit relation data from the pointwise semantic outcome. -/
def semanticRelation? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (run : family.DecodedRun basis O) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match family.semanticOutcome? basis O run with
  | some (Sum.inr relation) => some relation
  | _ => none

set_option maxRecDepth 10000 in
/-- Successful semantic exclusions produce witness data or relation data for the selected inputs. -/
theorem semanticOutcome?_isSome_of {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (run : family.DecodedRun basis O)
    (good : family.SemanticExclusions basis O run) :
    (family.semanticOutcome? basis O run).isSome := by
  exact ActionTerminal.actionWitnessOrRelationOfDecode?_isSome_of pp basis
    (family.runOutput basis O).inputs (family.runProof basis O).proof.1
    ((family.runProof basis O).aMulti (family.runPreIpaReads basis O))
    ((family.runProof basis O).multiU (family.runPreIpaReads basis O))
    ((family.runProof basis O).multiBlind (family.runPreIpaReads basis O))
    (family.runRecord basis O) run.hchar run.decode run.accepts
    good.xGood good.yGood good.permutation good.lookup

/-- On a false selected statement, a complete semantic outcome cannot be the witness branch. -/
theorem semanticRelation?_isSome_of_false {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (run : family.DecodedRun basis O)
    (good : family.SemanticExclusions basis O run)
    (hfalse : ¬BundleStatement (family.runOutput basis O).inputs) :
    (family.semanticRelation? basis O run).isSome := by
  obtain ⟨outcome, houtcome⟩ := Option.isSome_iff_exists.mp
    (family.semanticOutcome?_isSome_of basis O run good)
  cases outcome with
  | inl witness => exact False.elim (hfalse witness.statement)
  | inr relation =>
      unfold semanticRelation?
      rw [houtcome]
      rfl

/-- The computed relation finder for one adaptive-statement run.  Acceptance, batch construction,
root checks, decoding, and semantic checks all use the statement selected in that same run. -/
noncomputable def terminalRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
    family.Coins → Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
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
            match proof.straightLineBindingAttackZIndexedRootOrRelation nu rounds hattack with
            | PSum.inl _ => none
            | PSum.inr relation =>
                some (ComputedStraightLineIpaFSFamily.straightLineCanonicalRelation relation)
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
                    let run : family.DecodedRun basis O :=
                      { hchar := hchar basis O
                        decode := family.decodeOfBatchGoodRoots basis O witness
                          hroots.down hshifted
                        accepts := haccepts }
                    family.semanticRelation? basis O run
        else none

end ComputedAdaptiveActionStatementFSFamily

end Zcash.Snark
