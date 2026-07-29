import Zcash.Circuits.Integration.AdaptiveActionTerminal
import Zcash.Circuits.Integration.StraightLineActionBudgets
import Zcash.Snark.Soundness.AGM.AdaptiveSurfaces

/-!
# Action semantic surfaces for arbitrary adaptive online-AGM adversaries

The first five deployed squeezes are `theta`, `beta`, `gamma`, `y`, and `x`.  At each point an
online-AGM annotation fixes exactly the prover commitments already absorbed into that prefix.
This file records those stage-local representation lists before constructing the corresponding
finite bad sets.
-/

namespace Zcash.Snark

open Classical
open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open scoped ENNReal

variable {shape : Shape}

local instance vestaInhabitedAdaptiveActionSurfaces : Inhabited VestaG := ⟨0⟩

set_option maxRecDepth 10000

/-- Prover-emitted AGM representations available at one of the five Action semantic squeezes.
The definition follows the deployed transcript order literally. -/
def AlgebraicProofString.actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5) :
    List (AlgebraicPoint (F := Fp) basis) :=
  let advice :=
    (List.ofFn fun p => List.ofFn fun i => aps.adviceCommitments p i).flatten
  let lookupPermuted :=
    (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedInput p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedTable p i).flatten
  let products :=
    (List.ofFn fun p => List.ofFn fun i => aps.permutationProduct p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => aps.lookupProduct p i).flatten ++
      [aps.vanishingRandom]
  if (n : Nat) = 0 then advice
  else if (n : Nat) < 3 then advice ++ lookupPermuted
  else if (n : Nat) = 3 then advice ++ lookupPermuted ++ products
  else advice ++ lookupPermuted ++ products ++ List.ofFn aps.hPieces

/-- Coordinate-free counterpart of `actionRepresentationsBefore`. -/
def ProofString.actionCommitmentPointsBefore {G : Type*}
    (ps : ProofString shape Fp G) (n : Fin 5) : List G :=
  let advice :=
    (List.ofFn fun p => List.ofFn fun i => ps.adviceCommitments p i).flatten
  let lookupPermuted :=
    (List.ofFn fun p => List.ofFn fun i => ps.lookupPermutedInput p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => ps.lookupPermutedTable p i).flatten
  let products :=
    (List.ofFn fun p => List.ofFn fun i => ps.permutationProduct p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => ps.lookupProduct p i).flatten ++
      [ps.vanishingRandom]
  if (n : Nat) = 0 then advice
  else if (n : Nat) < 3 then advice ++ lookupPermuted
  else if (n : Nat) = 3 then advice ++ lookupPermuted ++ products
  else advice ++ lookupPermuted ++ products ++ List.ofFn ps.hPieces

@[simp] theorem AlgebraicProofString.actionRepresentationsBefore_points
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5) :
    (aps.actionRepresentationsBefore n).map AlgebraicPoint.point =
      aps.erase.actionCommitmentPointsBefore n := by
  fin_cases n <;>
    simp [AlgebraicProofString.actionRepresentationsBefore,
      ProofString.actionCommitmentPointsBefore, AlgebraicProofString.erase,
      Function.comp_def, List.map_flatten]

/-- Every representation used by an Action semantic surface occurs in the complete pre-`x`
online source. -/
theorem AlgebraicProofString.actionRepresentationsBefore_mem_preX1Points
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5)
    (ap : AlgebraicPoint (F := Fp) basis)
    (hap : ap ∈ aps.actionRepresentationsBefore n) :
    ap ∈ aps.preX1Points := by
  fin_cases n <;>
    simp [AlgebraicProofString.actionRepresentationsBefore,
      AlgebraicProofString.preX1Points] at hap ⊢ <;> aesop

/-- Appending verifier-fixed representations preserves inclusion in the complete pre-`x`
assembly source. -/
theorem AlgebraicProofString.actionStageSource_subset_preX1AssemblySource
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) (n : Fin 5)
    (ap : AlgebraicPoint (F := Fp) basis)
    (hap : ap ∈ aps.actionRepresentationsBefore n ++ fixed) :
    ap ∈ aps.preX1AssemblySource fixed := by
  unfold AlgebraicProofString.preX1AssemblySource
  rw [List.mem_append] at hap ⊢
  exact hap.imp (aps.actionRepresentationsBefore_mem_preX1Points n ap) id

/-- Every stage-local prover representation is already present in that stage's actual query
transcript. -/
theorem AlgebraicProofString.actionRepresentationsBefore_covered
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (aps : AlgebraicProofString shape basis) (hwf : PsWellFormed aps.erase) (n : Fin 5)
    (ap : AlgebraicPoint (F := Fp) basis)
    (hap : ap ∈ aps.actionRepresentationsBefore n) :
    ap.point ∈ transcriptGroupPoints
      (preIpaSqueezePoints init aps.erase (Fin.castLE (by omega) n)) := by
  have lift {P : VestaG} {i j : Fin 11} (hij : (i : Nat) ≤ (j : Nat))
      (hmem : TranscriptElt.point P ∈ preIpaSqueezePoints init aps.erase i) :
      P ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase j) := by
    apply (transcriptGroupPoints_prefix
      (preIpaSqueezePoints_prefix_of_le init aps.erase hwf i j hij)).mem
    exact mem_transcriptGroupPoints_of_mem_point hmem
  fin_cases n
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 0)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    obtain ⟨p, i, h⟩ := hap
    rw [← h]
    exact mem_transcriptGroupPoints_of_mem_point
      (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 1)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 1) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 2)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 2) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 3)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable | hperm | hlookup | hrandom
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 3) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hperm
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (permutationProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hlookup
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · rw [hrandom]
      exact mem_transcriptGroupPoints_of_mem_point
        (vanishingRandom_mem_preIpaSqueezePoints_three init aps.erase)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 4)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable | hperm | hlookup | hrandom | hpiece
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 4) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hperm
      rw [← h]
      exact lift (i := 3) (j := 4) (by omega)
        (permutationProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hlookup
      rw [← h]
      exact lift (i := 3) (j := 4) (by omega)
        (lookupProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · rw [hrandom]
      exact lift (i := 3) (j := 4) (by omega)
        (vanishingRandom_mem_preIpaSqueezePoints_three init aps.erase)
    · obtain ⟨i, h⟩ := hpiece
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (hPiece_mem_preIpaSqueezePoints_four init aps.erase i)

/-- Ordinary commitment points in the stage view are covered by the same exact prefix. -/
theorem ProofString.actionCommitmentPointsBefore_covered
    (init : List (TranscriptElt Fp VestaG))
    (ps : ProofString shape Fp VestaG) (hwf : PsWellFormed ps) (n : Fin 5)
    (P : VestaG) (hP : P ∈ ps.actionCommitmentPointsBefore n) :
    P ∈ transcriptGroupPoints
      (preIpaSqueezePoints init ps (Fin.castLE (by omega) n)) := by
  have lift {P : VestaG} {i j : Fin 11} (hij : (i : Nat) ≤ (j : Nat))
      (hmem : TranscriptElt.point P ∈ preIpaSqueezePoints init ps i) :
      P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps j) := by
    apply (transcriptGroupPoints_prefix
      (preIpaSqueezePoints_prefix_of_le init ps hwf i j hij)).mem
    exact mem_transcriptGroupPoints_of_mem_point hmem
  fin_cases n
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 0)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    obtain ⟨p, i, rfl⟩ := hP
    exact mem_transcriptGroupPoints_of_mem_point
      (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 1)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 1) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 2)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 2) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 3)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable | hperm | hlookup | hrandom
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 3) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := hperm
      exact mem_transcriptGroupPoints_of_mem_point
        (permutationProduct_mem_preIpaSqueezePoints_three init ps p i)
    · obtain ⟨p, i, rfl⟩ := hlookup
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupProduct_mem_preIpaSqueezePoints_three init ps p i)
    · subst P
      exact mem_transcriptGroupPoints_of_mem_point
        (vanishingRandom_mem_preIpaSqueezePoints_three init ps)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 4)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable | hperm | hlookup | hrandom | hpiece
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 4) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := hperm
      exact lift (i := 3) (j := 4) (by omega)
        (permutationProduct_mem_preIpaSqueezePoints_three init ps p i)
    · obtain ⟨p, i, rfl⟩ := hlookup
      exact lift (i := 3) (j := 4) (by omega)
        (lookupProduct_mem_preIpaSqueezePoints_three init ps p i)
    · subst P
      exact lift (i := 3) (j := 4) (by omega)
        (vanishingRandom_mem_preIpaSqueezePoints_three init ps)
    · obtain ⟨i, rfl⟩ := hpiece
      exact mem_transcriptGroupPoints_of_mem_point
        (hPiece_mem_preIpaSqueezePoints_four init ps i)

/-- Query-local stage source: first pre-answer representations of exactly the Action commitments
already absorbed at this squeeze, followed by verifier-fixed representations. -/
def adaptiveActionQuerySource
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 5)
    {t : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)}
    (decoded : DecodedPreIpaPrefix (shape := shape) init (Fin.castLE (by omega) n) t)
    (query : AlgebraicTranscriptQuery (F := Fp) basis t)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) :
    List (AlgebraicPoint (F := Fp) basis) :=
  query.representationsForPoints
      (decoded.proof.1.actionCommitmentPointsBefore n) (by
        intro P hP
        rw [← decoded.point_eq]
        exact decoded.proof.1.actionCommitmentPointsBefore_covered
          init decoded.proof.2 n P hP) ++ fixed

/-- Canonical polynomial carried by a stage-local AGM source. -/
def adaptiveActionPointPolynomial
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (source : List (AlgebraicPoint (F := Fp) basis)) :
    VestaG → Polynomial Fp :=
  onlinePointPolynomial source

/-- Commitment slots actually consumed by the constraint model.  Returning zero outside this
finite layout makes the stage resolver agree with canonical routing on absent identities. -/
def adaptiveActionCommitmentActive
    {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G) : CommitmentId → Prop
  | .instanceCol p i => p < shape.numProofs ∧
      ∃ rotation, (i, rotation) ∈ vk.instanceQueryLayout
  | .adviceCol p i => p < shape.numProofs ∧ i < shape.numAdviceColumns ∧
      ∃ rotation, (i, rotation) ∈ vk.adviceQueryLayout
  | .fixedCol i => ∃ rotation, (i, rotation) ∈ vk.fixedQueryLayout
  | .permProduct p s => p < shape.numProofs ∧ s < shape.numPermutationSets
  | .lookupProduct p l | .lookupPermInput p l | .lookupPermTable p l =>
      p < shape.numProofs ∧ l < shape.numLookups
  | .permCommon c => c < shape.numPermutationColumns
  | .vanishingH | .randomPoly => False

noncomputable instance adaptiveActionCommitmentActive_decidable
    {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G) (id : CommitmentId) :
    Decidable (adaptiveActionCommitmentActive vk id) := inferInstance

/-- Commitment-ID resolver induced by the stage-local point coordinates.  The quotient slot is
assembled from the explicit piece coordinates already present before `x`. -/
noncomputable def adaptiveActionCommitmentPolynomial
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp) :
    CommitmentId → Polynomial Fp :=
  let vk := ActionTerminal.vkAt pp basis
  let ic := actionCircuit.instanceCommitment pp
    (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs
  let pointPoly := adaptiveActionPointPolynomial source
  fun id =>
    if adaptiveActionCommitmentActive vk id then
        match assembledCommitment vk ic ps ch id with
        | .point P => pointPoly P
        | .msm _ => ComputablePolynomial.zero
    else ComputablePolynomial.zero

/-- The constraint model determined before `y`/`x` by the commitments already in the transcript. -/
noncomputable def adaptiveActionCommittedModel
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp) :
    ConstraintPolyModel (pp.mergeDerived actionCircuit).numProofs :=
  let urs := ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis
  canonicalConstraintModelOfPermutationResolver
    (ActionTerminal.vkAt pp basis) ch
    (adaptiveActionCommitmentPolynomial pp basis inputs ps source ch)
    (ActionPermutationDomain.blindingFactors_lt pp urs)

set_option maxHeartbeats 800000 in
/-- A plain commitment routed by an accepting adaptive decode carries the polynomial fixed by
the run's online pre-`x` AGM source. -/
theorem adaptiveAcceptedPolynomial_eq_online_of_query
    (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (pnu : WrappedAlgebraicOutput family basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (witness : DeployedBatchWitness family basis pnu)
    (hsrc : witness.fixedRepresentations = fixed)
    (decode : DeployedAlgebraicDecode (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu)
      (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decode.batches = witness.batches)
    (hchar : deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1
      (wrappedPreIpaRecord pnu) < Zcash.Arithmetic.scalarFieldOrder)
    (haccepts : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu))
    (id : CommitmentId) (q : VerifierQuery shape.k Fp VestaG)
    (hq : q ∈ assembleQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1
      (wrappedPreIpaRecord pnu))
    (hqid : q.commId = id) (P : VestaG)
    (hpoint : assembledCommitment (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1
      (wrappedPreIpaRecord pnu) id = .point P) :
    CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts id =
      onlinePointPolynomial (pnu.1.algebraicProof.preX1AssemblySource fixed) P := by
  let routing := canonicalRoutingConditions_of_accepts
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
    (family.instanceCommitment basis)
    pnu.1.proof.1 (wrappedPreIpaRecord pnu) haccepts
  have routed := assembledQueryMemberRoute_faithful
    (instanceCommitment := family.instanceCommitment basis)
    (family.vk basis) pnu.1.proof.1
    (wrappedPreIpaRecord pnu) routing.1 routing.2 q hq
  have hmemberPoint : ((deployedSetQueries (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) routed.slot.setIndex).getD
        (routed.slot.memberIndex : Nat) (.point 0, [])).1 = .point P := by
    rw [deployed_member_commitment_eq_assembled
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu) routed.slot.setIndex
        routed.slot.memberIndex CommitmentId.vanishingH
        (assembledQueryMemberRoute_id
          (instanceCommitment := family.instanceCommitment basis)
          (family.vk basis) pnu.1.proof.1
          (wrappedPreIpaRecord pnu)
          routing.1 routing.2 id routed.slot
          (by simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing, ← hqid]
            using routed.route_eq)) (.point 0, [])]
    exact hpoint
  have hmember : decode.memberPoly routed.slot.setIndex routed.slot.setIndex_lt
        routed.slot.memberIndex =
      onlinePointPolynomial (pnu.1.algebraicProof.preX1AssemblySource fixed) P := by
    unfold DeployedAlgebraicDecode.memberPoly onlinePointPolynomial
    rw [hbatches, ← hsrc]
    rw [congrFun (witness.memberCoeffs routed.slot.setIndex routed.slot.setIndex_lt)
      routed.slot.memberIndex]
    exact congrArg coeffsToPoly
      (deployedMemberRepresentationsOfCovered_coeffs_point
        pnu.1
        witness.fixedRepresentations witness.membersCovered
        (wrappedPreIpaReads pnu)
        routed.slot.setIndex routed.slot.setIndex_lt routed.slot.memberIndex P hmemberPoint)
  have hroute : CanonicalMemberConstraintRelation.acceptedRoute haccepts id =
      some routed.slot := by
    simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing, ← hqid] using
      routed.route_eq
  unfold CanonicalMemberConstraintRelation.acceptedPolynomial decodedPolynomialResolver
  rw [hroute]
  exact hmember

/-- Compare one stage-local representation with the deterministic first representation of the
same point in the complete pre-`x` source. -/
def representationAgainstSourceMismatch?
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ap : AlgebraicPoint (F := Fp) basis) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match hfound : source.find? (fun candidate => candidate.point = ap.point) with
  | none => none
  | some first => representationMismatchRelation? first ap (by
      simpa using List.find?_some hfound)

/-- Return the first mismatch between a stage source and the complete pre-`x` source. -/
def representationSourceMismatchFinder
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (source target : List (AlgebraicPoint (F := Fp) basis)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    (target.map (representationAgainstSourceMismatch? source))

/-- With no source-collision relation, deterministic point lookup gives the same polynomial in
the stage source and the complete pre-`x` source. -/
theorem onlinePointPolynomial_eq_of_sourceMismatch_none
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (source target : List (AlgebraicPoint (F := Fp) basis))
    (hsub : ∀ ap ∈ target, ap ∈ source)
    (hnone : representationSourceMismatchFinder source target = none)
    (P : VestaG) (hP : ∃ ap ∈ target, ap.point = P) :
    onlinePointPolynomial source P = onlinePointPolynomial target P := by
  obtain ⟨ap, hap, rfl⟩ := hP
  have htargetSome : (target.find? (fun candidate => candidate.point = ap.point)).isSome := by
    rw [List.find?_isSome]
    exact ⟨ap, hap, by simp⟩
  obtain ⟨stage, hstage⟩ := Option.isSome_iff_exists.mp htargetSome
  have hstageMem : stage ∈ target := List.mem_of_find?_eq_some hstage
  have hstagePoint : stage.point = ap.point := by
    simpa using List.find?_some hstage
  have hsourceSome : (source.find? (fun candidate => candidate.point = ap.point)).isSome := by
    rw [List.find?_isSome]
    exact ⟨stage, hsub stage hstageMem, by simpa [hstagePoint]⟩
  obtain ⟨first, hfirst⟩ := Option.isSome_iff_exists.mp hsourceSome
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1 hnone
  have hmismatch : representationAgainstSourceMismatch? source stage = none := by
    apply hall
    exact List.mem_map.mpr ⟨stage, hstageMem, rfl⟩
  have hfirstStage : source.find? (fun candidate => candidate.point = stage.point) =
      some first := by
    simpa only [hstagePoint] using hfirst
  have hcoeff : first.coeffs = stage.coeffs := by
    unfold representationAgainstSourceMismatch? at hmismatch
    split at hmismatch
    · rename_i hnone
      rw [hfirstStage] at hnone
      contradiction
    · rename_i found hfound
      have hfoundEq : found = first := Option.some.inj (hfound.symm.trans hfirstStage)
      subst found
      exact (representationMismatchRelation?_eq_none_iff first stage (by
        simpa using List.find?_some hfirstStage)).1 hmismatch
  unfold onlinePointPolynomial onlinePointCoordinates
  rw [hfirst, hstage]
  apply congrArg coeffsToPoly
  funext i
  exact congrFun hcoeff (AugmentedIndex.gen i)

/-- One of the five exact Action semantic bad sets, reconstructed only from the stage prefix,
earlier oracle answers, and stage-local AGM coordinates. -/
noncomputable def adaptiveActionSurfaceAt
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (n : Fin 5)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  let nu : Fin 11 → Fp := fun i =>
    if h : (i : Nat) < (n : Nat) then earlier ⟨i, h⟩ else 0
  let ch := chRecord nu (fun _ => 0)
  let urs := ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis
  let vk := ActionTerminal.vkAt pp basis
  let ic := actionCircuit.instanceCommitment pp urs inputs
  let pointPoly := adaptiveActionPointPolynomial source
  let poly := adaptiveActionCommitmentPolynomial pp basis inputs ps source ch
  if h0 : (n : Nat) = 0 then
    ↑(TopLevelLookupCoherence.allTopLevelLookupThetaBadSet
      actionCircuit pp urs poly)
  else if h1 : (n : Nat) = 1 then
    ↑(allResolverPermutationBetaBadSet vk poly actionActiveRows) ∪
      ↑(allResolverLookupBetaBadSet vk (ActionTerminal.semanticChRecord ch.theta 0) poly
        (vk.n - vk.blindingFactors - 2))
  else if h2 : (n : Nat) = 2 then
    ↑(allResolverPermutationGammaBadSet vk
        (ActionTerminal.semanticChRecord ch.theta ch.beta) poly actionActiveRows) ∪
      ↑(allResolverLookupGammaBadSet vk
        (ActionTerminal.semanticChRecord ch.theta ch.beta) poly
          (vk.n - vk.blindingFactors - 2))
  else if h3 : (n : Nat) = 3 then
    let model := adaptiveActionCommittedModel pp basis inputs ps source ch
    ⋃ j, ↑(szBadSet (foldSplitWitness model.constraints vk.n j))
  else
    ↑(szBadSet (committedPreXConstraintDifference pointPoly
      (fun i => onlinePointPolynomial source (ps.hPieces i)) vk ic ps ch))

/-- Equality of one exact semantic prefix pins precisely the ordinary commitment list used by
that stage. -/
theorem actionCommitmentPointsBefore_eq_of_prefix
    (init : List (TranscriptElt Fp VestaG)) (n : Fin 5)
    (ps ps' : ProofString shape Fp VestaG)
    (hprefix : preIpaSqueezePoints init ps (Fin.castLE (by omega) n) =
      preIpaSqueezePoints init ps' (Fin.castLE (by omega) n)) :
    ps.actionCommitmentPointsBefore n = ps'.actionCommitmentPointsBefore n := by
  fin_cases n
  · have h := preThetaSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, h]
  · obtain ⟨ha, hi, ht⟩ := preBetaSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht]
  · obtain ⟨ha, hi, ht⟩ := preGammaSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht]
  · obtain ⟨ha, hi, ht, hp, hl, hr⟩ := preYSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht, hp, hl, hr]
  · obtain ⟨ha, hi, ht, hp, hl, hr, hh⟩ := preXSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht, hp, hl, hr, hh]

theorem adaptiveActionCommitmentPolynomial_column_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps ps' : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (hsource : source = source') (hadvice : ps.adviceCommitments = ps'.adviceCommitments) :
    ∀ id, id.isColumnInput →
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch id =
        adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch id := by
  intro id hid
  subst source'
  cases id <;>
    simp_all [CommitmentId.isColumnInput, adaptiveActionCommitmentPolynomial,
      adaptiveActionPointPolynomial, assembledCommitment, hadvice]

theorem adaptiveActionCommitmentPolynomial_lookup_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps ps' : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (hsource : source = source') (hadvice : ps.adviceCommitments = ps'.adviceCommitments)
    (hinput : ps.lookupPermutedInput = ps'.lookupPermutedInput)
    (htable : ps.lookupPermutedTable = ps'.lookupPermutedTable) :
    ∀ id, id.isLookupInput →
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch id =
        adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch id := by
  intro id hid
  subst source'
  cases id <;>
    simp_all [CommitmentId.isLookupInput, adaptiveActionCommitmentPolynomial,
      adaptiveActionPointPolynomial, assembledCommitment, hadvice, hinput, htable]

theorem adaptiveActionCommitmentPolynomial_permutation_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps ps' : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (hsource : source = source') (hadvice : ps.adviceCommitments = ps'.adviceCommitments) :
    ∀ id, id.isPermutationInput →
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch id =
        adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch id := by
  intro id hid
  subst source'
  cases id <;>
    simp_all [CommitmentId.isPermutationInput, adaptiveActionCommitmentPolynomial,
      adaptiveActionPointPolynomial, assembledCommitment, hadvice]

theorem adaptiveActionCommitmentPolynomial_eq_of_preY_fields
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps ps' : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (hsource : source = source')
    (hadvice : ps.adviceCommitments = ps'.adviceCommitments)
    (hinput : ps.lookupPermutedInput = ps'.lookupPermutedInput)
    (htable : ps.lookupPermutedTable = ps'.lookupPermutedTable)
    (hperm : ps.permutationProduct = ps'.permutationProduct)
    (hlookup : ps.lookupProduct = ps'.lookupProduct)
    (hrandom : ps.vanishingRandom = ps'.vanishingRandom) :
    adaptiveActionCommitmentPolynomial pp basis inputs ps source ch =
      adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch := by
  funext id
  subst source'
  cases id <;>
    simp [adaptiveActionCommitmentPolynomial, adaptiveActionPointPolynomial,
      assembledCommitment, hadvice, hinput, htable, hperm, hlookup, hrandom]

set_option maxHeartbeats 800000 in
/-- Equal exact prefixes and equal stage-local coordinates define the same semantic bad set. -/
theorem adaptiveActionSurfaceAt_congr
    (pp : ProofParams)
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (n : Fin 5)
    (ps ps' : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (hwf : PsWellFormed ps) (hwf' : PsWellFormed ps')
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (n : Nat) → Fp)
    (hprefix : preIpaSqueezePoints init ps
        (Fin.castLE (by omega) n) =
      preIpaSqueezePoints init ps' (Fin.castLE (by omega) n))
    (hsource : source = source') :
    adaptiveActionSurfaceAt pp basis inputs n ps source earlier =
      adaptiveActionSurfaceAt pp basis inputs n ps' source' earlier := by
  subst source'
  let nu : Fin 11 → Fp := fun i =>
    if h : (i : Nat) < (n : Nat) then earlier ⟨i, h⟩ else 0
  let ch : Challenges (pp.mergeDerived actionCircuit).k Fp :=
    chRecord nu (fun _ => 0)
  fin_cases n
  · have ha := preThetaSqueezePoint_inj init hprefix
    have hp := adaptiveActionCommitmentPolynomial_column_eq
      pp basis inputs ps ps' source source ch rfl ha
    have hs := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (TopLevelLookupCoherence.allTopLevelLookupThetaBadSet_congr
        actionCircuit pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) hp)
    simpa [adaptiveActionSurfaceAt, nu, ch] using hs
  · obtain ⟨ha, hi, ht⟩ := preBetaSqueezePoint_inj init hprefix
    have hpPerm := adaptiveActionCommitmentPolynomial_permutation_eq
      pp basis inputs ps ps' source source ch rfl ha
    have hpLookup := adaptiveActionCommitmentPolynomial_lookup_eq
      pp basis inputs ps ps' source source ch rfl ha hi ht
    have hsPerm := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverPermutationBetaBadSet_congr
        (ActionTerminal.vkAt pp basis) actionActiveRows hpPerm)
    have hsLookup := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverLookupBetaBadSet_congr (ActionTerminal.vkAt pp basis)
        ((ActionTerminal.vkAt pp basis).n -
          (ActionTerminal.vkAt pp basis).blindingFactors - 2)
        (ch₁ := ActionTerminal.semanticChRecord ch.theta 0)
        (ch₂ := ActionTerminal.semanticChRecord ch.theta 0) rfl hpLookup)
    simpa [adaptiveActionSurfaceAt, nu, ch] using
      congrArg₂ (fun a b : Set Fp => a ∪ b) hsPerm hsLookup
  · obtain ⟨ha, hi, ht⟩ := preGammaSqueezePoint_inj init hprefix
    have hpPerm := adaptiveActionCommitmentPolynomial_permutation_eq
      pp basis inputs ps ps' source source ch rfl ha
    have hpLookup := adaptiveActionCommitmentPolynomial_lookup_eq
      pp basis inputs ps ps' source source ch rfl ha hi ht
    have hsPerm := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverPermutationGammaBadSet_congr
        (ActionTerminal.vkAt pp basis) actionActiveRows
        (ch₁ := ActionTerminal.semanticChRecord ch.theta ch.beta)
        (ch₂ := ActionTerminal.semanticChRecord ch.theta ch.beta) rfl hpPerm)
    have hsLookup := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverLookupGammaBadSet_congr (ActionTerminal.vkAt pp basis)
        ((ActionTerminal.vkAt pp basis).n -
          (ActionTerminal.vkAt pp basis).blindingFactors - 2)
        (ch₁ := ActionTerminal.semanticChRecord ch.theta ch.beta)
        (ch₂ := ActionTerminal.semanticChRecord ch.theta ch.beta) rfl rfl hpLookup)
    simpa [adaptiveActionSurfaceAt, nu, ch] using
      congrArg₂ (fun a b : Set Fp => a ∪ b) hsPerm hsLookup
  · obtain ⟨ha, hi, ht, hp, hl, hr⟩ := preYSqueezePoint_inj init hprefix
    have hpoly := adaptiveActionCommitmentPolynomial_eq_of_preY_fields
      pp basis inputs ps ps' source source ch rfl ha hi ht hp hl hr
    have hmodel :
        adaptiveActionCommittedModel pp basis inputs ps source ch =
          adaptiveActionCommittedModel pp basis inputs ps' source ch := by
      unfold adaptiveActionCommittedModel
      rw [hpoly]
    have hs := congrArg (fun model : ConstraintPolyModel
        (pp.mergeDerived actionCircuit).numProofs =>
      ⋃ j, (↑(szBadSet (foldSplitWitness model.constraints
        (ActionTerminal.vkAt pp basis).n j)) : Set Fp)) hmodel
    simpa [adaptiveActionSurfaceAt, nu, ch] using hs
  · obtain ⟨ha, hi, ht, hp, hl, _hr, hh⟩ := preXSqueezePoint_inj init hprefix
    have hdifference :
        committedPreXConstraintDifference (onlinePointPolynomial source)
            (fun i => onlinePointPolynomial source (ps.hPieces i))
            (ActionTerminal.vkAt pp basis)
            (actionCircuit.instanceCommitment pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
            ps ch =
          committedPreXConstraintDifference (onlinePointPolynomial source)
            (fun i => onlinePointPolynomial source (ps'.hPieces i))
            (ActionTerminal.vkAt pp basis)
            (actionCircuit.instanceCommitment pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
            ps' ch := by
      rw [← hh]
      apply committedPreXConstraintDifference_ps_congr
        (onlinePointPolynomial source) (fun i => onlinePointPolynomial source (ps.hPieces i))
        _ _ ch
      · intro q
        exact congrFun ha q
      · intro q s
        exact congrFun (congrFun hp q) s
      · exact hwf
      · exact hwf'
      · intro q l
        exact congrFun (congrFun hl q) l
      · intro q l
        exact congrFun (congrFun hi q) l
      · intro q l
        exact congrFun (congrFun ht q) l
    have hs := congrArg
      (fun polynomial : Polynomial Fp => (↑(szBadSet polynomial) : Set Fp)) hdifference
    simpa [adaptiveActionSurfaceAt, adaptiveActionPointPolynomial, nu, ch] using hs

/-! ## Pointwise prices of the five Action surfaces -/

/-- The adaptive `theta` surface has the ordinary top-level lookup budget. -/
theorem adaptiveActionThetaSurface_measure_le
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 0 → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAt pp basis inputs 0 ps source earlier) ≤
      (TopLevelLookupCoherence.topLevelLookupThetaBudget actionCircuit pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)
        (adaptiveActionCommitmentPolynomial pp basis inputs ps source
          (chRecord (fun _ => 0) (fun _ => 0))) : ENNReal) /
        Fintype.card Fp := by
  simpa [adaptiveActionSurfaceAt] using
    (ActionTerminal.actionThetaBadSet_measure_le pp basis
      (adaptiveActionCommitmentPolynomial pp basis inputs ps source
        (chRecord (fun _ => 0) (fun _ => 0))))

/-- The adaptive `beta` surface is priced by the same permutation/lookup counts as the staged
Action remainder. -/
theorem adaptiveActionBetaSurface_measure_le
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 1 → Fp) :
    let ch : Challenges (pp.mergeDerived actionCircuit).k Fp :=
      chRecord (fun i => if h : (i : Nat) < 1 then earlier ⟨i, h⟩ else 0) (fun _ => 0)
    let poly := adaptiveActionCommitmentPolynomial pp basis inputs ps source ch
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAt pp basis inputs 1 ps source earlier) ≤
      ((∑ p : Fin (pp.mergeDerived actionCircuit).numProofs,
        (Fintype.card (ResolverPermutationCell (ActionTerminal.vkAt pp basis) poly p
          actionActiveRows) + 1) *
          Fintype.card (ResolverPermutationCell (ActionTerminal.vkAt pp basis) poly p
            actionActiveRows) : Nat) : ENNReal) / Fintype.card Fp +
      (((pp.mergeDerived actionCircuit).numProofs *
        (pp.mergeDerived actionCircuit).numLookups *
        (((ActionTerminal.vkAt pp basis).n -
            (ActionTerminal.vkAt pp basis).blindingFactors - 2 + 2) *
          ((ActionTerminal.vkAt pp basis).n -
            (ActionTerminal.vkAt pp basis).blindingFactors - 2 + 1) +
          ((ActionTerminal.vkAt pp basis).n -
            (ActionTerminal.vkAt pp basis).blindingFactors - 2 + 1)) : Nat) : ENNReal) /
        Fintype.card Fp := by
  dsimp only
  simpa [adaptiveActionSurfaceAt] using
    (ActionTerminal.actionBetaBadSets_measure_le pp basis (earlier 0)
      (adaptiveActionCommitmentPolynomial pp basis inputs ps source
        (chRecord (fun i => if h : (i : Nat) < 1 then earlier ⟨i, h⟩ else 0)
          (fun _ => 0))))

/-- The adaptive `gamma` surface is priced by the same doubled permutation/lookup count. -/
theorem adaptiveActionGammaSurface_measure_le
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 2 → Fp) :
    let ch : Challenges (pp.mergeDerived actionCircuit).k Fp :=
      chRecord (fun i => if h : (i : Nat) < 2 then earlier ⟨i, h⟩ else 0) (fun _ => 0)
    let poly := adaptiveActionCommitmentPolynomial pp basis inputs ps source ch
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAt pp basis inputs 2 ps source earlier) ≤
      ((∑ p : Fin (pp.mergeDerived actionCircuit).numProofs,
        2 * Fintype.card (ResolverPermutationCell (ActionTerminal.vkAt pp basis) poly p
          actionActiveRows) : Nat) : ENNReal) / Fintype.card Fp +
      (((pp.mergeDerived actionCircuit).numProofs *
        (pp.mergeDerived actionCircuit).numLookups *
        (2 * ((ActionTerminal.vkAt pp basis).n -
          (ActionTerminal.vkAt pp basis).blindingFactors - 2 + 1)) : Nat) : ENNReal) /
        Fintype.card Fp := by
  dsimp only
  simpa [adaptiveActionSurfaceAt] using
    (ActionTerminal.actionGammaBadSets_measure_le pp basis (earlier 0) (earlier ⟨1, by omega⟩)
      (adaptiveActionCommitmentPolynomial pp basis inputs ps source
        (chRecord (fun i => if h : (i : Nat) < 2 then earlier ⟨i, h⟩ else 0)
          (fun _ => 0))))

/-- The adaptive `y` surface is the standard fold-split union. -/
theorem adaptiveActionYSurface_measure_le
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 3 → Fp)
    (hn : (ActionTerminal.vkAt pp basis).n ≠ 0) :
    let ch : Challenges (pp.mergeDerived actionCircuit).k Fp :=
      chRecord (fun i => if h : (i : Nat) < 3 then earlier ⟨i, h⟩ else 0) (fun _ => 0)
    let model := adaptiveActionCommittedModel pp basis inputs ps source ch
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAt pp basis inputs 3 ps source earlier) ≤
      (((ActionTerminal.vkAt pp basis).n * model.constraints.length : Nat) : ENNReal) /
        Fintype.card Fp := by
  dsimp only
  simpa [adaptiveActionSurfaceAt] using
    (ActionTerminal.actionYBadSet_measure_le pp basis
      (adaptiveActionCommittedModel pp basis inputs ps source
        (chRecord (fun i => if h : (i : Nat) < 3 then earlier ⟨i, h⟩ else 0)
          (fun _ => 0))).constraints hn)

/-- The adaptive `x` surface is one Schwartz--Zippel set at the explicit pre-`x` committed
constraint difference. -/
theorem adaptiveActionXSurface_measure_le
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 4 → Fp) :
    let ch : Challenges (pp.mergeDerived actionCircuit).k Fp :=
      chRecord (fun i => if h : (i : Nat) < 4 then earlier ⟨i, h⟩ else 0) (fun _ => 0)
    let difference := committedPreXConstraintDifference (onlinePointPolynomial source)
      (fun i => onlinePointPolynomial source (ps.hPieces i)) (ActionTerminal.vkAt pp basis)
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs) ps ch
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAt pp basis inputs 4 ps source earlier) ≤
      (difference.natDegree : ENNReal) / Fintype.card Fp := by
  dsimp only
  simpa [adaptiveActionSurfaceAt, adaptiveActionPointPolynomial] using
    (uniformChallenge_szBadSet
      (committedPreXConstraintDifference (onlinePointPolynomial source)
        (fun i => onlinePointPolynomial source (ps.hPieces i)) (ActionTerminal.vkAt pp basis)
        (actionCircuit.instanceCommitment pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs) ps
        (chRecord (fun i => if h : (i : Nat) < 4 then earlier ⟨i, h⟩ else 0)
          (fun _ => 0))))

/-- On a queried prefix with no provenance relation, the query-time stage source is literally
the final stage source. -/
theorem adaptiveActionQuerySource_eq_of_pinned
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 5)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (decoded : DecodedPreIpaPrefix (shape := shape) family.init
      (Fin.castLE (by omega) n)
      (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O).toAlgebraicWfProof (Fin.castLE (by omega) n)))
    (pinned : SelectedQueryRepresentationPinned
      (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O).toAlgebraicWfProof (Fin.castLE (by omega) n))
      (family.adversary basis) O
      (((family.adversary basis).run O).algebraicProof.actionRepresentationsBefore n)) :
    adaptiveActionQuerySource family.init basis n decoded pinned.query
        (family.fixedRepresentations basis) =
      ((family.adversary basis).run O).algebraicProof.actionRepresentationsBefore n ++
        family.fixedRepresentations basis := by
  let data := (family.adversary basis).run O
  let final := data.algebraicProof.actionRepresentationsBefore n
  have hprefixBounded : fullPrefixesPre family.init decoded.proof (Fin.castLE (by omega) n) =
      fullPrefixesPre family.init data.toAlgebraicWfProof.proof
        (Fin.castLE (by omega) n) := decoded.point_eq
  have hprefix : preIpaSqueezePoints family.init decoded.proof.1
      (Fin.castLE (by omega) n) =
      preIpaSqueezePoints family.init data.algebraicProof.erase
        (Fin.castLE (by omega) n) := congrArg Subtype.val hprefixBounded
  have hordinary : decoded.proof.1.actionCommitmentPointsBefore n =
      data.algebraicProof.erase.actionCommitmentPointsBefore n :=
    actionCommitmentPointsBefore_eq_of_prefix family.init n _ _ hprefix
  have hselected : pinned.query.representationsFor final pinned.covered = final :=
    algebraicPointList_eq_of_maps_eq
      (pinned.query.representationsFor_points final pinned.covered)
      pinned.coefficients_eq
  let decodedCovered : ∀ P ∈ decoded.proof.1.actionCommitmentPointsBefore n,
      P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (Fin.castLE (by omega) n)).val := by
    intro P hP
    rw [← decoded.point_eq]
    exact decoded.proof.1.actionCommitmentPointsBefore_covered family.init
      decoded.proof.2 n P hP
  unfold adaptiveActionQuerySource
  change pinned.query.representationsForPoints
      (decoded.proof.1.actionCommitmentPointsBefore n) decodedCovered ++
        family.fixedRepresentations basis = _
  have hordinaryFinal : decoded.proof.1.actionCommitmentPointsBefore n =
      final.map AlgebraicPoint.point :=
    hordinary.trans (data.algebraicProof.actionRepresentationsBefore_points n).symm
  let finalCoveredPoints : ∀ P ∈ final.map AlgebraicPoint.point,
      P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (Fin.castLE (by omega) n)).val := by
    intro P hP
    obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hP
    exact pinned.covered ap hap
  have representationsForPoints_congr
      (points points' : List VestaG)
      (hcovered : ∀ P ∈ points, P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (Fin.castLE (by omega) n)).val)
      (hcovered' : ∀ P ∈ points', P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (Fin.castLE (by omega) n)).val)
      (hpoints : points = points') :
      pinned.query.representationsForPoints points hcovered =
        pinned.query.representationsForPoints points' hcovered' := by
    subst points'
    rfl
  have hqueryPoints : pinned.query.representationsForPoints
      (decoded.proof.1.actionCommitmentPointsBefore n) decodedCovered =
      pinned.query.representationsForPoints
        (final.map AlgebraicPoint.point) finalCoveredPoints := by
    exact representationsForPoints_congr _ _ decodedCovered finalCoveredPoints hordinaryFinal
  rw [hqueryPoints,
    ← pinned.query.representationsFor_eq_representationsForPoints final pinned.covered]
  exact congrArg (fun source => source ++ family.fixedRepresentations basis) hselected

/-- Query-time Action surface reconstructed from the exact ordinary prefix and its pre-answer AGM
annotation. -/
noncomputable def adaptiveQueriedActionSurface
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (pp.mergeDerived actionCircuit))
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (n : Fin 5)
    (t : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10 +
        3 * (pp.mergeDerived actionCircuit).k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  let n11 : Fin 11 := ⟨n, by omega⟩
  match decodePreIpaPrefix? (shape := pp.mergeDerived actionCircuit) family.init n11 t with
  | none => ∅
  | some decoded =>
      adaptiveActionSurfaceAt pp basis inputs n decoded.proof.1
        (adaptiveActionQuerySource family.init basis n decoded label
          (family.fixedRepresentations basis)) earlier

/-- Fresh-prefix fallback reconstructed from the final output's own stage-local AGM
representations. -/
noncomputable def adaptiveFallbackActionSurface
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (pp.mergeDerived actionCircuit))
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (n : Fin 5)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (_t : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10 +
        3 * (pp.mergeDerived actionCircuit).k))
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  adaptiveActionSurfaceAt pp basis inputs n data.algebraicProof.erase
    (data.algebraicProof.actionRepresentationsBefore n ++ family.fixedRepresentations basis)
    earlier

namespace ComputedAdaptiveOnlineAGMFSFamily

/-- Compare the final stage-local Action commitments with the first online-AGM annotation at the
actual semantic squeeze.  Any coefficient mismatch is returned as explicit relation data. -/
def adaptiveActionRepresentationRelationAt?
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (n : Fin 5) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let p := data.toAlgebraicWfProof
  let n11 : Fin 11 := Fin.castLE (by omega) n
  let t := algebraicFullPrefixesPre family.init p n11
  selectedQueryRepresentationRelation? t (family.adversary basis) O
    (data.algebraicProof.actionRepresentationsBefore n) (by
      intro ap hap
      change ap.point ∈ transcriptGroupPoints
        (preIpaSqueezePoints family.init data.algebraicProof.erase n11)
      exact data.algebraicProof.actionRepresentationsBefore_covered
        family.init data.wellFormed n ap hap)

/-- Compare the polynomial source visible at one semantic squeeze with the complete pre-`x`
source used by the executable decoder.  A collision with different coordinates is an explicit
relation rather than an unpriced future dependency. -/
def adaptiveActionSourceMismatchAt?
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (n : Fin 5) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  representationSourceMismatchFinder
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    (data.algebraicProof.actionRepresentationsBefore n ++
      family.fixedRepresentations basis)

/-- One shared run checks provenance at `theta`, `beta`, `gamma`, `y`, and `x`. -/
def adaptiveActionRepresentationRelationFinder
    (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    let data := (family.adversary basis).run O
    firstAdaptiveRelation?
      ((List.ofFn fun n => family.adaptiveActionRepresentationRelationAt? basis O data n) ++
        (List.ofFn fun n => family.adaptiveActionSourceMismatchAt? basis data n))

/-- No aggregate semantic-provenance relation means every stage-local comparison was empty. -/
theorem adaptiveActionRepresentationRelationFinder_none_at
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (n : Fin 5) :
    let data := (family.adversary basis).run O
    family.adaptiveActionRepresentationRelationAt? basis O data n = none := by
  dsimp only
  have hall := (firstAdaptiveRelation?_eq_none_iff _).1 (by
    simpa only [adaptiveActionRepresentationRelationFinder] using hnone)
  apply hall
  exact List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨n, rfl⟩))

/-- No aggregate provenance relation also rules out every future source collision. -/
theorem adaptiveActionRepresentationRelationFinder_none_source_at
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (n : Fin 5) :
    let data := (family.adversary basis).run O
    family.adaptiveActionSourceMismatchAt? basis data n = none := by
  dsimp only
  have hall := (firstAdaptiveRelation?_eq_none_iff _).1 (by
    simpa only [adaptiveActionRepresentationRelationFinder] using hnone)
  apply hall
  exact List.mem_append.mpr (Or.inr (List.mem_ofFn.mpr ⟨n, rfl⟩))

/-- Outside the combined Action provenance finder, the stage-local polynomial at every covered
point is exactly the polynomial used by the complete pre-`x` decoder source. -/
theorem adaptiveActionStagePolynomial_eq_full
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (n : Fin 5) (P : VestaG)
    (hP : ∃ ap ∈
      ((family.adversary basis).run O).algebraicProof.actionRepresentationsBefore n ++
        family.fixedRepresentations basis,
      ap.point = P) :
    onlinePointPolynomial
        (((family.adversary basis).run O).algebraicProof.preX1AssemblySource
          (family.fixedRepresentations basis)) P =
      onlinePointPolynomial
        (((family.adversary basis).run O).algebraicProof.actionRepresentationsBefore n ++
          family.fixedRepresentations basis) P := by
  apply onlinePointPolynomial_eq_of_sourceMismatch_none
  · intro ap hap
    exact AlgebraicProofString.actionStageSource_subset_preX1AssemblySource
      ((family.adversary basis).run O).algebraicProof
      (family.fixedRepresentations basis) n ap hap
  · exact family.adaptiveActionRepresentationRelationFinder_none_source_at basis O hnone n
  · exact hP

end ComputedAdaptiveOnlineAGMFSFamily

/-- Restrict the generic pre-IPA earlier-answer vector to the first five Action squeezes. -/
def adaptiveActionEarlier (n : Fin 5)
    (earlier : Fin ((Fin.castLE (by omega) n : Fin 11) : Nat) → Fp) :
    Fin (n : Nat) → Fp :=
  fun i => earlier ⟨i, by simpa using i.isLt⟩

/-- The final-output semantic event at one of the five Action squeezes, decoded through the same
strict-prefix wrapper used by the arbitrary-adaptive squeeze theorem. -/
noncomputable def adaptiveFinalActionBad
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (pp.mergeDerived actionCircuit))
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (n : Fin 5)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10 +
        3 * (pp.mergeDerived actionCircuit).k))
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10 +
        3 * (pp.mergeDerived actionCircuit).k) → Fp) : Set Fp :=
  adaptivePrefixBad (shape := pp.mergeDerived actionCircuit) family.init
    (Fin.castLE (by omega) n)
    (fun t earlier => adaptiveFallbackActionSurface pp family inputs basis n data t
      (adaptiveActionEarlier n earlier)) t O

/-- Every Action semantic squeeze of a bare malicious adaptive online-AGM adversary is priced at
its first actual annotated query (or the fresh verifier fallback), unless the executable Action
provenance finder has already produced a DLOG relation. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveFinalActionBadWithoutRelation_table_le
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (pp.mergeDerived actionCircuit))
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (n : Fin 5) {epsilon : ENNReal}
    (hsurface : ∀
      (ps : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
      (hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt pp basis inputs n ps source earlier) ≤ epsilon) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10 +
        3 * (pp.mergeDerived actionCircuit).k) → Fp)).toOuterMeasure
      {O | let data := (family.adversary basis).run O
        let n11 : Fin 11 := Fin.castLE (by omega) n
        let t := (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof) n11
        O t ∈ adaptiveFinalActionBad pp family inputs basis n data t O ∧
          family.adaptiveActionRepresentationRelationFinder basis O = none} ≤
      (family.Q + 1 : Nat) * epsilon := by
  apply family.adaptiveFinalPrefixBadWithoutRelation_table_le basis (Fin.castLE (by omega) n)
    (adaptiveFinalActionBad pp family inputs basis n)
    (family.adaptiveActionRepresentationRelationFinder basis)
    (fun t label earlier => adaptiveQueriedActionSurface pp family inputs basis n t label
      (adaptiveActionEarlier n earlier))
    (fun data t earlier => adaptiveFallbackActionSurface pp family inputs basis n data t
      (adaptiveActionEarlier n earlier))
  · intro O
    dsimp only
    intro hbad hnone
    let data := (family.adversary basis).run O
    let t := (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof)
      (Fin.castLE (by omega) n)
    change O t ∈ adaptiveFinalActionBad pp family inputs basis n data t O at hbad
    change O t ∈ LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
      (fun t label O => adaptiveLabeledPrefixBad (shape := pp.mergeDerived actionCircuit)
        family.init basis (Fin.castLE (by omega) n)
          (fun t label earlier => adaptiveQueriedActionSurface pp family inputs basis n t label
            (adaptiveActionEarlier n earlier))
          t label O)
      (fun data t O => adaptivePrefixBad (shape := pp.mergeDerived actionCircuit)
        family.init (Fin.castLE (by omega) n)
          (fun t earlier => adaptiveFallbackActionSurface pp family inputs basis n data t
            (adaptiveActionEarlier n earlier)) t O)
      t O
    have hlen : t.val.length =
        preIpaLen (pp.mergeDerived actionCircuit) family.init.length
          (Fin.castLE (by omega) n) := by
      exact preIpaSqueezePoints_length_eq family.init data.algebraicProof.erase
        data.wellFormed (Fin.castLE (by omega) n)
    unfold LabeledOracleComp.firstLabelOrFallbackBad
    cases hfind : (family.adversary basis).findLabel O t with
    | none =>
        simpa only [adaptiveFinalActionBad] using hbad
    | some label =>
        have hat := family.adaptiveActionRepresentationRelationFinder_none_at
          basis O hnone n
        have hlocal : selectedQueryRepresentationRelation? t (family.adversary basis) O
            (data.algebraicProof.actionRepresentationsBefore n) (by
              intro ap hap
              change ap.point ∈ transcriptGroupPoints
                (preIpaSqueezePoints family.init data.algebraicProof.erase
                  (Fin.castLE (by omega) n))
              exact data.algebraicProof.actionRepresentationsBefore_covered
                family.init data.wellFormed n ap hap) = none := by
          simpa only [
            ComputedAdaptiveOnlineAGMFSFamily.adaptiveActionRepresentationRelationAt?, data, t]
            using hat
        have hprov := selectedQueryRepresentationRelation?_eq_none t
          (family.adversary basis) O (data.algebraicProof.actionRepresentationsBefore n) _ hlocal
        cases hprov with
        | inl hfresh => simp [hfind] at hfresh
        | inr pinned =>
            have hlabel : pinned.query = label := by
              exact Option.some.inj (pinned.found.symm.trans hfind)
            subst label
            have hdecode := decodePreIpaPrefix?_isSome family.init (Fin.castLE (by omega) n)
              data.toAlgebraicWfProof.proof
            change (decodePreIpaPrefix? (shape := pp.mergeDerived actionCircuit)
              family.init (Fin.castLE (by omega) n) t).isSome at hdecode
            cases hdec : decodePreIpaPrefix? (shape := pp.mergeDerived actionCircuit)
                family.init (Fin.castLE (by omega) n) t with
            | none => simp [hdec] at hdecode
            | some decoded =>
                have hsource := adaptiveActionQuerySource_eq_of_pinned
                  family basis n O decoded pinned
                have hprefixBounded : fullPrefixesPre family.init decoded.proof
                      (Fin.castLE (by omega) n) =
                    fullPrefixesPre family.init data.toAlgebraicWfProof.proof
                      (Fin.castLE (by omega) n) :=
                  decoded.point_eq
                have hprefix : preIpaSqueezePoints family.init decoded.proof.1
                      (Fin.castLE (by omega) n) =
                    preIpaSqueezePoints family.init data.algebraicProof.erase
                      (Fin.castLE (by omega) n) :=
                  congrArg Subtype.val hprefixBounded
                change O t ∈ adaptivePrefixBad
                  (shape := pp.mergeDerived actionCircuit) family.init
                    (Fin.castLE (by omega) n)
                    (fun t earlier => adaptiveFallbackActionSurface pp family inputs basis n data t
                      (adaptiveActionEarlier n earlier)) t O at hbad
                unfold adaptivePrefixBad at hbad
                rw [if_pos hlen] at hbad
                unfold adaptiveLabeledPrefixBad
                simp only [if_pos hlen]
                have hsurfaceEq : adaptiveQueriedActionSurface pp family inputs basis n t
                    pinned.query (adaptiveActionEarlier n (fun i => O (adaptiveEarlierPrefix
                      (shape := pp.mergeDerived actionCircuit) family.init t
                        (i.castLE (le_of_lt (Fin.castLE (by omega) n).isLt))))) =
                    adaptiveFallbackActionSurface pp family inputs basis n data t
                      (adaptiveActionEarlier n (fun i => O (adaptiveEarlierPrefix
                        (shape := pp.mergeDerived actionCircuit) family.init t
                          (i.castLE (le_of_lt (Fin.castLE (by omega) n).isLt))))) := by
                  unfold adaptiveQueriedActionSurface
                  dsimp only
                  split
                  · rename_i hnone
                    have hdecode' := decodePreIpaPrefix?_isSome family.init
                      (⟨n, by omega⟩ : Fin 11) data.toAlgebraicWfProof.proof
                    change (decodePreIpaPrefix? (shape := pp.mergeDerived actionCircuit)
                      family.init (⟨n, by omega⟩ : Fin 11) t).isSome at hdecode'
                    rw [hnone] at hdecode'
                    simp at hdecode'
                  · rename_i decoded' hsome
                    have hsource' := adaptiveActionQuerySource_eq_of_pinned
                      family basis n O decoded' pinned
                    have hprefixBounded' : fullPrefixesPre family.init decoded'.proof
                          (Fin.castLE (by omega) n) =
                        fullPrefixesPre family.init data.toAlgebraicWfProof.proof
                          (Fin.castLE (by omega) n) :=
                      decoded'.point_eq
                    have hprefix' : preIpaSqueezePoints family.init decoded'.proof.1
                          (Fin.castLE (by omega) n) =
                        preIpaSqueezePoints family.init data.algebraicProof.erase
                          (Fin.castLE (by omega) n) :=
                      congrArg Subtype.val hprefixBounded'
                    unfold adaptiveFallbackActionSurface
                    rw [hsource']
                    apply adaptiveActionSurfaceAt_congr pp family.init basis inputs n
                      decoded'.proof.1 data.algebraicProof.erase decoded'.proof.2 data.wellFormed
                      _ _ _ hprefix' rfl
                rw [hsurfaceEq]
                exact hbad
  · intro t label earlier
    unfold adaptiveQueriedActionSurface
    dsimp only
    split
    · simp
    · rename_i decoded hdecoded
      exact hsurface decoded.proof.1 decoded.proof.2 _ (adaptiveActionEarlier n earlier)
  · intro data t earlier
    exact hsurface data.algebraicProof.erase data.wellFormed _
      (adaptiveActionEarlier n earlier)

/-- One actual Action semantic bad event, excluding the executable stage-provenance relation. -/
noncomputable def ComputedAdaptiveOnlineAGMFSFamily.adaptiveActionBadWithoutRelation
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (pp.mergeDerived actionCircuit))
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (n : Fin 5) :
    Set (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10 +
        3 * (pp.mergeDerived actionCircuit).k) → Fp) :=
  {O | let data := (family.adversary basis).run O
    let n11 : Fin 11 := Fin.castLE (by omega) n
    let t := algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n11
    O t ∈ adaptiveFinalActionBad pp family inputs basis n data t O ∧
      family.adaptiveActionRepresentationRelationFinder basis O = none}

/-- The actual Action semantic event inherits the annotation-aware first-query price. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveActionBadWithoutRelation_measure_le
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (pp.mergeDerived actionCircuit))
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (n : Fin 5) {epsilon : ENNReal}
    (hsurface : ∀
      (ps : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
      (hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt pp basis inputs n ps source earlier) ≤ epsilon) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10 +
        3 * (pp.mergeDerived actionCircuit).k) → Fp)).toOuterMeasure
      (family.adaptiveActionBadWithoutRelation pp inputs basis n) ≤
        (family.Q + 1 : Nat) * epsilon := by
  simpa only [ComputedAdaptiveOnlineAGMFSFamily.adaptiveActionBadWithoutRelation] using
    family.adaptiveFinalActionBadWithoutRelation_table_le pp inputs basis n hsurface

end Zcash.Snark
