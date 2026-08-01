import Zcash.Circuits.Integration.ActionCorrectness
import Zcash.Snark.Soundness.AGM.AdaptiveOnline
import Zcash.Snark.Verifier.Deployed

/-!
# Adaptive-statement Action soundness model

The existing Action capstones fix the public inputs outside the random-oracle experiment.  This
module introduces the stronger deployed game in which one online-AGM adversary returns the public
inputs and proof together.  Its verifier transcript is not a free `init`: it is reconstructed from
the basis-dependent VK transcript representation and the instance commitments derived from the
adversary's output.

This file defines the game and its load-bearing pre-`theta` invariant.  Probability composition is
kept in later modules so the existing fixed-statement capstones remain unchanged.
-/

namespace Zcash.Snark

open Halo2 Keygen
open Zcash.Circuits
open Zcash.Circuits.Action

local instance adaptiveStatementVestaInhabited : Inhabited VestaG := ⟨0⟩

/-- The Action verifier shape used by an adaptive-statement experiment. -/
abbrev AdaptiveActionStatementShape (pp : ProofParams) : Shape :=
  pp.mergeDerived actionCircuit

/-- The canonical Action verifying key at one AGM basis. -/
abbrev adaptiveActionStatementVk (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) :
    VerifyingKey (AdaptiveActionStatementShape pp) Fp VestaG :=
  actionCircuit.toVerifierKey pp
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)

/-- Public inputs determine the complete instance-commitment family used by the verifier. -/
abbrev adaptiveActionStatementInstanceCommitment (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp) :
    Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG :=
  actionCircuit.instanceCommitmentForShape pp
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) inputs

/-- Canonical initial-transcript length, independent of the selected statement's values. -/
def adaptiveStatementInitLength (shape : Shape) : ℕ :=
  1 + shape.numProofs * shape.numInstanceColumns

/-- One common finite oracle domain for every statement and AGM basis. -/
abbrev AdaptiveActionStatementTranscript (pp : ProofParams) :=
  BTranscript Fp VestaG
    (preIpaLen (AdaptiveActionStatementShape pp)
      (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
        3 * (AdaptiveActionStatementShape pp).k)

/-- Instance representations in the same proof-major, column-major order as the transcript. -/
def adaptiveStatementInstanceRepresentationList {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (representations : Fin shape.numProofs → Fin shape.numInstanceColumns →
      AlgebraicPoint (F := Fp) basis) : List (AlgebraicPoint (F := Fp) basis) :=
  (List.ofFn fun p => List.ofFn fun column => representations p column).flatten

/-- An online-AGM output that selects both the Action public statement and its proof. -/
structure AdaptiveActionStatementOutput (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)) where
  inputs : Fin pp.numProofs → PublicInputs Fp
  instanceRepresentations :
    Fin (AdaptiveActionStatementShape pp).numProofs →
      Fin (AdaptiveActionStatementShape pp).numInstanceColumns →
        AlgebraicPoint (F := Fp) basis
  instanceRepresented : ∀ p column,
    (instanceRepresentations p column).point =
      adaptiveActionStatementInstanceCommitment pp basis inputs p column
  proofData : OnlineMemberProofData
    (vk := adaptiveActionStatementVk pp basis)
    (instanceCommitment := adaptiveActionStatementInstanceCommitment pp basis inputs)
    basis
    (adaptiveStatementInstanceRepresentationList instanceRepresentations ++
      fixedRepresentations)

namespace AdaptiveActionStatementOutput

/-- Erase the member-coverage wrapper to the algebraic proof consumed by verifier reductions. -/
def toAlgebraicWfProof {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    AlgebraicWfProof basis (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis output.inputs) :=
  output.proofData.toAlgebraicWfProof

/-- The verifier-controlled transcript prefix for the output statement. -/
def init {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    List (TranscriptElt Fp VestaG) :=
  initialTranscript vkTranscriptRepr
    (adaptiveActionStatementInstanceCommitment pp basis output.inputs)

@[simp] theorem init_length {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    (output.init vkTranscriptRepr).length =
      adaptiveStatementInitLength (AdaptiveActionStatementShape pp) := by
  simp [init, adaptiveStatementInitLength]

/-- The eleven statement-bound pre-IPA query points in the common oracle domain. -/
def prefixesPre {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    Fin 11 → AdaptiveActionStatementTranscript pp :=
  fun i =>
    let t := algebraicFullPrefixesPre (output.init vkTranscriptRepr)
      output.toAlgebraicWfProof i
    ⟨t.val, by simpa using t.prop⟩

/-- The statement-bound IPA-round query points in the common oracle domain. -/
def prefixes {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    Fin (AdaptiveActionStatementShape pp).k → AdaptiveActionStatementTranscript pp :=
  fun j =>
    let t := algebraicFullPrefixes (output.init vkTranscriptRepr)
      output.toAlgebraicWfProof j
    ⟨t.val, by simpa using t.prop⟩

/-- The first oracle query is exactly VK, instances, advice commitments, then the challenge marker. -/
theorem prefixesPre_zero_val {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    (output.prefixesPre vkTranscriptRepr 0).val =
      preThetaTranscriptForStatement vkTranscriptRepr
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        output.toAlgebraicWfProof.proof.1 := by
  rfl

/-- The basis-dependent VK transcript representation is present before `theta`. -/
theorem vkTranscriptRepr_mem_prefixesPre_zero {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    TranscriptElt.scalar vkTranscriptRepr ∈
      (output.prefixesPre vkTranscriptRepr 0).val := by
  rw [prefixesPre_zero_val]
  exact vkTranscriptRepr_mem_preThetaTranscriptForStatement _ _ _

/-- Every commitment derived from the adversary-selected public inputs is present before `theta`. -/
theorem instanceCommitment_mem_prefixesPre_zero {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns) :
    TranscriptElt.point
      (adaptiveActionStatementInstanceCommitment pp basis output.inputs p column) ∈
        (output.prefixesPre vkTranscriptRepr 0).val := by
  rw [prefixesPre_zero_val]
  exact instanceCommitment_mem_preThetaTranscriptForStatement _ _ _ p column

/-- Recover a query-time AGM representation for an instance commitment from the `theta` label. -/
def queryInstanceRepresentation {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (label : AlgebraicTranscriptQuery (F := Fp) basis
      (output.prefixesPre vkTranscriptRepr 0))
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns) :
    AlgebraicPoint (F := Fp) basis :=
  label.representationOfPoint
    (adaptiveActionStatementInstanceCommitment pp basis output.inputs p column)
    (mem_transcriptGroupPoints_of_mem_point
      (output.instanceCommitment_mem_prefixesPre_zero vkTranscriptRepr p column))

@[simp] theorem queryInstanceRepresentation_point {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (label : AlgebraicTranscriptQuery (F := Fp) basis
      (output.prefixesPre vkTranscriptRepr 0))
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns) :
    (output.queryInstanceRepresentation vkTranscriptRepr label p column).point =
      adaptiveActionStatementInstanceCommitment pp basis output.inputs p column := by
  exact AlgebraicTranscriptQuery.representationOfPoint_point _ _ _

/-- All final instance representations denote points already absorbed at the first squeeze. -/
theorem instanceRepresentations_coveredAtTheta {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations) :
    ∀ ap ∈ adaptiveStatementInstanceRepresentationList output.instanceRepresentations,
      ap.point ∈ transcriptGroupPoints (output.prefixesPre vkTranscriptRepr 0).val := by
  intro ap hap
  rw [adaptiveStatementInstanceRepresentationList] at hap
  obtain ⟨row, hrow, hapRow⟩ := List.mem_flatten.mp hap
  obtain ⟨p, hp⟩ := List.mem_ofFn.mp hrow
  obtain ⟨column, hcolumn⟩ := List.mem_ofFn.mp (hp ▸ hapRow)
  rw [← hcolumn, output.instanceRepresented p column]
  exact mem_transcriptGroupPoints_of_mem_point
    (output.instanceCommitment_mem_prefixesPre_zero vkTranscriptRepr p column)

/-- Every proof-controlled advice commitment follows the statement prefix and precedes `theta`. -/
theorem adviceCommitment_mem_prefixesPre_zero {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numAdviceColumns) :
    TranscriptElt.point
      (output.toAlgebraicWfProof.proof.1.adviceCommitments p column) ∈
        (output.prefixesPre vkTranscriptRepr 0).val := by
  rw [prefixesPre_zero_val]
  exact adviceCommitment_mem_preThetaTranscriptForStatement _ _ _ p column

end AdaptiveActionStatementOutput

/-- A basis-indexed online-AGM adversary that chooses its public statement and proof together. -/
structure ComputedAdaptiveActionStatementFSFamily (pp : ProofParams) where
  vkTranscriptRepr :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) → Fp
  fixedRepresentations :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      List (AlgebraicPoint (F := Fp) basis)
  fixedRepresented : ∀ basis i,
    (∃ rotation, (i, rotation) ∈ (adaptiveActionStatementVk pp basis).fixedQueryLayout) →
    ∃ ap ∈ fixedRepresentations basis,
      ap.point = (adaptiveActionStatementVk pp basis).fixedCommitment i
  permutationCommonRepresented : ∀ basis
      (column : Fin (AdaptiveActionStatementShape pp).numPermutationColumns),
    ∃ ap ∈ fixedRepresentations basis,
      ap.point = (adaptiveActionStatementVk pp basis).permutationCommonCommitment column
  adversary :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      LabeledOracleComp (AdaptiveActionStatementTranscript pp) Fp
        (AlgebraicTranscriptQuery (F := Fp) basis)
        (AdaptiveActionStatementOutput pp basis (fixedRepresentations basis))
  Q : ℕ
  queryBound : ∀ basis, (adversary basis).QueryBound Q

namespace ComputedAdaptiveActionStatementFSFamily

/-- One adaptive-statement random-oracle table. -/
abbrev Coins {pp : ProofParams} (_family : ComputedAdaptiveActionStatementFSFamily pp) :=
  AdaptiveActionStatementTranscript pp → Fp

/-- Run the adversary once and retain its jointly selected statement and proof. -/
def runOutput {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis) :=
  (family.adversary basis).run O

/-- Read every challenge from the canonical prefixes determined by the output statement and proof. -/
def runRecord {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Challenges (AdaptiveActionStatementShape pp).k Fp :=
  let output := family.runOutput basis O
  chRecord
    (fun i => O (output.prefixesPre (family.vkTranscriptRepr basis) i))
    (fun j => O (output.prefixes (family.vkTranscriptRepr basis) j))

/-- The table-read record is exactly the canonical statement-bound Fiat--Shamir execution. -/
theorem runRecord_eq_roChallenges {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.runRecord basis O =
      roChallenges (extendO O)
        ((family.runOutput basis O).init (family.vkTranscriptRepr basis))
        (family.runOutput basis O).toAlgebraicWfProof.proof.1 := by
  let output := family.runOutput basis O
  let init := output.init (family.vkTranscriptRepr basis)
  let ps := output.toAlgebraicWfProof.proof.1
  have hpre : ∀ i : Fin 11,
      (preIpaSqueezePoints init ps i).length ≤
        preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
            3 * (AdaptiveActionStatementShape pp).k := by
    intro i
    exact (output.prefixesPre (family.vkTranscriptRepr basis) i).prop
  have hround : ∀ j : Fin (AdaptiveActionStatementShape pp).k,
      (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j).length ≤
        preIpaLen (AdaptiveActionStatementShape pp)
          (adaptiveStatementInitLength (AdaptiveActionStatementShape pp)) 10 +
            3 * (AdaptiveActionStatementShape pp).k := by
    intro j
    exact (output.prefixes (family.vkTranscriptRepr basis) j).prop
  have h := roChallenges_extendO_eq_chRecord O init ps hpre hround
  rw [h]
  rfl

/-- Checked Halo2 acceptance for the adversary-selected public statement and proof. -/
def accepts {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Prop :=
  let output := family.runOutput basis O
  DeployedAccepts
    (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
    (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
    output.toAlgebraicWfProof.proof.1 (family.runRecord basis O)

/-- The strong soundness event: the adversary jointly outputs an accepted proof and false statement. -/
def acceptFalseStatementEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  {q | family.accepts q.1 q.2 ∧
    ¬BundleStatement (family.runOutput q.1 q.2).inputs}

end ComputedAdaptiveActionStatementFSFamily

end Zcash.Snark
