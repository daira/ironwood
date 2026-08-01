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

/-- The deployed Action circuit has exactly one configured instance column. -/
theorem adaptiveActionStatement_numInstanceColumns (pp : ProofParams) :
    (AdaptiveActionStatementShape pp).numInstanceColumns = 1 := by
  rw [pp.mergeDerived_numInstanceColumns actionCircuit]
  native_decide

/-- Every unconfigured Action instance column serializes only zero rows. -/
theorem adaptiveActionPublicInputRows_ne_zero (input : PublicInputs Fp)
    {column : ℕ} (hcolumn : column ≠ 0) :
    ∀ i, (actionCircuit.publicInputRows input ⟨column⟩).getD i 0 = 0 := by
  have hzero : ∀ x ∈ actionCircuit.publicInputRows input ⟨column⟩, x = (0 : Fp) := by
    intro x hx
    rw [show actionCircuit.publicInputRows input ⟨column⟩ =
        (List.range PublicInputs.layout.usedRows).map (fun row =>
          (toElements input).toList.getD
            (PublicInputs.layout.cellList.idxOf ((⟨column⟩ : Column .instance), row)) 0)
        from rfl] at hx
    obtain ⟨row, -, rfl⟩ := List.mem_map.mp hx
    rw [List.idxOf_eq_length (by
      simp only [PublicInputs.layout, PublicInputLayout.cellList]
      simp
      intro _ hindex
      exact hcolumn hindex.symm)]
    have hlen : (toElements input).toList.length ≤
        PublicInputs.layout.cellList.length := by
      simp only [PublicInputLayout.cellList_length, Vector.length_toList]
      exact le_refl _
    exact List.getD_eq_default _ _ hlen
  intro i
  rcases lt_or_ge i (actionCircuit.publicInputRows input ⟨column⟩).length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact hzero _ (List.getElem_mem h)
  · exact List.getD_eq_default _ _ h

/-- A zero public-instance column commits only to its blinding generator, for any verifier URS. -/
theorem adaptiveCommitInstance_of_rows_zero {G : Type*} [AddCommGroup G] [Module Fp G]
    {urs : URS G} {omega : Fp} (key : LagrangeCommitmentKey urs omega)
    {values : List Fp} (hzero : ∀ i, values.getD i 0 = 0) (blind : Fp) :
    key.commitInstance values blind = blind • urs.w := by
  rw [LagrangeCommitmentKey.commitInstance, LagrangeCommitmentKey.commitRows,
    show zeroPaddedRows (n := 2 ^ urs.k) values = 0 from funext fun i => hzero (i : ℕ)]
  rw [show commitGen key.generators (0 : Fin (2 ^ urs.k) → Fp) = 0 by
    simp [commitGen], zero_add]

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

/-- Normalize the total verifier function outside the configured Action instance-column range.
Those indices are never absorbed or queried; using the URS blind generator matches the commitment
of Action's all-zero unconfigured columns. -/
def boundedAdaptiveStatementInstanceCommitment (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (instanceCommitment :
      Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG) :
    Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG :=
  fun p column =>
    if column < (AdaptiveActionStatementShape pp).numInstanceColumns then
      instanceCommitment p column
    else (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w

/-- The Action circuit's derived commitment family is already equal to its bounded normalization. -/
theorem adaptiveActionStatementInstanceCommitment_eq_bounded (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp) :
    adaptiveActionStatementInstanceCommitment pp basis inputs =
      boundedAdaptiveStatementInstanceCommitment pp basis
        (adaptiveActionStatementInstanceCommitment pp basis inputs) := by
  funext p column
  unfold boundedAdaptiveStatementInstanceCommitment
  by_cases hcolumn : column < (AdaptiveActionStatementShape pp).numInstanceColumns
  · rw [if_pos hcolumn]
  · rw [if_neg hcolumn]
    have hne : column ≠ 0 := by
      intro hzero
      subst column
      apply hcolumn
      rw [adaptiveActionStatement_numInstanceColumns]
      omega
    change (actionCircuit.instanceCommitmentKey pp
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis)).commitInstance
          (actionCircuit.publicInputRows
            (inputs (Fin.cast (pp.mergeDerived_numProofs actionCircuit) p)) ⟨column⟩) 1 =
      (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis).w
    rw [adaptiveCommitInstance_of_rows_zero _
      (adaptiveActionPublicInputRows_ne_zero _ hne)]
    simp

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

/-- The canonical augmented-basis coordinates of one selected public-instance commitment.
Unlike an adversary-supplied representation, these coefficients are computed from the actual
public-input rows and the verifier's default instance blind. -/
def canonicalAdaptiveStatementInstanceRepresentation (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns) :
    AlgebraicPoint (F := Fp) basis :=
  let urs := ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis
  let proofIndex : Fin pp.numProofs :=
    Fin.cast (pp.mergeDerived_numProofs actionCircuit) p
  let instanceColumn : Column .instance := ⟨column⟩
  let coeffs := instanceCoefficients (2 ^ urs.k) actionCircuit.omega
    (actionCircuit.publicInputRows (inputs proofIndex) instanceColumn)
  { point := adaptiveActionStatementInstanceCommitment pp basis inputs p column
    repr :=
      { coeffs := augmentedCoeffs coeffs 0 1
        hEq := by
          calc
            representationEval basis (augmentedCoeffs coeffs 0 1) =
                representationEval (augmentedBasis urs.g urs.u urs.w)
                  (augmentedCoeffs coeffs 0 1) := by
              exact congrArg (fun b => representationEval b (augmentedCoeffs coeffs 0 1))
                (augmentedBasis_ursOfAugmentedBasis
                  (AdaptiveActionStatementShape pp).k basis).symm
            _ = commitGen urs.g coeffs + 0 • urs.u + 1 • urs.w :=
              representationEval_augmentedBasis urs.g urs.u urs.w coeffs 0 1
            _ = commit urs coeffs + urs.w := by
              simp only [zero_smul, add_zero, one_smul, commit]
              rfl
            _ = adaptiveActionStatementInstanceCommitment pp basis inputs p column := by
              change commit urs coeffs + urs.w =
                actionCircuit.instanceCommitment pp urs inputs proofIndex instanceColumn.index
              exact (actionCircuit.instanceCommitment_column_eq_commit
                pp urs inputs proofIndex instanceColumn).symm } }

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

/-- Final instance representations remain covered at every later pre-IPA squeeze. -/
theorem instanceRepresentations_coveredPre {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (n : Fin 11) :
    ∀ ap ∈ adaptiveStatementInstanceRepresentationList output.instanceRepresentations,
      ap.point ∈ transcriptGroupPoints (output.prefixesPre vkTranscriptRepr n).val := by
  intro ap hap
  have hzero := output.instanceRepresentations_coveredAtTheta vkTranscriptRepr ap hap
  apply (transcriptGroupPoints_prefix ?_).mem hzero
  exact preIpaSqueezePoints_prefix_of_le
    (output.init vkTranscriptRepr) output.toAlgebraicWfProof.proof.1
    output.toAlgebraicWfProof.proof.2 0 n (by omega)

/-- Final instance representations also remain covered throughout the IPA round chain. -/
theorem instanceRepresentations_coveredRound {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (j : Fin (AdaptiveActionStatementShape pp).k) :
    ∀ ap ∈ adaptiveStatementInstanceRepresentationList output.instanceRepresentations,
      ap.point ∈ transcriptGroupPoints (output.prefixes vkTranscriptRepr j).val := by
  intro ap hap
  have hzero := output.instanceRepresentations_coveredAtTheta vkTranscriptRepr ap hap
  apply (transcriptGroupPoints_prefix ?_).mem hzero
  change preIpaSqueezePoints (output.init vkTranscriptRepr)
      output.toAlgebraicWfProof.proof.1 0 <+:
    roundTranscriptFin
      (preIpaTranscript (output.init vkTranscriptRepr)
        output.toAlgebraicWfProof.proof.1)
      output.toAlgebraicWfProof.proof.1.ipaRounds j
  exact (preIpaSqueezePoints_prefix
    (output.init vkTranscriptRepr) output.toAlgebraicWfProof.proof.1 0).trans (by
      unfold roundTranscriptFin
      exact List.prefix_append _ _)

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
