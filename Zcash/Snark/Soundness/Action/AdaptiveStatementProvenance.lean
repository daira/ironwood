import Zcash.Snark.Soundness.Action.AdaptiveStatementSurfaces

/-!
# Cached provenance for adaptive Action statements

This module layers the shared executable output/annotation cache over the unchanged logical
surface proofs.  All instance, pre-IPA, IPA, semantic, and complete-source comparisons consume
one retained adaptive execution.
-/

namespace Zcash.Snark

open Keygen

namespace ComputedAdaptiveActionStatementFSFamily

/-- Query annotations retained from one adaptive-statement execution. -/
abbrev AnnotationLog {pp : ProofParams}
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) :=
  List (LabeledOracleComp.QueryAnnotation (AdaptiveActionStatementTranscript pp)
    (AlgebraicTranscriptQuery (F := Fp) basis))

/-- Run the adaptive-statement adversary once and retain its output and query annotations. -/
def cachedExecution {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis) ×
      AnnotationLog basis :=
  (family.adversary basis).runWithAnnotations O

@[simp] theorem cachedExecution_output_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.cachedExecution basis O).1 = family.runOutput basis O := by
  simp [cachedExecution, runOutput]

@[simp] theorem cachedExecution_annotations_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.cachedExecution basis O).2 = (family.adversary basis).annotations O := by
  simp [cachedExecution]

/-- The retained annotation log has the adversary's original query bound. -/
theorem cachedExecution_log_length_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.cachedExecution basis O).2.length ≤ family.Q := by
  exact LabeledOracleComp.runWithAnnotations_log_length_le
    (family.adversary basis) (family.queryBound basis) O

/-- Canonical selected-instance coordinate check over a retained output. -/
def canonicalInstanceRepresentationRelationFinderOfOutput {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    ((List.ofFn fun p => List.ofFn fun column =>
      representationMismatchRelation?
        (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column)
        (output.instanceRepresentations p column) (by
          exact output.instanceRepresented p column |>.symm)).flatten)

@[simp] theorem canonicalInstanceRepresentationRelationFinderOfOutput_runOutput
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.canonicalInstanceRepresentationRelationFinderOfOutput basis
        (family.runOutput basis O) =
      family.canonicalInstanceRepresentationRelationFinder basis O := by
  rfl

/-- Cached comparison between final instance coordinates and the first `theta` annotation. -/
def queryInstanceRepresentationRelationFinderFromAnnotations {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (annotations : AnnotationLog basis)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let t := family.thetaPoint basis output
  selectedQueryRepresentationRelationFromAnnotations? t annotations
    (adaptiveStatementInstanceRepresentationList output.instanceRepresentations)
    (output.instanceRepresentations_coveredAtTheta (family.vkTranscriptRepr basis))

@[simp] theorem queryInstanceRepresentationRelationFinderFromAnnotations_annotations
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.queryInstanceRepresentationRelationFinderFromAnnotations basis
        ((family.adversary basis).annotations O) (family.runOutput basis O) =
      family.queryInstanceRepresentationRelationFinder basis O := by
  unfold queryInstanceRepresentationRelationFinderFromAnnotations
    queryInstanceRepresentationRelationFinder runOutput
  exact selectedQueryRepresentationRelationFromAnnotations?_eq _ _ _ _ _

/-- Complete retained-output instance binding. -/
def instanceRepresentationRelationFinderFromAnnotations {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (annotations : AnnotationLog basis)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match family.canonicalInstanceRepresentationRelationFinderOfOutput basis output with
  | some relation => some relation
  | none => family.queryInstanceRepresentationRelationFinderFromAnnotations basis annotations
      output

@[simp] theorem instanceRepresentationRelationFinderFromAnnotations_annotations
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.instanceRepresentationRelationFinderFromAnnotations basis
        ((family.adversary basis).annotations O) (family.runOutput basis O) =
      family.instanceRepresentationRelationFinder basis O := by
  unfold instanceRepresentationRelationFinderFromAnnotations
    instanceRepresentationRelationFinder
  rw [canonicalInstanceRepresentationRelationFinderOfOutput_runOutput,
    queryInstanceRepresentationRelationFinderFromAnnotations_annotations]
  split <;> rename_i heq <;> rw [heq]

/-- Cached-log form of one pre-IPA provenance comparison. -/
def preIpaRepresentationRelationAtFromAnnotations? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (annotations : AnnotationLog basis)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (n : Fin 11) (h5n : 5 ≤ (n : Nat)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let t := family.preIpaPoint basis n output
  selectedQueryRepresentationRelationFromAnnotations? t annotations
    (preIpaRepresentationTarget output n) (by
      intro ap hap
      rw [preIpaRepresentationTarget, List.mem_append] at hap
      rcases hap with hproof | hinstance
      · change ap.point ∈ transcriptGroupPoints
          (preIpaSqueezePoints (output.init (family.vkTranscriptRepr basis))
            output.proofData.algebraicProof.erase n)
        exact output.proofData.algebraicProof.representationsBefore_covered
          (output.init (family.vkTranscriptRepr basis)) output.proofData.wellFormed
          n h5n ap hproof
      · exact output.instanceRepresentations_coveredPre
          (family.vkTranscriptRepr basis) n ap hinstance)

@[simp] theorem preIpaRepresentationRelationAtFromAnnotations?_annotations
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11) (h5n : 5 ≤ (n : Nat)) :
    family.preIpaRepresentationRelationAtFromAnnotations? basis
        ((family.adversary basis).annotations O) (family.runOutput basis O) n h5n =
      family.preIpaRepresentationRelationAt? basis O n h5n := by
  unfold preIpaRepresentationRelationAtFromAnnotations?
    preIpaRepresentationRelationAt? runOutput
  exact selectedQueryRepresentationRelationFromAnnotations?_eq _ _ _ _ _

/-- One retained log performs all six pre-IPA provenance comparisons. -/
def preIpaRepresentationRelationFinderFromAnnotations {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (annotations : AnnotationLog basis)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    [family.preIpaRepresentationRelationAtFromAnnotations? basis annotations output 5 (by omega),
     family.preIpaRepresentationRelationAtFromAnnotations? basis annotations output 6 (by omega),
     family.preIpaRepresentationRelationAtFromAnnotations? basis annotations output 7 (by omega),
     family.preIpaRepresentationRelationAtFromAnnotations? basis annotations output 8 (by omega),
     family.preIpaRepresentationRelationAtFromAnnotations? basis annotations output 9 (by omega),
     family.preIpaRepresentationRelationAtFromAnnotations? basis annotations output 10 (by omega)]

@[simp] theorem preIpaRepresentationRelationFinderFromAnnotations_annotations
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.preIpaRepresentationRelationFinderFromAnnotations basis
        ((family.adversary basis).annotations O) (family.runOutput basis O) =
      family.preIpaRepresentationRelationFinder basis O := by
  simp [preIpaRepresentationRelationFinderFromAnnotations,
    preIpaRepresentationRelationFinder]

/-- Cached-log form of one IPA-round provenance comparison. -/
def ipaRepresentationRelationAtFromAnnotations? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (annotations : AnnotationLog basis)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (j : Fin (AdaptiveActionStatementShape pp).k) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let t := family.ipaPoint basis j output
  selectedQueryRepresentationRelationFromAnnotations? t annotations
    (ipaRepresentationTarget output j) (by
      intro ap hap
      rw [ipaRepresentationTarget, List.mem_append] at hap
      rcases hap with hproof | hinstance
      · change ap.point ∈ transcriptGroupPoints
          (roundTranscriptFin
            (preIpaTranscript (output.init (family.vkTranscriptRepr basis))
              output.proofData.algebraicProof.erase)
            output.proofData.algebraicProof.erase.ipaRounds j)
        exact output.proofData.algebraicProof.representationsBeforeRound_covered
          (output.init (family.vkTranscriptRepr basis)) output.proofData.wellFormed
          j ap hproof
      · exact output.instanceRepresentations_coveredRound
          (family.vkTranscriptRepr basis) j ap hinstance)

@[simp] theorem ipaRepresentationRelationAtFromAnnotations?_annotations
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k) :
    family.ipaRepresentationRelationAtFromAnnotations? basis
        ((family.adversary basis).annotations O) (family.runOutput basis O) j =
      family.ipaRepresentationRelationAt? basis O j := by
  unfold ipaRepresentationRelationAtFromAnnotations?
    ipaRepresentationRelationAt? runOutput
  exact selectedQueryRepresentationRelationFromAnnotations?_eq _ _ _ _ _

/-- One retained log performs every IPA-round provenance comparison. -/
def ipaRepresentationRelationFinderFromAnnotations {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (annotations : AnnotationLog basis)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    (List.ofFn fun j => family.ipaRepresentationRelationAtFromAnnotations? basis
      annotations output j)

@[simp] theorem ipaRepresentationRelationFinderFromAnnotations_annotations
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.ipaRepresentationRelationFinderFromAnnotations basis
        ((family.adversary basis).annotations O) (family.runOutput basis O) =
      family.ipaRepresentationRelationFinder basis O := by
  simp [ipaRepresentationRelationFinderFromAnnotations,
    ipaRepresentationRelationFinder]

/-- Cached-log form of one Action semantic-squeeze provenance comparison. -/
def semanticRepresentationRelationAtFromAnnotations? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (annotations : AnnotationLog basis)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
    (n : Fin 5) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let n11 : Fin 11 := Fin.castLE (by omega) n
  let t := family.preIpaPoint basis n11 output
  selectedQueryRepresentationRelationFromAnnotations? t annotations
    (semanticRepresentationTarget output n) (by
      intro ap hap
      rw [semanticRepresentationTarget, List.mem_append] at hap
      rcases hap with hproof | hinstance
      · change ap.point ∈ transcriptGroupPoints
          (preIpaSqueezePoints (output.init (family.vkTranscriptRepr basis))
            output.proofData.algebraicProof.erase n11)
        exact output.proofData.algebraicProof.actionRepresentationsBefore_covered
          (output.init (family.vkTranscriptRepr basis)) output.proofData.wellFormed
          n ap hproof
      · exact output.instanceRepresentations_coveredPre
          (family.vkTranscriptRepr basis) n11 ap hinstance)

@[simp] theorem semanticRepresentationRelationAtFromAnnotations?_annotations
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 5) :
    family.semanticRepresentationRelationAtFromAnnotations? basis
        ((family.adversary basis).annotations O) (family.runOutput basis O) n =
      family.semanticRepresentationRelationAt? basis O n := by
  unfold semanticRepresentationRelationAtFromAnnotations?
    semanticRepresentationRelationAt? runOutput
  exact selectedQueryRepresentationRelationFromAnnotations?_eq _ _ _ _ _

/-- One retained log performs all five Action semantic-squeeze provenance comparisons. -/
def semanticRepresentationRelationFinderFromAnnotations {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (annotations : AnnotationLog basis)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    (List.ofFn fun n => family.semanticRepresentationRelationAtFromAnnotations? basis
      annotations output n)

@[simp] theorem semanticRepresentationRelationFinderFromAnnotations_annotations
    {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.semanticRepresentationRelationFinderFromAnnotations basis
        ((family.adversary basis).annotations O) (family.runOutput basis O) =
      family.semanticRepresentationRelationFinder basis O := by
  simp [semanticRepresentationRelationFinderFromAnnotations,
    semanticRepresentationRelationFinder]

/-- One retained adaptive execution covers instance binding, all pre-IPA and IPA annotations, all
five semantic annotations, and all five complete-source comparisons. -/
def provenanceRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let execution := family.cachedExecution basis O
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    [family.instanceRepresentationRelationFinderFromAnnotations basis execution.2 execution.1,
     family.preIpaRepresentationRelationFinderFromAnnotations basis execution.2 execution.1,
     family.ipaRepresentationRelationFinderFromAnnotations basis execution.2 execution.1,
     family.semanticRepresentationRelationFinderFromAnnotations basis execution.2 execution.1,
     family.semanticSourceMismatchRelationFinderOfOutput basis execution.1]

/-- The shared-execution provenance finder is extensionally the five original aggregate checks. -/
theorem provenanceRelationFinder_eq_aggregates {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.provenanceRelationFinder basis O =
      ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
        [family.instanceRepresentationRelationFinder basis O,
         family.preIpaRepresentationRelationFinder basis O,
         family.ipaRepresentationRelationFinder basis O,
         family.semanticRepresentationRelationFinder basis O,
         family.semanticSourceMismatchRelationFinder basis O] := by
  simp [provenanceRelationFinder]

/-- An empty shared provenance finder means every constituent check was empty. -/
theorem provenanceRelationFinder_eq_none_iff {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.provenanceRelationFinder basis O = none ↔
      family.instanceRepresentationRelationFinder basis O = none ∧
      family.preIpaRepresentationRelationFinder basis O = none ∧
      family.ipaRepresentationRelationFinder basis O = none ∧
      family.semanticRepresentationRelationFinder basis O = none ∧
      family.semanticSourceMismatchRelationFinder basis O = none := by
  rw [family.provenanceRelationFinder_eq_aggregates basis O]
  simp [ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff]

end ComputedAdaptiveActionStatementFSFamily
end Zcash.Snark
