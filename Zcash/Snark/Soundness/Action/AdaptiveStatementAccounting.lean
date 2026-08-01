import Zcash.Snark.Soundness.Action.AdaptiveStatementModel
import Zcash.Snark.Soundness.Action.AdaptiveSurfaces
import Zcash.Snark.Soundness.AGM.AdaptiveStraightLine

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

/-- One output-selected pre-IPA Fiat--Shamir query. -/
def preIpaPoint {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (i : Fin 11)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    AdaptiveActionStatementTranscript pp :=
  output.prefixesPre (family.vkTranscriptRepr basis) i

/-- One output-selected IPA-round Fiat--Shamir query. -/
def ipaPoint {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    AdaptiveActionStatementTranscript pp :=
  output.prefixes (family.vkTranscriptRepr basis) j

/-- The output-selected first Fiat--Shamir query. -/
def thetaPoint {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    AdaptiveActionStatementTranscript pp :=
  output.prefixesPre (family.vkTranscriptRepr basis) 0

@[simp] theorem preIpaPoint_zero {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    family.preIpaPoint basis 0 output = family.thetaPoint basis output := by
  rfl

/-- Detect whether adversary-supplied instance coordinates differ from the canonical MSM
coordinates computed from the selected public-input rows. -/
def canonicalInstanceRepresentationRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let output := (family.adversary basis).run O
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    ((List.ofFn fun p => List.ofFn fun column =>
      representationMismatchRelation?
        (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column)
        (output.instanceRepresentations p column) (by
          exact output.instanceRepresented p column |>.symm)).flatten)

/-- Detect whether the final instance representations differ from those fixed by the first actual
query at the statement-bound `theta` prefix. A mismatch is an explicit AGM relation. -/
def queryInstanceRepresentationRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let output := (family.adversary basis).run O
  let t := family.thetaPoint basis output
  selectedQueryRepresentationRelation? t (family.adversary basis) O
    (adaptiveStatementInstanceRepresentationList output.instanceRepresentations)
    (output.instanceRepresentations_coveredAtTheta (family.vkTranscriptRepr basis))

/-- The complete instance-binding finder checks both public-input-to-commitment coordinates and
commitment-to-first-query coordinates. -/
def instanceRepresentationRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match family.canonicalInstanceRepresentationRelationFinder basis O with
  | some relation => some relation
  | none => family.queryInstanceRepresentationRelationFinder basis O

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
  unfold instanceRepresentationRelationFinder at hnone
  split at hnone
  · simp_all
  · exact hnone

/-- Outside the canonical-coordinate relation branch, every adversary-supplied instance
representation has exactly the public-input-derived MSM coefficients. -/
theorem instanceRepresentation_eq_canonical_of_none {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.instanceRepresentationRelationFinder basis O = none)
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns) :
    ((family.runOutput basis O).instanceRepresentations p column).coeffs =
      (canonicalAdaptiveStatementInstanceRepresentation pp basis
        (family.runOutput basis O).inputs p column).coeffs := by
  have hcanonical : family.canonicalInstanceRepresentationRelationFinder basis O = none := by
    unfold instanceRepresentationRelationFinder at hnone
    split at hnone
    · simp_all
    · assumption
  let output := family.runOutput basis O
  unfold canonicalInstanceRepresentationRelationFinder at hcanonical
  change ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
      ((List.ofFn fun p => List.ofFn fun column =>
        representationMismatchRelation?
          (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column)
          (output.instanceRepresentations p column) (by
            exact output.instanceRepresented p column |>.symm)).flatten) = none at hcanonical
  have hall :=
    (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1 hcanonical
  let check := representationMismatchRelation?
    (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column)
    (output.instanceRepresentations p column) (by
      exact output.instanceRepresented p column |>.symm)
  have hrow : (List.ofFn fun column => representationMismatchRelation?
        (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column)
        (output.instanceRepresentations p column) (by
          exact output.instanceRepresented p column |>.symm)) ∈
      List.ofFn (fun p => List.ofFn fun column => representationMismatchRelation?
        (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column)
        (output.instanceRepresentations p column) (by
          exact output.instanceRepresented p column |>.symm)) :=
    List.mem_ofFn.mpr ⟨p, rfl⟩
  have hcheck : check ∈ (List.ofFn fun p => List.ofFn fun column =>
      representationMismatchRelation?
        (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column)
        (output.instanceRepresentations p column) (by
          exact output.instanceRepresented p column |>.symm)).flatten :=
    List.mem_flatten.mpr ⟨_, hrow, List.mem_ofFn.mpr ⟨column, rfl⟩⟩
  have hat : check = none := hall check hcheck
  change (output.instanceRepresentations p column).coeffs =
    (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column).coeffs
  exact (representationMismatchRelation?_eq_none_iff _ _ _).1 hat |>.symm

/-! ## Proof-coordinate provenance at every verifier squeeze -/

/-- Final coordinates relevant to one of the six multiopen/root squeezes.  Instance coordinates
are included because the root polynomials use the public commitments as ordinary MSM members. -/
def preIpaRepresentationTarget {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (n : Fin 11) : List (AlgebraicPoint (F := Fp) basis) :=
  output.proofData.algebraicProof.representationsBefore n ++
    adaptiveStatementInstanceRepresentationList output.instanceRepresentations

/-- Compare all final coordinates needed at one multiopen/root squeeze with that query's first
pre-answer annotation. -/
def preIpaRepresentationRelationAt? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11) (h5n : 5 ≤ (n : Nat)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let output := family.runOutput basis O
  let t := family.preIpaPoint basis n output
  selectedQueryRepresentationRelation? t (family.adversary basis) O
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

/-- One finite finder covers `x₁`, `x₂`, `x₃`, `x₄`, `ξ`, and `z`. -/
def preIpaRepresentationRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    [family.preIpaRepresentationRelationAt? basis O 5 (by omega),
     family.preIpaRepresentationRelationAt? basis O 6 (by omega),
     family.preIpaRepresentationRelationAt? basis O 7 (by omega),
     family.preIpaRepresentationRelationAt? basis O 8 (by omega),
     family.preIpaRepresentationRelationAt? basis O 9 (by omega),
     family.preIpaRepresentationRelationAt? basis O 10 (by omega)]

/-- No combined pre-IPA relation means the phase-local comparison is empty. -/
theorem preIpaRepresentationRelationFinder_none_at {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.preIpaRepresentationRelationFinder basis O = none)
    (n : Fin 11) (h5n : 5 ≤ (n : Nat)) :
    family.preIpaRepresentationRelationAt? basis O n h5n = none := by
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1 hnone
  simp only [List.mem_cons, forall_eq_or_imp] at hall
  rcases hall with ⟨h5, h6, h7, h8, h9, h10⟩
  fin_cases n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · simpa using h5
  · simpa using h6
  · simpa using h7
  · simpa using h8
  · simpa using h9
  · simpa using h10

/-- Final coordinates relevant to one IPA-round squeeze, including the public-instance members. -/
def ipaRepresentationTarget {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (j : Fin (AdaptiveActionStatementShape pp).k) :
    List (AlgebraicPoint (F := Fp) basis) :=
  output.proofData.algebraicProof.representationsBeforeRound j ++
    adaptiveStatementInstanceRepresentationList output.instanceRepresentations

/-- Compare every coordinate affecting one IPA quadratic with the first annotation at that
round's actual statement-bound query. -/
def ipaRepresentationRelationAt? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let output := family.runOutput basis O
  let t := family.ipaPoint basis j output
  selectedQueryRepresentationRelation? t (family.adversary basis) O
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

/-- One finite finder covers every IPA round. -/
def ipaRepresentationRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    (List.ofFn fun j => family.ipaRepresentationRelationAt? basis O j)

/-- No combined IPA relation means every round-local comparison is empty. -/
theorem ipaRepresentationRelationFinder_none_at {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.ipaRepresentationRelationFinder basis O = none)
    (j : Fin (AdaptiveActionStatementShape pp).k) :
    family.ipaRepresentationRelationAt? basis O j = none := by
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1 hnone
  apply hall
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

/-- Final coordinates used by one of the five Action semantic surfaces. -/
def semanticRepresentationTarget {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (n : Fin 5) : List (AlgebraicPoint (F := Fp) basis) :=
  output.proofData.algebraicProof.actionRepresentationsBefore n ++
    adaptiveStatementInstanceRepresentationList output.instanceRepresentations

/-- Compare the final semantic-stage coordinates with the first annotation at that exact squeeze. -/
def semanticRepresentationRelationAt? {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 5) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let output := family.runOutput basis O
  let n11 : Fin 11 := Fin.castLE (by omega) n
  let t := family.preIpaPoint basis n11 output
  selectedQueryRepresentationRelation? t (family.adversary basis) O
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

/-- One finite finder covers all five semantic squeezes. -/
def semanticRepresentationRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    (List.ofFn fun n => family.semanticRepresentationRelationAt? basis O n)

/-- No combined semantic relation means every stage-local comparison is empty. -/
theorem semanticRepresentationRelationFinder_none_at {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.semanticRepresentationRelationFinder basis O = none)
    (n : Fin 5) :
    family.semanticRepresentationRelationAt? basis O n = none := by
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1 hnone
  apply hall
  exact List.mem_ofFn.mpr ⟨n, rfl⟩

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

/-- Exact `(Q + 1)` accounting for a bad set at any adaptive-statement pre-IPA squeeze. -/
theorem preIpaSurface_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (i : Fin 11)
    (bad : (t : AdaptiveActionStatementTranscript pp) →
      AlgebraicTranscriptQuery (F := Fp) basis t → family.Coins → Set Fp)
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
      {O | O (family.preIpaPoint basis i ((family.adversary basis).run O)) ∈
        LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
          bad fallback (family.preIpaPoint basis i ((family.adversary basis).run O)) O} ≤
      (family.Q + 1 : ℕ) * epsilon := by
  exact LabeledOracleComp.firstLabelOrFallbackBad_measure_le
    (family.adversary basis) (family.preIpaPoint basis i) bad fallback
    hbadBlind hfallbackBlind hbad hfallback (family.queryBound basis)

/-- Exact `(Q + 1)` accounting for a bad set at any adaptive-statement IPA-round squeeze. -/
theorem ipaSurface_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (bad : (t : AdaptiveActionStatementTranscript pp) →
      AlgebraicTranscriptQuery (F := Fp) basis t → family.Coins → Set Fp)
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
      {O | O (family.ipaPoint basis j ((family.adversary basis).run O)) ∈
        LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
          bad fallback (family.ipaPoint basis j ((family.adversary basis).run O)) O} ≤
      (family.Q + 1 : ℕ) * epsilon := by
  exact LabeledOracleComp.firstLabelOrFallbackBad_measure_le
    (family.adversary basis) (family.ipaPoint basis j) bad fallback
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

/-- A relation finder may cover final-output/query-label mismatches at any pre-IPA squeeze while
retaining the same single `(Q + 1)` factor. -/
theorem preIpaFinalBadWithoutRelation_table_le {pp : ProofParams} {Relation : Type*}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (i : Fin 11)
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
      let t := family.preIpaPoint basis i output
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
        let t := family.preIpaPoint basis i output
        O t ∈ finalBad output t O ∧ finder O = none} ≤
      (family.Q + 1 : ℕ) * epsilon := by
  exact LabeledOracleComp.finalBadWithoutRelation_measure_le
    (family.adversary basis) (family.preIpaPoint basis i) finalBad finder bad fallback
    hcover hbadBlind hfallbackBlind hbad hfallback (family.queryBound basis)

/-- IPA-round counterpart of `preIpaFinalBadWithoutRelation_table_le`. -/
theorem ipaFinalBadWithoutRelation_table_le {pp : ProofParams} {Relation : Type*}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (j : Fin (AdaptiveActionStatementShape pp).k)
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
      let t := family.ipaPoint basis j output
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
        let t := family.ipaPoint basis j output
        O t ∈ finalBad output t O ∧ finder O = none} ≤
      (family.Q + 1 : ℕ) * epsilon := by
  exact LabeledOracleComp.finalBadWithoutRelation_measure_le
    (family.adversary basis) (family.ipaPoint basis j) finalBad finder bad fallback
    hcover hbadBlind hfallbackBlind hbad hfallback (family.queryBound basis)

end ComputedAdaptiveActionStatementFSFamily

end Zcash.Snark
