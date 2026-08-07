import Zcash.Snark.Soundness.AGM.CostedOracle
import Zcash.Snark.Soundness.Action.AdaptiveStatementCached
import Zcash.Snark.Soundness.Action.AdaptiveStatementReads
import Zcash.Snark.Soundness.Composition.AssembleGroupCost

/-!
# Certified adaptive-statement work accounting

This module replaces the two free natural-number work declarations in
`AdaptiveStatementDlogProfile` with executable accounting objects:

* `AdaptiveStatementAdversaryCostCertificate` supplies a staged costed oracle program, proves that
  its erasure is the original online-AGM adversary, and proves a structural path bound;
* `adaptiveStatementFinderReductionProgram` and
  `adaptiveStatementExtractorReductionProgram` execute group-valued postprocessing through
  reified Vesta primitives, using the one-execution cache from `AdaptiveStatementCached`.

The executable programs charge the group-operation work of each stage that actually runs, while
the public bound retains conservative slack for quotient and terminal proof construction.  It
includes programmed-basis evaluation, canonical instance evaluation, verifier assembly, the
identity/terminal path, and the final witness projection.  Equality tests,
annotation/source-list scans, field operations, and direct-coordinate decode work are not DLOG
group operations; the latter remains in its existing separate model.  Random-oracle queries are
also kept separate: one adversary run plus the canonical `11 + k` challenge reads.
-/

namespace Zcash.Snark

open Keygen

local instance adaptiveStatementCostVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- A basis-indexed staged program whose erasure is the supplied adaptive-statement adversary.
`staged` is the explicit host-language fidelity boundary described by
`CostedLabeledOracleComp.StagedGroupWorkFaithful`; the remaining fields are checked entirely by
Lean. -/
structure AdaptiveStatementAdversaryCostCertificate {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (workLimit : Nat) where
  program :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      CostedLabeledOracleComp (AdaptiveActionStatementTranscript pp) Fp
        (AlgebraicTranscriptQuery (F := Fp) basis)
        (AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
  erase_eq : ∀ basis, (program basis).erase = family.adversary basis
  staged : ∀ basis, (program basis).StagedGroupWorkFaithful
  workBound : ∀ basis, (program basis).GroupWorkBound workLimit

namespace AdaptiveStatementAdversaryCostCertificate

/-- Pointwise adversary group work read from the costed syntax. -/
def proverGroupWork {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Nat :=
  (certificate.program basis).groupWork O

theorem proverGroupWork_le {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    certificate.proverGroupWork basis O ≤ workLimit :=
  certificate.workBound basis O

/-- Erasure gives exactly the output used by the original adaptive game. -/
theorem run_eq {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (certificate.program basis).run O = family.runOutput basis O := by
  unfold CostedLabeledOracleComp.run runOutput
  rw [certificate.erase_eq]

end AdaptiveStatementAdversaryCostCertificate

/-- Number of fixed augmented-basis entries evaluated by one full-width representation. -/
def adaptiveStatementBasisWidth (pp : ProofParams) : Nat :=
  2 ^ (AdaptiveActionStatementShape pp).k + 2

/-! ## Concrete MSM encodings

These lists are the operands consumed by the reified Vesta MSM primitive.  Their lengths, and not
caller-supplied natural numbers, determine reduction work.
-/

/-- Concrete terms for a generator-only commitment. -/
def vestaCommitGenTerms {n : Nat} (g : Fin n → VestaG) (coeffs : Fin n → Fp) :
    List (Fp × VestaG) :=
  List.ofFn fun i => (coeffs i, g i)

@[simp] theorem vestaCommitGenTerms_length {n : Nat} (g : Fin n → VestaG)
    (coeffs : Fin n → Fp) :
    (vestaCommitGenTerms g coeffs).length = n := by
  simp [vestaCommitGenTerms]

theorem vestaCommitGenTerms_sum {n : Nat} (g : Fin n → VestaG)
    (coeffs : Fin n → Fp) :
    ((vestaCommitGenTerms g coeffs).map fun term => term.1 • term.2).sum =
      commitGen g coeffs := by
  simp [vestaCommitGenTerms, commitGen, List.sum_ofFn]

/-- Concrete terms for an augmented-basis representation. -/
def vestaAugmentedRepresentationTerms {k : Nat}
    (basis : AugmentedIndex (2 ^ k) → VestaG)
    (coeffs : AugmentedIndex (2 ^ k) → Fp) : List (Fp × VestaG) :=
  List.ofFn (fun i : Fin (2 ^ k) =>
      (coeffs (AugmentedIndex.gen i), basis (AugmentedIndex.gen i))) ++
    [(coeffs AugmentedIndex.u, basis AugmentedIndex.u),
     (coeffs AugmentedIndex.w, basis AugmentedIndex.w)]

@[simp] theorem vestaAugmentedRepresentationTerms_length {k : Nat}
    (basis : AugmentedIndex (2 ^ k) → VestaG)
    (coeffs : AugmentedIndex (2 ^ k) → Fp) :
    (vestaAugmentedRepresentationTerms basis coeffs).length = 2 ^ k + 2 := by
  simp [vestaAugmentedRepresentationTerms]

theorem vestaAugmentedRepresentationTerms_sum {k : Nat}
    (basis : AugmentedIndex (2 ^ k) → VestaG)
    (coeffs : AugmentedIndex (2 ^ k) → Fp) :
    ((vestaAugmentedRepresentationTerms basis coeffs).map
      fun term => term.1 • term.2).sum = representationEval basis coeffs := by
  rw [representationEval_augmented_components]
  simp [vestaAugmentedRepresentationTerms, List.sum_ofFn]
  abel

/-- Concrete terms for evaluating the verifier's assembled MSM. -/
def vestaAssembledMsmTerms (urs : Zcash.Arithmetic.URS VestaG)
    (msm : Zcash.Arithmetic.Msm urs.k Fp VestaG) : List (Fp × VestaG) :=
  List.ofFn (fun i => (msm.gScalars i, urs.g i)) ++
    [(msm.wScalar, urs.w), (msm.uScalar, urs.u)] ++ msm.other

@[simp] theorem vestaAssembledMsmTerms_length (urs : Zcash.Arithmetic.URS VestaG)
    (msm : Zcash.Arithmetic.Msm urs.k Fp VestaG) :
    (vestaAssembledMsmTerms urs msm).length = 2 ^ urs.k + 2 + msm.other.length := by
  simp [vestaAssembledMsmTerms]
  omega

theorem vestaAssembledMsmTerms_sum (urs : Zcash.Arithmetic.URS VestaG)
    (msm : Zcash.Arithmetic.Msm urs.k Fp VestaG) :
    ((vestaAssembledMsmTerms urs msm).map fun term => term.1 • term.2).sum =
      msm.eval urs := by
  simp [vestaAssembledMsmTerms, Zcash.Arithmetic.Msm.eval,
    List.sum_ofFn]
  abel

/-- Canonical enumeration of the augmented public-basis slots. -/
def adaptiveStatementAugmentedIndices (pp : ProofParams) :
    List (AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k)) :=
  List.ofFn (fun i => AugmentedIndex.gen i) ++
    [AugmentedIndex.u, AugmentedIndex.w]

@[simp] theorem adaptiveStatementAugmentedIndices_length (pp : ProofParams) :
    (adaptiveStatementAugmentedIndices pp).length = adaptiveStatementBasisWidth pp := by
  simp [adaptiveStatementAugmentedIndices, adaptiveStatementBasisWidth]

private theorem sum_mapped_lengths_of_constant {α : Type*} (lists : List (List α)) (n : Nat)
    (hlength : ∀ list ∈ lists, list.length = n) :
    (lists.map List.length).sum = n * lists.length := by
  induction lists with
  | nil => simp
  | cons head tail ih =>
      have hhead := hlength head (by simp)
      have htail : ∀ list ∈ tail, list.length = n := by
        intro list hmem
        exact hlength list (by simp [hmem])
      simp [hhead, ih htail, Nat.mul_add]
      omega

/-- Actual two-term MSM operands used to program every public-basis slot from a DLOG challenge. -/
def adaptiveStatementProgrammedBasisTermSets (pp : ProofParams) (B C : VestaG)
    (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) :
    List (List (Fp × VestaG)) :=
  (adaptiveStatementAugmentedIndices pp).map fun i => [(x i, B), (y i, C)]

/-- Operational programmed-basis construction. -/
def costedAdaptiveStatementProgrammedBasis (pp : ProofParams) (B C : VestaG)
    (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) :
    CostedVestaComp (List VestaG) :=
  CostedVestaComp.evalMsms (adaptiveStatementProgrammedBasisTermSets pp B C x y)

@[simp] theorem costedAdaptiveStatementProgrammedBasis_run (pp : ProofParams) (B C : VestaG)
    (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) :
    (costedAdaptiveStatementProgrammedBasis pp B C x y).run =
      (adaptiveStatementAugmentedIndices pp).map fun i => x i • B + y i • C := by
  simp [costedAdaptiveStatementProgrammedBasis,
    adaptiveStatementProgrammedBasisTermSets]

@[simp] theorem costedAdaptiveStatementProgrammedBasis_groupWork (pp : ProofParams)
    (B C : VestaG)
    (x y : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) :
    (costedAdaptiveStatementProgrammedBasis pp B C x y).groupWork =
      2 * adaptiveStatementBasisWidth pp := by
  rw [costedAdaptiveStatementProgrammedBasis,
    CostedVestaComp.groupWork_evalMsms]
  have hlength : ∀ terms ∈ adaptiveStatementProgrammedBasisTermSets pp B C x y,
      terms.length = 2 := by
    intro terms hterms
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hterms
    rfl
  rw [sum_mapped_lengths_of_constant _ 2 hlength]
  simp [adaptiveStatementProgrammedBasisTermSets]

/-- Actual augmented-basis operands of every canonical selected-instance commitment. -/
def adaptiveStatementCanonicalInstanceTermSets {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    List (List (Fp × VestaG)) :=
  (List.ofFn fun p => List.ofFn fun column =>
    vestaAugmentedRepresentationTerms basis
      (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column).coeffs
  ).flatten

theorem adaptiveStatementCanonicalInstanceTermSets_work {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    ((adaptiveStatementCanonicalInstanceTermSets family basis output).map List.length).sum =
      (AdaptiveActionStatementShape pp).numProofs *
        (AdaptiveActionStatementShape pp).numInstanceColumns *
          adaptiveStatementBasisWidth pp := by
  have hlength : ∀ terms ∈ adaptiveStatementCanonicalInstanceTermSets family basis output,
      terms.length = adaptiveStatementBasisWidth pp := by
    intro terms hterms
    obtain ⟨row, hrow, hterms⟩ := List.mem_flatten.mp hterms
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hrow
    obtain ⟨column, rfl⟩ := List.mem_ofFn.mp hterms
    simp [adaptiveStatementBasisWidth]
  have hcount : (adaptiveStatementCanonicalInstanceTermSets family basis output).length =
      (AdaptiveActionStatementShape pp).numProofs *
        (AdaptiveActionStatementShape pp).numInstanceColumns := by
    simp [adaptiveStatementCanonicalInstanceTermSets, List.sum_ofFn,
      Finset.sum_const]
  rw [sum_mapped_lengths_of_constant _ _ hlength]
  rw [hcount]
  rw [Nat.mul_comm]

/-- Execute all canonical instance commitment evaluations through the reified MSM primitive and
retain the resulting points in proof-major, column-major order. -/
def costedAdaptiveStatementCanonicalInstanceValues {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    CostedVestaComp (List VestaG) :=
  CostedVestaComp.evalMsms
    (adaptiveStatementCanonicalInstanceTermSets family basis output)

@[simp] theorem costedAdaptiveStatementCanonicalInstanceValues_run {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    (costedAdaptiveStatementCanonicalInstanceValues family basis output).run =
      (List.ofFn fun p => List.ofFn fun column =>
        (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column).point
      ).flatten := by
  rw [costedAdaptiveStatementCanonicalInstanceValues,
    CostedVestaComp.run_evalMsms]
  unfold adaptiveStatementCanonicalInstanceTermSets
  rw [List.map_flatten]
  apply congrArg List.flatten
  rw [List.map_ofFn, List.ofFn_inj]
  funext p
  simp only [Function.comp_apply, List.map_ofFn]
  rw [List.ofFn_inj]
  funext column
  exact (vestaAugmentedRepresentationTerms_sum basis
    (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column).coeffs
  ).trans (canonicalAdaptiveStatementInstanceRepresentation pp basis output.inputs p column).hEq

/-- Execute all canonical instance commitment evaluations for their audited effects. -/
def costedAdaptiveStatementCanonicalInstances {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    CostedVestaComp Unit :=
  CostedVestaComp.map (fun _ => ())
    (costedAdaptiveStatementCanonicalInstanceValues family basis output)

@[simp] theorem costedAdaptiveStatementCanonicalInstances_run {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    (costedAdaptiveStatementCanonicalInstances family basis output).run = () := by
  simp [costedAdaptiveStatementCanonicalInstances]

@[simp] theorem costedAdaptiveStatementCanonicalInstances_groupWork {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (output : AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis)) :
    (costedAdaptiveStatementCanonicalInstances family basis output).groupWork =
      (AdaptiveActionStatementShape pp).numProofs *
        (AdaptiveActionStatementShape pp).numInstanceColumns *
          adaptiveStatementBasisWidth pp := by
  simp [costedAdaptiveStatementCanonicalInstances,
    costedAdaptiveStatementCanonicalInstanceValues,
    adaptiveStatementCanonicalInstanceTermSets_work]

/-- Acceptance driven by the same reified MSM, with an intrinsic equation to the ordinary
executable check.  The equation lets later costed branches consume the reified verdict without
re-running `accepts?V` in a host-language `pure` payload. -/
def costedAcceptsVCertified {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) :
    CostedVestaComp
      {result : Option (PLift (family.acceptsV basis view)) //
        result = family.accepts?V basis view} :=
  let shape := AdaptiveActionStatementShape pp
  let urs := ursOfAugmentedBasis shape.k basis
  match hassemble : assemble? (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := shape.k) view.pre view.rounds) with
  | none => CostedVestaComp.pure ⟨none, by
      have hreject : ¬family.acceptsV basis view := by
        unfold acceptsV DeployedAccepts
        rw [hassemble]
        simp
      simp [accepts?V, hreject]⟩
  | some msm =>
      CostedVestaComp.bind
        (CostedVestaComp.vestaMsmCertified (vestaAssembledMsmTerms urs msm)) fun evaluated =>
      if hzero : evaluated.1 = 0 then
        let haccepts : family.acceptsV basis view := by
          unfold acceptsV DeployedAccepts
          rw [hassemble]
          rw [evaluated.2, vestaAssembledMsmTerms_sum] at hzero
          exact hzero
        CostedVestaComp.pure ⟨some ⟨haccepts⟩, by
          simp [accepts?V, haccepts]⟩
      else
        CostedVestaComp.pure ⟨none, by
          have heval : msm.eval urs ≠ 0 := by
            intro hz
            apply hzero
            rw [evaluated.2, vestaAssembledMsmTerms_sum, hz]
          have hreject : ¬family.acceptsV basis view := by
            unfold acceptsV DeployedAccepts
            rw [hassemble]
            exact heval
          simp [accepts?V, hreject]⟩

/-- The selected verifier acceptance check executed through a concrete reified MSM. -/
def costedAcceptsV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) :
    CostedVestaComp (Option (PLift (family.acceptsV basis view))) :=
  CostedVestaComp.map Subtype.val (family.costedAcceptsVCertified basis view)

@[simp] theorem costedAcceptsVCertified_run {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) :
    (family.costedAcceptsVCertified basis view).run =
      ⟨family.accepts?V basis view, rfl⟩ := by
  apply Subtype.ext
  exact (family.costedAcceptsVCertified basis view).run.property

@[simp] theorem costedAcceptsVCertified_groupWork {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) :
    (family.costedAcceptsVCertified basis view).groupWork =
      deployedAssembleGroupOps (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        view.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) := by
  unfold costedAcceptsVCertified deployedAssembleGroupOps
  dsimp only
  split
  · rename_i hassemble
    simp [hassemble]
  · rename_i msm hassemble
    simp only [CostedVestaComp.groupWork_bind,
      CostedVestaComp.groupWork_vestaMsmCertified,
      CostedVestaComp.run_vestaMsmCertified]
    rw [vestaAssembledMsmTerms_length]
    split <;> simp [hassemble, ursOfAugmentedBasis]

theorem costedAcceptsVCertified_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) :
    (family.costedAcceptsVCertified basis view).groupWork ≤
      assembleGroupOpsBudget (AdaptiveActionStatementShape pp) := by
  rw [family.costedAcceptsVCertified_groupWork basis view]
  exact deployedAssembleGroupOps_le _ _ _ _

@[simp] theorem costedAcceptsV_run {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) :
    (family.costedAcceptsV basis view).run = family.accepts?V basis view := by
  simp [costedAcceptsV]

/-- Operational acceptance work is the term count of the actual assembled MSM. -/
theorem costedAcceptsV_groupWork {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) :
    (family.costedAcceptsV basis view).groupWork =
      deployedAssembleGroupOps (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
        view.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) := by
  simp [costedAcceptsV, family.costedAcceptsVCertified_groupWork basis view]

theorem costedAcceptsV_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis) :
    (family.costedAcceptsV basis view).groupWork ≤
      assembleGroupOpsBudget (AdaptiveActionStatementShape pp) := by
  rw [family.costedAcceptsV_groupWork basis view]
  exact deployedAssembleGroupOps_le _ _ _ _

/-- Result of the operational four-stage finder.  The retained implication is group-free proof
data used by the extractor when the relation branch is empty. -/
structure AdaptiveStatementOperationalFinderResult {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis) where
  value : Option (AlgebraicRelationWitness (F := Fp) basis)
  calls : Nat
  provenance_none : value = none →
    family.provenanceRelationFinderOfCachedRun basis cache = none

/-- Data-bearing verdict of the group-free provenance stage. -/
inductive AdaptiveStatementProvenanceVerdict {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis) where
  | found (relation : AlgebraicRelationWitness (F := Fp) basis)
      (hfound : family.provenanceRelationFinderOfCachedRun basis cache = some relation)
  | clear (hnone : family.provenanceRelationFinderOfCachedRun basis cache = none)

/-- Provenance verdict together with the already-established facts consumed after a clear pass. -/
structure AdaptiveStatementProvenancePlan {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis) where
  facts : family.provenanceRelationFinderOfCachedRun basis cache = none →
    family.SemanticStageFacts basis cache.toRunView
  verdict : AdaptiveStatementProvenanceVerdict family basis cache

/-- Evaluate provenance once and retain its equation for the operational program. -/
def adaptiveStatementProvenancePlan {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis)
    (facts : family.provenanceRelationFinderOfCachedRun basis cache = none →
      family.SemanticStageFacts basis cache.toRunView) :
    AdaptiveStatementProvenancePlan family basis cache :=
  { facts := facts
    verdict :=
      match hprovenance : family.provenanceRelationFinderOfCachedRun basis cache with
      | some relation => .found relation hprovenance
      | none => .clear hprovenance }

/-- Operational quotient, identity, and terminal stages after provenance has been discharged. -/
def adaptiveStatementFinderAfterProvenanceProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis cache.output.inputs)
      cache.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) cache.pre cache.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (facts : family.SemanticStageFacts basis cache.toRunView)
    (hprovenance : family.provenanceRelationFinderOfCachedRun basis cache = none) :
    CostedVestaComp (AdaptiveStatementOperationalFinderResult family basis cache) :=
  match family.statementQuotientRelationFinderV basis cache.toRunView with
  | some relation => CostedVestaComp.pure
      { value := some relation
        calls := 2
        provenance_none := fun _ => hprovenance }
  | none =>
      CostedVestaComp.bind (family.costedAcceptsVCertified basis cache.toRunView)
        fun acceptance =>
      match family.identityRelationFinderWithAcceptanceV basis cache.toRunView hcharV
          acceptance.1 none (fun _ => facts) with
      | some relation => CostedVestaComp.pure
          { value := some relation
            calls := 3
            provenance_none := fun _ => hprovenance }
      | none =>
          CostedVestaComp.bind (family.costedAcceptsVCertified basis cache.toRunView)
            fun acceptance =>
          CostedVestaComp.pure
            { value := family.terminalRelationFinderWithAcceptanceV basis cache.toRunView
                hcharV acceptance.1
              calls := 4
              provenance_none := fun _ => hprovenance }

@[simp] theorem adaptiveStatementFinderAfterProvenanceProgram_run_pair {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV)
    (facts) (hprovenance) :
    let result := (adaptiveStatementFinderAfterProvenanceProgram family basis cache hcharV
      facts hprovenance).run
    (result.value, result.calls) =
      family.relationFinderAfterCachedProvenance basis cache hcharV facts := by
  cases hquotient : family.statementQuotientRelationFinderV basis cache.toRunView with
  | some relation =>
      simp [adaptiveStatementFinderAfterProvenanceProgram,
        relationFinderAfterCachedProvenance, hquotient]
  | none =>
      cases hidentity : family.identityRelationFinderWithAcceptanceV basis cache.toRunView
          hcharV (family.accepts?V basis cache.toRunView) none (fun _ => facts) with
      | some relation =>
          simp [adaptiveStatementFinderAfterProvenanceProgram,
            relationFinderAfterCachedProvenance, identityRelationFinderV,
            hquotient, hidentity]
      | none =>
          simp [adaptiveStatementFinderAfterProvenanceProgram,
            relationFinderAfterCachedProvenance, identityRelationFinderV,
            terminalRelationFinderV, hquotient, hidentity]

theorem adaptiveStatementFinderAfterProvenanceProgram_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV)
    (facts) (hprovenance) :
    (adaptiveStatementFinderAfterProvenanceProgram family basis cache hcharV facts
      hprovenance).groupWork ≤
        2 * assembleGroupOpsBudget (AdaptiveActionStatementShape pp) := by
  unfold adaptiveStatementFinderAfterProvenanceProgram
  split
  · simp
  · rw [CostedVestaComp.groupWork_bind, costedAcceptsVCertified_groupWork,
      costedAcceptsVCertified_run]
    split
    · simp
      have haccept : deployedAssembleGroupOps
          (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis cache.toRunView.output.inputs)
          cache.toRunView.output.toAlgebraicWfProof.proof.1
          (chRecord (k := (AdaptiveActionStatementShape pp).k)
            cache.toRunView.pre cache.toRunView.rounds) ≤
            assembleGroupOpsBudget (AdaptiveActionStatementShape pp) :=
        deployedAssembleGroupOps_le _ _ _ _
      omega
    · rw [CostedVestaComp.groupWork_bind, costedAcceptsVCertified_groupWork,
        costedAcceptsVCertified_run]
      simp
      have haccept : deployedAssembleGroupOps
          (adaptiveActionStatementVk pp basis)
          (adaptiveActionStatementInstanceCommitment pp basis cache.toRunView.output.inputs)
          cache.toRunView.output.toAlgebraicWfProof.proof.1
          (chRecord (k := (AdaptiveActionStatementShape pp).k)
            cache.toRunView.pre cache.toRunView.rounds) ≤
            assembleGroupOpsBudget (AdaptiveActionStatementShape pp) :=
        deployedAssembleGroupOps_le _ _ _ _
      omega

/-- Operational four-stage finder over one cached run.  Canonical instance commitments and each
verifier equation are executed through reified MSM nodes; the verifier result itself selects the
identity and terminal branches.  The remaining computations inspect field coordinates, lists, or
proof-erased evidence only. -/
def adaptiveStatementFinderReductionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis cache.output.inputs)
      cache.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) cache.pre cache.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (plan : AdaptiveStatementProvenancePlan family basis cache) :
    CostedVestaComp (AdaptiveStatementOperationalFinderResult family basis cache) :=
  CostedVestaComp.bind
    (costedAdaptiveStatementCanonicalInstances family basis cache.output) fun _ =>
  match plan.verdict with
  | .found relation _ => CostedVestaComp.pure
      { value := some relation
        calls := 1
        provenance_none := by simp }
  | .clear hprovenance =>
      adaptiveStatementFinderAfterProvenanceProgram family basis cache hcharV
        (plan.facts hprovenance) hprovenance

@[simp] theorem adaptiveStatementFinderReductionProgram_run_pair {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (plan) :
    let result :=
      (adaptiveStatementFinderReductionProgram family basis cache hcharV plan).run
    (result.value, result.calls) =
      family.relationFinderWithCallsOfCachedRun basis cache hcharV plan.facts := by
  cases plan with
  | mk facts verdict =>
    cases verdict with
    | found relation hprovenance =>
      rw [family.relationFinderWithCallsOfCachedRun_of_some basis cache hcharV facts
        relation hprovenance]
      simp [adaptiveStatementFinderReductionProgram]
    | clear hprovenance =>
      rw [family.relationFinderWithCallsOfCachedRun_of_none basis cache hcharV facts
        hprovenance]
      unfold adaptiveStatementFinderReductionProgram
      simp [adaptiveStatementFinderAfterProvenanceProgram_run_pair]

@[simp] theorem adaptiveStatementFinderReductionProgram_run_value {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (plan) :
    (adaptiveStatementFinderReductionProgram family basis cache hcharV plan).run.value =
      (family.relationFinderWithCallsOfCachedRun basis cache hcharV plan.facts).1 := by
  exact congrArg Prod.fst
    (adaptiveStatementFinderReductionProgram_run_pair family basis cache hcharV plan)

@[simp] theorem adaptiveStatementFinderReductionProgram_run_calls {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (plan) :
    (adaptiveStatementFinderReductionProgram family basis cache hcharV plan).run.calls =
      (family.relationFinderWithCallsOfCachedRun basis cache hcharV plan.facts).2 := by
  exact congrArg Prod.snd
    (adaptiveStatementFinderReductionProgram_run_pair family basis cache hcharV plan)

/-- Operational witness extraction over the same finder program.  A retained relation returns no
witness; otherwise a third reified verifier execution drives the post-finder outcome. -/
def adaptiveStatementKnowledgeExtractorWithAcceptanceV {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (view : RunView pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (acceptance : Option (PLift (family.acceptsV basis view)))
    (facts : family.SemanticStageFacts basis view)
    (finderResult : Option (AlgebraicRelationWitness (F := Fp) basis)) :
    Option (ActionTerminal.ActionBundleWitness view.output.inputs) :=
  match finderResult with
  | some _ => none
  | none =>
      match family.adaptiveStatementKnowledgeOutcomeCoreWithAcceptanceV basis view hcharV
          acceptance facts with
      | some (Sum.inl witness) => some witness
      | _ => none

@[simp] theorem adaptiveStatementKnowledgeExtractorWithAcceptanceV_accepts {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (view) (hcharV) (facts)
    (finderResult) :
    family.adaptiveStatementKnowledgeExtractorWithAcceptanceV basis view hcharV
        (family.accepts?V basis view) facts finderResult =
      family.adaptiveStatementKnowledgeExtractorV basis view hcharV finderResult
        (fun _ => facts) := by
  cases finderResult <;> rfl

def adaptiveStatementExtractorReductionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (cache : CachedRun pp family basis)
    (hcharV : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis cache.output.inputs)
      cache.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) cache.pre cache.rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (plan : AdaptiveStatementProvenancePlan family basis cache) :
    CostedVestaComp (Option (ActionTerminal.ActionBundleWitness cache.output.inputs)) :=
  match plan.verdict with
  | .found _ _ =>
      CostedVestaComp.bind
        (adaptiveStatementFinderReductionProgram family basis cache hcharV plan) fun _ =>
      CostedVestaComp.pure none
  | .clear hprovenance =>
      let facts := plan.facts hprovenance
      CostedVestaComp.bind
        (adaptiveStatementFinderReductionProgram family basis cache hcharV plan) fun finder =>
      match finder.value with
      | some _ => CostedVestaComp.pure none
      | none =>
          CostedVestaComp.bind (family.costedAcceptsVCertified basis cache.toRunView)
            fun acceptance =>
          CostedVestaComp.pure
            (family.adaptiveStatementKnowledgeExtractorWithAcceptanceV basis cache.toRunView
              hcharV acceptance.1 facts none)

@[simp] theorem adaptiveStatementExtractorReductionProgram_run {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (plan) :
    (adaptiveStatementExtractorReductionProgram family basis cache hcharV plan).run =
      match plan.verdict with
      | .found _ _ => none
      | .clear hprovenance =>
          family.adaptiveStatementKnowledgeExtractorWithAcceptanceV basis cache.toRunView
            hcharV (family.accepts?V basis cache.toRunView) (plan.facts hprovenance)
            (family.relationFinderWithCallsOfCachedRun basis cache hcharV plan.facts).1 := by
  cases plan with
  | mk facts verdict =>
    cases verdict with
    | found relation hprovenance =>
      unfold adaptiveStatementExtractorReductionProgram
      simp
    | clear hprovenance =>
      unfold adaptiveStatementExtractorReductionProgram
      rw [CostedVestaComp.run_bind,
        adaptiveStatementFinderReductionProgram_run_value]
      split <;> simp_all [adaptiveStatementKnowledgeExtractorWithAcceptanceV]
      all_goals rfl

@[simp] theorem adaptiveStatementExtractorReductionProgram_run_provenancePlan
    {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (facts) :
    (adaptiveStatementExtractorReductionProgram family basis cache hcharV
      (adaptiveStatementProvenancePlan family basis cache facts)).run =
      family.adaptiveStatementKnowledgeExtractorV basis cache.toRunView hcharV
        (family.relationFinderWithCallsOfCachedRun basis cache hcharV facts).1
        (fun hnone => facts
          (family.relationFinderWithCallsOfCachedRun_none_provenance basis cache hcharV facts
            hnone)) := by
  rw [adaptiveStatementExtractorReductionProgram_run]
  unfold adaptiveStatementProvenancePlan
  split
  · rename_i verdict relation hfound hplan
    simp only [family.relationFinderWithCallsOfCachedRun_of_some basis cache hcharV facts
      relation hfound]
    rfl
  · simp_all [relationFinderWithCallsOfCachedRun]

theorem adaptiveStatementFinderReductionProgram_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (plan) :
    (adaptiveStatementFinderReductionProgram family basis cache hcharV plan).groupWork ≤
      (AdaptiveActionStatementShape pp).numProofs *
          (AdaptiveActionStatementShape pp).numInstanceColumns *
            adaptiveStatementBasisWidth pp +
        2 * assembleGroupOpsBudget (AdaptiveActionStatementShape pp) := by
  unfold adaptiveStatementFinderReductionProgram
  rw [CostedVestaComp.groupWork_bind,
    costedAdaptiveStatementCanonicalInstances_groupWork]
  cases plan.verdict with
  | found => simp
  | clear hprovenance =>
      exact Nat.add_le_add_left
        (adaptiveStatementFinderAfterProvenanceProgram_groupWork_le family basis cache hcharV
          (plan.facts hprovenance) hprovenance) _

theorem adaptiveStatementExtractorReductionProgram_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (basis) (cache) (hcharV) (plan) :
    (adaptiveStatementExtractorReductionProgram family basis cache hcharV plan).groupWork ≤
      (AdaptiveActionStatementShape pp).numProofs *
          (AdaptiveActionStatementShape pp).numInstanceColumns *
            adaptiveStatementBasisWidth pp +
        3 * assembleGroupOpsBudget (AdaptiveActionStatementShape pp) := by
  unfold adaptiveStatementExtractorReductionProgram
  have hfinder := adaptiveStatementFinderReductionProgram_groupWork_le
    family basis cache hcharV plan
  simp only [AdaptiveActionStatementShape,
    CircuitShape.withProofParams_numProofs,
    CircuitShape.withProofParams_numInstanceColumns,
    Halo2.TopLevelCircuit.shape_numInstanceColumns] at hfinder ⊢
  cases plan.verdict with
  | found =>
    rw [CostedVestaComp.groupWork_bind]
    simp
    exact hfinder.trans (by omega)
  | clear =>
    rw [CostedVestaComp.groupWork_bind]
    split
    · simp
      exact hfinder.trans (by omega)
    · rw [CostedVestaComp.groupWork_bind, costedAcceptsVCertified_groupWork,
        costedAcceptsVCertified_run]
      simp only [CostedVestaComp.groupWork_pure, Nat.add_zero]
      have haccept := deployedAssembleGroupOps_le
        (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis cache.toRunView.output.inputs)
        cache.toRunView.output.toAlgebraicWfProof.proof.1
        (chRecord (k := (AdaptiveActionStatementShape pp).k)
          cache.toRunView.pre cache.toRunView.rounds)
      simp only [AdaptiveActionStatementShape] at haccept
      exact (Nat.add_le_add hfinder haccept).trans (by omega)

/-- Conservative structural envelope for the complete relation finder.  It intentionally retains
the previously published slack for quotient and terminal proof construction; the executable
program below is proved to fit it. -/
def adaptiveStatementFinderReductionGroupWork (pp : ProofParams) : Nat :=
  let shape := AdaptiveActionStatementShape pp
  let width := adaptiveStatementBasisWidth pp
  2 * width +
    shape.numProofs * shape.numInstanceColumns * width +
    (2 * width + shape.numQuotientPieces) +
    assembleGroupOpsBudget shape +
    (4 * width + assembleGroupOpsBudget shape)

/-- Conservative structural envelope for relation finding plus witness projection. -/
def adaptiveStatementReductionGroupWork (pp : ProofParams) : Nat :=
  adaptiveStatementFinderReductionGroupWork pp +
    (4 * adaptiveStatementBasisWidth pp +
      assembleGroupOpsBudget (AdaptiveActionStatementShape pp))

theorem adaptiveStatementFinderReductionGroupWork_le (pp : ProofParams) :
    adaptiveStatementFinderReductionGroupWork pp ≤
      adaptiveStatementReductionGroupWork pp :=
  Nat.le_add_right _ _

/-- Closed shape formula for the worst-case reduction group-operation envelope. -/
theorem adaptiveStatementReductionGroupWork_eq (pp : ProofParams) :
    adaptiveStatementReductionGroupWork pp =
      let shape := AdaptiveActionStatementShape pp
      let width := adaptiveStatementBasisWidth pp
      2 * width +
        shape.numProofs * shape.numInstanceColumns * width +
        (2 * width + shape.numQuotientPieces) +
        assembleGroupOpsBudget shape +
        (4 * width + assembleGroupOpsBudget shape) +
        (4 * width + assembleGroupOpsBudget shape) := by
  rfl

/-- Internal representation of one instrumented execution.  Its constructor is private so callers
cannot attach an unrelated work object to a value. -/
private inductive AdaptiveStatementInstrumentationSeal where
  | seal

private inductive AdaptiveStatementCostedExecutionCore (pp : ProofParams) (α : Type*) where
  | mk (marker : AdaptiveStatementInstrumentationSeal)
      (reductionProgram : CostedVestaComp α) (proverGroupWork : Nat)

/-- One cached execution whose value and work are projections of the same private reduction
program. -/
abbrev AdaptiveStatementCostedExecution (pp : ProofParams) (α : Type*) :=
  AdaptiveStatementCostedExecutionCore pp α

namespace AdaptiveStatementCostedExecution

variable {pp : ProofParams} {α : Type*}

def reductionProgram : AdaptiveStatementCostedExecution pp α → CostedVestaComp α
  | .mk _ program _ => program

def value (execution : AdaptiveStatementCostedExecution pp α) : α :=
  execution.reductionProgram.run

def proverGroupWork : AdaptiveStatementCostedExecution pp α → Nat
  | .mk _ _ work => work

/-- Reduction work is the universally certified two-term programmed-basis construction plus the
work read from the concrete postprocessing program. -/
def reductionGroupWork (execution : AdaptiveStatementCostedExecution pp α) : Nat :=
  2 * adaptiveStatementBasisWidth pp + execution.reductionProgram.groupWork

/-- Complete group work of one costed execution. -/
def groupWork (execution : AdaptiveStatementCostedExecution pp α) : Nat :=
  execution.proverGroupWork + execution.reductionGroupWork

end AdaptiveStatementCostedExecution

/-- Costed complete cached relation finder at one oracle table. -/
def costedCachedRelationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
  AdaptiveStatementCostedExecution pp
      (Option (AlgebraicRelationWitness (F := Fp) basis)) :=
  let cache := family.cachedRun basis O
  let hcharV := family.cachedRun_pairCount_lt hchar basis O
  let facts := family.semanticStageFacts_of_cachedProvenance_none basis O
  let plan := adaptiveStatementProvenancePlan family basis cache facts
  let program := CostedVestaComp.map AdaptiveStatementOperationalFinderResult.value
    (adaptiveStatementFinderReductionProgram family basis cache hcharV plan)
  AdaptiveStatementCostedExecutionCore.mk AdaptiveStatementInstrumentationSeal.seal program
    (certificate.proverGroupWork basis O)

/-- Costed complete cached witness extractor at one oracle table. -/
def costedCachedKnowledgeExtractor {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    {workLimit : Nat} (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    AdaptiveStatementCostedExecution pp
      (Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs)) :=
  let cache := family.cachedRun basis O
  let hcharV := family.cachedRun_pairCount_lt hchar basis O
  let facts := family.semanticStageFacts_of_cachedProvenance_none basis O
  let plan := adaptiveStatementProvenancePlan family basis cache facts
  let hinputs : cache.output.inputs = (family.runOutput basis O).inputs :=
    congrArg AdaptiveActionStatementOutput.inputs (family.cachedRun_output_eq basis O)
  let program := CostedVestaComp.map (fun value => hinputs ▸ value)
    (adaptiveStatementExtractorReductionProgram family basis cache hcharV plan)
  AdaptiveStatementCostedExecutionCore.mk AdaptiveStatementInstrumentationSeal.seal program
    (certificate.proverGroupWork basis O)

@[simp] theorem costedCachedRelationFinder_value {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedRelationFinder hchar certificate basis O).value =
      family.cachedRelationFinder hchar basis O := by
  simp [costedCachedRelationFinder, AdaptiveStatementCostedExecution.value,
    AdaptiveStatementCostedExecution.reductionProgram, cachedRelationFinder,
    cachedRelationFinderWithCalls]

@[simp] theorem costedCachedKnowledgeExtractor_value {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).value =
      family.cachedKnowledgeExtractor hchar basis O := by
  unfold costedCachedKnowledgeExtractor AdaptiveStatementCostedExecution.value
    AdaptiveStatementCostedExecution.reductionProgram cachedKnowledgeExtractor
    cachedKnowledgeExecution
  dsimp only
  rw [CostedVestaComp.run_map,
    adaptiveStatementExtractorReductionProgram_run_provenancePlan]

@[simp] theorem costedCachedRelationFinder_reductionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedRelationFinder hchar certificate basis O).reductionProgram =
      CostedVestaComp.map AdaptiveStatementOperationalFinderResult.value
        (adaptiveStatementFinderReductionProgram family basis (family.cachedRun basis O)
          (family.cachedRun_pairCount_lt hchar basis O)
          (adaptiveStatementProvenancePlan family basis (family.cachedRun basis O)
            (family.semanticStageFacts_of_cachedProvenance_none basis O))) := rfl

@[simp] theorem costedCachedKnowledgeExtractor_reductionProgram {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).reductionProgram =
      CostedVestaComp.map (fun value =>
        congrArg AdaptiveActionStatementOutput.inputs
          (family.cachedRun_output_eq basis O) ▸ value)
        (adaptiveStatementExtractorReductionProgram family basis (family.cachedRun basis O)
          (family.cachedRun_pairCount_lt hchar basis O)
          (adaptiveStatementProvenancePlan family basis (family.cachedRun basis O)
            (family.semanticStageFacts_of_cachedProvenance_none basis O))) := rfl

theorem costedCachedRelationFinder_reductionGroupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedRelationFinder hchar certificate basis O).reductionGroupWork ≤
      adaptiveStatementFinderReductionGroupWork pp := by
  rw [AdaptiveStatementCostedExecution.reductionGroupWork,
    costedCachedRelationFinder_reductionProgram,
    CostedVestaComp.groupWork_map]
  have hprogram := adaptiveStatementFinderReductionProgram_groupWork_le family basis
    (family.cachedRun basis O) (family.cachedRun_pairCount_lt hchar basis O)
    (adaptiveStatementProvenancePlan family basis (family.cachedRun basis O)
      (family.semanticStageFacts_of_cachedProvenance_none basis O))
  simp only [adaptiveStatementFinderReductionGroupWork] at *
  omega

theorem costedCachedKnowledgeExtractor_reductionGroupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).reductionGroupWork ≤
      adaptiveStatementReductionGroupWork pp := by
  rw [AdaptiveStatementCostedExecution.reductionGroupWork,
    costedCachedKnowledgeExtractor_reductionProgram,
    CostedVestaComp.groupWork_map]
  have hprogram := adaptiveStatementExtractorReductionProgram_groupWork_le family basis
    (family.cachedRun basis O) (family.cachedRun_pairCount_lt hchar basis O)
    (adaptiveStatementProvenancePlan family basis (family.cachedRun basis O)
      (family.semanticStageFacts_of_cachedProvenance_none basis O))
  simp only [adaptiveStatementReductionGroupWork,
    adaptiveStatementFinderReductionGroupWork] at *
  omega

theorem costedCachedRelationFinder_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedRelationFinder hchar certificate basis O).groupWork ≤
      workLimit + adaptiveStatementReductionGroupWork pp := by
  unfold AdaptiveStatementCostedExecution.groupWork costedCachedRelationFinder
  exact Nat.add_le_add (certificate.proverGroupWork_le basis O)
    (family.costedCachedRelationFinder_reductionGroupWork_le hchar certificate basis O |>.trans
      (adaptiveStatementFinderReductionGroupWork_le pp))

theorem costedCachedKnowledgeExtractor_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).groupWork ≤
      workLimit + adaptiveStatementReductionGroupWork pp := by
  unfold AdaptiveStatementCostedExecution.groupWork
  exact Nat.add_le_add (certificate.proverGroupWork_le basis O)
    (family.costedCachedKnowledgeExtractor_reductionGroupWork_le hchar certificate basis O)

/-- One adversary execution plus one materialization of the canonical challenge vectors. -/
def adaptiveStatementCachedRandomOracleQueries {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) : Nat :=
  family.Q + 11 + (AdaptiveActionStatementShape pp).k

/-- The cached query number is connected to the executable read set, rather than serving only as
an argument label on the advantage function. -/
theorem relationFinderReads_card_le_cachedRandomOracleQueries {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    (family.relationFinderReads basis O).card ≤
      adaptiveStatementCachedRandomOracleQueries family := by
  simpa only [adaptiveStatementCachedRandomOracleQueries, Nat.add_assoc] using
    family.relationFinderReads_card_le basis O

/-- Cached group work is at most twice the adversary target whenever the complete structural
reduction program fits that same target. -/
theorem costedCachedKnowledgeExtractor_two_mul_bound {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit)
    (hreduction : adaptiveStatementReductionGroupWork pp ≤ workLimit) (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).groupWork ≤
      2 * workLimit := by
  refine (family.costedCachedKnowledgeExtractor_groupWork_le hchar certificate basis O).trans ?_
  omega

/-- DLOG advantage interface for the certified one-execution finder.  Unlike the legacy profile,
there are no caller-selected prover or reduction work numbers. -/
structure CertifiedAdaptiveStatementDlogProfile {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) (workLimit : Nat)
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) where
  advantage : Nat → Nat → ENNReal
  advantage_mono : ∀ {q q' g g'}, q ≤ q' → g ≤ g' →
    advantage q g ≤ advantage q' g'
  directDecodeWorkBound : ∀ basis O,
    adaptiveStatementKnowledgeExtractorDirectDecodeSlots *
      adaptiveStatementDirectDecodeOps family basis O ≤ workLimit
  finderAdvantageLE : TextbookDLWithCoinsAdvantageLE B (family.cachedRelationFinder hchar)
    (advantage (adaptiveStatementCachedRandomOracleQueries family)
      (workLimit + adaptiveStatementReductionGroupWork pp))

theorem CertifiedAdaptiveStatementDlogProfile.finderAdvantageLE_current {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {hchar} {B : VestaG}
    {workLimit : Nat} {certificate : AdaptiveStatementAdversaryCostCertificate family workLimit}
    (profile : CertifiedAdaptiveStatementDlogProfile family hchar B workLimit certificate) :
    TextbookDLWithCoinsAdvantageLE B (family.relationFinder hchar)
      (profile.advantage (adaptiveStatementCachedRandomOracleQueries family)
        (workLimit + adaptiveStatementReductionGroupWork pp)) := by
  exact family.cachedRelationFinder_fun_eq hchar ▸ profile.finderAdvantageLE

theorem CertifiedAdaptiveStatementDlogProfile.queryCoverage {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {hchar} {B : VestaG}
    {workLimit : Nat} {certificate : AdaptiveStatementAdversaryCostCertificate family workLimit}
    (_profile : CertifiedAdaptiveStatementDlogProfile family hchar B workLimit certificate)
    (basis) (O) :
    (family.relationFinderReads basis O).card ≤
      adaptiveStatementCachedRandomOracleQueries family :=
  family.relationFinderReads_card_le_cachedRandomOracleQueries basis O

theorem CertifiedAdaptiveStatementDlogProfile.extractorGroupWorkCoverage {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp} {hchar} {B : VestaG}
    {workLimit : Nat} {certificate : AdaptiveStatementAdversaryCostCertificate family workLimit}
    (_profile : CertifiedAdaptiveStatementDlogProfile family hchar B workLimit certificate)
    (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).groupWork ≤
      workLimit + adaptiveStatementReductionGroupWork pp :=
  family.costedCachedKnowledgeExtractor_groupWork_le hchar certificate basis O

end ComputedAdaptiveActionStatementFSFamily
end Zcash.Snark
