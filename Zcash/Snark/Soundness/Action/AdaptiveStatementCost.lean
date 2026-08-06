import Zcash.Snark.Soundness.AGM.CostedOracle
import Zcash.Snark.Soundness.Action.AdaptiveStatementCached
import Zcash.Snark.Soundness.Composition.AssembleGroupCost

/-!
# Certified adaptive-statement work accounting

This module replaces the two free natural-number work declarations in
`AdaptiveStatementDlogProfile` with executable accounting objects:

* `AdaptiveStatementAdversaryCostCertificate` supplies a costed oracle program, proves that its
  erasure is the original online-AGM adversary, and proves a structural path bound;
* `adaptiveStatementFinderReductionTrace` and
  `adaptiveStatementExtractorReductionTrace` enumerate every group-valued reduction phase once,
  using the one-execution cache from `AdaptiveStatementCached`.

The trace deliberately charges the full branch envelope even when a finder short-circuits.  It
includes programmed-basis evaluation, canonical instance/provenance comparisons, quotient
reconstruction, verifier assembly, group-valued branch comparisons, the identity/terminal path,
and the final witness projection.  Field operations and direct-coordinate decode work remain in
their existing separate models.  Random-oracle queries are also kept separate: one adversary run
plus the canonical `11 + k` challenge reads.
-/

namespace Zcash.Snark

open Keygen

local instance adaptiveStatementCostVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- A basis-indexed costed program whose erasure is the supplied adaptive-statement adversary. -/
structure AdaptiveStatementAdversaryCostCertificate {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (workLimit : Nat) where
  program :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      CostedLabeledOracleComp (AdaptiveActionStatementTranscript pp) Fp
        (AlgebraicTranscriptQuery (F := Fp) basis)
        (AdaptiveActionStatementOutput pp basis (family.fixedRepresentations basis))
  erase_eq : ∀ basis, (program basis).erase = family.adversary basis
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

/-- Group comparisons performed by the retained provenance pass. -/
def adaptiveStatementProvenanceComparisons (pp : ProofParams) : Nat :=
  (AdaptiveActionStatementShape pp).numProofs *
      (AdaptiveActionStatementShape pp).numInstanceColumns +
    11 + (AdaptiveActionStatementShape pp).k + 5 + 5

/-- Group-valued work trace of the complete cached relation finder.

The seven entries correspond, in order, to basis programming; canonical instance evaluation;
provenance equality checks; quotient reconstruction; the deployed acceptance MSM; group-valued
branch checks; and the identity/terminal reconstruction envelope. -/
def adaptiveStatementFinderReductionTrace (pp : ProofParams) : VestaGroupTrace :=
  let shape := AdaptiveActionStatementShape pp
  let width := adaptiveStatementBasisWidth pp
  [.scalarMultiplications width,
   .msm (shape.numProofs * shape.numInstanceColumns * width),
   .equalities (adaptiveStatementProvenanceComparisons pp),
   .msm (2 * width + shape.numQuotientPieces),
   .msm (assembleGroupOpsBudget shape),
   .equalities (queryBudget shape + 11 + shape.k),
   .msm (4 * width + assembleGroupOpsBudget shape)]

/-- The witness projection reuses the finder cache and adds one terminal reconstruction envelope. -/
def adaptiveStatementExtractorReductionTrace (pp : ProofParams) : VestaGroupTrace :=
  adaptiveStatementFinderReductionTrace pp ++
    [.msm (4 * adaptiveStatementBasisWidth pp +
      assembleGroupOpsBudget (AdaptiveActionStatementShape pp))]

/-- Structural group-work bound for the complete relation finder. -/
def adaptiveStatementFinderReductionGroupWork (pp : ProofParams) : Nat :=
  (adaptiveStatementFinderReductionTrace pp).work

/-- Structural group-work bound for relation finding plus witness projection. -/
def adaptiveStatementReductionGroupWork (pp : ProofParams) : Nat :=
  (adaptiveStatementExtractorReductionTrace pp).work

theorem adaptiveStatementFinderReductionGroupWork_le (pp : ProofParams) :
    adaptiveStatementFinderReductionGroupWork pp ≤
      adaptiveStatementReductionGroupWork pp := by
  unfold adaptiveStatementFinderReductionGroupWork adaptiveStatementReductionGroupWork
    adaptiveStatementExtractorReductionTrace
  simp

/-- Closed shape formula for the complete reduction trace. -/
theorem adaptiveStatementReductionGroupWork_eq (pp : ProofParams) :
    adaptiveStatementReductionGroupWork pp =
      let shape := AdaptiveActionStatementShape pp
      let width := adaptiveStatementBasisWidth pp
      width +
        shape.numProofs * shape.numInstanceColumns * width +
        adaptiveStatementProvenanceComparisons pp +
        (2 * width + shape.numQuotientPieces) +
        assembleGroupOpsBudget shape +
        (queryBudget shape + 11 + shape.k) +
        (4 * width + assembleGroupOpsBudget shape) +
        (4 * width + assembleGroupOpsBudget shape) := by
  simp [adaptiveStatementReductionGroupWork, adaptiveStatementExtractorReductionTrace,
    adaptiveStatementFinderReductionTrace, VestaGroupTrace.work]
  omega

/-- One cached execution's result and its two independently inspectable group-work components. -/
structure AdaptiveStatementCostedExecution (α : Type*) where
  value : α
  proverGroupWork : Nat
  reductionTrace : VestaGroupTrace

namespace AdaptiveStatementCostedExecution

variable {α : Type*}

/-- Reduction work is derived from the trace, not supplied as a profile number. -/
def reductionGroupWork (execution : AdaptiveStatementCostedExecution α) : Nat :=
  execution.reductionTrace.work

/-- Complete group work of one costed execution. -/
def groupWork (execution : AdaptiveStatementCostedExecution α) : Nat :=
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
    AdaptiveStatementCostedExecution
      (Option (AlgebraicRelationWitness (F := Fp) basis)) :=
  { value := family.cachedRelationFinder hchar basis O
    proverGroupWork := certificate.proverGroupWork basis O
    reductionTrace := adaptiveStatementFinderReductionTrace pp }

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
    AdaptiveStatementCostedExecution
      (Option (ActionTerminal.ActionBundleWitness (family.runOutput basis O).inputs)) :=
  { value := family.cachedKnowledgeExtractor hchar basis O
    proverGroupWork := certificate.proverGroupWork basis O
    reductionTrace := adaptiveStatementExtractorReductionTrace pp }

@[simp] theorem costedCachedRelationFinder_reductionGroupWork {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedRelationFinder hchar certificate basis O).reductionGroupWork =
      adaptiveStatementFinderReductionGroupWork pp := rfl

@[simp] theorem costedCachedKnowledgeExtractor_reductionGroupWork {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).reductionGroupWork =
      adaptiveStatementReductionGroupWork pp := rfl

theorem costedCachedRelationFinder_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedRelationFinder hchar certificate basis O).groupWork ≤
      workLimit + adaptiveStatementReductionGroupWork pp := by
  unfold AdaptiveStatementCostedExecution.groupWork costedCachedRelationFinder
  exact Nat.add_le_add (certificate.proverGroupWork_le basis O)
    (adaptiveStatementFinderReductionGroupWork_le pp)

theorem costedCachedKnowledgeExtractor_groupWork_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) (hchar) {workLimit : Nat}
    (certificate : AdaptiveStatementAdversaryCostCertificate family workLimit) (basis) (O) :
    (family.costedCachedKnowledgeExtractor hchar certificate basis O).groupWork ≤
      workLimit + adaptiveStatementReductionGroupWork pp := by
  unfold AdaptiveStatementCostedExecution.groupWork costedCachedKnowledgeExtractor
  exact Nat.add_le_add_right (certificate.proverGroupWork_le basis O) _

/-- One adversary execution plus one materialization of the canonical challenge vectors. -/
def adaptiveStatementCachedRandomOracleQueries {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) : Nat :=
  family.Q + 11 + (AdaptiveActionStatementShape pp).k

/-- Cached group work is at most twice the adversary target whenever the complete structural
reduction trace fits that same target. -/
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

end ComputedAdaptiveActionStatementFSFamily
end Zcash.Snark
