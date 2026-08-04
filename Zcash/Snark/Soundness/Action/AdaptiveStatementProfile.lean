import Zcash.Snark.Soundness.Action.AdaptiveStatementKnowledge

/-!
# Adaptive-statement finite-security profile

This module records the four-stage price for the executable adaptive-statement relation finder and
knowledge-failure theorem, records the direct-decode work premise, and transfers events across the
Orchard generator random-oracle setup.  One retained execution covers every provenance and source
comparison before the quotient, identity, and terminal stages.
-/

namespace Zcash.Snark

open Keygen
open Zcash.Circuits.Action
open scoped ENNReal

local instance adaptiveStatementProfileVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- Independently charged traversals of the four-stage combined relation finder. -/
def adaptiveStatementDlogTraversalSlots : Nat := 4

@[simp] theorem adaptiveStatementDlogTraversalSlots_eq_four :
    adaptiveStatementDlogTraversalSlots = 4 := rfl

/-- Pointwise traversal count of the short-circuiting four-stage finder. -/
def relationFinderCalls {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Nat :=
  if (family.provenanceRelationFinder basis O).isSome then 1
  else if (family.statementQuotientRelationFinder basis O).isSome then 2
  else if (family.identityRelationFinder hchar basis O).isSome then 3
  else 4

theorem relationFinderCalls_le_traversalSlots {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    family.relationFinderCalls hchar basis O ≤ adaptiveStatementDlogTraversalSlots := by
  unfold relationFinderCalls adaptiveStatementDlogTraversalSlots
  split <;> try omega
  split <;> try omega
  split <;> omega

/-- Direct-coordinate work of the actual selected-statement deployed-root decode. -/
def adaptiveStatementDirectDecodeOps {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Nat :=
  let output := family.runOutput basis O
  deployedDirectDecodeOps (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
    (family.runProof basis O).proof.1 (family.runRecord basis O)
    (output.proofData.algebraicProof.preX1AssemblySource
      (adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
        family.fixedRepresentations basis)).length

/-- Conservative random-oracle work for the combined finder, charging all four stages. -/
def adaptiveStatementDlogRandomOracleQueries {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) : Nat :=
  adaptiveStatementDlogTraversalSlots * family.Q +
    adaptiveStatementDlogTraversalSlots * (11 + (AdaptiveActionStatementShape pp).k)

/-- Knowledge extraction reruns the complete terminal once after the four-stage relation finder
returns no relation, for a total of five independently charged traversals. -/
def adaptiveStatementKnowledgeExtractorTraversalSlots : Nat := 5

/-- Random-oracle work of the executable witness extractor. -/
def adaptiveStatementKnowledgeExtractorRandomOracleQueries {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) : Nat :=
  adaptiveStatementKnowledgeExtractorTraversalSlots * family.Q +
    adaptiveStatementKnowledgeExtractorTraversalSlots *
      (11 + (AdaptiveActionStatementShape pp).k)

theorem adaptiveStatementDlogRandomOracleQueries_le_knowledgeExtractor {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    adaptiveStatementDlogRandomOracleQueries family ≤
      adaptiveStatementKnowledgeExtractorRandomOracleQueries family := by
  unfold adaptiveStatementDlogRandomOracleQueries
    adaptiveStatementKnowledgeExtractorRandomOracleQueries
    adaptiveStatementKnowledgeExtractorTraversalSlots adaptiveStatementDlogTraversalSlots
  omega

/-- Group-work envelope for the four charged traversals and one relation reduction. -/
def adaptiveStatementDlogGroupWork (proverGroupWork reductionGroupWork : Nat) : Nat :=
  4 * proverGroupWork + reductionGroupWork

/-- Group-work envelope of witness extraction's five traversals and relation post-processing. -/
def adaptiveStatementKnowledgeExtractorGroupWork
    (proverGroupWork reductionGroupWork : Nat) : Nat :=
  5 * proverGroupWork + reductionGroupWork

/-- Finite-security premise for the complete adaptive-statement relation finder.

The three resource kinds have different provenance.  Random-oracle queries are derived from the
code (`adaptiveStatementDlogRandomOracleQueries` counts the finder's traversals of the `Q`-bounded
adversary and its canonical reads), and the finder's field-operation footprint is certified per
run by `directDecodeWorkBound` on the direct profile.  `proverGroupWork` is a declared adversary
resource — the concrete-security premise playing the role of the paper model's time `t`; deriving
it needs group operations reified in the adversary type.  `reductionGroupWork` is declared but
floored: `reductionProgrammingCovered` keeps it at least the textbook-DLOG embedding's own basis
programming, one scalar multiplication per augmented slot. -/
structure AdaptiveStatementDlogProfile {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) where
  proverGroupWork : Nat
  reductionGroupWork : Nat
  reductionProgrammingCovered :
    2 ^ (AdaptiveActionStatementShape pp).k + 2 ≤ reductionGroupWork
  advantage : Nat → Nat → ENNReal
  advantage_mono : ∀ {q q' g g'}, q ≤ q' → g ≤ g' →
    advantage q g ≤ advantage q' g'
  hardness : TextbookDLWithCoinsAdvantageLE B (family.relationFinder hchar)
    (advantage (adaptiveStatementDlogRandomOracleQueries family)
      (adaptiveStatementDlogGroupWork proverGroupWork reductionGroupWork))

/-- Concrete work profile for adaptive-statement soundness and knowledge soundness. -/
structure AdaptiveStatementDirectDlogProfile {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) (T : Nat) extends AdaptiveStatementDlogProfile family hchar B where
  targetAtLeastThirtySeven : 37 ≤ T
  queryBound : family.Q ≤ T
  proverWorkBound : toAdaptiveStatementDlogProfile.proverGroupWork ≤ T
  reductionWorkBound : toAdaptiveStatementDlogProfile.reductionGroupWork ≤ T
  directDecodeWorkBound : ∀ basis O,
    2 * adaptiveStatementDirectDecodeOps family basis O ≤ T

theorem AdaptiveStatementDirectDlogProfile.solverCost_le {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder}
    {B : VestaG} {T : Nat}
    (profile : AdaptiveStatementDirectDlogProfile family hchar B T) :
    adaptiveStatementDlogRandomOracleQueries family ≤ 8 * T ∧
      adaptiveStatementDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        8 * T ∧
      ∀ basis O, 2 * adaptiveStatementDirectDecodeOps family basis O ≤ T := by
  constructor
  · unfold adaptiveStatementDlogRandomOracleQueries
    rw [adaptiveStatementDlogTraversalSlots_eq_four]
    rw [CircuitShape.withProofParams_k, actionCircuit.shape_k,
      ActionPermutationDomain.domainExponent_eq]
    have hT := profile.targetAtLeastThirtySeven
    calc
      4 * family.Q + 4 * (11 + 11) ≤ 4 * T + 4 * (11 + 11) := by
        gcongr
        exact profile.queryBound
      _ ≤ 8 * T := by omega
  constructor
  · unfold adaptiveStatementDlogGroupWork
    calc
      4 * profile.proverGroupWork + profile.reductionGroupWork ≤ 4 * T + T := by
        gcongr
        · exact profile.proverWorkBound
        · exact profile.reductionWorkBound
      _ ≤ 8 * T := by omega
  · exact profile.directDecodeWorkBound

theorem AdaptiveStatementDirectDlogProfile.knowledgeExtractorCost_le {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder}
    {B : VestaG} {T : Nat}
    (profile : AdaptiveStatementDirectDlogProfile family hchar B T) :
    adaptiveStatementKnowledgeExtractorRandomOracleQueries family ≤ 8 * T ∧
      adaptiveStatementKnowledgeExtractorGroupWork profile.proverGroupWork
          profile.reductionGroupWork ≤
        8 * T ∧
      ∀ basis O, 2 * adaptiveStatementDirectDecodeOps family basis O ≤ T := by
  constructor
  · unfold adaptiveStatementKnowledgeExtractorRandomOracleQueries
      adaptiveStatementKnowledgeExtractorTraversalSlots
    rw [CircuitShape.withProofParams_k, actionCircuit.shape_k,
      ActionPermutationDomain.domainExponent_eq]
    have hT := profile.targetAtLeastThirtySeven
    calc
      5 * family.Q + 5 * (11 + 11) ≤ 5 * T + 5 * (11 + 11) := by
        gcongr
        exact profile.queryBound
      _ ≤ 8 * T := by omega
  constructor
  · unfold adaptiveStatementKnowledgeExtractorGroupWork
    calc
      5 * profile.proverGroupWork + profile.reductionGroupWork ≤ 5 * T + T := by
        gcongr
        · exact profile.proverWorkBound
        · exact profile.reductionWorkBound
      _ ≤ 8 * T := by omega
  · exact profile.directDecodeWorkBound

/-- Transfer any adaptive-statement event across a uniform-URS basis identification. -/
theorem event_prob_eq_of_uniformURS {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    {Omega : Type*} (setup : PMF Omega) (B : VestaG)
    (basisOf : Omega → AugmentedIndex actionCircuit.n → VestaG)
    (hURS : OrchardUniformURSIdentification setup actionCircuit.domainExponent B basisOf)
    (event : Set ((AugmentedIndex actionCircuit.n → VestaG) × family.Coins)) :
    (independentProductPMF setup (PMF.uniformOfFintype family.Coins)).toOuterMeasure
      ((fun p => (basisOf p.1, p.2)) ⁻¹' event) =
    (PMF.uniformOfFintype
      ((AugmentedIndex actionCircuit.n → Fp) × family.Coins)).toOuterMeasure
      ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' event) := by
  let oraclePMF := PMF.uniformOfFintype family.Coins
  have hprod :
      (independentProductPMF setup oraclePMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex actionCircuit.n → Fp))
          oraclePMF).map (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) oraclePMF :=
        independentProductPMF_map_left setup oraclePMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype (AugmentedIndex actionCircuit.n → Fp)).map
            (scalarBasis B)) oraclePMF :=
        congrArg (fun p => independentProductPMF p oraclePMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype (AugmentedIndex actionCircuit.n → Fp))
        oraclePMF (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex actionCircuit.n → VestaG) × family.Coins) =>
      p.toOuterMeasure event) hprod
  change ((independentProductPMF setup oraclePMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure event =
    ((independentProductPMF
      (PMF.uniformOfFintype (AugmentedIndex actionCircuit.n → Fp))
      oraclePMF).map (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure event at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  calc
    _ = (independentProductPMF
        (PMF.uniformOfFintype (AugmentedIndex actionCircuit.n → Fp))
        oraclePMF).toOuterMeasure
      ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' event) := hmeasure
    _ = _ := by rw [independentProductPMF_uniform]

end ComputedAdaptiveActionStatementFSFamily
end Zcash.Snark
