import Zcash.Snark.Soundness.Action.AdaptiveStatementKnowledge

/-!
# Adaptive-statement finite-security profile

This module records the conservative eight-traversal price for the adaptive-statement relation
finder and knowledge-failure theorem, records the direct-decode work premise, and transfers events
across the Orchard generator random-oracle setup.  The implementation does not retain one global
adversary execution across the complete eight-stage finder.
-/

namespace Zcash.Snark

open Keygen
open Zcash.Circuits.Action
open scoped ENNReal

local instance adaptiveStatementProfileVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- Independently charged traversals of the eight-stage combined relation finder. -/
def adaptiveStatementDlogTraversalSlots : Nat := 8

@[simp] theorem adaptiveStatementDlogTraversalSlots_eq_eight :
    adaptiveStatementDlogTraversalSlots = 8 := rfl

/-- Pointwise traversal count of the short-circuiting eight-stage finder. -/
noncomputable def relationFinderCalls {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Nat :=
  if (family.instanceRepresentationRelationFinder basis O).isSome then 1
  else if (family.preIpaRepresentationRelationFinder basis O).isSome then 2
  else if (family.ipaRepresentationRelationFinder basis O).isSome then 3
  else if (family.semanticRepresentationRelationFinder basis O).isSome then 4
  else if (family.semanticSourceMismatchRelationFinder basis O).isSome then 5
  else if (family.statementQuotientRelationFinder basis O).isSome then 6
  else if (family.identityRelationFinder hchar basis O).isSome then 7
  else 8

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
  split <;> try omega
  split <;> try omega
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

/-- Conservative random-oracle work for the combined finder, charging all eight stages. -/
def adaptiveStatementDlogRandomOracleQueries {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) : Nat :=
  adaptiveStatementDlogTraversalSlots * family.Q +
    adaptiveStatementDlogTraversalSlots * (11 + (AdaptiveActionStatementShape pp).k)

/-- The knowledge-failure profile uses the same conservative relation-finder query charge. -/
def adaptiveStatementKnowledgeExtractorRandomOracleQueries {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) : Nat :=
  adaptiveStatementDlogRandomOracleQueries family

@[simp] theorem adaptiveStatementKnowledgeExtractorRandomOracleQueries_eq {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    adaptiveStatementKnowledgeExtractorRandomOracleQueries family =
      adaptiveStatementDlogRandomOracleQueries family := rfl

/-- Group-work envelope for the eight charged traversals and one relation reduction. -/
def adaptiveStatementDlogGroupWork (proverGroupWork reductionGroupWork : Nat) : Nat :=
  8 * proverGroupWork + reductionGroupWork

/-- Finite-security premise for the complete adaptive-statement relation finder. -/
structure AdaptiveStatementDlogProfile {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) where
  proverGroupWork : Nat
  reductionGroupWork : Nat
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
  targetAtLeastTwentyTwo : 22 ≤ T
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
    adaptiveStatementDlogRandomOracleQueries family ≤ 16 * T ∧
      adaptiveStatementDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        16 * T ∧
      ∀ basis O, 2 * adaptiveStatementDirectDecodeOps family basis O ≤ T := by
  constructor
  · unfold adaptiveStatementDlogRandomOracleQueries
    rw [adaptiveStatementDlogTraversalSlots_eq_eight]
    rw [CircuitShape.withProofParams_k, ActionPermutationDomain.domainExponent_eq]
    have hT := profile.targetAtLeastTwentyTwo
    calc
      8 * family.Q + 8 * (11 + 11) ≤ 8 * T + 8 * (11 + 11) := by
        gcongr
        exact profile.queryBound
      _ ≤ 16 * T := by omega
  constructor
  · unfold adaptiveStatementDlogGroupWork
    calc
      8 * profile.proverGroupWork + profile.reductionGroupWork ≤ 8 * T + T := by
        gcongr
        · exact profile.proverWorkBound
        · exact profile.reductionWorkBound
      _ ≤ 16 * T := by omega
  · exact profile.directDecodeWorkBound

theorem AdaptiveStatementDirectDlogProfile.knowledgeExtractorCost_le {pp : ProofParams}
    {family : ComputedAdaptiveActionStatementFSFamily pp}
    {hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder}
    {B : VestaG} {T : Nat}
    (profile : AdaptiveStatementDirectDlogProfile family hchar B T) :
    adaptiveStatementKnowledgeExtractorRandomOracleQueries family ≤ 16 * T ∧
      adaptiveStatementDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        16 * T ∧
      ∀ basis O, 2 * adaptiveStatementDirectDecodeOps family basis O ≤ T := by
  simpa only [adaptiveStatementKnowledgeExtractorRandomOracleQueries_eq] using
    profile.solverCost_le

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
