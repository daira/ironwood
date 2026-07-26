import Zcash.Snark.Soundness.AGM.OnlineConstraint
import Zcash.Snark.Soundness.Composition.DeployedRootContainment

/-!
# Composite constraint bound for the rewind-free AGM path

This module carries any additional explicit relation produced while upgrading the deployed member
decode to the concrete constraint relation through the same textbook-DLOG finder.  The remaining
`x`-challenge failure is an additive event supplied by the concrete pre-`x` schedule; no multiopen
rewind or fourth-root threshold appears.
-/

namespace Zcash.Snark

open Classical
open ComputedAlgebraicFSFamily
open ComputedDeployedRootFSFamily
open scoped ENNReal

variable {shape : Shape}

/-- Extend the recursive/multiopen relation finder with the explicit relation branch produced by
the constraint adapter. -/
def deployedConstraintRelationFinder (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis)) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis coins =>
    match family.deployedRelationFinder basis coins with
    | some relation => some relation
    | none => constraintFinder basis coins

/-- The combined relation event used by the constraint capstone. -/
def deployedConstraintRelationEvent (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis)) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins) :=
  {p | (deployedConstraintRelationFinder family constraintFinder p.1 p.2).isSome}

/-- The existing deployed relation event is contained in the combined constraint finder. -/
theorem deployedRelationEvent_subset_constraintRelationEvent
    (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis)) :
    family.deployedRelationEvent <=
      deployedConstraintRelationEvent family constraintFinder := by
  rintro ⟨basis, coins⟩ hrelation
  simp only [deployedConstraintRelationEvent, Set.mem_setOf_eq,
    deployedConstraintRelationFinder]
  change (family.deployedRelationFinder basis coins).isSome at hrelation
  cases h : family.deployedRelationFinder basis coins with
  | none => simp [h] at hrelation
  | some relation => simp [h]

/-- Transfer an arbitrary explicit family relation finder across the uniform-URS basis
identification. -/
theorem deployedConstraintRelation_prob_eq_of_uniformURS {Omega : Type*} (setup : PMF Omega)
    (B : VestaG) (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis))
    (basisOf : Omega -> AugmentedIndex (2 ^ shape.k) -> VestaG)
    (hURS : OrchardUniformURSIdentification setup shape.k B basisOf) :
    (independentProductPMF setup
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹'
          deployedConstraintRelationEvent family constraintFinder) =
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) -> Fp) × family.toFamily.Coins)).toOuterMeasure
        (relSetWithCoins B (deployedConstraintRelationFinder family constraintFinder)) := by
  let coinPMF := PMF.uniformOfFintype family.toFamily.Coins
  have hprod :
      (independentProductPMF setup coinPMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF).map
            (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) coinPMF :=
        independentProductPMF_map_left setup coinPMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)).map (scalarBasis B))
          coinPMF := congrArg (fun p => independentProductPMF p coinPMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF
        (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins) =>
      p.toOuterMeasure (deployedConstraintRelationEvent family constraintFinder)) hprod
  change ((independentProductPMF setup coinPMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure
        (deployedConstraintRelationEvent family constraintFinder) =
    ((independentProductPMF
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF).map
        (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure
          (deployedConstraintRelationEvent family constraintFinder) at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  calc
    _ = (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF).toOuterMeasure
          ((fun p => (scalarBasis B p.1, p.2)) ⁻¹'
            deployedConstraintRelationEvent family constraintFinder) := hmeasure
    _ = (PMF.uniformOfFintype
          ((AugmentedIndex (2 ^ shape.k) -> Fp) × family.toFamily.Coins)).toOuterMeasure
          (relSetWithCoins B (deployedConstraintRelationFinder family constraintFinder)) := by
      rw [independentProductPMF_uniform]
      congr 1
      ext p
      simp only [Set.mem_preimage, deployedConstraintRelationEvent, Set.mem_setOf_eq,
        relSetWithCoins, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Generator-random-oracle form of the combined relation bound.  Recursive IPA, algebraic
multiopen, and constraint-binding relations are all charged to one textbook-DLOG assumption. -/
theorem deployedConstraintRelation_prob_le_of_generatorRO_textbookDL
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis))
    {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder family constraintFinder) bound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          deployedConstraintRelationEvent family constraintFinder)
      <= Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound := by
  rw [deployedConstraintRelation_prob_eq_of_uniformURS
    (orchardGeneratorROSetup query) B family constraintFinder
    (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery)]
  exact relationWithCoins_prob_le_of_textbookDL B
    (deployedConstraintRelationFinder family constraintFinder) hDL

/-- Deterministic containment needed by the final constraint capstone.  Once the root decode is
available, failure to obtain the constraint relation must either make the combined finder return
an explicit relation or hit the pre-`x` bad event. -/
def DeployedConstraintUpgradeContained (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis))
    (constraintDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Prop)
    (badX : Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins)) : Prop :=
  {p | deployedRootDecoded family p.1 p.2 ∧ ¬ constraintDecoded p.1 p.2} <=
    deployedConstraintRelationEvent family constraintFinder ∪ badX

/-- Full deterministic decomposition for the concrete constraint endpoint. -/
theorem deployedConstraintFailure_subset_union
    (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis))
    (constraintDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Prop)
    (badX : Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins))
    (hupgrade : DeployedConstraintUpgradeContained family constraintFinder
      constraintDecoded badX) :
    snarkExtractionFailureEventDeployed family.toFamily constraintDecoded <=
      deployedNonRelationFailureEvent family ∪
        (deployedConstraintRelationEvent family constraintFinder ∪
          (cleanButNotExtractedDeployed family.toFamily (deployedRootExtracted family) ∪
            badX)) := by
  rintro p ⟨haccept, hnotConstraint⟩
  by_cases hroot : deployedRootDecoded family p.1 p.2
  · rcases hupgrade ⟨hroot, hnotConstraint⟩ with hrelation | hbad
    · exact Or.inr (Or.inl hrelation)
    · exact Or.inr (Or.inr (Or.inr hbad))
  · have hdecodeFailure : p ∈
        snarkExtractionFailureEventDeployed family.toFamily (deployedRootDecoded family) :=
      ⟨haccept, hroot⟩
    rcases deployedDecodeFailure_subset_union family hdecodeFailure with
        hnonRelation | hrelation | hresidual
    · exact Or.inl hnonRelation
    · exact Or.inr (Or.inl
        (deployedRelationEvent_subset_constraintRelationEvent family constraintFinder hrelation))
    · exact Or.inr (Or.inr (Or.inl hresidual))

/-- DLOG-based composite bound for the concrete constraint endpoint.  `badXBound` is additive and
is intended to be instantiated by the pre-`x` prefix schedule. -/
theorem snarkConstraintsDeployed_prob_le_via_deployed_roots
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis))
    (constraintDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Prop)
    (badX : Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins))
    (hupgrade : DeployedConstraintUpgradeContained family constraintFinder
      constraintDecoded badX)
    {dlogBound badXBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder family constraintFinder) dlogBound)
    (hbadX : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badX) <= badXBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily constraintDecoded)
      <= ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * dlogBound)
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
        + badXBound := by
  let setup := orchardGeneratorROSetup query
  let coinPMF := PMF.uniformOfFintype family.toFamily.Coins
  let basisOf := orchardGeneratorROBasis query
  let nonRelationBound : ENNReal :=
    (family.Q + shape.k) * (3 / Fintype.card Fp) +
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp)
  let relationBound : ENNReal :=
    Fintype.card (AugmentedIndex (2 ^ shape.k)) * dlogBound
  let rootBound : ENNReal :=
    (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
  have hnonRelation := deployedNonRelationFailure_prob_le_of_generatorRO query family
  have hrelation := deployedConstraintRelation_prob_le_of_generatorRO_textbookDL
    B hB query hquery family constraintFinder hDL
  have hroots :
      (independentProductPMF setup coinPMF).toOuterMeasure
          ((fun p => (basisOf p.1, p.2)) ⁻¹'
            cleanButNotExtractedDeployed family.toFamily (deployedRootExtracted family))
        <= rootBound := by
    exact residual_le_via_wrapped_deployed_pinned_roots query family.toFamily
      (deployedRootExtracted family) (family.pinnedRoots)
      (family.pinnedRoots_budget_le) (deployedRootFailure_subset_landing family)
  calc
    (independentProductPMF setup coinPMF).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily constraintDecoded)
      <= (independentProductPMF setup coinPMF).toOuterMeasure
          ((fun p => (basisOf p.1, p.2)) ⁻¹'
            (deployedNonRelationFailureEvent family ∪
              (deployedConstraintRelationEvent family constraintFinder ∪
                (cleanButNotExtractedDeployed family.toFamily (deployedRootExtracted family) ∪
                  badX)))) := MeasureTheory.measure_mono
        (Set.preimage_mono
          (deployedConstraintFailure_subset_union family constraintFinder constraintDecoded
            badX hupgrade))
    _ = (independentProductPMF setup coinPMF).toOuterMeasure
          (((fun p => (basisOf p.1, p.2)) ⁻¹' deployedNonRelationFailureEvent family) ∪
            (((fun p => (basisOf p.1, p.2)) ⁻¹'
                deployedConstraintRelationEvent family constraintFinder) ∪
              (((fun p => (basisOf p.1, p.2)) ⁻¹'
                  cleanButNotExtractedDeployed family.toFamily (deployedRootExtracted family)) ∪
                ((fun p => (basisOf p.1, p.2)) ⁻¹' badX)))) := by
      simp only [Set.preimage_union]
    _ <= (independentProductPMF setup coinPMF).toOuterMeasure
          ((fun p => (basisOf p.1, p.2)) ⁻¹' deployedNonRelationFailureEvent family) +
        ((independentProductPMF setup coinPMF).toOuterMeasure
            ((fun p => (basisOf p.1, p.2)) ⁻¹'
              deployedConstraintRelationEvent family constraintFinder) +
          ((independentProductPMF setup coinPMF).toOuterMeasure
              ((fun p => (basisOf p.1, p.2)) ⁻¹'
                cleanButNotExtractedDeployed family.toFamily (deployedRootExtracted family)) +
            (independentProductPMF setup coinPMF).toOuterMeasure
              ((fun p => (basisOf p.1, p.2)) ⁻¹' badX))) := by
      exact (MeasureTheory.measure_union_le _ _).trans
        (add_le_add le_rfl ((MeasureTheory.measure_union_le _ _).trans
          (add_le_add le_rfl (MeasureTheory.measure_union_le _ _))))
    _ <= nonRelationBound + (relationBound + (rootBound + badXBound)) :=
      add_le_add hnonRelation (add_le_add hrelation (add_le_add hroots hbadX))
    _ = ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * dlogBound)
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
        + badXBound := by
      simp only [nonRelationBound, relationBound, rootBound]
      ac_rfl

/-- Specialization of the composite bound to the concrete online constraint outcome provider. -/
theorem snarkConstraintsDeployed_prob_le_of_online_outcome
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape)
    (provider : DeployedConstraintOutcomeProvider family)
    (badX : Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins))
    (hupgrade : DeployedConstraintUpgradeContained family
      (deployedConstraintFinderOfOutcome family provider)
      (deployedConstraintDecodedOfOutcome family provider) badX)
    {dlogBound badXBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder family
        (deployedConstraintFinderOfOutcome family provider)) dlogBound)
    (hbadX : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badX) <= badXBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily
            (deployedConstraintDecodedOfOutcome family provider))
      <= ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * dlogBound)
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
        + badXBound :=
  snarkConstraintsDeployed_prob_le_via_deployed_roots B hB query hquery family
    (deployedConstraintFinderOfOutcome family provider)
    (deployedConstraintDecodedOfOutcome family provider) badX hupgrade hDL hbadX

end Zcash.Snark
