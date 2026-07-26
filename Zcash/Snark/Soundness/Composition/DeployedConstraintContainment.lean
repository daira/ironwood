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

local instance vestaInhabitedDeployedConstraintContainment : Inhabited VestaG := ⟨0⟩

/-- Verifying-key facts that do not depend on the adversary run.  The captured Orchard fixture
discharges these once; deployed acceptance supplies the remaining per-run routing checks. -/
structure DeployedConstraintStaticChecks (family : ComputedDeployedRootFSFamily shape) : Prop where
  adviceLength : forall basis,
    shape.numAdviceQueries <= (family.vk basis).adviceQueryLayout.length
  instanceLength : forall basis,
    shape.numInstanceQueries <= (family.vk basis).instanceQueryLayout.length
  fixedLength : forall basis,
    shape.numFixedQueries <= (family.vk basis).fixedQueryLayout.length
  omegaOrder : forall basis, (family.vk basis).omega ^ (family.vk basis).n = 1
  characteristic : forall basis, (((family.vk basis).n : Nat) : Fp) ≠ 0

/-- The exact pre-`x` constraint polynomial attached to retained root-decode provenance. -/
noncomputable def deployedConstraintDifferenceOfRoot
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins)
    (root : DeployedRootDecodeWitness family basis coins) : Polynomial Fp :=
  let pnu := deployedRootRunOutput family basis coins
  committedPreXConstraintDifference
    (deployedConstraintPointPolynomial family basis pnu root.batchWitness)
    (fun i => coeffsToPoly
      (deployedConstraintPieceCoordinates family basis pnu root.batchWitness i).1)
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
    (wrappedPreIpaRecord pnu)

/-- Run the concrete online constraint adapter from a successful root decode and deployed
acceptance.  The result still preserves the explicit quotient-collision relation branch. -/
noncomputable def deployedConstraintOutcomeOfRoot
    (family : ComputedDeployedRootFSFamily shape)
    (static : DeployedConstraintStaticChecks family)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins)
    (haccept : fsWinsFull (family.adversary basis)
      (fullAlgebraicAcceptDeployed basis (family.vk basis)
        (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1)
    (root : DeployedRootDecodeWitness family basis coins)
    (hxgood : (wrappedPreIpaRecord (deployedRootRunOutput family basis coins)).x ∉
      szBadSet (deployedConstraintDifferenceOfRoot family basis coins root)) :
    let pnu := deployedRootRunOutput family basis coins
    DeployedConstraintWitness (ursOfAugmentedBasis shape.k basis) rfl
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
        (pnu.1.multiU (wrappedPreIpaReads pnu))
        (pnu.1.multiBlind (wrappedPreIpaReads pnu)) ⊕'
      AugmentedRelationWitness (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w := by
  let pnu := deployedRootRunOutput family basis coins
  have hdeployed := deployedAccepts_of_fsWinsFull family.toFamily basis coins.1 haccept
  have hdeployed' : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis coins.1)) := by
    simpa [pnu, deployedRootRunOutput, wrappedAdversary_run_fst,
      wrappedPreIpaReads_run] using hdeployed
  let checks := DeployedConstraintChecks.of_accepts_chRecord
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
    (family.instanceCommitment basis) pnu.1.proof.1 (wrappedPreIpaReads pnu)
    (runRounds family.toFamily basis coins.1) hdeployed'
  exact deployedOnlineConstraintOutcomeOfDecode family basis pnu root.batchWitness root.decoded
    root.batches_eq checks (static.adviceLength basis) (static.instanceLength basis)
    (static.fixedLength basis) (static.omegaOrder basis) (static.characteristic basis) hxgood

/-- A relation returned by the proof-producing root adapter is exactly the relation returned by
the standalone computable quotient comparison. -/
theorem deployedConstraintOutcomeOfRoot_relation_eq_online
    (family : ComputedDeployedRootFSFamily shape)
    (static : DeployedConstraintStaticChecks family)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins)
    (haccept : fsWinsFull (family.adversary basis)
      (fullAlgebraicAcceptDeployed basis (family.vk basis)
        (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1)
    (root : DeployedRootDecodeWitness family basis coins)
    (hxgood : (wrappedPreIpaRecord (deployedRootRunOutput family basis coins)).x ∉
      szBadSet (deployedConstraintDifferenceOfRoot family basis coins root))
    (relation : AugmentedRelationWitness (F := Fp)
      (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w)
    (hout : deployedConstraintOutcomeOfRoot family static basis coins haccept root hxgood =
      PSum.inr relation) :
    deployedConstraintQuotientAgreementOrRelation family basis
      (deployedRootRunOutput family basis coins) root.batchWitness = PSum.inr relation := by
  let pnu := deployedRootRunOutput family basis coins
  have hdeployed := deployedAccepts_of_fsWinsFull family.toFamily basis coins.1 haccept
  have hdeployed' : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis coins.1)) := by
    simpa [pnu, deployedRootRunOutput, wrappedAdversary_run_fst,
      wrappedPreIpaReads_run] using hdeployed
  let checks := DeployedConstraintChecks.of_accepts_chRecord
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
    (family.instanceCommitment basis) pnu.1.proof.1 (wrappedPreIpaReads pnu)
    (runRounds family.toFamily basis coins.1) hdeployed'
  apply deployedOnlineConstraintOutcome_relation_eq_online family basis pnu root.batchWitness
    root.decoded root.batches_eq checks (static.adviceLength basis) (static.instanceLength basis)
    (static.fixedLength basis) (static.omegaOrder basis) (static.characteristic basis) hxgood relation
  simpa [deployedConstraintOutcomeOfRoot, pnu, checks] using hout

/-- Provider obtained from the actual root-decode data.  A bad `x`, a non-accepting run, or a root
decode failure returns `none`; every good accepting root decode returns the concrete constraint
witness or its explicit relation coefficients. -/
noncomputable def deployedConstraintOutcomeProviderOfRoot
    (family : ComputedDeployedRootFSFamily shape)
    (static : DeployedConstraintStaticChecks family) :
    DeployedConstraintOutcomeProvider family :=
  fun basis coins =>
    if haccept : fsWinsFull (family.adversary basis)
        (fullAlgebraicAcceptDeployed basis (family.vk basis)
          (family.instanceCommitment basis))
        (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 then
      if hroot : deployedRootDecoded family basis coins then
        let root := Classical.choice hroot
        if hxgood : (wrappedPreIpaRecord
            (deployedRootRunOutput family basis coins)).x ∉
            szBadSet (deployedConstraintDifferenceOfRoot family basis coins root) then
          some (deployedConstraintOutcomeOfRoot family static basis coins haccept root hxgood)
        else none
      else none
    else none

/-- The concrete pre-`x` failure event selected by the automatic provider. -/
def deployedConstraintBadXEvent (family : ComputedDeployedRootFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins) :=
  {p | ∃ root : DeployedRootDecodeWitness family p.1 p.2,
    (wrappedPreIpaRecord (deployedRootRunOutput family p.1 p.2)).x ∈
      szBadSet (deployedConstraintDifferenceOfRoot family p.1 p.2 root)}

/-- The exact constraint-difference root set of one oracle table.  The extractor tape does not
enter: root witnesses for the same table carry the same batch data, so the union over tapes below
adds no new roots. -/
def deployedConstraintXBadSet (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) : Set Fp :=
  {x | ∃ (tape : RecursiveForkTape Fp shape.k)
      (root : DeployedRootDecodeWitness family basis (O, tape)),
    x ∈ szBadSet (deployedConstraintDifferenceOfRoot family basis (O, tape) root)}

/-- Causal condition for the constraint evaluation challenge: the exact constraint-difference
root set carries a uniform direct bound and is unchanged when the run's own `x` squeeze answer is
reprogrammed.  The set may consume the earlier `θ`/`β`/`γ`/`y` answers and the retained
representations — data fixed before the `x` squeeze — but cannot be chosen retrospectively after
seeing `x`. -/
structure DeployedConstraintXSqueezeSchedule (family : ComputedDeployedRootFSFamily shape)
    (epsilonX : ENNReal) where
  measure_le : forall basis O,
    (PMF.uniformOfFintype Fp).toOuterMeasure
      (deployedConstraintXBadSet family basis O) <= epsilonX
  pinned : forall basis
      (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (v : Fp),
    deployedConstraintXBadSet family basis
        (Function.update O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O) 4) v) =
      deployedConstraintXBadSet family basis O

/-- The single prefix-pinned event for the constraint evaluation challenge. -/
noncomputable def deployedConstraintXPinnedEvent
    (family : ComputedDeployedRootFSFamily shape) {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    PinnedRootEvent (family.adversary basis) where
  point := fun p => algebraicFullPrefixesPre family.init p 4
  bad := fun _p O => deployedConstraintXBadSet family basis O
  budget := epsilonX
  measure_le := fun _p O => schedule.measure_le basis O
  pinned := fun O v => schedule.pinned basis O v

/-- The bad-`x` event selected by the provider lands in its run's exact pinned root set. -/
theorem deployedConstraintBadX_subset_landing
    (family : ComputedDeployedRootFSFamily shape) {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    {coins : family.toFamily.Coins | (basis, coins) ∈ deployedConstraintBadXEvent family} <=
      {coins : family.toFamily.Coins |
        (deployedConstraintXPinnedEvent family schedule basis).Landing coins.1} := by
  rintro coins ⟨root, hx⟩
  change coins.1 (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run coins.1) 4) ∈
    deployedConstraintXBadSet family basis coins.1
  refine ⟨coins.2, root, ?_⟩
  simpa [deployedRootRunOutput, wrappedPreIpaRecord, chRecord,
    wrappedPreIpaReads_run, runReads, runProof] using hx

/-- The exact constraint bad-root event has the direct additive cost `(Q + 1) * epsilonX`.
There is no multiopen rewind, continuation threshold, or fourth-root loss. -/
theorem deployedConstraintBadX_prob_le
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ shape.k) -> T)
    (family : ComputedDeployedRootFSFamily shape) {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          deployedConstraintBadXEvent family)
      <= (family.Q + 1 : Nat) * epsilonX := by
  have hset : (fun p : (↥(Set.range query) -> VestaG) × family.toFamily.Coins =>
        (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        deployedConstraintBadXEvent family =
      {x : (↥(Set.range query) -> VestaG) × family.toFamily.Coins | x.2 ∈
        (fun setup => {coins : family.toFamily.Coins |
          (orchardGeneratorROBasis query setup, coins) ∈
            deployedConstraintBadXEvent family}) x.1} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [hset]
  refine independentProductPMF_fiber_bound (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.toFamily.Coins)
    (fun setup => {coins : family.toFamily.Coins |
      (orchardGeneratorROBasis query setup, coins) ∈
        deployedConstraintBadXEvent family}) ?_
  intro setup
  let basis := orchardGeneratorROBasis query setup
  refine le_trans (MeasureTheory.measure_mono
    (deployedConstraintBadX_subset_landing family schedule basis)) ?_
  refine uniformOfFintype_prod_fiber_bound
    (fun _ : RecursiveForkTape Fp shape.k =>
      {O | (deployedConstraintXPinnedEvent family schedule basis).Landing O})
    (fun _ => ?_)
  exact (deployedConstraintXPinnedEvent family schedule basis).landing_measure_le
    (family.queryBound basis)

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
  | some relation => simp

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
  {p | fsWinsFull (family.adversary p.1)
      (fullAlgebraicAcceptDeployed p.1 (family.vk p.1)
        (family.instanceCommitment p.1))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) p.2.1 ∧
    deployedRootDecoded family p.1 p.2 ∧ ¬ constraintDecoded p.1 p.2} <=
    deployedConstraintRelationEvent family constraintFinder ∪ badX

/-- The automatic root-backed provider closes the deterministic upgrade seam: on an accepting
root-decode run, it either returns the constraint witness, exposes concrete relation coefficients,
or records that the run's `x` challenge lies in the exact constraint-difference root set. -/
theorem deployedConstraintUpgradeContained_of_root
    (family : ComputedDeployedRootFSFamily shape)
    (static : DeployedConstraintStaticChecks family) :
    DeployedConstraintUpgradeContained family
      (deployedConstraintQuotientFinder family)
      (deployedConstraintDecodedOfOutcome family
        (deployedConstraintOutcomeProviderOfRoot family static))
      (deployedConstraintBadXEvent family) := by
  rintro ⟨basis, coins⟩ ⟨haccept, hroot, hnotDecoded⟩
  let root := Classical.choice hroot
  by_cases hxgood : (wrappedPreIpaRecord
      (deployedRootRunOutput family basis coins)).x ∉
      szBadSet (deployedConstraintDifferenceOfRoot family basis coins root)
  · cases hout : deployedConstraintOutcomeOfRoot family static basis coins haccept root hxgood with
    | inl witness =>
        exfalso
        apply hnotDecoded
        refine ⟨witness, ?_⟩
        simp [deployedConstraintOutcomeProviderOfRoot, haccept, hroot, root, hxgood, hout]
    | inr relation =>
        apply Or.inl
        simp only [deployedConstraintRelationEvent, Set.mem_setOf_eq,
          deployedConstraintRelationFinder]
        cases hbase : family.deployedRelationFinder basis coins with
        | some baseRelation => simp
        | none =>
            have hrelation := deployedConstraintOutcomeOfRoot_relation_eq_online family static
              basis coins haccept root hxgood relation hout
            simp [deployedConstraintQuotientFinder, root.outcome_eq, hrelation]
  · apply Or.inr
    refine ⟨root, ?_⟩
    exact Classical.not_not.mp hxgood

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
  · rcases hupgrade ⟨haccept, hroot, hnotConstraint⟩ with hrelation | hbad
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

/-- Concrete rewind-free constraint capstone.  The only computational premise is textbook
single-instance DLOG for the executable combined finder.  The online prefix schedule discharges
the exact bad-`x` event additively at `(Q + 1) * epsilonX`; it is not an `n`-DLOG assumption and
introduces no fourth-root multiopen loss. -/
theorem snarkConstraintsDeployed_prob_le_of_root_schedule
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape)
    (static : DeployedConstraintStaticChecks family)
    {epsilonX dlogBound : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX)
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder family
        (deployedConstraintQuotientFinder family)) dlogBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily
            (deployedConstraintDecodedOfOutcome family
              (deployedConstraintOutcomeProviderOfRoot family static)))
      <= ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * dlogBound)
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
        + (family.Q + 1 : Nat) * epsilonX := by
  exact snarkConstraintsDeployed_prob_le_via_deployed_roots B hB query hquery family
    (deployedConstraintQuotientFinder family)
    (deployedConstraintDecodedOfOutcome family
      (deployedConstraintOutcomeProviderOfRoot family static))
    (deployedConstraintBadXEvent family)
    (deployedConstraintUpgradeContained_of_root family static) hDL
    (deployedConstraintBadX_prob_le query family schedule)

end Zcash.Snark
