import Zcash.Snark.Capstones.ActionBudgets

/-!
# Exact Action soundness and knowledge-soundness capstones

Captured checks and executable terminals yield ordinary- and knowledge-soundness bounds against
an adaptive online-AGM prover, for every consensus-valid Action bundle size. Each is censused
directly in `Fixtures/MultiAction/Honest/TrustBoundary.lean`.
-/

namespace Zcash.Snark.Capstone

-- The captured facts these endpoints are stated at.
open Zcash.Snark.Fixture

open Zcash.Snark CompPoly.CPolynomial
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Keygen (actionProofParams actionProofParamsFor
  actionCircuitShape_eq_fixtureCircuitShape actionShapeFor_eq_fixtureShape
  actionShape_eq_fixtureShape vk_eq_toVerifierKey)
open Zcash.Circuits Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder URS)
open scoped ENNReal

/-! ## Exact false-Action-statement endpoints -/

/-- Compositional adaptive Action soundness formula with one finder and five semantic surfaces. -/
theorem orchard_action_adaptive_soundness_error_bound
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionCircuit.shape.withProofParams actionProofParams))
    (inputs : Fin actionProofParams.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDlogProfile actionProofParams family inputs hvk hI hchar B) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams actionProofParams) family.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
      ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        adaptiveActionAcceptFalseStatementEvent actionProofParams family inputs) ≤
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (actionCircuit.domainExponent *
          ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) +
        ((family.Q + 1 : Nat) *
          algebraicRootBudget (actionCircuit.shape.withProofParams actionProofParams)
            actionCircuit.domainExponent +
        ((profile.advantage (adaptiveActionDlogOracleQueryCost actionProofParams family)
              (adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * ∑ n : Fin 5,
            ((![2 ^ 25, 2 ^ 35, 2 ^ 21, 2 ^ 23, 20470] n : Nat) : ENNReal) /
              Fintype.card Fp))) := by
  let epsilon : Fin 5 → ENNReal := fun n =>
    ((![2 ^ 25, 2 ^ 35, 2 ^ 21, 2 ^ 23, 20470] n : Nat) : ENNReal) /
      Fintype.card Fp
  have hsurface : ∀
      (basis : AugmentedIndex
        actionCircuit.n → VestaG)
      (n : Fin 5)
      (ps : ProofString (actionCircuit.shape.withProofParams actionProofParams) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt actionProofParams basis inputs n ps source earlier) ≤
        epsilon n := by
    intro basis n ps _hwf source earlier
    fin_cases n
    · refine le_trans
        (adaptiveActionThetaSurface_probability_bound actionProofParams basis inputs ps source earlier) ?_
      dsimp only [epsilon]
      gcongr
      exact_mod_cast capturedActionThetaBudget basis
        (adaptiveActionCommitmentPolynomial actionProofParams basis inputs ps source
          (chRecord (fun _ => 0) (fun _ => 0)))
    · have h := adaptiveActionBetaSurface_probability_bound
        actionProofParams basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      rw [ENNReal.div_add_div_same]
      gcongr
      exact_mod_cast capturedActionBetaBudget basis
        (adaptiveActionCommitmentPolynomial actionProofParams basis inputs ps source
          (chRecord (fun i => if h : (i : Nat) < 1 then earlier ⟨i, h⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionGammaSurface_probability_bound
        actionProofParams basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      rw [ENNReal.div_add_div_same]
      gcongr
      exact_mod_cast capturedActionGammaBudget basis
        (adaptiveActionCommitmentPolynomial actionProofParams basis inputs ps source
          (chRecord (fun i => if h : (i : Nat) < 2 then earlier ⟨i, h⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionYSurface_probability_bound
        actionProofParams basis inputs ps source earlier derived_n_ne_zero
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      gcongr
      exact_mod_cast capturedActionYBudget
        (capturedActionConstraintCount_bound basis inputs ps source
          (chRecord (fun i => if h : (i : Nat) < 3 then earlier ⟨i, h⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionXSurface_probability_bound
        actionProofParams basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      gcongr
      simpa only [Zcash.Snark.Keygen.actionProofParamsFor_one] using
        (adaptiveActionXDegree_bound 1 basis inputs ps source
          (chRecord (fun i => if h : (i : Nat) < 4 then earlier ⟨i, h⟩ else 0)
            (fun _ => 0)))
  have hevent := adaptiveActionEvent_prob_eq_of_uniformURS actionProofParams family
    (orchardGeneratorROSetup query) B (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO
      actionCircuit.domainExponent B hB query hquery)
    (adaptiveActionAcceptFalseStatementEvent actionProofParams family inputs)
  calc
    _ = _ := hevent
    _ ≤ _ := by
      simpa only [epsilon] using
        (adaptiveActionAcceptFalseStatement_probability_bound actionProofParams family inputs hvk hI hchar
          B epsilon profile hsurface)

/-- Compositional adaptive Action soundness formula for arbitrary bundle size. -/
theorem orchard_action_adaptive_bundle_soundness_error_bound
    (numProofs : ℕ) {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex
      actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDlogProfile (actionProofParamsFor numProofs)
      family inputs hvk hI hchar B) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            family.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
      ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        adaptiveActionAcceptFalseStatementEvent
          (actionProofParamsFor numProofs) family inputs) ≤
      (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (actionCircuit.domainExponent *
          ((family.Q + 1 : ℕ) * (2 / (Fintype.card Fp : ENNReal))) +
        ((family.Q + 1 : ℕ) *
          algebraicRootBudget
            (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            actionCircuit.domainExponent +
        ((profile.advantage
              (adaptiveActionDlogOracleQueryCost (actionProofParamsFor numProofs) family)
              (adaptiveActionDlogGroupWork
                profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * ∑ i : Fin 5,
            ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
                numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) /
              Fintype.card Fp))) := by
  let epsilon : Fin 5 → ENNReal := fun i =>
    ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
        numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp
  have hsurface : ∀
      (basis : AugmentedIndex
        actionCircuit.n → VestaG)
      (i : Fin 5)
      (ps : ProofString
        (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (i : ℕ) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt (actionProofParamsFor numProofs)
            basis inputs i ps source earlier) ≤ epsilon i := by
    intro basis i ps _hwf source earlier
    fin_cases i
    · refine le_trans
        (adaptiveActionThetaSurface_probability_bound (actionProofParamsFor numProofs)
          basis inputs ps source earlier) ?_
      dsimp only [epsilon]
      gcongr
      exact_mod_cast actionThetaBudget numProofs basis
        (adaptiveActionCommitmentPolynomial (actionProofParamsFor numProofs)
          basis inputs ps source (chRecord (fun _ => 0) (fun _ => 0)))
    · have h := adaptiveActionBetaSurface_probability_bound
        (actionProofParamsFor numProofs) basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      rw [ENNReal.div_add_div_same]
      gcongr
      exact_mod_cast actionBetaBudget numProofs basis
        (adaptiveActionCommitmentPolynomial (actionProofParamsFor numProofs)
          basis inputs ps source
          (chRecord (fun j => if hj : (j : ℕ) < 1 then earlier ⟨j, hj⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionGammaSurface_probability_bound
        (actionProofParamsFor numProofs) basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      rw [ENNReal.div_add_div_same]
      gcongr
      exact_mod_cast actionGammaBudget numProofs basis
        (adaptiveActionCommitmentPolynomial (actionProofParamsFor numProofs)
          basis inputs ps source
          (chRecord (fun j => if hj : (j : ℕ) < 2 then earlier ⟨j, hj⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionYSurface_probability_bound
        (actionProofParamsFor numProofs) basis inputs ps source earlier
        derived_n_ne_zero
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      gcongr
      exact_mod_cast actionYBudget numProofs
        (actionConstraintCount_bound numProofs basis inputs ps source
          (chRecord (fun j => if hj : (j : ℕ) < 3 then earlier ⟨j, hj⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionXSurface_probability_bound
        (actionProofParamsFor numProofs) basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      gcongr
      exact_mod_cast adaptiveActionXDegree_bound numProofs basis inputs ps source
        (chRecord (fun j => if hj : (j : ℕ) < 4 then earlier ⟨j, hj⟩ else 0)
          (fun _ => 0))
  have hevent := adaptiveActionEvent_prob_eq_of_uniformURS
    (actionProofParamsFor numProofs) family
    (orchardGeneratorROSetup query) B (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO
      actionCircuit.domainExponent B hB query hquery)
    (adaptiveActionAcceptFalseStatementEvent (actionProofParamsFor numProofs) family inputs)
  calc
    _ = _ := hevent
    _ ≤ _ := by
      simpa only [epsilon] using
        (adaptiveActionAcceptFalseStatement_probability_bound (actionProofParamsFor numProofs)
          family inputs hvk hI hchar B epsilon profile hsurface)

/-- Probability bound for each of the five adaptive Action surfaces at arbitrary `numProofs`,
shared by ordinary and knowledge soundness. -/
theorem adaptiveActionSurface_probability_bound
    (numProofs : ℕ)
    (basis : AugmentedIndex
      (2 ^ actionCircuit.domainExponent) → VestaG)
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (i : Fin 5)
    (ps : ProofString
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
    (_hwf : PsWellFormed ps)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (i : ℕ) → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAt (actionProofParamsFor numProofs)
          basis inputs i ps source earlier) ≤
      ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
          numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp := by
  fin_cases i
  · refine le_trans
      (adaptiveActionThetaSurface_probability_bound (actionProofParamsFor numProofs)
        basis inputs ps source earlier) ?_
    gcongr
    exact_mod_cast actionThetaBudget numProofs basis
      (adaptiveActionCommitmentPolynomial (actionProofParamsFor numProofs)
        basis inputs ps source (chRecord (fun _ => 0) (fun _ => 0)))
  · have h := adaptiveActionBetaSurface_probability_bound
      (actionProofParamsFor numProofs) basis inputs ps source earlier
    dsimp only at h
    refine le_trans h ?_
    rw [ENNReal.div_add_div_same]
    gcongr
    exact_mod_cast actionBetaBudget numProofs basis
      (adaptiveActionCommitmentPolynomial (actionProofParamsFor numProofs)
        basis inputs ps source
        (chRecord (fun j => if hj : (j : ℕ) < 1 then earlier ⟨j, hj⟩ else 0)
          (fun _ => 0)))
  · have h := adaptiveActionGammaSurface_probability_bound
      (actionProofParamsFor numProofs) basis inputs ps source earlier
    dsimp only at h
    refine le_trans h ?_
    rw [ENNReal.div_add_div_same]
    gcongr
    exact_mod_cast actionGammaBudget numProofs basis
      (adaptiveActionCommitmentPolynomial (actionProofParamsFor numProofs)
        basis inputs ps source
        (chRecord (fun j => if hj : (j : ℕ) < 2 then earlier ⟨j, hj⟩ else 0)
          (fun _ => 0)))
  · have h := adaptiveActionYSurface_probability_bound
      (actionProofParamsFor numProofs) basis inputs ps source earlier
      derived_n_ne_zero
    dsimp only at h
    refine le_trans h ?_
    gcongr
    exact_mod_cast actionYBudget numProofs
      (actionConstraintCount_bound numProofs basis inputs ps source
        (chRecord (fun j => if hj : (j : ℕ) < 3 then earlier ⟨j, hj⟩ else 0)
          (fun _ => 0)))
  · have h := adaptiveActionXSurface_probability_bound
      (actionProofParamsFor numProofs) basis inputs ps source earlier
    dsimp only at h
    refine le_trans h ?_
    gcongr
    exact_mod_cast adaptiveActionXDegree_bound numProofs basis inputs ps source
      (chRecord (fun j => if hj : (j : ℕ) < 4 then earlier ⟨j, hj⟩ else 0)
        (fun _ => 0))

/-- Compositional adaptive Action knowledge bound for executable private-witness extraction. -/
theorem orchard_action_adaptive_bundle_knowledge_error_bound
    (numProofs : ℕ) {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex
      (2 ^ actionCircuit.domainExponent) → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDlogProfile (actionProofParamsFor numProofs)
      family inputs hvk hI hchar B) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            family.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
      ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        adaptiveActionKnowledgeFailureEvent
          (actionProofParamsFor numProofs) family inputs hvk hI hchar) ≤
      (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (actionCircuit.domainExponent *
          ((family.Q + 1 : ℕ) * (2 / (Fintype.card Fp : ENNReal))) +
        ((family.Q + 1 : ℕ) *
          algebraicRootBudget
            (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            actionCircuit.domainExponent +
        ((profile.advantage
              (adaptiveActionDlogOracleQueryCost (actionProofParamsFor numProofs) family)
              (adaptiveActionDlogGroupWork
                profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * ∑ i : Fin 5,
            ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
                numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) /
              Fintype.card Fp))) := by
  let epsilon : Fin 5 → ENNReal := fun i =>
    ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
        numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp
  have hsurface : ∀
      (basis : AugmentedIndex
        (2 ^ actionCircuit.domainExponent) → VestaG)
      (i : Fin 5)
      (ps : ProofString
        (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (i : ℕ) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt (actionProofParamsFor numProofs)
            basis inputs i ps source earlier) ≤ epsilon i := by
    intro basis i ps hwf source earlier
    exact adaptiveActionSurface_probability_bound
      numProofs basis inputs i ps hwf source earlier
  have hevent := adaptiveActionEvent_prob_eq_of_uniformURS
    (actionProofParamsFor numProofs) family
    (orchardGeneratorROSetup query) B (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO
      actionCircuit.domainExponent B hB query hquery)
    (adaptiveActionKnowledgeFailureEvent
      (actionProofParamsFor numProofs) family inputs hvk hI hchar)
  calc
    _ = _ := hevent
    _ ≤ _ := by
      simpa only [epsilon] using
        (adaptiveActionKnowledgeFailure_probability_bound (actionProofParamsFor numProofs)
          family inputs hvk hI hchar B epsilon profile
          hsurface)

/-- Resource-accounted adaptive Action capstone at `Q ≤ 2^123`, with finder work at `2^127`,
decoder work at `2^123`, and statistical error at `2^-84`. -/
theorem orchard_action_adaptive_soundness_finite_security
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionCircuit.shape.withProofParams actionProofParams))
    (inputs : Fin actionProofParams.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDirectDlogProfile actionProofParams family inputs hvk hI hchar B
      (2 ^ 123)) :
    ((independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams actionProofParams) family.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          adaptiveActionAcceptFalseStatementEvent actionProofParams family inputs) ≤
      profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 84 : ENNReal)) ∧
      adaptiveActionDlogOracleQueryCost actionProofParams family ≤ 2 ^ 127 ∧
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 127 ∧
      ∀ basis O, 2 * adaptiveActionDirectDecodeOps actionProofParams family basis O ≤
        2 ^ 123 := by
  have hcost := profile.solverCost_le
  have hqueries : adaptiveActionDlogOracleQueryCost actionProofParams family ≤
      2 ^ 127 := by
    calc
      adaptiveActionDlogOracleQueryCost actionProofParams family ≤ 16 * 2 ^ 123 :=
        hcost.1
      _ = 2 ^ 127 := by norm_num
  have hgroup :
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 127 := by
    calc
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
          16 * 2 ^ 123 := hcost.2.1
      _ = 2 ^ 127 := by norm_num
  refine ⟨?_, hqueries, hgroup, hcost.2.2⟩
  refine le_trans
    (orchard_action_adaptive_soundness_error_bound B hB query hquery family inputs
      hvk hI hchar profile.toAdaptiveActionDlogProfile) ?_
  rw [adaptiveActionSemanticSum_eq]
  calc
    _ =
        profile.advantage (adaptiveActionDlogOracleQueryCost actionProofParams family)
            (adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          adaptiveActionStatisticalModel family.Q := by
      unfold adaptiveActionStatisticalModel
      ring
    _ ≤ profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 84 : ENNReal) :=
      add_le_add (profile.advantage_mono hqueries hgroup)
        (le_trans (adaptiveActionStatisticalModel_le_action family.Q)
          (actionStatisticalModel_at_2pow123 profile.queryBound))

/-- Resource-accounted adaptive bundle capstone with `2^127` DLOG work and `2^-83` statistical
error. -/
theorem orchard_action_adaptive_bundle_soundness_finite_security
    (numProofs : ℕ) (hn : numProofs ≤ orchardConsensusMaxProofs)
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex
      actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDirectDlogProfile (actionProofParamsFor numProofs)
      family inputs hvk hI hchar B (2 ^ 123)) :
    ((independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            family.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          adaptiveActionAcceptFalseStatementEvent
            (actionProofParamsFor numProofs) family inputs) ≤
      profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 83 : ENNReal)) ∧
      adaptiveActionDlogOracleQueryCost (actionProofParamsFor numProofs) family ≤
        2 ^ 127 ∧
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 127 ∧
      (∀ basis O,
        2 * adaptiveActionDirectDecodeOps
          (actionProofParamsFor numProofs) family basis O ≤ 2 ^ 123) ∧
      ∀ (actual : PMF
          ((↥(Set.range query) → VestaG) ×
            (BTranscript Fp VestaG
              (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
                family.init.length 10 +
                3 * actionCircuit.domainExponent) → Fp)))
        (εBias : ENNReal),
        PMFEventBiasLE actual
          (independentProductPMF (orchardGeneratorROSetup query)
            (PMF.uniformOfFintype
              (BTranscript Fp VestaG
                (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
                  family.init.length 10 +
                  3 * actionCircuit.domainExponent) → Fp)))
          εBias →
        actual.toOuterMeasure
            ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
              adaptiveActionAcceptFalseStatementEvent
                (actionProofParamsFor numProofs) family inputs) ≤
          (profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 83 : ENNReal)) + εBias := by
  have hcost := profile.solverCost_le
  have hqueries :
      adaptiveActionDlogOracleQueryCost (actionProofParamsFor numProofs) family ≤
        2 ^ 127 := by
    calc
      adaptiveActionDlogOracleQueryCost (actionProofParamsFor numProofs) family ≤
          16 * 2 ^ 123 := hcost.1
      _ = 2 ^ 127 := by norm_num
  have hgroup :
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 127 := by
    calc
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
          16 * 2 ^ 123 := hcost.2.1
      _ = 2 ^ 127 := by norm_num
  have hprob :
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype
          (BTranscript Fp VestaG
            (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
              family.init.length 10 +
              3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            adaptiveActionAcceptFalseStatementEvent
              (actionProofParamsFor numProofs) family inputs) ≤
        profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 83 : ENNReal) := by
    refine le_trans
      (orchard_action_adaptive_bundle_soundness_error_bound numProofs B hB query hquery
        family inputs hvk hI hchar profile.toAdaptiveActionDlogProfile) ?_
    refine le_trans ?_
      (add_le_add (profile.advantage_mono hqueries hgroup)
        (actionStatisticalModelFor_at_2pow123 hn profile.queryBound))
    refine le_trans ?_ (add_le_add le_rfl
      (adaptiveActionStatisticalModelFor_le_action numProofs family.Q))
    have hsum :
        (∑ i : Fin 5,
          ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
              numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp) =
          (((numProofs * 992851621 + 20470 : ℕ) : ENNReal) /
            Fintype.card Fp) := by
      norm_num [Fin.sum_univ_succ]
      simp only [div_eq_mul_inv]
      ring
    rw [hsum]
    unfold adaptiveActionStatisticalModelFor actionSemanticModelFor
    dsimp only
    push_cast
    simp only [div_eq_mul_inv]
    ring_nf
    exact le_rfl
  refine ⟨hprob, hqueries, hgroup, hcost.2.2, ?_⟩
  intro actual εBias hbias
  exact event_measure_le_of_bias hbias _ hprob

/-- Consensus-generic knowledge capstone: extractor failure is bounded by one profiled Vesta-DLOG
advantage plus `2^-83`.  This is the concrete resource-accounted finite-security capstone for
knowledge soundness. -/
theorem orchard_action_adaptive_bundle_knowledge_soundness_finite_security
    (numProofs : ℕ) (hn : numProofs ≤ orchardConsensusMaxProofs)
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex
      (2 ^ actionCircuit.domainExponent) → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDirectDlogProfile (actionProofParamsFor numProofs)
      family inputs hvk hI hchar B (2 ^ 123)) :
    ((independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            family.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          adaptiveActionKnowledgeFailureEvent
            (actionProofParamsFor numProofs) family inputs hvk hI hchar) ≤
      profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 83 : ENNReal)) ∧
      adaptiveActionKnowledgeExtractorOracleQueryCost
          (actionProofParamsFor numProofs) family ≤ 2 ^ 127 ∧
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 127 ∧
      (∀ basis O,
        2 * adaptiveActionDirectDecodeOps
          (actionProofParamsFor numProofs) family basis O ≤ 2 ^ 123) ∧
      ∀ (actual : PMF
          ((↥(Set.range query) → VestaG) ×
            (BTranscript Fp VestaG
              (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
                family.init.length 10 +
                3 * actionCircuit.domainExponent) → Fp)))
        (εBias : ENNReal),
        PMFEventBiasLE actual
          (independentProductPMF (orchardGeneratorROSetup query)
            (PMF.uniformOfFintype
              (BTranscript Fp VestaG
                (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
                  family.init.length 10 +
                  3 * actionCircuit.domainExponent) → Fp)))
          εBias →
        actual.toOuterMeasure
            ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
              adaptiveActionKnowledgeFailureEvent
                (actionProofParamsFor numProofs) family inputs hvk hI hchar) ≤
          (profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 83 : ENNReal)) + εBias := by
  have hcost := profile.knowledgeExtractorCost_le
  have hqueries :
      adaptiveActionKnowledgeExtractorOracleQueryCost
          (actionProofParamsFor numProofs) family ≤ 2 ^ 127 := by
    calc
      adaptiveActionKnowledgeExtractorOracleQueryCost
          (actionProofParamsFor numProofs) family ≤ 16 * 2 ^ 123 := hcost.1
      _ = 2 ^ 127 := by norm_num
  have hqueriesDlog :
      adaptiveActionDlogOracleQueryCost (actionProofParamsFor numProofs) family ≤
        2 ^ 127 := by
    simpa only [adaptiveActionKnowledgeExtractorOracleQueryCost_eq] using hqueries
  have hgroup :
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 127 := by
    calc
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
          16 * 2 ^ 123 := hcost.2.1
      _ = 2 ^ 127 := by norm_num
  have hprob :
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype
          (BTranscript Fp VestaG
            (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
              family.init.length 10 +
              3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            adaptiveActionKnowledgeFailureEvent
              (actionProofParamsFor numProofs) family inputs hvk hI hchar) ≤
        profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 83 : ENNReal) := by
    refine le_trans
      (orchard_action_adaptive_bundle_knowledge_error_bound numProofs B hB query hquery
        family inputs hvk hI hchar profile.toAdaptiveActionDlogProfile) ?_
    refine le_trans ?_
      (add_le_add (profile.advantage_mono hqueriesDlog hgroup)
        (actionStatisticalModelFor_at_2pow123 hn profile.queryBound))
    refine le_trans ?_ (add_le_add le_rfl
      (adaptiveActionStatisticalModelFor_le_action numProofs family.Q))
    have hsum :
        (∑ i : Fin 5,
          ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
              numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp) =
          (((numProofs * 992851621 + 20470 : ℕ) : ENNReal) /
            Fintype.card Fp) := by
      norm_num [Fin.sum_univ_succ]
      simp only [div_eq_mul_inv]
      ring
    rw [hsum]
    unfold adaptiveActionStatisticalModelFor actionSemanticModelFor
    dsimp only
    push_cast
    simp only [div_eq_mul_inv]
    ring_nf
    exact le_rfl
  refine ⟨hprob, hqueries, hgroup, hcost.2.2, ?_⟩
  intro actual εBias hbias
  exact event_measure_le_of_bias hbias _ hprob

end Zcash.Snark.Capstone
