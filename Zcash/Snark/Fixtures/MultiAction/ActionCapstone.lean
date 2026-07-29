import Zcash.Snark.Fixtures.SingleAction.StaticChecks
import Zcash.Snark.Soundness.Composition.ScheduleBudget
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity
import Zcash.Snark.Keygen.Certificate
import Zcash.Circuits.Integration.StraightLineActionEvent
import Zcash.Circuits.Integration.StraightLineActionBudgets
import Zcash.Circuits.Integration.AdaptiveActionEvent

/-!
# The captured exact Action soundness capstone

Issue #128's assembly: the captured static checks and `x`-squeeze schedule rebuilt at the
circuit-derived shape, the retained statement-or-relation intermediate, and the exact accepting
false-Action-statement endpoint closed by the combined computed relation finder.

Everything here lives at `actionProofParams.mergeDerived actionCircuit` — the derived one-proof
shape the Action semantics are stated at — with no shape casts in any statement: the derived
verifying key's scalar fields never read the URS, so the single-Action captured facts transfer
through nine field equalities.

## The adversary model

The public endpoint quantifies over `SequentialOnlineAGMProver`, a bounded sequential online-AGM
Fiat–Shamir adversary in the random-oracle model, against Vesta DLOG, together with its phased
Action execution.  The prover's stopped computations generate the deployed-root, IPA, and
constraint-`x` traces.  The Action phases emit typed snapshots before the five semantic squeezes;
their cuts and views are generated projections, never caller-supplied trace/cut objects.
The four semantic budgets are discharged inside the sequential endpoint from decided counting
caps; the hash-function boundary of the compressed model is unchanged.  The exact endpoint uses
the literal `accept ∧ ¬BundleStatement` event and one DLOG profile for all computed relation
branches.
-/

namespace Zcash.Snark.Fixture

open Zcash.Snark
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Keygen (actionProofParams shape_eq_mergeDerived vk_eq_toVerifierKey)
open Zcash.Circuits Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder URS)
open scoped ENNReal

/-! ## The statement-or-relation intermediate and exact target -/

/-- **The existing statement-or-relation failure event** (issue #128 F1): the deployed verifier
accepts and the terminal produces neither the Orchard Action bundle statement nor a nontrivial
relation.  This is an intermediate event, strictly narrower than false Action-statement
acceptance until the terminal relation branch is exposed as a computed DLOG break. -/
noncomputable def actionNoStatementOrRelationEvent
    (family : ComputedStraightLineDeployedFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs →
      PublicInputs Fp) :
    Set ((AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
          + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp)) :=
  family.straightLineConstraintSemanticFailureEvent
    (actionStatementOrRelationDecoded actionProofParams family inputs)

/-- **The exact public Action-soundness event.**  The deployed verifier accepts while the Orchard
Action bundle statement at its supplied public inputs is false.  The final #128 capstone must
bound this set, rather than only `actionNoStatementOrRelationEvent`. -/
def actionAcceptFalseStatementEvent
    (family : ComputedStraightLineDeployedFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs →
      PublicInputs Fp) :
    Set ((AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
          + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp)) :=
  family.straightLineConstraintSemanticFailureEvent
    (actionBundleStatementDecoded actionProofParams family inputs)

/-! ## The derived key's captured scalars -/

/-- Field projections commute with the shape cast when the field's type does not mention the
shape. -/
private theorem castVk_field {s₁ s₂ : Shape} (h : s₁ = s₂)
    (K : VerifyingKey s₁ Fp VestaG) :
    K.omega = (h ▸ K : VerifyingKey s₂ Fp VestaG).omega ∧
    K.n = (h ▸ K : VerifyingKey s₂ Fp VestaG).n ∧
    K.gates = (h ▸ K : VerifyingKey s₂ Fp VestaG).gates ∧
    K.instanceQueryLayout = (h ▸ K : VerifyingKey s₂ Fp VestaG).instanceQueryLayout ∧
    K.adviceQueryLayout = (h ▸ K : VerifyingKey s₂ Fp VestaG).adviceQueryLayout ∧
    K.fixedQueryLayout = (h ▸ K : VerifyingKey s₂ Fp VestaG).fixedQueryLayout ∧
    K.permutationChunks = (h ▸ K : VerifyingKey s₂ Fp VestaG).permutationChunks := by
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Lookup-expression projections commute with the shape cast, up to the index cast. -/
private theorem castVk_lookup {s₁ s₂ : Shape} (h : s₁ = s₂)
    (K : VerifyingKey s₁ Fp VestaG) (l : Fin s₁.numLookups) :
    K.lookupInputExprs l =
      (h ▸ K : VerifyingKey s₂ Fp VestaG).lookupInputExprs
        (Fin.cast (congrArg Shape.numLookups h) l) ∧
    K.lookupTableExprs l =
      (h ▸ K : VerifyingKey s₂ Fp VestaG).lookupTableExprs
        (Fin.cast (congrArg Shape.numLookups h) l) := by
  cases h
  exact ⟨rfl, rfl⟩

/-- **The derived Action key carries the captured scalar data at every URS.**  The scalar fields
never read the URS, and at the captured URS the keygen certificate pins them to the capture. -/
theorem derived_scalars (urs : URS VestaG) :
    (actionCircuit.toVerifierKey actionProofParams urs).omega = vk.omega ∧
    (actionCircuit.toVerifierKey actionProofParams urs).n = vk.n ∧
    (actionCircuit.toVerifierKey actionProofParams urs).gates = vk.gates ∧
    (actionCircuit.toVerifierKey actionProofParams urs).instanceQueryLayout =
      vk.instanceQueryLayout ∧
    (actionCircuit.toVerifierKey actionProofParams urs).adviceQueryLayout =
      vk.adviceQueryLayout ∧
    (actionCircuit.toVerifierKey actionProofParams urs).fixedQueryLayout =
      vk.fixedQueryLayout ∧
    (actionCircuit.toVerifierKey actionProofParams urs).permutationChunks =
      vk.permutationChunks := by
  have hcast := castVk_field shape_eq_mergeDerived
    (actionCircuit.toVerifierKey actionProofParams capturedURS)
  have hvk : (shape_eq_mergeDerived ▸
      actionCircuit.toVerifierKey actionProofParams capturedURS :
      VerifyingKey shape Fp VestaG) = vk := vk_eq_toVerifierKey.symm
  exact ⟨hcast.1.trans (congrArg VerifyingKey.omega hvk),
    hcast.2.1.trans (congrArg VerifyingKey.n hvk),
    hcast.2.2.1.trans (congrArg VerifyingKey.gates hvk),
    hcast.2.2.2.1.trans (congrArg VerifyingKey.instanceQueryLayout hvk),
    hcast.2.2.2.2.1.trans (congrArg VerifyingKey.adviceQueryLayout hvk),
    hcast.2.2.2.2.2.1.trans (congrArg VerifyingKey.fixedQueryLayout hvk),
    hcast.2.2.2.2.2.2.trans (congrArg VerifyingKey.permutationChunks hvk)⟩

/-- The derived key's lookup expressions are the captured ones, up to the index cast. -/
theorem derived_lookups (urs : URS VestaG)
    (l : Fin (actionProofParams.mergeDerived actionCircuit).numLookups) :
    (actionCircuit.toVerifierKey actionProofParams urs).lookupInputExprs l =
      vk.lookupInputExprs
        (Fin.cast (congrArg Shape.numLookups shape_eq_mergeDerived) l) ∧
    (actionCircuit.toVerifierKey actionProofParams urs).lookupTableExprs l =
      vk.lookupTableExprs
        (Fin.cast (congrArg Shape.numLookups shape_eq_mergeDerived) l) := by
  have hcast := castVk_lookup shape_eq_mergeDerived
    (actionCircuit.toVerifierKey actionProofParams capturedURS) l
  have hvk : (shape_eq_mergeDerived ▸
      actionCircuit.toVerifierKey actionProofParams capturedURS :
      VerifyingKey shape Fp VestaG) = vk := vk_eq_toVerifierKey.symm
  constructor
  · exact hcast.1.trans (by rw [hvk])
  · exact hcast.2.trans (by rw [hvk])

/-! ## The captured checks and schedule at the derived shape -/

/-- The derived shape's count fields are the captured ones. -/
private theorem md_counts :
    (actionProofParams.mergeDerived actionCircuit).k = shape.k ∧
    (actionProofParams.mergeDerived actionCircuit).numAdviceQueries =
      shape.numAdviceQueries ∧
    (actionProofParams.mergeDerived actionCircuit).numInstanceQueries =
      shape.numInstanceQueries ∧
    (actionProofParams.mergeDerived actionCircuit).numFixedQueries =
      shape.numFixedQueries ∧
    (actionProofParams.mergeDerived actionCircuit).numQuotientPieces =
      shape.numQuotientPieces :=
  ⟨congrArg Shape.k shape_eq_mergeDerived,
    congrArg Shape.numAdviceQueries shape_eq_mergeDerived,
    congrArg Shape.numInstanceQueries shape_eq_mergeDerived,
    congrArg Shape.numFixedQueries shape_eq_mergeDerived,
    congrArg Shape.numQuotientPieces shape_eq_mergeDerived⟩

/-- **The captured static checks at the derived key** (issue #128 F3): the five decided facts,
transferred through the derived key's scalar equalities. -/
theorem staticChecks_of_derived
    (family : ComputedStraightLineDeployedFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis)) :
    DeployedConstraintStaticChecks family.toRootFamily where
  adviceLength := fun basis => by
    rw [hvk basis, (derived_scalars _).2.2.2.2.1, md_counts.2.1]
    exact vk_advice_layout_length
  instanceLength := fun basis => by
    rw [hvk basis, (derived_scalars _).2.2.2.1, md_counts.2.2.1]
    exact vk_instance_layout_length
  fixedLength := fun basis => by
    rw [hvk basis, (derived_scalars _).2.2.2.2.2.1, md_counts.2.2.2.1]
    exact vk_fixed_layout_length
  omegaOrder := fun basis => by
    rw [hvk basis, (derived_scalars _).1, (derived_scalars _).2.1]
    exact vk_omega_order
  characteristic := fun basis => by
    rw [hvk basis, (derived_scalars _).2.1]
    exact vk_n_cast_ne_zero

/-- **The captured `x`-squeeze schedule at the derived key** (issue #128 F3): the degree caps
transfer through the scalar equalities, and pinning is the family's own derived projection. -/
noncomputable def schedule_of_derived
    (family : ComputedStraightLineDeployedFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis)) :
    DeployedConstraintXSqueezeSchedule family.toRootFamily
      ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞)) := by
  have hk : 2 ^ (actionProofParams.mergeDerived actionCircuit).k - 1 = 2047 := by
    rw [md_counts.1]
    norm_num [shape]
  have h := deployedConstraintXSqueezeSchedule_of_pinned family.toRootFamily
    (B := 2047) (W := 7) (Dc := 8188) (D := 20470) (Dq := 20470)
    (by norm_num) (le_of_eq hk)
    (fun basis => by rw [hvk basis, (derived_scalars _).2.1]; exact vk_n_pred_le)
    (fun basis => by rw [hvk basis, (derived_scalars _).2.2.1]; exact vk_gates_degree_le)
    (fun basis => by
      rw [hvk basis, (derived_scalars _).2.2.2.2.2.2]; exact vk_chunk_width_le)
    (fun basis l => by
      rw [hvk basis, (derived_lookups _ l).1]
      exact vk_lookup_input_degree_le _)
    (fun basis l => by
      rw [hvk basis, (derived_lookups _ l).2]
      exact vk_lookup_table_degree_le _)
    (fun basis => by
      rw [hvk basis, (derived_scalars _).2.1, md_counts.2.2.2.2, ← hk, md_counts.1]
      exact vk_quotient_tail_le)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    family.constraintXTrace.toPinning
  simpa using h

/-! ## The composed bound -/

/-- **The captured statement-or-relation failure bound, composed** (issue #128 F4/F5): the
probability that acceptance yields neither the Action statement nor a relation is at most the
compressed straight-line knowledge error at the derived key plus the four semantic challenge
budgets.  The terminal data — batch openings, member decodes, acceptance, and the canonical
quotient — all come from the same straight-line decoded run, via the fusion this bound
instantiates.

The four budgets remain premises here; the remaining #128 pricing work discharges them
concretely. -/
theorem orchard_action_noStatementOrRelation_prob_le_captured
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → T)
    (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (profile : family.StraightLineConstraintDlogProfile B)
    {xyBound betaBound gammaBound thetaBound : ENNReal}
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionXYFailureEvent actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionBetaFailureEvent actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionGammaFailureEvent actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionThetaFailureEvent actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionNoStatementOrRelationEvent family inputs)
      ≤ ((family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) *
            ((actionProofParams.mergeDerived actionCircuit).k *
              (2 / (Fintype.card Fp : ENNReal))) +
          (family.Q + (11 + (actionProofParams.mergeDerived actionCircuit).k) + 1 : ℕ) *
            algebraicRootBudget (actionProofParams.mergeDerived actionCircuit)
              (actionProofParams.mergeDerived actionCircuit).k +
          (profile.advantage family.straightLineDlogRandomOracleQueries
              (ComputedStraightLineDeployedFSFamily.straightLineDlogGroupWork
                profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞))) +
        (xyBound + (betaBound + (gammaBound + thetaBound))) :=
  actionNoStatementOrRelation_prob_le_of_compressed_bound actionProofParams family
    (staticChecks_of_derived family hvk) inputs hvk hI hchar query
    (family.straightLineConstraintFailure_prob_le_of_generatorRO_dlogProfile B hB query hquery
      (staticChecks_of_derived family hvk) (schedule_of_derived family hvk) profile)
    hXY hBeta hGamma hTheta

/-! ## The sequential endpoint: every semantic budget discharged and counted

The counting caps below are decided at the captured key and transferred through the derived
key's field equalities, so the endpoint takes a bundle of cuts and views — the sequential
adversary — and nothing else numeric.  The caps are generous round powers of two: each sits
orders of magnitude under the field size, and the final margin analysis only needs
`(Q + 1) · Σcaps / |Fp|` small at `Q ≤ 2^123`.
-/

private theorem castVk_blinding {s₁ s₂ : Shape} (h : s₁ = s₂)
    (K : VerifyingKey s₁ Fp VestaG) :
    K.blindingFactors = (h ▸ K : VerifyingKey s₂ Fp VestaG).blindingFactors := by
  cases h
  rfl

/-- The derived key's blinding count is the captured one at every URS. -/
theorem derived_blinding (urs : URS VestaG) :
    (actionCircuit.toVerifierKey actionProofParams urs).blindingFactors =
      vk.blindingFactors := by
  have hcast := castVk_blinding shape_eq_mergeDerived
    (actionCircuit.toVerifierKey actionProofParams capturedURS)
  have hvk : (shape_eq_mergeDerived ▸
      actionCircuit.toVerifierKey actionProofParams capturedURS :
      VerifyingKey shape Fp VestaG) = vk := vk_eq_toVerifierKey.symm
  exact hcast.trans (congrArg VerifyingKey.blindingFactors hvk)

private theorem actionLookupActivationCount_le :
    (operationEnabledLookups actionCircuit.operations 0).length ≤ 2 ^ 12 := by
  native_decide

private theorem actionLookupInputArity_le :
    ∀ i : Fin (operationEnabledLookups actionCircuit.operations 0).length,
      ((operationEnabledLookups actionCircuit.operations 0).get i).argument.inputs.length ≤ 4 := by
  native_decide

private theorem resolverPermutationCell_card_le
    (pp : Keygen.ProofParams) (urs : URS VestaG)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin (pp.mergeDerived actionCircuit).numProofs) :
    Fintype.card
        (ResolverPermutationCell (actionCircuit.toVerifierKey pp urs) poly p actionActiveRows) ≤
      2 ^ 16 := by
  rw [resolverPermutationCell_card]
  calc
    ∑ c : Fin (pp.mergeDerived actionCircuit).numPermutationSets,
          actionActiveRows *
            ((actionCircuit.toVerifierKey pp urs).permutationChunks.getD c []).length
        ≤ ∑ _c : Fin (pp.mergeDerived actionCircuit).numPermutationSets,
            actionActiveRows * 7 := by
          apply Finset.sum_le_sum
          intro c _hc
          gcongr
          simpa only [actionChunkLen_eq] using
            ActionPermutationDomain.chunkLength_le pp urs c c.isLt
    _ = (pp.mergeDerived actionCircuit).numPermutationSets * (actionActiveRows * 7) := by
          simp
    _ = 3 * (actionActiveRows * 7) := by
          rw [actionNumPermutationSets_eq]
    _ ≤ 2 ^ 16 := by
          have hrows := actionActiveRows_le_domainSize
          rw [actionDomainSize, ActionPermutationDomain.domainExponent_eq] at hrows
          norm_num at hrows ⊢
          omega

private theorem cap_theta :
    ∀ (basis : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG)
      (poly : CommitmentId → Polynomial Fp),
      TopLevelLookupCoherence.topLevelLookupThetaBudget actionCircuit actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) poly ≤
        2 ^ 25 := by
  intro basis poly
  rw [TopLevelLookupCoherence.topLevelLookupThetaBudget_eq]
  calc
    ∑ index : TopLevelLookupCoherence.TopLevelLookupActivationIndex
          actionCircuit actionProofParams,
        actionCircuit.usableRowsAt actionCircuit.domainExponent *
          ((operationEnabledLookups actionCircuit.operations 0).get
            index.2).argument.inputs.length
      ≤ ∑ _index : TopLevelLookupCoherence.TopLevelLookupActivationIndex
          actionCircuit actionProofParams, 2 ^ 11 * 4 := by
        gcongr with index
        · change actionActiveRows ≤ 2 ^ 11
          have hrows := actionActiveRows_le_domainSize
          rw [actionDomainSize, ActionPermutationDomain.domainExponent_eq] at hrows
          norm_num at hrows ⊢
          exact hrows
        · exact actionLookupInputArity_le index.2
    _ ≤ 2 ^ 25 := by
        simp only [TopLevelLookupCoherence.TopLevelLookupActivationIndex,
          Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        have hscaled :
            (operationEnabledLookups actionCircuit.operations 0).length *
                (2 ^ 11 * 4) ≤ 2 ^ 25 := by
          calc
            (operationEnabledLookups actionCircuit.operations 0).length * (2 ^ 11 * 4)
                ≤ 2 ^ 12 * (2 ^ 11 * 4) :=
              Nat.mul_le_mul_right _ actionLookupActivationCount_le
            _ = 2 ^ 25 := by norm_num
        simpa only [Keygen.ProofParams.mergeDerived, actionProofParams,
          one_mul, Nat.cast_id] using hscaled

private theorem cap_beta :
    ∀ (basis : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG)
      (poly : CommitmentId → Polynomial Fp),
      (∑ p : Fin (actionProofParams.mergeDerived actionCircuit).numProofs,
        (Fintype.card (ResolverPermutationCell (vkAt actionProofParams basis) poly p
            actionActiveRows) + 1) *
          Fintype.card (ResolverPermutationCell (vkAt actionProofParams basis) poly p
            actionActiveRows)) +
      (actionProofParams.mergeDerived actionCircuit).numProofs *
        (actionProofParams.mergeDerived actionCircuit).numLookups *
        (((vkAt actionProofParams basis).n - (vkAt actionProofParams basis).blindingFactors -
              2 + 2) *
            ((vkAt actionProofParams basis).n - (vkAt actionProofParams basis).blindingFactors -
              2 + 1) +
          ((vkAt actionProofParams basis).n - (vkAt actionProofParams basis).blindingFactors -
            2 + 1)) ≤ 2 ^ 35 := by
  intro basis poly
  let urs := ursOfAugmentedBasis
    (actionProofParams.mergeDerived actionCircuit).k basis
  have hcell : ∀ p : Fin (actionProofParams.mergeDerived actionCircuit).numProofs,
      Fintype.card (ResolverPermutationCell (vkAt actionProofParams basis) poly p
        actionActiveRows) ≤ 2 ^ 16 := by
    intro p
    exact resolverPermutationCell_card_le actionProofParams urs poly p
  have hn : (vkAt actionProofParams basis).n = 2 ^ 11 := by
    change (actionCircuit.toVerifierKey actionProofParams urs).n = 2 ^ 11
    rw [← actionDomainSize_eq actionProofParams urs, actionDomainSize,
      ActionPermutationDomain.domainExponent_eq]
  have hu : (vkAt actionProofParams basis).n -
      (vkAt actionProofParams basis).blindingFactors - 2 ≤ 2 ^ 11 := by
    omega
  calc
    (∑ p : Fin (actionProofParams.mergeDerived actionCircuit).numProofs,
        (Fintype.card (ResolverPermutationCell (vkAt actionProofParams basis) poly p
            actionActiveRows) + 1) *
          Fintype.card (ResolverPermutationCell (vkAt actionProofParams basis) poly p
            actionActiveRows)) +
        (actionProofParams.mergeDerived actionCircuit).numProofs *
          (actionProofParams.mergeDerived actionCircuit).numLookups *
          (((vkAt actionProofParams basis).n -
                (vkAt actionProofParams basis).blindingFactors - 2 + 2) *
              ((vkAt actionProofParams basis).n -
                (vkAt actionProofParams basis).blindingFactors - 2 + 1) +
            ((vkAt actionProofParams basis).n -
              (vkAt actionProofParams basis).blindingFactors - 2 + 1))
        ≤
      (∑ _p : Fin (actionProofParams.mergeDerived actionCircuit).numProofs,
          (2 ^ 16 + 1) * 2 ^ 16) +
      (actionProofParams.mergeDerived actionCircuit).numProofs *
          (actionProofParams.mergeDerived actionCircuit).numLookups *
          ((2 ^ 11 + 2) * (2 ^ 11 + 1) + (2 ^ 11 + 1)) := by
      gcongr with p
      all_goals exact hcell p
    _ ≤ 2 ^ 35 := by
      rw [shape_eq_mergeDerived]
      norm_num [shape]

private theorem cap_gamma :
    ∀ (basis : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG)
      (poly : CommitmentId → Polynomial Fp),
      (∑ p : Fin (actionProofParams.mergeDerived actionCircuit).numProofs,
        2 * Fintype.card (ResolverPermutationCell (vkAt actionProofParams basis) poly p
          actionActiveRows)) +
      (actionProofParams.mergeDerived actionCircuit).numProofs *
        (actionProofParams.mergeDerived actionCircuit).numLookups *
        (2 * ((vkAt actionProofParams basis).n - (vkAt actionProofParams basis).blindingFactors -
          2 + 1)) ≤ 2 ^ 21 := by
  intro basis poly
  let urs := ursOfAugmentedBasis
    (actionProofParams.mergeDerived actionCircuit).k basis
  have hcell : ∀ p : Fin (actionProofParams.mergeDerived actionCircuit).numProofs,
      Fintype.card (ResolverPermutationCell (vkAt actionProofParams basis) poly p
        actionActiveRows) ≤ 2 ^ 16 := by
    intro p
    exact resolverPermutationCell_card_le actionProofParams urs poly p
  have hn : (vkAt actionProofParams basis).n = 2 ^ 11 := by
    change (actionCircuit.toVerifierKey actionProofParams urs).n = 2 ^ 11
    rw [← actionDomainSize_eq actionProofParams urs, actionDomainSize,
      ActionPermutationDomain.domainExponent_eq]
  have hu : (vkAt actionProofParams basis).n -
      (vkAt actionProofParams basis).blindingFactors - 2 ≤ 2 ^ 11 := by
    omega
  calc
    (∑ p : Fin (actionProofParams.mergeDerived actionCircuit).numProofs,
        2 * Fintype.card (ResolverPermutationCell (vkAt actionProofParams basis) poly p
          actionActiveRows)) +
        (actionProofParams.mergeDerived actionCircuit).numProofs *
          (actionProofParams.mergeDerived actionCircuit).numLookups *
          (2 * ((vkAt actionProofParams basis).n -
            (vkAt actionProofParams basis).blindingFactors - 2 + 1))
        ≤
      (∑ _p : Fin (actionProofParams.mergeDerived actionCircuit).numProofs,
          2 * 2 ^ 16) +
      (actionProofParams.mergeDerived actionCircuit).numProofs *
          (actionProofParams.mergeDerived actionCircuit).numLookups *
          (2 * (2 ^ 11 + 1)) := by
      gcongr with p
      all_goals exact hcell p
    _ ≤ 2 ^ 21 := by
      rw [shape_eq_mergeDerived]
      norm_num [shape]

private theorem derived_n_ne_zero :
    ∀ basis : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG,
      (vkAt actionProofParams basis).n ≠ 0 := by
  intro basis
  let urs := ursOfAugmentedBasis
    (actionProofParams.mergeDerived actionCircuit).k basis
  change (actionCircuit.toVerifierKey actionProofParams urs).n ≠ 0
  rw [← actionDomainSize_eq actionProofParams urs, actionDomainSize,
    ActionPermutationDomain.domainExponent_eq]
  norm_num

private theorem derived_n_yn {L : ℕ} (hL : L ≤ 2 ^ 12) :
    ∀ basis : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG,
      (vkAt actionProofParams basis).n * L ≤ 2 ^ 23 := by
  intro basis
  let urs := ursOfAugmentedBasis
    (actionProofParams.mergeDerived actionCircuit).k basis
  have hn : (vkAt actionProofParams basis).n = 2 ^ 11 := by
    change (actionCircuit.toVerifierKey actionProofParams urs).n = 2 ^ 11
    rw [← actionDomainSize_eq actionProofParams urs, actionDomainSize,
      ActionPermutationDomain.domainExponent_eq]
  rw [hn]
  calc 2 ^ 11 * L ≤ 2 ^ 11 * 2 ^ 12 := Nat.mul_le_mul_left _ hL
    _ = 2 ^ 23 := by norm_num

/-- The adaptive Action model has the same captured, shape-determined constraint count for every
prover polynomial assignment. -/
private theorem adaptive_action_constraint_count_le
    (basis : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (actionProofParams.mergeDerived actionCircuit) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionProofParams.mergeDerived actionCircuit).k Fp) :
    (adaptiveActionCommittedModel actionProofParams basis inputs ps source ch).constraints.length
      ≤ 2 ^ 12 := by
  unfold adaptiveActionCommittedModel adaptiveActionCommittedModelOf
    canonicalConstraintModelOfPermutationResolver
    constraintModelOfPermutationResolver constraintModelOfResolver
    ConstraintPolyModel.constraints ConstraintPolyModel.subProofConstraints
    ConstraintPolyModel.gateConstraints ConstraintPolyModel.permutationConstraints
    ConstraintPolyModel.lookupConstraints
  simp only [List.length_flatten, permutationExpressions, lookupExpressions,
    permutationChunksOfResolver_length, lookupEntriesOfResolver]
  rw [(derived_scalars _).2.2.1, (derived_scalars _).2.2.2.2.2.2]
  have hproofs := congrArg Shape.numProofs shape_eq_mergeDerived
  have hsets := congrArg Shape.numPermutationSets shape_eq_mergeDerived
  have hlookups := congrArg Shape.numLookups shape_eq_mergeDerived
  norm_num [shape] at hproofs hsets hlookups
  simp [hproofs, hsets, hlookups, permutationSetsOfResolver,
    permutationChunksOfResolver]
  have hm : min vk.permutationChunks.length
      (min 3 (vkAt actionProofParams basis).permutationChunks.length) ≤
      vk.permutationChunks.length := Nat.min_le_left _ _
  have hc : vk.gates.length + (vk.permutationChunks.length + 19) ≤ 2 ^ 12 := by
    native_decide
  omega

/-- The adaptive pre-`x` polynomial is assembled from coordinate vectors of degree below the
captured basis size, so the existing captured degree walk applies without a trace premise. -/
private theorem adaptive_action_x_degree_le
    (basis : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (actionProofParams.mergeDerived actionCircuit) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionProofParams.mergeDerived actionCircuit).k Fp) :
    (adaptiveActionPreXDifference actionProofParams basis inputs ps source ch).natDegree ≤
      20470 := by
  let avk := ActionTerminal.vkAt actionProofParams basis
  let ic := actionCircuit.instanceCommitment actionProofParams
    (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs
  let poly := adaptiveActionCommitmentPolynomial actionProofParams basis inputs ps source ch
  have hk : 2 ^ (actionProofParams.mergeDerived actionCircuit).k - 1 = 2047 := by
    rw [md_counts.1]
    norm_num [shape]
  have hpoint : ∀ g, (onlinePointPolynomial source g).natDegree ≤ 2047 := by
    intro g
    unfold onlinePointPolynomial
    have h := coeffsToPoly_natDegree_lt
      (n := 2 ^ (actionProofParams.mergeDerived actionCircuit).k) (by positivity)
      (onlinePointCoordinates source g).1
    omega
  have hpoly : ∀ id, (poly id).natDegree ≤ 2047 := by
    intro id
    unfold poly adaptiveActionCommitmentPolynomial
      adaptiveActionCommitmentPolynomialOf adaptiveActionPointPolynomial
    split
    · split
      · exact hpoint _
      · rw [ComputablePolynomial.zero_eq]
        simp
    · rw [ComputablePolynomial.zero_eq]
      simp
  have hresolver : ∀ {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
      (column : ℕ → Polynomial Fp),
      (∀ i, (column i).natDegree ≤ 2047) →
      ∀ i, (resolverQueryFeed (n := n) omega layout column i).natDegree ≤ 2047 := by
    intro n omega layout column hcolumn i
    unfold resolverQueryFeed
    split
    · exact natDegree_comp_rotateData_le _ _ (hcolumn _)
    · rw [ComputablePolynomial.zero_eq]
      simp
  have hfixed : ∀ i, (fixedQueryFeedOfResolver avk poly i).natDegree ≤ 2047 :=
    hresolver avk.omega avk.fixedQueryLayout _ (fun _ => hpoly _)
  have hadvice : ∀ p i, (adviceQueryFeedOfResolver avk poly p i).natDegree ≤ 2047 :=
    fun p => hresolver avk.omega avk.adviceQueryLayout _ (fun _ => hpoly _)
  have hinstance : ∀ p i, (instanceQueryFeedOfResolver avk poly p i).natDegree ≤ 2047 :=
    fun p => hresolver avk.omega avk.instanceQueryLayout _ (fun _ => hpoly _)
  have hpermutationColumn : ∀ p cr,
      (permutationColumnPolynomialOfResolver avk poly p cr).natDegree ≤ 2047 := by
    intro p cr
    rcases cr with i | i | i <;>
      simp only [permutationColumnPolynomialOfResolver, ColumnRef.resolve] <;>
      unfold finFn <;> split
    all_goals
      first
      | exact hpoly _
      | change ComputablePolynomial.zero.natDegree ≤ 2047
        rw [ComputablePolynomial.zero_eq]
        simp
  have hnB : avk.n - 1 ≤ 2047 := by
    dsimp only [avk]
    rw [(derived_scalars _).2.1]
    exact vk_n_pred_le
  have hrows : Function.Injective fun i : Fin avk.n => avk.omega ^ (i : ℕ) := by
    exact ActionPermutationDomain.rowsInjective actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis)
  have hblinding : avk.blindingFactors < avk.n :=
    ActionPermutationDomain.blindingFactors_lt actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis)
  have hn : 0 < avk.n := Nat.zero_lt_of_lt hblinding
  have hlookups : ∀ p, ∀ lk ∈ lookupEntriesOfResolver avk poly p,
      (lk.1.productEval.natDegree ≤ 2047 ∧ lk.1.productNextEval.natDegree ≤ 2047 ∧
        lk.1.permutedInputEval.natDegree ≤ 2047 ∧
        lk.1.permutedInputInvEval.natDegree ≤ 2047 ∧
        lk.1.permutedTableEval.natDegree ≤ 2047) ∧
      (∀ e ∈ lk.2.1, e.degreeBound * 2047 ≤ 8188) ∧
      ∀ e ∈ lk.2.2, e.degreeBound * 2047 ≤ 8188 := by
    intro p lk hlk
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hlk
    refine ⟨⟨hpoly _, natDegree_comp_rotateData_le _ _ (hpoly _), hpoly _,
      natDegree_comp_rotateData_le _ _ (hpoly _), hpoly _⟩, ?_, ?_⟩
    · dsimp only [avk]
      rw [(derived_lookups _ l).1]
      exact vk_lookup_input_degree_le _
    · dsimp only [avk]
      rw [(derived_lookups _ l).2]
      exact vk_lookup_table_degree_le _
  have hmodel :
      adaptiveActionCommittedModel actionProofParams basis inputs ps source ch =
        canonicalConstraintModelOfPermutationResolver avk ch poly hblinding := by
    rfl
  rw [adaptiveActionPreXDifference_eq]
  rw [hmodel]
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · apply natDegree_combineConstraints_le (B := 2047) (W := 7)
      (Dc := 8188) (D := 20470)
    · norm_num
    · simpa [canonicalConstraintModelOfPermutationResolver,
        constraintModelOfPermutationResolver, constraintModelOfResolver] using hfixed
    · simpa [canonicalConstraintModelOfPermutationResolver,
        constraintModelOfPermutationResolver, constraintModelOfResolver] using hadvice
    · simpa [canonicalConstraintModelOfPermutationResolver,
        constraintModelOfPermutationResolver, constraintModelOfResolver] using hinstance
    · simpa only [canonicalConstraintModelOfPermutationResolver,
        constraintModelOfPermutationResolver, constraintModelOfResolver] using
        (show ∀ e ∈ avk.gates, e.degreeBound * 2047 ≤ 20470 by
          dsimp only [avk]
          rw [(derived_scalars _).2.2.1]
          exact vk_gates_degree_le)
    · intro p s hs
      change s ∈ permutationSetsOfResolver avk poly p at hs
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
      dsimp only [permutationSetOfResolver]
      refine ⟨hpoly _, ?_⟩
      split
      · simp
      · exact natDegree_comp_rotateData_le _ _ (hpoly _)
    · intro p c hc
      change c ∈ permutationChunksOfResolver avk poly p at hc
      obtain ⟨sc, hsc, rfl⟩ := List.mem_map.mp hc
      obtain ⟨s1, s2⟩ := sc
      obtain ⟨hs1, hs2⟩ := List.of_mem_zip hsc
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs1
        exact ⟨hpoly _, natDegree_comp_rotateData_le _ _ (hpoly _)⟩
      · dsimp only [avk] at hs2
        rw [(derived_scalars _).2.2.2.2.2.2] at hs2
        simpa using vk_chunk_width_le _ hs2
      · intro pr hpr
        obtain ⟨cr, -, hpr'⟩ := List.mem_map.mp hpr
        rw [← hpr']
        exact ⟨hpermutationColumn _ _, hpoly _⟩
    · simpa only [canonicalConstraintModelOfPermutationResolver,
        constraintModelOfPermutationResolver, constraintModelOfResolver] using hlookups
    · change (rowSelectorPolynomial avk.omega _).natDegree ≤ 2047
      exact le_trans (Nat.le_pred_of_lt (by
        simpa [rowSelectorPolynomial] using rowPolynomial_natDegree_lt hrows hn)) hnB
    · change (rowSelectorPolynomial avk.omega _).natDegree ≤ 2047
      exact le_trans (Nat.le_pred_of_lt (by
        simpa [rowSelectorPolynomial] using rowPolynomial_natDegree_lt hrows hn)) hnB
    · change (blindSelectorPolynomial avk.omega _).natDegree ≤ 2047
      exact le_trans (Nat.le_pred_of_lt (by
        simpa [blindSelectorPolynomial] using rowPolynomial_natDegree_lt hrows hn)) hnB
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · rw [committedPreXQuotient_eq]
    refine le_trans (natDegree_preXQuotient_mul_le (Bq := 2047) _ _ ?_) ?_
    · intro j
      exact hpoint _
    · dsimp only [avk]
      rw [(derived_scalars _).2.1, md_counts.2.2.2.2, ← hk, md_counts.1]
      exact vk_quotient_tail_le


/-- **The semantic counts at the query ceiling** (issue #128 F7): at `Q ≤ 2^123` the five
counted caps total at most `2^160`. -/
theorem action_semantic_count_le {Q : ℕ} (hQ : Q ≤ 2 ^ 123) :
    (Q + 1) * 20470 + (Q + 1) * 2 ^ 23 + ((Q + 1) * 2 ^ 35 +
      ((Q + 1) * 2 ^ 21 + (Q + 1) * 2 ^ 25)) ≤ 2 ^ 160 := by
  have h1 : 1 ≤ (2 : ℕ) ^ 123 := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ^ 124 = 2 ^ 123 * 2 := pow_succ 2 123
  have hs : (20470 + 2 ^ 23 + (2 ^ 35 + (2 ^ 21 + 2 ^ 25)) : ℕ) ≤ 2 ^ 36 := by norm_num
  have h3 : (2 : ℕ) ^ 160 = 2 ^ 124 * 2 ^ 36 := by rw [← pow_add]
  calc (Q + 1) * 20470 + (Q + 1) * 2 ^ 23 + ((Q + 1) * 2 ^ 35 +
        ((Q + 1) * 2 ^ 21 + (Q + 1) * 2 ^ 25))
      = (Q + 1) * (20470 + 2 ^ 23 + (2 ^ 35 + (2 ^ 21 + 2 ^ 25))) := by ring
    _ ≤ 2 ^ 124 * 2 ^ 36 := Nat.mul_le_mul (by omega) hs
    _ = 2 ^ 160 := h3.symm

/-- The scalar field clears `2^254`: the counted remainder is at most `2^160 / |Fp| ≤ 2^-94`,
ten bits under the compressed model's `2^-84` ceiling. -/
theorem two_pow_254_le_card : 2 ^ 254 ≤ Fintype.card Fp := by
  rw [Zcash.Arithmetic.card_Fp]
  native_decide

/-- **The five semantic terms collapse to one count over the field** (issue #128 F7): the
endpoint's added tail is at most `2^160 / |Fp|`, with the count proven at the ceiling and no
absorption assumed. -/
theorem action_semantic_terms_le {Q : ℕ} (hQ : Q ≤ 2 ^ 123) :
    (((Q + 1 : ℕ) : ℝ≥0∞) * (((20470 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
        ((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 23 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞))) +
      (((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
        (((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 21 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
          ((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 25 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞))))
      ≤ ((2 ^ 160 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) := by
  have hcollapse :
      (((Q + 1 : ℕ) : ℝ≥0∞) * (((20470 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
          ((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 23 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞))) +
        (((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
          (((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 21 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
            ((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 25 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)))) =
        (((Q + 1) * 20470 + (Q + 1) * 2 ^ 23 + ((Q + 1) * 2 ^ 35 +
          ((Q + 1) * 2 ^ 21 + (Q + 1) * 2 ^ 25)) : ℕ) : ℝ≥0∞) /
          (Fintype.card Fp : ℝ≥0∞) := by
    rw [mul_div_assoc', mul_div_assoc', mul_div_assoc', mul_div_assoc', mul_div_assoc',
      ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
      ENNReal.div_add_div_same]
    norm_cast
  rw [hcollapse]
  gcongr
  exact_mod_cast action_semantic_count_le hQ

/-- The deployed one-Action shape has a much smaller pinned-root numerator than the
consensus-maximum bundle: `queryBudget = 96` and the six root families total `48808 / |Fp|`. -/
theorem action_algebraicRootBudget_eq :
    algebraicRootBudget (actionProofParams.mergeDerived actionCircuit)
        (actionProofParams.mergeDerived actionCircuit).k =
      (48808 : ENNReal) / Fintype.card Fp := by
  rw [shape_eq_mergeDerived]
  norm_num [algebraicRootBudget, queryBudget, shape]

/-- All non-DLOG terms in the exact Action endpoint, including the five semantic tails. -/
noncomputable def actionStatisticalModel (Q : Nat) : ENNReal :=
  (Q + 1 : Nat) * (1 / Fintype.card Fp) +
    (Q + 1 : Nat) *
      ((actionProofParams.mergeDerived actionCircuit).k *
        (2 / (Fintype.card Fp : ENNReal))) +
    (Q + (11 + (actionProofParams.mergeDerived actionCircuit).k) + 1 : Nat) *
      algebraicRootBudget (actionProofParams.mergeDerived actionCircuit)
        (actionProofParams.mergeDerived actionCircuit).k +
    1 / Fintype.card Fp +
    (Q + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal)) +
    (((Q + 1 : Nat) * (((20470 : Nat) : ENNReal) /
        (Fintype.card Fp : ENNReal)) +
      (Q + 1 : Nat) * (((2 ^ 23 : Nat) : ENNReal) /
        (Fintype.card Fp : ENNReal))) +
      ((Q + 1 : Nat) * (((2 ^ 35 : Nat) : ENNReal) /
          (Fintype.card Fp : ENNReal)) +
        ((Q + 1 : Nat) * (((2 ^ 21 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal)) +
          (Q + 1 : Nat) * (((2 ^ 25 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal)))))

/-- The non-DLOG remainder on the bare adaptive route.  Its deployed-root walk uses the original
run only; the larger sequential model below is therefore a conservative upper bound. -/
noncomputable def adaptiveActionStatisticalModel (Q : Nat) : ENNReal :=
  (Q + 1 : Nat) * (1 / Fintype.card Fp) +
    (actionProofParams.mergeDerived actionCircuit).k *
      ((Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) +
    (Q + 1 : Nat) * algebraicRootBudget
      (actionProofParams.mergeDerived actionCircuit)
      (actionProofParams.mergeDerived actionCircuit).k +
    1 / Fintype.card Fp +
    (Q + 1 : Nat) *
      ((((2 ^ 25 : Nat) : ENNReal) / Fintype.card Fp +
        ((2 ^ 35 : Nat) : ENNReal) / Fintype.card Fp) +
        (((2 ^ 21 : Nat) : ENNReal) / Fintype.card Fp +
          (((2 ^ 23 : Nat) : ENNReal) / Fintype.card Fp +
            (20470 : ENNReal) / Fintype.card Fp)))

theorem adaptiveActionSemanticSum_eq :
    (∑ n : Fin 5,
      ((![2 ^ 25, 2 ^ 35, 2 ^ 21, 2 ^ 23, 20470] n : Nat) : ENNReal) /
        Fintype.card Fp) =
      ((((2 ^ 25 : Nat) : ENNReal) / Fintype.card Fp +
        ((2 ^ 35 : Nat) : ENNReal) / Fintype.card Fp) +
        (((2 ^ 21 : Nat) : ENNReal) / Fintype.card Fp +
          (((2 ^ 23 : Nat) : ENNReal) / Fintype.card Fp +
            (20470 : ENNReal) / Fintype.card Fp))) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_one]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ]
  ring

/-- The sequential statistical model conservatively contains the adaptive remainder. -/
theorem adaptiveActionStatisticalModel_le_action (Q : Nat) :
    adaptiveActionStatisticalModel Q ≤ actionStatisticalModel Q := by
  have hk : (actionProofParams.mergeDerived actionCircuit).k = 11 := by
    change actionCircuit.domainExponent = 11
    exact ActionPermutationDomain.domainExponent_eq
  have hsplit : actionStatisticalModel Q =
      adaptiveActionStatisticalModel Q +
        22 * algebraicRootBudget (actionProofParams.mergeDerived actionCircuit) 11 +
        (Q + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal)) := by
    rw [actionStatisticalModel, adaptiveActionStatisticalModel, hk]
    push_cast
    ring
  rw [hsplit]
  exact le_add_right (le_add_right le_rfl)

/-- At `Q <= 2^123`, the compressed remainder and all five Action semantic tails together fit
inside `2^-84`.  The semantic numerator is at most `2^160`; the remaining Action-shape terms are
below `2^140`, leaving a wide margin against the 254-bit scalar field. -/
theorem actionStatisticalModel_at_2pow123 {Q : Nat} (hQ : Q <= 2 ^ 123) :
    actionStatisticalModel Q <= 1 / (2 ^ 84 : ENNReal) := by
  have hbase :
      (Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 <= 2 ^ 141 := by
    calc
      (Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 <=
          (2 ^ 123 + 1) * (1 + 11 * 2 + 20470) +
            (2 ^ 123 + 23) * 48808 + 1 := by omega
      _ <= 2 ^ 141 := by norm_num
  have htotal :
      (Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 + 2 ^ 160 <=
        2 ^ 170 := by
    calc
      (Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 + 2 ^ 160 ≤
          2 ^ 141 + 2 ^ 160 := Nat.add_le_add_right hbase _
      _ ≤ 2 ^ 170 := by norm_num
  have hcount :
      actionStatisticalModel Q <=
        (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 +
          2 ^ 160 : Nat) : ENNReal) / Fintype.card Fp := by
    rw [actionStatisticalModel, action_algebraicRootBudget_eq]
    have hk : (actionProofParams.mergeDerived actionCircuit).k = 11 := by
      change actionCircuit.domainExponent = 11
      exact ActionPermutationDomain.domainExponent_eq
    rw [hk]
    calc
      ((Q + 1 : Nat) : ENNReal) * (1 / (Fintype.card Fp : ENNReal)) +
          ((Q + 1 : Nat) : ENNReal) * (11 * (2 / (Fintype.card Fp : ENNReal))) +
          ((Q + 23 : Nat) : ENNReal) * (48808 / (Fintype.card Fp : ENNReal)) +
          1 / (Fintype.card Fp : ENNReal) +
          ((Q + 1 : Nat) : ENNReal) * (20470 / (Fintype.card Fp : ENNReal)) +
          ((((Q + 1 : Nat) : ENNReal) * (20470 / (Fintype.card Fp : ENNReal)) +
            ((Q + 1 : Nat) : ENNReal) * ((2 ^ 23 : Nat) /
              (Fintype.card Fp : ENNReal))) +
            (((Q + 1 : Nat) : ENNReal) * ((2 ^ 35 : Nat) /
                (Fintype.card Fp : ENNReal)) +
              (((Q + 1 : Nat) : ENNReal) * ((2 ^ 21 : Nat) /
                  (Fintype.card Fp : ENNReal)) +
                ((Q + 1 : Nat) : ENNReal) * ((2 ^ 25 : Nat) /
                  (Fintype.card Fp : ENNReal))))) =
          (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 : Nat) :
              ENNReal) / Fintype.card Fp +
            ((((Q + 1 : Nat) : ENNReal) * (20470 / (Fintype.card Fp : ENNReal)) +
              ((Q + 1 : Nat) : ENNReal) * ((2 ^ 23 : Nat) /
                (Fintype.card Fp : ENNReal))) +
              (((Q + 1 : Nat) : ENNReal) * ((2 ^ 35 : Nat) /
                  (Fintype.card Fp : ENNReal)) +
                (((Q + 1 : Nat) : ENNReal) * ((2 ^ 21 : Nat) /
                    (Fintype.card Fp : ENNReal)) +
                  ((Q + 1 : Nat) : ENNReal) * ((2 ^ 25 : Nat) /
                    (Fintype.card Fp : ENNReal))))) := by
        simp only [div_eq_mul_inv]
        push_cast
        ring
      _ ≤
          (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 : Nat) :
              ENNReal) / Fintype.card Fp +
            ((2 ^ 160 : Nat) : ENNReal) / Fintype.card Fp := by
        exact add_le_add_right (action_semantic_terms_le hQ) _
      _ = (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 +
            2 ^ 160 : Nat) : ENNReal) / Fintype.card Fp := by
        rw [ENNReal.div_add_div_same]
        norm_cast
  refine hcount.trans ?_
  calc
    (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 +
        2 ^ 160 : Nat) : ENNReal) / Fintype.card Fp <=
        ((2 ^ 170 : Nat) : ENNReal) / Fintype.card Fp := by gcongr
    _ <= ((2 ^ 170 : Nat) : ENNReal) / (2 ^ 254 : Nat) := by
      gcongr
      exact_mod_cast two_pow_254_le_card
    _ ≤ 1 / (2 ^ 84 : ENNReal) := by
      rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
      rw [show ((2 ^ 254 : Nat) : ENNReal) =
          (2 ^ 84 : ENNReal) * (2 ^ 170 : ENNReal) by
            norm_num [← pow_add]]
      rw [div_eq_mul_inv, one_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
      norm_num

/-- The combined constraint-plus-Action finder stays within the same conservative three-bit
query envelope at the `2^123` adversary target. -/
theorem action_dlog_queries_le_2pow126
    (family : ComputedStraightLineDeployedFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (hQ : family.Q ≤ 2 ^ 123) :
    actionDlogRandomOracleQueries actionProofParams family ≤ 2 ^ 126 := by
  unfold actionDlogRandomOracleQueries
  have hk : (actionProofParams.mergeDerived actionCircuit).k = 11 := by
    change actionCircuit.domainExponent = 11
    exact ActionPermutationDomain.domainExponent_eq
  rw [hk]
  calc
    6 * family.Q + 6 * (11 + 11) ≤ 6 * 2 ^ 123 + 6 * (11 + 11) := by omega
    _ ≤ 8 * 2 ^ 123 := by norm_num
    _ = 2 ^ 126 := by norm_num

/-- If prover and terminal-reduction group work each fit the `2^123` target, the combined
six-call finder fits the matching `2^126` DLOG-solver envelope. -/
theorem action_dlog_groupWork_le_2pow126
    {proverGroupWork reductionGroupWork : Nat}
    (hprover : proverGroupWork ≤ 2 ^ 123)
    (hreduction : reductionGroupWork ≤ 2 ^ 123) :
    actionDlogGroupWork proverGroupWork reductionGroupWork ≤ 2 ^ 126 := by
  unfold actionDlogGroupWork
  calc
    6 * proverGroupWork + reductionGroupWork ≤ 6 * 2 ^ 123 + 2 ^ 123 := by omega
    _ ≤ 8 * 2 ^ 123 := by norm_num
    _ = 2 ^ 126 := by norm_num

/-- **The captured statement-or-relation bound for sequential adversaries** (issue #128 F8).  A family
equipped with cuts and views at the five semantic squeeze indices — the bounded sequential
online-AGM Fiat–Shamir adversary — admits the full capstone bound with every semantic budget
discharged and counted: the four abstract bounds become
`(Q + 1) · N / |Fp|` for the decided caps `N = 2^25` (`θ`), `2^35` (`β`), `2^21` (`γ`),
`20470` (the `x` fold degree) and `2^23` (`y`, from the view's constraint count `L ≤ 2^12`).

Named assumptions: `hvk`/`hI` pin the family's key and instance commitments to the deployed
Action artifacts; `hchar` bounds the run's pair count below the field characteristic;
`profile` supplies the DLOG reduction; `cuts` is the sequential adversary itself, with its
views' well-formedness (`xdeg` at `20470`, `ylen` at `L`). -/
theorem orchard_action_noStatementOrRelation_prob_le_sequential
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → T)
    (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (profile : family.StraightLineConstraintDlogProfile B)
    {L : ℕ} (hL : L ≤ 2 ^ 12)
    (cuts : ActionSequentialCuts actionProofParams family
      (staticChecks_of_derived family hvk) inputs hvk hI hchar 20470 L) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionNoStatementOrRelationEvent family inputs)
      ≤ ((family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) *
            ((actionProofParams.mergeDerived actionCircuit).k *
              (2 / (Fintype.card Fp : ENNReal))) +
          (family.Q + (11 + (actionProofParams.mergeDerived actionCircuit).k) + 1 : ℕ) *
            algebraicRootBudget (actionProofParams.mergeDerived actionCircuit)
              (actionProofParams.mergeDerived actionCircuit).k +
          (profile.advantage family.straightLineDlogRandomOracleQueries
              (ComputedStraightLineDeployedFSFamily.straightLineDlogGroupWork
                profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞))) +
        (((family.Q + 1 : ℕ) * (((20470 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
            (family.Q + 1 : ℕ) * (((2 ^ 23 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞))) +
          ((family.Q + 1 : ℕ) * (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
            ((family.Q + 1 : ℕ) * (((2 ^ 21 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
              (family.Q + 1 : ℕ) * (((2 ^ 25 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞))))) :=
  orchard_action_noStatementOrRelation_prob_le_captured B hB query hquery family inputs hvk hI hchar
    profile
    (cuts.xy_prob_le actionProofParams family (staticChecks_of_derived family hvk) inputs
      hvk hI hchar query derived_n_ne_zero (derived_n_yn hL))
    (cuts.beta_prob_le actionProofParams family (staticChecks_of_derived family hvk) inputs
      hvk hI hchar query cap_beta)
    (cuts.gamma_prob_le actionProofParams family (staticChecks_of_derived family hvk) inputs
      hvk hI hchar query cap_gamma)
    (cuts.theta_prob_le actionProofParams family (staticChecks_of_derived family hvk) inputs
      hvk hI hchar query cap_theta)

/-! ## Exact false-Action-statement endpoints -/

/-- **The exact captured Action soundness bound.**  Its left-hand event is literal deployed
acceptance with a false `BundleStatement`.  The combined profile prices IPA, unbatching, quotient,
and Action-terminal relation branches once. -/
theorem orchard_action_acceptFalseStatement_prob_le_captured
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → T)
    (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (profile : StraightLineActionDlogProfile actionProofParams family
      (staticChecks_of_derived family hvk) inputs hvk hI hchar B)
    {xyBound betaBound gammaBound thetaBound : ENNReal}
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionXYFailureEvent actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionBetaFailureEvent actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionGammaFailureEvent actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionThetaFailureEvent actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionAcceptFalseStatementEvent family inputs) ≤
      ((family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (family.Q + 1 : Nat) *
            ((actionProofParams.mergeDerived actionCircuit).k *
              (2 / (Fintype.card Fp : ENNReal))) +
          (family.Q + (11 + (actionProofParams.mergeDerived actionCircuit).k) + 1 : Nat) *
            algebraicRootBudget (actionProofParams.mergeDerived actionCircuit)
              (actionProofParams.mergeDerived actionCircuit).k +
          (profile.advantage (actionDlogRandomOracleQueries actionProofParams family)
              (actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal))) +
        (xyBound + (betaBound + (gammaBound + thetaBound))) :=
  actionBundleStatementFailure_prob_le_of_base_union_bound actionProofParams family
    (staticChecks_of_derived family hvk) inputs hvk hI hchar query
    (actionRelationFinder actionProofParams family (staticChecks_of_derived family hvk)
      inputs hvk hI hchar)
    (actionRelationFinder_covers actionProofParams family
      (staticChecks_of_derived family hvk) inputs hvk hI hchar)
    (actionBaseUnion_prob_le_of_dlogProfile actionProofParams family
      (staticChecks_of_derived family hvk) inputs hvk hI hchar B hB query hquery
      (schedule_of_derived family hvk) profile)
    hXY hBeta hGamma hTheta

/-- **Bare adaptive Action composition.**  This is the arbitrary adaptive-RO/online-AGM sibling
of `orchard_action_acceptFalseStatement_prob_le_captured`.  Its quantified adversary is only
`ComputedAdaptiveOnlineAGMFSFamily`: there is no sequential prover, execution, phase, trace, or
cut input.  The executable combined finder closes every algebraic relation branch once, its DLOG
term is evaluated at an explicit adaptive resource profile, and the five annotation-aware Action
semantic surfaces are discharged from the captured key below.
-/
theorem orchard_action_acceptFalseStatement_prob_le_adaptive
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDlogProfile actionProofParams family inputs hvk hI hchar B) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
      ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        adaptiveActionAcceptFalseStatementEvent actionProofParams family inputs) ≤
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        ((actionProofParams.mergeDerived actionCircuit).k *
          ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) +
        ((family.Q + 1 : Nat) *
          algebraicRootBudget (actionProofParams.mergeDerived actionCircuit)
            (actionProofParams.mergeDerived actionCircuit).k +
        ((profile.advantage (adaptiveActionDlogRandomOracleQueries actionProofParams family)
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
        (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG)
      (n : Fin 5)
      (ps : ProofString (actionProofParams.mergeDerived actionCircuit) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt actionProofParams basis inputs n ps source earlier) ≤
        epsilon n := by
    intro basis n ps _hwf source earlier
    fin_cases n
    · refine le_trans
        (adaptiveActionThetaSurface_measure_le actionProofParams basis inputs ps source earlier) ?_
      dsimp only [epsilon]
      gcongr
      exact_mod_cast cap_theta basis
        (adaptiveActionCommitmentPolynomial actionProofParams basis inputs ps source
          (chRecord (fun _ => 0) (fun _ => 0)))
    · have h := adaptiveActionBetaSurface_measure_le
        actionProofParams basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      rw [ENNReal.div_add_div_same]
      gcongr
      exact_mod_cast cap_beta basis
        (adaptiveActionCommitmentPolynomial actionProofParams basis inputs ps source
          (chRecord (fun i => if h : (i : Nat) < 1 then earlier ⟨i, h⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionGammaSurface_measure_le
        actionProofParams basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      rw [ENNReal.div_add_div_same]
      gcongr
      exact_mod_cast cap_gamma basis
        (adaptiveActionCommitmentPolynomial actionProofParams basis inputs ps source
          (chRecord (fun i => if h : (i : Nat) < 2 then earlier ⟨i, h⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionYSurface_measure_le
        actionProofParams basis inputs ps source earlier (derived_n_ne_zero basis)
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      gcongr
      exact_mod_cast derived_n_yn
        (adaptive_action_constraint_count_le basis inputs ps source
          (chRecord (fun i => if h : (i : Nat) < 3 then earlier ⟨i, h⟩ else 0)
            (fun _ => 0))) basis
    · have h := adaptiveActionXSurface_measure_le
        actionProofParams basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      gcongr
      exact_mod_cast adaptive_action_x_degree_le basis inputs ps source
        (chRecord (fun i => if h : (i : Nat) < 4 then earlier ⟨i, h⟩ else 0)
          (fun _ => 0))
  rw [adaptiveActionEvent_prob_eq_of_uniformURS actionProofParams family
    (orchardGeneratorROSetup query) B (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO
      (actionProofParams.mergeDerived actionCircuit).k B hB query hquery)]
  simpa only [epsilon] using
    (adaptiveActionAcceptFalseStatement_prob_le actionProofParams family inputs hvk hI hchar
      B epsilon profile hsurface)

/-- **Concrete bare-adaptive Action capstone.**  At `Q <= 2^123`, the complete adaptive finder
fits a conservative `2^127` random-oracle/group-work envelope (eight uncached represented runs),
while the direct-coordinate decoder fits `2^123`.  The statistical remainder remains `2^-84`. -/
theorem orchard_action_acceptFalseStatement_adaptive_2pow123_workFactor_generatorRO
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDirectDlogProfile actionProofParams family inputs hvk hI hchar B
      (2 ^ 123)) :
    ((independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          adaptiveActionAcceptFalseStatementEvent actionProofParams family inputs) ≤
      profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 84 : ENNReal)) ∧
      adaptiveActionDlogRandomOracleQueries actionProofParams family ≤ 2 ^ 127 ∧
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 127 ∧
      ∀ basis O, 2 * adaptiveActionDirectDecodeOps actionProofParams family basis O ≤
        2 ^ 123 := by
  have hcost := profile.solverCost_le
  have hqueries : adaptiveActionDlogRandomOracleQueries actionProofParams family ≤
      2 ^ 127 := by
    calc
      adaptiveActionDlogRandomOracleQueries actionProofParams family ≤ 16 * 2 ^ 123 :=
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
    (orchard_action_acceptFalseStatement_prob_le_adaptive B hB query hquery family inputs
      hvk hI hchar profile.toAdaptiveActionDlogProfile) ?_
  rw [adaptiveActionSemanticSum_eq]
  calc
    _ =
        profile.advantage (adaptiveActionDlogRandomOracleQueries actionProofParams family)
            (adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          adaptiveActionStatisticalModel family.Q := by
      unfold adaptiveActionStatisticalModel
      ring
    _ ≤ profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 84 : ENNReal) :=
      add_le_add (profile.advantage_mono hqueries hgroup)
        (le_trans (adaptiveActionStatisticalModel_le_action family.Q)
          (actionStatisticalModel_at_2pow123 profile.queryBound))

/-- **Final sequential Action capstone.**  For every query-bounded sequential online-AGM prover
with executable root, IPA, constraint-`x`, and Action phases, deployed verifier acceptance of a
false Action statement is bounded by the extraction terms, one combined Vesta-DLOG advantage,
and the five counted semantic tails.  All traces, cuts, and views consumed below are generated
from `prover` and `execution`. -/
theorem orchard_action_acceptFalseStatement_prob_le_sequential
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → T)
    (hquery : Function.Injective query)
    (prover : SequentialOnlineAGMProver
      (actionProofParams.mergeDerived actionCircuit))
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : ∀ basis, prover.toFamily.vk basis = actionCircuit.toVerifierKey actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, prover.toFamily.instanceCommitment basis =
      actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
      (straightLineRunOutput prover.toFamily basis O).1.proof.1
      (straightLineRunRecord prover.toFamily basis O) < scalarFieldOrder)
    (profile : StraightLineActionDlogProfile actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs hvk hI hchar B)
    {L : Nat} (hL : L ≤ 2 ^ 12)
    (execution : ActionSequentialExecution actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs hvk hI hchar 20470 L) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) prover.toFamily.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionAcceptFalseStatementEvent prover.toFamily inputs) ≤
      ((prover.toFamily.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (prover.toFamily.Q + 1 : Nat) *
            ((actionProofParams.mergeDerived actionCircuit).k *
              (2 / (Fintype.card Fp : ENNReal))) +
          (prover.toFamily.Q + (11 + (actionProofParams.mergeDerived actionCircuit).k) + 1 : Nat) *
            algebraicRootBudget (actionProofParams.mergeDerived actionCircuit)
              (actionProofParams.mergeDerived actionCircuit).k +
          (profile.advantage (actionDlogRandomOracleQueries actionProofParams prover.toFamily)
              (actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (prover.toFamily.Q + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal))) +
        (((prover.toFamily.Q + 1 : Nat) * (((20470 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal)) +
          (prover.toFamily.Q + 1 : Nat) * (((2 ^ 23 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal))) +
          ((prover.toFamily.Q + 1 : Nat) * (((2 ^ 35 : Nat) : ENNReal) /
              (Fintype.card Fp : ENNReal)) +
            ((prover.toFamily.Q + 1 : Nat) * (((2 ^ 21 : Nat) : ENNReal) /
                (Fintype.card Fp : ENNReal)) +
              (prover.toFamily.Q + 1 : Nat) * (((2 ^ 25 : Nat) : ENNReal) /
                (Fintype.card Fp : ENNReal))))) :=
  orchard_action_acceptFalseStatement_prob_le_captured B hB query hquery prover.toFamily inputs hvk hI
    hchar profile
    (execution.toCuts.xy_prob_le actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs
      hvk hI hchar query derived_n_ne_zero (derived_n_yn hL))
    (execution.toCuts.beta_prob_le actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs
      hvk hI hchar query cap_beta)
    (execution.toCuts.gamma_prob_le actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs
      hvk hI hchar query cap_gamma)
    (execution.toCuts.theta_prob_le actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs
      hvk hI hchar query cap_theta)

/-- **Concrete exact-Action work-factor endpoint.**  The query ceiling is carried by the direct
profile, all six prover runs and terminal postprocessing are charged once to the combined DLOG
solver, and the compressed plus semantic statistical remainder is composed into `2^-84`. -/
theorem orchard_action_acceptFalseStatement_2pow123_workFactor_generatorRO
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → T)
    (hquery : Function.Injective query)
    (prover : SequentialOnlineAGMProver
      (actionProofParams.mergeDerived actionCircuit))
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : ∀ basis, prover.toFamily.vk basis = actionCircuit.toVerifierKey actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, prover.toFamily.instanceCommitment basis =
      actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
      (straightLineRunOutput prover.toFamily basis O).1.proof.1
      (straightLineRunRecord prover.toFamily basis O) < scalarFieldOrder)
    (profile : StraightLineActionDirectDlogProfile actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs hvk hI hchar B (2 ^ 123))
    {L : Nat} (hL : L ≤ 2 ^ 12)
    (execution : ActionSequentialExecution actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs hvk hI hchar 20470 L) :
    ((independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) prover.toFamily.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionAcceptFalseStatementEvent prover.toFamily inputs) ≤
      profile.advantage (2 ^ 126) (2 ^ 126) + 1 / (2 ^ 84 : ENNReal)) ∧
      actionDlogRandomOracleQueries actionProofParams prover.toFamily ≤ 2 ^ 126 ∧
      actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤ 2 ^ 126 ∧
      ∀ basis O, 2 * prover.toFamily.straightLineDirectDecodeOps basis O ≤ 2 ^ 123 := by
  have hcost := profile.solverCost_le
  have hqueries : actionDlogRandomOracleQueries actionProofParams prover.toFamily ≤
      2 ^ 126 := by
    calc
      actionDlogRandomOracleQueries actionProofParams prover.toFamily ≤ 8 * 2 ^ 123 := hcost.1
      _ = 2 ^ 126 := by norm_num
  have hgroup : actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
      2 ^ 126 := by
    calc
      actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
          8 * 2 ^ 123 := hcost.2.1
      _ = 2 ^ 126 := by norm_num
  refine ⟨?_, hqueries, hgroup, hcost.2.2⟩
  refine le_trans
    (orchard_action_acceptFalseStatement_prob_le_sequential B hB query hquery prover inputs
      hvk hI hchar profile.toStraightLineActionDlogProfile hL execution) ?_
  calc
    ((prover.toFamily.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (prover.toFamily.Q + 1 : Nat) *
            ((actionProofParams.mergeDerived actionCircuit).k *
              (2 / (Fintype.card Fp : ENNReal))) +
          (prover.toFamily.Q + (11 + (actionProofParams.mergeDerived actionCircuit).k) + 1 : Nat) *
            algebraicRootBudget (actionProofParams.mergeDerived actionCircuit)
              (actionProofParams.mergeDerived actionCircuit).k +
          (profile.advantage (actionDlogRandomOracleQueries actionProofParams prover.toFamily)
              (actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (prover.toFamily.Q + 1 : Nat) * ((20470 : Nat) /
            (Fintype.card Fp : ENNReal))) +
        (((prover.toFamily.Q + 1 : Nat) * (((20470 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal)) +
          (prover.toFamily.Q + 1 : Nat) * (((2 ^ 23 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal))) +
          ((prover.toFamily.Q + 1 : Nat) * (((2 ^ 35 : Nat) : ENNReal) /
              (Fintype.card Fp : ENNReal)) +
            ((prover.toFamily.Q + 1 : Nat) * (((2 ^ 21 : Nat) : ENNReal) /
                (Fintype.card Fp : ENNReal)) +
              (prover.toFamily.Q + 1 : Nat) * (((2 ^ 25 : Nat) : ENNReal) /
                (Fintype.card Fp : ENNReal))))) =
        profile.advantage (actionDlogRandomOracleQueries actionProofParams prover.toFamily)
            (actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          actionStatisticalModel prover.toFamily.Q := by
      unfold actionStatisticalModel
      ring
    _ ≤ profile.advantage (2 ^ 126) (2 ^ 126) + 1 / (2 ^ 84 : ENNReal) :=
      add_le_add (profile.advantage_mono hqueries hgroup)
        (actionStatisticalModel_at_2pow123 profile.queryBound)

end Zcash.Snark.Fixture
