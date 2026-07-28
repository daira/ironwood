import Zcash.Snark.Fixtures.SingleAction.StaticChecks
import Zcash.Snark.Soundness.Composition.ScheduleBudget
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity
import Zcash.Snark.Keygen.Certificate
import Zcash.Circuits.Integration.StraightLineActionEvent
import Zcash.Circuits.Integration.StraightLineActionBudgets
import Zcash.Circuits.Integration.StraightLineActionBudgets

/-!
# The captured Action capstone event and its composed bound

Issue #128's assembly, first stage: the exact terminal event, the captured static checks and
`x`-squeeze schedule rebuilt at the circuit-derived shape, and the composition of the compressed
straight-line bound with the Action bundle-statement fusion.

Everything here lives at `actionProofParams.mergeDerived actionCircuit` — the derived one-proof
shape the Action semantics are stated at — with no shape casts in any statement: the derived
verifying key's scalar fields never read the URS, so the single-Action captured facts transfer
through nine field equalities.

## The adversary model

The endpoint quantifies over a family equipped with `ActionSequentialCuts`: a bounded
sequential online-AGM Fiat–Shamir adversary in the random-oracle model, against Vesta DLOG.
Sequential means each commitment and its algebraic representation are emitted before the next
challenge is squeezed — the cuts and views are that execution order made structural, and the
views' well-formedness (fold degree, constraint count) is the online-AGM decode's own shape.
The four semantic budgets are discharged inside the endpoint from decided counting caps; the
hash-function boundary of the compressed model is unchanged.
-/

namespace Zcash.Snark.Fixture

open Zcash.Snark
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Keygen (actionProofParams shape_eq_mergeDerived vk_eq_toVerifierKey)
open Zcash.Circuits Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder URS)
open scoped ENNReal

/-! ## The exact terminal event -/

/-- **The end-to-end failure event** (issue #128 F1): the deployed verifier accepts and the
Orchard Action bundle statement does not hold — modulo the explicit nontrivial-relation branch,
which the reduction converts into a Vesta DLOG break rather than assuming away. -/
noncomputable def actionAcceptFalseEvent
    (family : ComputedStraightLineDeployedFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs →
      PublicInputs Fp) :
    Set ((AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
          + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp)) :=
  family.straightLineConstraintSemanticFailureEvent
    (actionStatementDecoded actionProofParams family inputs)

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

/-- **The captured Action failure bound, composed** (issue #128 F4/F5): the probability of the
end-to-end failure event is at most the compressed straight-line knowledge error at the derived
key plus the four semantic challenge budgets.  The terminal data — batch openings, member
decodes, acceptance, and the canonical quotient — all come from the same straight-line decoded
run, via the fusion this bound instantiates.

The four budgets remain premises here; the remaining #128 pricing work discharges them
concretely. -/
theorem orchard_action_acceptFalse_prob_le_captured
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
          actionAcceptFalseEvent family inputs)
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
  actionBundleStatementFailure_prob_le_of_compressed_bound actionProofParams family
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

private theorem cap_theta :
    ∀ (basis : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG)
      (poly : CommitmentId → Polynomial Fp),
      TopLevelLookupCoherence.topLevelLookupThetaBudget actionCircuit actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) poly ≤
        2 ^ 25 := by
  intro basis poly
  rw [TopLevelLookupCoherence.topLevelLookupThetaBudget_eq]
  native_decide

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
  simp only [resolverPermutationCell_card, ActionTerminal.vkAt,
    (derived_scalars (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)).2.2.2.2.2.2,
    (derived_scalars (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)).2.1,
    derived_blinding (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)]
  native_decide

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
  simp only [resolverPermutationCell_card, ActionTerminal.vkAt,
    (derived_scalars (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)).2.2.2.2.2.2,
    (derived_scalars (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)).2.1,
    derived_blinding (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)]
  native_decide

private theorem derived_n_ne_zero :
    ∀ basis : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG,
      (vkAt actionProofParams basis).n ≠ 0 := by
  intro basis
  simp only [ActionTerminal.vkAt,
    (derived_scalars (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)).2.1]
  native_decide

private theorem derived_n_yn {L : ℕ} (hL : L ≤ 2 ^ 12) :
    ∀ basis : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG,
      (vkAt actionProofParams basis).n * L ≤ 2 ^ 23 := by
  intro basis
  simp only [ActionTerminal.vkAt,
    (derived_scalars (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)).2.1]
  have hn : vk.n ≤ 2 ^ 11 := by native_decide
  calc vk.n * L ≤ 2 ^ 11 * 2 ^ 12 := Nat.mul_le_mul hn hL
    _ = 2 ^ 23 := by norm_num


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

/-- **The captured Action bound for sequential adversaries** (issue #128 F8).  A family
equipped with cuts and views at the five semantic squeeze indices — the bounded sequential
online-AGM Fiat–Shamir adversary — admits the full capstone bound with every semantic budget
discharged and counted: the four abstract bounds become
`(Q + 1) · N / |Fp|` for the decided caps `N = 2^25` (`θ`), `2^35` (`β`), `2^21` (`γ`),
`20470` (the `x` fold degree) and `2^23` (`y`, from the view's constraint count `L ≤ 2^12`).

Named assumptions: `hvk`/`hI` pin the family's key and instance commitments to the deployed
Action artifacts; `hchar` bounds the run's pair count below the field characteristic;
`profile` supplies the DLOG reduction; `cuts` is the sequential adversary itself, with its
views' well-formedness (`xdeg` at `20470`, `ylen` at `L`). -/
theorem orchard_action_acceptFalse_prob_le_sequential
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
          actionAcceptFalseEvent family inputs)
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
  orchard_action_acceptFalse_prob_le_captured B hB query hquery family inputs hvk hI hchar
    profile
    (cuts.xy_prob_le actionProofParams family (staticChecks_of_derived family hvk) inputs
      hvk hI hchar query derived_n_ne_zero (derived_n_yn hL))
    (cuts.beta_prob_le actionProofParams family (staticChecks_of_derived family hvk) inputs
      hvk hI hchar query cap_beta)
    (cuts.gamma_prob_le actionProofParams family (staticChecks_of_derived family hvk) inputs
      hvk hI hchar query cap_gamma)
    (cuts.theta_prob_le actionProofParams family (staticChecks_of_derived family hvk) inputs
      hvk hI hchar query cap_theta)

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

private theorem cap_theta :
    ∀ (basis : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG)
      (poly : CommitmentId → Polynomial Fp),
      TopLevelLookupCoherence.topLevelLookupThetaBudget actionCircuit actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) poly ≤
        2 ^ 25 := by
  intro basis poly
  rw [TopLevelLookupCoherence.topLevelLookupThetaBudget_eq]
  native_decide

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
  simp only [resolverPermutationCell_card, ActionTerminal.vkAt,
    (derived_scalars (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)).2.2.2.2.2.2,
    (derived_scalars (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)).2.1,
    derived_blinding (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)]
  native_decide

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
  simp only [resolverPermutationCell_card, ActionTerminal.vkAt,
    (derived_scalars (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)).2.2.2.2.2.2,
    (derived_scalars (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)).2.1,
    derived_blinding (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)]
  native_decide

private theorem derived_n_ne_zero :
    ∀ basis : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG,
      (vkAt actionProofParams basis).n ≠ 0 := by
  intro basis
  simp only [ActionTerminal.vkAt,
    (derived_scalars (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)).2.1]
  native_decide

private theorem derived_n_yn {L : ℕ} (hL : L ≤ 2 ^ 12) :
    ∀ basis : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG,
      (vkAt actionProofParams basis).n * L ≤ 2 ^ 23 := by
  intro basis
  simp only [ActionTerminal.vkAt,
    (derived_scalars (ursOfAugmentedBasis
      (actionProofParams.mergeDerived actionCircuit).k basis)).2.1]
  have hn : vk.n ≤ 2 ^ 11 := by native_decide
  calc vk.n * L ≤ 2 ^ 11 * 2 ^ 12 := Nat.mul_le_mul hn hL
    _ = 2 ^ 23 := by norm_num


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

/-- **The captured Action bound for sequential adversaries** (issue #128 F8).  A family
equipped with cuts and views at the five semantic squeeze indices — the bounded sequential
online-AGM Fiat–Shamir adversary — admits the full capstone bound with every semantic budget
discharged and counted: the four abstract bounds become
`(Q + 1) · N / |Fp|` for the decided caps `N = 2^25` (`θ`), `2^35` (`β`), `2^21` (`γ`),
`20470` (the `x` fold degree) and `2^23` (`y`, from the view's constraint count `L ≤ 2^12`).

Named assumptions: `hvk`/`hI` pin the family's key and instance commitments to the deployed
Action artifacts; `hchar` bounds the run's pair count below the field characteristic;
`profile` supplies the DLOG reduction; `cuts` is the sequential adversary itself, with its
views' well-formedness (`xdeg` at `20470`, `ylen` at `L`). -/
theorem orchard_action_acceptFalse_prob_le_sequential
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
          actionAcceptFalseEvent family inputs)
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
  orchard_action_acceptFalse_prob_le_captured B hB query hquery family inputs hvk hI hchar
    profile
    (cuts.xy_prob_le actionProofParams family (staticChecks_of_derived family hvk) inputs
      hvk hI hchar query derived_n_ne_zero (derived_n_yn hL))
    (cuts.beta_prob_le actionProofParams family (staticChecks_of_derived family hvk) inputs
      hvk hI hchar query cap_beta)
    (cuts.gamma_prob_le actionProofParams family (staticChecks_of_derived family hvk) inputs
      hvk hI hchar query cap_gamma)
    (cuts.theta_prob_le actionProofParams family (staticChecks_of_derived family hvk) inputs
      hvk hI hchar query cap_theta)

end Zcash.Snark.Fixture
