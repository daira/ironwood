import Zcash.Snark.Soundness.Composition.StraightLineConstraint

/-!
# Finite-security profile for the straight-line AGM reduction

The probability capstone and the work-factor interpretation are deliberately separate.  This
module records random-oracle queries, group work, and reduction overhead as distinct quantities.
It does not assert a generic-group DLOG success formula.  A caller supplies the finite-security
Vesta DLOG advantage for the resulting concrete solver cost.
-/

namespace Zcash.Snark

open scoped ENNReal

variable {shape : Shape}

namespace ComputedStraightLineDeployedFSFamily

/-- Conservative random-oracle work of the complete straight-line finder.  One direct IPA run
uses `Q` queries.  The three possible wrapped replays each add the `11+k` designated reads. -/
def straightLineDlogRandomOracleQueries
    (family : ComputedStraightLineDeployedFSFamily shape) : Nat :=
  4 * family.Q + 3 * (11 + shape.k)

/-- Concrete group-work accounting: at most four prover invocations plus the algebraic
postprocessing performed by the reduction. -/
def straightLineDlogGroupWork (proverGroupWork reductionGroupWork : Nat) : Nat :=
  4 * proverGroupWork + reductionGroupWork

/-- Finite-security DLOG premise for the complete straight-line finder.  The advantage function
receives random-oracle queries and group operations separately; the profile also records the
prover and postprocessing components used to obtain the latter. -/
structure StraightLineConstraintDlogProfile (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape) where
  proverGroupWork : Nat
  reductionGroupWork : Nat
  advantage : Nat -> Nat -> ENNReal
  advantage_mono : forall {q q' g g'}, q <= q' -> g <= g' ->
    advantage q g <= advantage q' g'
  hardness : TextbookDLWithCoinsAdvantageLE B
    family.straightLineConstraintRelationFinder
    (advantage family.straightLineDlogRandomOracleQueries
      (straightLineDlogGroupWork proverGroupWork reductionGroupWork))

/-- The profile automatically supplies the fixed-call DLOG premise because the pointwise
four-invocation bound is proved by the finder itself. -/
theorem StraightLineConstraintDlogProfile.fixedCalls
    {B : VestaG} {family : ComputedStraightLineDeployedFSFamily shape}
    (profile : StraightLineConstraintDlogProfile B family) :
    TextbookDLWithCoinsFixedCallsAdvantageLE B
      family.straightLineConstraintRelationFinder
      family.straightLineConstraintRelationFinderCalls 4
      (profile.advantage family.straightLineDlogRandomOracleQueries
        (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork)) :=
  (family.straightLineConstraint_fixedCalls_iff B).2 profile.hardness

/-- Finite-security spelling of the straight-line constraint capstone. -/
theorem straightLineConstraintFailure_prob_le_of_dlogProfile
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX)
    (profile : StraightLineConstraintDlogProfile B family) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B static) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (profile.advantage family.straightLineDlogRandomOracleQueries
            (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) * epsilonX :=
  family.straightLineConstraintFailure_prob_le_of_fixedCallsTextbookDL B static schedule
    profile.fixedCalls

/-- Generator-random-oracle form of the finite-security capstone. -/
theorem straightLineConstraintFailure_prob_le_of_generatorRO_dlogProfile
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX)
    (profile : StraightLineConstraintDlogProfile B family) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (profile.advantage family.straightLineDlogRandomOracleQueries
            (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) * epsilonX := by
  rw [family.straightLineConstraintFailure_prob_eq_of_uniformURS
    (orchardGeneratorROSetup query) B static (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery)]
  exact family.straightLineConstraintFailure_prob_le_of_dlogProfile B static schedule profile

/-! ## Work-factor arithmetic -/

/-- A four-call reduction with at most twenty-eight adversary-work units of postprocessing has at
most a five-bit multiplicative overhead.  The `28` is an explicit profile obligation, not an
unstated claim about the implementation. -/
theorem straightLineDlogGroupWork_le_32_mul
    {T proverGroupWork reductionGroupWork : Nat}
    (hprover : proverGroupWork <= T)
    (hreduction : reductionGroupWork <= 28 * T) :
    straightLineDlogGroupWork proverGroupWork reductionGroupWork <= 32 * T := by
  unfold straightLineDlogGroupWork
  omega

/-- At the consensus IPA depth, the random-oracle side also fits the same five-bit overhead for
every nonzero work target. -/
theorem straightLineDlogRandomOracleQueries_le_32_mul
    (family : ComputedStraightLineDeployedFSFamily shape) {T : Nat}
    (hk : shape.k = 11) (hT : 3 <= T) (hQ : family.Q <= T) :
    family.straightLineDlogRandomOracleQueries <= 32 * T := by
  unfold straightLineDlogRandomOracleQueries
  omega

/-- A fully explicit five-bit-overhead profile.  The bounds on prover work and algebraic
postprocessing are named obligations; no implementation-cost claim is smuggled into the
probability theorem. -/
structure StraightLineFiveBitDlogProfile (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape) (T : Nat)
    extends StraightLineConstraintDlogProfile B family where
  ipaDepth : shape.k = 11
  targetAtLeastThree : 3 <= T
  queryBound : family.Q <= T
  proverWorkBound : toStraightLineConstraintDlogProfile.proverGroupWork <= T
  reductionWorkBound :
    toStraightLineConstraintDlogProfile.reductionGroupWork <= 28 * T

/-- Both separately recorded solver resources fit the five-bit overhead promised by the profile.
-/
theorem StraightLineFiveBitDlogProfile.solverCost_le
    {B : VestaG} {family : ComputedStraightLineDeployedFSFamily shape} {T : Nat}
    (profile : StraightLineFiveBitDlogProfile B family T) :
    family.straightLineDlogRandomOracleQueries <= 32 * T ∧
      straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork <= 32 * T := by
  constructor
  · exact family.straightLineDlogRandomOracleQueries_le_32_mul
      profile.ipaDepth profile.targetAtLeastThree profile.queryBound
  · exact straightLineDlogGroupWork_le_32_mul
      profile.proverWorkBound profile.reductionWorkBound

/-- Exact arithmetic behind the conservative work-factor wording: five bits of total reduction
overhead map a `2^122` adversary budget to a `2^127` DLOG-solver budget. -/
theorem five_bit_overhead_at_2pow122 :
    32 * 2 ^ 122 = 2 ^ 127 := by norm_num

/-- At the concrete target, a five-bit profile bounds both solver resources by `2^127`. -/
theorem StraightLineFiveBitDlogProfile.solverCost_at_2pow122
    {B : VestaG} {family : ComputedStraightLineDeployedFSFamily shape}
    (profile : StraightLineFiveBitDlogProfile B family (2 ^ 122)) :
    family.straightLineDlogRandomOracleQueries <= 2 ^ 127 ∧
      straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork <= 2 ^ 127 := by
  have h := profile.solverCost_le
  rw [five_bit_overhead_at_2pow122] at h
  exact h

end ComputedStraightLineDeployedFSFamily

end Zcash.Snark
