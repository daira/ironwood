import Zcash.Snark.Soundness.Action.StraightLineTerminal
import Zcash.Snark.Soundness.Composition.PrefixedSqueeze
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity
import Zcash.Snark.Soundness.StraightLine.TopLevelEvent

/-!
# The Action bundle statement as a priced straight-line event

`StraightLineActionTerminal` reaches the Action bundle statement from one decoding run, leaving
the challenge exclusions open.  This module prices that gap twice.  The compatibility endpoint
bounds the older statement-or-relation failure event.  The exact endpoint instead bounds literal
acceptance with a false bundle statement: its combined executable finder returns every constraint
or Action-terminal relation branch as data, so one DLOG profile charges the entire break event.

- `topLevelStatementOrRelationDecoded actionCircuit` — the intermediate target:
  the bundle statement or a relation exists.
- The four generic `topLevel*FailureEvent actionCircuit` predicates — a decoding
  run whose `x`/`y`, `β`, `γ`, or `θ` challenge lands in the terminal's exclusion
  set. The `x` event is charged here at the terminal's own constraint difference
  rather than aligned with the decode-level difference the compressed event
  already prices: the alignment is a deep pipeline equality, and the extra
  charge is one more per-challenge term.
- `actionSemanticUpgradeContained` — the containment, proved from the terminal bridge.
- `actionNoStatementOrRelation_prob_le_of_compressed_bound` — the intermediate endpoint, event bounds as
  premises.
- `actionNoStatementOrRelation_prob_le_of_surfaces` — the same intermediate endpoint with every event bound
  discharged from the squeeze machinery, given prefix-determined covers and per-challenge
  measures.
- `actionRelationFinder` — the single computed constraint-plus-Action relation finder.
- `actionBundleStatementFailure_prob_le_of_base_union_bound` — the exact false-statement endpoint,
  with the combined relation event already charged in the base union.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)
open scoped ENNReal

local instance vestaInhabitedStraightLineActionEvent : Inhabited VestaG := ⟨0⟩

variable (pp : ProofParams)
  (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
  (static : DeployedConstraintStaticChecks family.toRootFamily)
  (inputs : Fin pp.numProofs → PublicInputs Fp)

variable
  (hvk : ∀ basis, family.vk basis =
    actionCircuit.toVerifierKey pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
  (hI : ∀ basis, family.instanceCommitment basis =
    actionCircuit.instanceCommitment pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
  (hchar : ∀ basis O, deployedX4PairCount
    (actionCircuit.toVerifierKey pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (actionCircuit.instanceCommitment pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (straightLineRunOutput family basis O).1.proof.1
    (straightLineRunRecord family basis O) < scalarFieldOrder)

set_option maxHeartbeats 800000 in
/-- The concrete combined finder covers every false-statement branch of the Action terminal.  The
proof identifies the success value returned by the executable constraint adapter, then uses the
four event complements as the exact finite checks performed by the terminal fallback. -/
theorem actionRelationFinder_covers :
    topLevelTerminalRelationFinderCovers actionCircuit
      pp family static inputs hvk hI hchar
      (actionRelationFinder pp family static inputs hvk hI hchar) := by
  intro basis O hdecoded hXY hBeta hGamma hTheta hfalse
  obtain ⟨success, hout⟩ :=
    family.straightLineConstraintOutcome?_eq_some_of_decoded static basis O hdecoded
  have hsuccess := family.straightLineConstraintSuccess_eq_of_outcome
    static basis O hdecoded success hout
  have hxy := not_exists.mp hXY hdecoded
  rw [not_not] at hxy
  have hbeta := not_exists.mp hBeta hdecoded
  rw [not_not] at hbeta
  have hgamma := not_exists.mp hGamma hdecoded
  rw [not_not] at hgamma
  have htheta := not_exists.mp hTheta hdecoded
  rw [not_not] at htheta
  have hdecode : straightLineRunDecodeAt family static basis O
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      (hvk basis) (hI basis) hdecoded =
      hI basis ▸ hvk basis ▸
        success.witness.decode.reRound (runRounds family.toFamily basis O) := by
    simp only [straightLineRunDecodeAt, straightLineDecode,
      straightLineConstraintWitness, hsuccess]
    rfl
  have haccepts := straightLineRunAcceptsAt family static basis O
    (actionCircuit.toVerifierKey pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (actionCircuit.instanceCommitment pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hvk basis) (hI basis) hdecoded
  have hacceptsEq : straightLineRunAcceptsAt family static basis O
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      (hvk basis) (hI basis) hdecoded =
      hI basis ▸ hvk basis ▸ success.accepts :=
    Subsingleton.elim _ _
  let successDecode : DeployedAlgebraicDecode
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) rfl
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O)
      ((straightLineRunOutput family basis O).1.aMulti
        (wrappedPreIpaReads (straightLineRunOutput family basis O)))
      ((straightLineRunOutput family basis O).1.multiU
        (wrappedPreIpaReads (straightLineRunOutput family basis O)))
      ((straightLineRunOutput family basis O).1.multiBlind
        (wrappedPreIpaReads (straightLineRunOutput family basis O))) :=
    hI basis ▸ hvk basis ▸
      success.witness.decode.reRound (runRounds family.toFamily basis O)
  let successAccepts : DeployedAccepts
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) rfl
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) :=
    hI basis ▸ hvk basis ▸ success.accepts
  have hdecodeEq : straightLineRunDecodeAt family static basis O
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      (hvk basis) (hI basis) hdecoded = successDecode := hdecode
  have hacceptsEq' : straightLineRunAcceptsAt family static basis O
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      (hvk basis) (hI basis) hdecoded = successAccepts :=
    Subsingleton.elim _ _
  have hmodelEq : topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded =
      CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi =>
          successDecode.toMemberDecode (hchar basis O) i hi)
        (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
        successAccepts := by
    unfold topLevelRunModel
    rw [hdecodeEq]
  have hpolyEq : topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O hdecoded =
      CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi =>
          successDecode.toMemberDecode (hchar basis O) i hi)
        successAccepts := by
    unfold topLevelRunPolynomial
    rw [hdecodeEq]
  unfold actionRelationFinder
  split
  · rfl
  · unfold actionTerminalRelationFinder
    rw [hout]
    simp only
    have hxgood : (straightLineRunRecord family basis O).x ∉ szBadSet
        (combineConstraints
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).fixedCols
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).adviceCols
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).instanceCols
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).gates
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).sets
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).chunks
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).lookups
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).beta
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).gamma
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).delta
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).theta
          (straightLineRunRecord family basis O).y
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).chunkLen
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).l0
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).lLast
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O hdecoded).lBlind -
          topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O hdecoded
              CommitmentId.vanishingH *
            (Polynomial.X ^ (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n - 1)) := hxy.1
    rw [hmodelEq, hpolyEq] at hxgood
    have hxgoodData := hxgood
    rw [← combineConstraintsData_eq, ← ComputablePolynomial.sub_eq,
      ← ComputablePolynomial.mul_eq, ← ComputablePolynomial.sub_eq,
      ← ComputablePolynomial.pow_eq, ← ComputablePolynomial.X_eq] at hxgoodData
    have hone : (1 : Polynomial Fp) = ComputablePolynomial.const 1 := by
      rw [ComputablePolynomial.const_eq, Polynomial.C_1]
    rw [hone] at hxgoodData
    unfold straightLineRunRecord straightLineRunOutput at hxgoodData
    have hxgoodSome := (szBadSetAvoidance?_isSome_iff _ _).2 hxgoodData
    split
    · rename_i hxgoodProof _
      have hgoodY' := hxy.2
      rw [hmodelEq] at hgoodY'
      let hn : (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n ≠ 0 := by
        change 2 ^ actionCircuit.domainExponent ≠ 0
        positivity
      have hgoodYSome := foldSplitAvoidance?_isSome_of _ _ hn _ hgoodY'
      split
      · rename_i hgoodYProof _
        have hpermutation' : ResolverPermutationChallengeExclusions
                (actionCircuit.toVerifierKey pp
                  (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
                (straightLineRunRecord family basis O)
                (topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar
                  basis O hdecoded) actionActiveRows := ⟨hgamma.1, hbeta.1⟩
        rw [hpolyEq] at hpermutation'
        have hpermutationSome := resolverPermutationChallengeExclusions?_isSome_of
          _ _ _ _ hpermutation'
        split
        · have hlookup' : TopLevelLookup.ChallengeExclusions
                  actionCircuit pp
                  (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)
                  (straightLineRunRecord family basis O)
                  (topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar
                    basis O hdecoded) := ⟨hgamma.2, hbeta.2, htheta⟩
          rw [hpolyEq] at hlookup'
          have hlookupSome :=
            TopLevelLookup.topLevelLookupChallengeExclusions?_isSome_of
              actionCircuit pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) _ _ hlookup'
          split
          · split
            · rename_i statement _
              exact False.elim (hfalse statement)
            · rfl
          · rename_i hlookupEq
            simpa only [hlookupEq] using hlookupSome
        · rename_i hpermutationEq
          simpa only [hpermutationEq] using hpermutationSome
      · rename_i hgoodYEq
        simpa only [hgoodYEq] using hgoodYSome
    · rename_i hxgoodEq
      simpa only [hxgoodEq] using hxgoodSome

/-- Conservative black-box calls of the combined finder: the existing constraint finder has its
proved four-call bound, and the terminal fallback performs at most two further represented-run
evaluations. -/
def actionRelationFinderCalls
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) : Nat :=
  family.straightLineConstraintRelationFinderCalls basis O + 2

theorem actionRelationFinderCalls_le_six
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) :
    actionRelationFinderCalls pp family basis O ≤ 6 := by
  unfold actionRelationFinderCalls
  have hcalls := family.straightLineConstraintRelationFinderCalls_le_four basis O
  omega

/-- Random-oracle work of the combined constraint-plus-Action solver.  All six represented prover
runs include their own `11+k` designated transcript reads; no cache-sharing convention is assumed.
-/
def actionDlogRandomOracleQueries : Nat :=
  6 * family.Q + 6 * (11 + actionCircuit.domainExponent)

/-- Group-work envelope of the combined solver.  Terminal comparison work is included in the
explicit reduction component. -/
def actionDlogGroupWork (proverGroupWork reductionGroupWork : Nat) : Nat :=
  6 * proverGroupWork + reductionGroupWork

/-- One finite-security premise for the complete constraint-plus-Action relation finder. -/
structure StraightLineActionDlogProfile (B : VestaG) where
  proverGroupWork : Nat
  reductionGroupWork : Nat
  advantage : Nat → Nat → ENNReal
  advantage_mono : ∀ {q q' g g'}, q ≤ q' → g ≤ g' →
    advantage q g ≤ advantage q' g'
  hardness : TextbookDLWithCoinsAdvantageLE B
    (actionRelationFinder pp family static inputs hvk hI hchar)
    (advantage (actionDlogRandomOracleQueries pp family)
      (actionDlogGroupWork proverGroupWork reductionGroupWork))

/-- Concrete resource profile for the direct constraint-plus-Action route.  In addition to the
single DLOG premise for the combined executable finder, it prices the underlying prover, all
postprocessing group operations (including the Action-terminal comparison), and both possible
direct-coordinate decoder executions.  The small lower bound is exactly what is needed for
`6Q + 6(11+k) <= 8T` at the deployed IPA depth. -/
structure StraightLineActionDirectDlogProfile (B : VestaG) (T : Nat)
    extends StraightLineActionDlogProfile pp family static inputs hvk hI hchar B where
  ipaDepth : actionCircuit.domainExponent = 11
  targetAtLeastSixtySix : 66 <= T
  queryBound : family.Q <= T
  proverWorkBound : toStraightLineActionDlogProfile.proverGroupWork <= T
  reductionWorkBound : toStraightLineActionDlogProfile.reductionGroupWork <= T
  directDecodeWorkBound : forall basis O,
    2 * family.straightLineDirectDecodeOps basis O <= T

/-- The concrete Action profile bounds both DLOG-solver resources by an eightfold envelope and
retains the direct-decoder certificate used by the straight-line implementation. -/
theorem StraightLineActionDirectDlogProfile.solverCost_le
    {B : VestaG} {T : Nat}
    (profile : StraightLineActionDirectDlogProfile pp family static inputs
      hvk hI hchar B T) :
    actionDlogRandomOracleQueries pp family <= 8 * T /\
      actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork <= 8 * T /\
      forall basis O, 2 * family.straightLineDirectDecodeOps basis O <= T := by
  constructor
  · unfold actionDlogRandomOracleQueries
    rw [profile.ipaDepth]
    have hT := profile.targetAtLeastSixtySix
    calc
      6 * family.Q + 6 * (11 + 11) <= 6 * T + 6 * (11 + 11) := by
        gcongr
        exact profile.queryBound
      _ <= 8 * T := by omega
  constructor
  · unfold actionDlogGroupWork
    calc
      6 * profile.proverGroupWork + profile.reductionGroupWork <= 6 * T + T := by
        gcongr
        · exact profile.proverWorkBound
        · exact profile.reductionWorkBound
      _ <= 8 * T := by omega
  · exact profile.directDecodeWorkBound

/-- The combined finder exactly extends the old constraint finder on every successful old branch.
-/
theorem actionRelationFinder_extends_constraint
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) :
    (family.straightLineConstraintRelationFinder basis O).isSome →
      (actionRelationFinder pp family static inputs hvk hI hchar basis O).isSome := by
  intro hsome
  unfold actionRelationFinder
  cases hfinder : family.straightLineConstraintRelationFinder basis O with
  | none => simp [hfinder] at hsome
  | some relation => rfl

/-- Generator-random-oracle bound for compressed failure union the complete Action relation event.
The combined DLOG advantage occurs once. -/
theorem actionBaseUnion_prob_le_of_dlogProfile
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → T)
    (hquery : Function.Injective query)
    {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX)
    (profile : StraightLineActionDlogProfile pp family static inputs hvk hI hchar B) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          (family.straightLineConstraintFailureEvent static ∪
            family.straightLineRelationEvent
              (actionRelationFinder pp family static inputs hvk hI hchar))) ≤
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (actionCircuit.domainExponent *
            (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + actionCircuit.domainExponent) + 1 : Nat) *
          algebraicRootBudget (pp.mergeDerived actionCircuit)
            actionCircuit.domainExponent +
        (profile.advantage (actionDlogRandomOracleQueries pp family)
            (actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) * epsilonX := by
  rw [family.straightLineConstraintFailure_union_relation_prob_eq_of_uniformURS
    (orchardGeneratorROSetup query) B static
    (actionRelationFinder pp family static inputs hvk hI hchar)
    (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO
      (pp.mergeDerived actionCircuit).k B hB query hquery)]
  simpa only [ProofParams.mergeDerived_k] using
    family.straightLineConstraintFailure_union_relation_prob_le_of_relationSupersetTextbookDL
      B static (actionRelationFinder pp family static inputs hvk hI hchar)
      (actionRelationFinder_extends_constraint pp family static inputs hvk hI hchar)
      schedule profile.hardness

/-- **The containment behind the fusion.**  A decoding run without the bundle statement or a
relation must have a challenge in one of the terminal's exclusion sets: otherwise the terminal
bridge produces the statement.  Stepped through in the body. -/
theorem actionSemanticUpgradeContained :
    family.StraightLineConstraintSemanticUpgradeContained static
      (topLevelStatementOrRelationDecoded actionCircuit pp family inputs)
      (topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      (topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      (topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      (topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) := by
  intro q hq
  obtain ⟨hdecoded, hsem⟩ := hq
  by_contra hnot
  simp only [Set.mem_union, not_or] at hnot
  obtain ⟨hXY, hBeta, hGamma, hTheta⟩ := hnot
  -- Non-membership in each event gives the corresponding exclusion at the run's own decode.
  have hxy := not_exists.mp hXY hdecoded
  rw [not_not] at hxy
  have hbeta := not_exists.mp hBeta hdecoded
  rw [not_not] at hbeta
  have hgamma := not_exists.mp hGamma hdecoded
  rw [not_not] at hgamma
  have htheta := not_exists.mp hTheta hdecoded
  rw [not_not] at htheta
  -- The terminal bridge assembles the exclusions into the statement.
  exact hsem ⟨action_bundleStatement_or_relation_of_straightLineDecoded pp family static
    q.1 q.2 inputs (hvk q.1) (hI q.1) hdecoded (hchar q.1 q.2)
    hxy.1 hxy.2 ⟨hgamma.1, hbeta.1⟩ ⟨hgamma.2, hbeta.2, htheta⟩⟩

/-- **Exact Action-statement containment.**  Outside the compressed decode failure and the four
challenge surfaces, a false Action statement forces the good-run terminal onto its relation
branch.  A covering computed finder therefore turns that branch into the explicit event priced
by DLOG. -/
theorem actionBundleStatementUpgradeContained
    (finder :
      (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis))
    (hcovers : topLevelTerminalRelationFinderCovers actionCircuit pp family static inputs hvk hI hchar finder) :
    family.StraightLineConstraintSemanticUpgradeContained static
      (topLevelBundleStatementDecoded actionCircuit pp family inputs)
      (topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      (topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      (topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      (topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar ∪
        straightLineTerminalRelationEvent family finder) := by
  rintro q ⟨hdecoded, hfalse⟩
  by_cases hXY : q ∈ topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar
  · exact Or.inl hXY
  by_cases hBeta : q ∈ topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar
  · exact Or.inr (Or.inl hBeta)
  by_cases hGamma : q ∈ topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar
  · exact Or.inr (Or.inr (Or.inl hGamma))
  by_cases hTheta : q ∈ topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar
  · exact Or.inr (Or.inr (Or.inr (Or.inl hTheta)))
  refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
  exact hcovers q.1 q.2 hdecoded hXY hBeta hGamma hTheta hfalse

/-- Literal accepting-false-Action runs are covered by the *single* base union (compressed decode
failure or the combined relation finder) plus the four semantic challenge surfaces.  The finder
event is not added again after the compressed bound. -/
theorem actionBundleStatementFailure_subset_union
    (finder :
      (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis))
    (hcovers : topLevelTerminalRelationFinderCovers actionCircuit pp family static inputs hvk hI hchar finder) :
    family.straightLineConstraintSemanticFailureEvent
        (topLevelBundleStatementDecoded actionCircuit pp family inputs) <=
      (family.straightLineConstraintFailureEvent static ∪
        family.straightLineRelationEvent finder) ∪
      (topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar ∪
        (topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar ∪
          (topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar ∪
            topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar))) := by
  rintro q ⟨haccept, hfalse⟩
  by_cases hdecoded : family.straightLineConstraintDecoded static q.1 q.2
  · have hsemantic : family.straightLineConstraintDecoded static q.1 q.2 ∧
        ¬topLevelBundleStatementDecoded actionCircuit pp family inputs q.1 q.2 := ⟨hdecoded, hfalse⟩
    rcases actionBundleStatementUpgradeContained pp family static inputs hvk hI hchar
        finder hcovers hsemantic with hXY | hBeta | hGamma | hTheta | hrelation
    · exact Or.inr (Or.inl hXY)
    · exact Or.inr (Or.inr (Or.inl hBeta))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hGamma)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hTheta)))
    · exact Or.inl (Or.inr hrelation)
  · exact Or.inl (Or.inl ⟨haccept, hdecoded⟩)

/-- Exact Action probability composition with the combined relation event priced once. -/
theorem actionBundleStatementFailure_prob_le_of_base_union_bound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → T)
    (finder :
      (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis))
    (hcovers : topLevelTerminalRelationFinderCovers actionCircuit pp family static inputs hvk hI hchar finder)
    {baseBound xyBound betaBound gammaBound thetaBound : ENNReal}
    (hbase : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          (family.straightLineConstraintFailureEvent static ∪
            family.straightLineRelationEvent finder)) ≤ baseBound)
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintSemanticFailureEvent
            (topLevelBundleStatementDecoded actionCircuit pp family inputs)) <=
      baseBound + (xyBound + (betaBound + (gammaBound + thetaBound))) := by
  refine le_trans (MeasureTheory.measure_mono
    (Set.preimage_mono (actionBundleStatementFailure_subset_union pp family static inputs
      hvk hI hchar finder hcovers))) ?_
  rw [Set.preimage_union, Set.preimage_union, Set.preimage_union, Set.preimage_union]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add hbase ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add hXY ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add hBeta ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add hGamma hTheta

/-- **The statement-or-relation intermediate, priced.**  The probability that an accepting straight-line
run carries neither the bundle statement nor a nontrivial relation is at most the compressed
constraint failure bound plus the four per-challenge exclusion bounds. -/
theorem actionNoStatementOrRelation_prob_le_of_compressed_bound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → T)
    {compressedBound xyBound betaBound gammaBound thetaBound : ENNReal}
    (hcompressed : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) ≤ compressedBound)
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintSemanticFailureEvent
            (topLevelStatementOrRelationDecoded actionCircuit pp family inputs))
      ≤ compressedBound + (xyBound + (betaBound + (gammaBound + thetaBound))) :=
  family.straightLineConstraintSemanticFailure_prob_le_of_compressed_bound query static
    (topLevelStatementOrRelationDecoded actionCircuit pp family inputs)
    (topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar)
    (topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
    (topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
    (topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
    (actionSemanticUpgradeContained pp family static inputs hvk hI hchar)
    hcompressed hXY hBeta hGamma hTheta

/-- **The exact Action-statement bound, factored at the computed finder.**  This theorem bounds
literal accepting false statements.  Its last premise is the probability that the executable
terminal finder returns relation coefficients; a DLOG profile must discharge that premise.
Unlike the statement-or-relation intermediate above, no existential relation is accepted as
semantic success. -/
theorem actionBundleStatementFailure_prob_le_of_compressed_bound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → T)
    (finder :
      (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis))
    (hcovers : topLevelTerminalRelationFinderCovers actionCircuit pp family static inputs hvk hI hchar finder)
    {compressedBound xyBound betaBound gammaBound thetaBound relationBound : ENNReal}
    (hcompressed : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) ≤ compressedBound)
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ thetaBound)
    (hRelation : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          straightLineTerminalRelationEvent family finder) ≤ relationBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintSemanticFailureEvent
            (topLevelBundleStatementDecoded actionCircuit pp family inputs))
      ≤ compressedBound +
          (xyBound + (betaBound + (gammaBound + (thetaBound + relationBound)))) := by
  refine family.straightLineConstraintSemanticFailure_prob_le_of_compressed_bound query static
    (topLevelBundleStatementDecoded actionCircuit pp family inputs)
    (topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar)
    (topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
    (topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
    (topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar ∪
      straightLineTerminalRelationEvent family finder)
    (actionBundleStatementUpgradeContained pp family static inputs hvk hI hchar finder hcovers)
    hcompressed hXY hBeta hGamma ?_
  calc
    (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype _)).toOuterMeasure
      ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        (topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar ∪
          straightLineTerminalRelationEvent family finder))
        = (independentProductPMF (orchardGeneratorROSetup query)
            (PMF.uniformOfFintype _)).toOuterMeasure
          (((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
              topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ∪
            ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
              straightLineTerminalRelationEvent family finder)) := by rw [Set.preimage_union]
    _ ≤ (independentProductPMF (orchardGeneratorROSetup query)
            (PMF.uniformOfFintype _)).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) +
        (independentProductPMF (orchardGeneratorROSetup query)
            (PMF.uniformOfFintype _)).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            straightLineTerminalRelationEvent family finder) :=
      MeasureTheory.measure_union_le _ _
    _ ≤ thetaBound + relationBound := add_le_add hTheta hRelation

/-! ## Pricing the events over their squeezes

Each failure event fires on one challenge, and the run reads that challenge from the oracle at
its own squeeze prefix (`straightLineRunReads_eq`).  A caller who covers the run's exclusion set
with a prefix-determined bad-value function embeds the event into the index-generic squeeze
surface, so it costs `(Q + 1)` times a per-challenge measure.  Covering with a prefix-determined
function is a family-level fact — an AGM family's decode is pinned by the transcript prefix —
supplied here as the `hcompat` premises.
-/

/-- The `θ` event embeds into the index-`0` squeeze surface. -/
theorem actionThetaFailureEvent_subset_surface
    (badF : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) →
      (Fin 0 → Fp) → Set Fp)
    (hcompat : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(TopLevelLookup.thetaBadSet actionCircuit pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)
          (topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h)) ⊆
        badF basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 0)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (0 : Fin 11).isLt))))) :
    topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar ⊆
      squeezeSurfaceEvent 0 family.toFamily badF := by
  rintro q ⟨h, hbad⟩
  rw [not_not] at hbad
  have hread : (straightLineRunRecord family q.1 q.2).theta =
      q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 0) :=
    congrFun (straightLineRunReads_eq family q.1 q.2) 0
  have hmem := hcompat q.1 q.2 h (Finset.mem_coe.mpr hbad)
  rw [hread] at hmem
  exact hmem

/-- The `β` event embeds into the index-`1` squeeze surface. -/
theorem actionBetaFailureEvent_subset_surface
    (badF : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) →
      (Fin 1 → Fp) → Set Fp)
    (hcompat : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(allResolverPermutationBetaBadSet
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h)
          actionActiveRows ∪
        allResolverLookupBetaBadSet
          pp.numProofs
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (straightLineRunRecord family basis O)
          (topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h)
          ((actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n -
            (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).blindingFactors
            - 2)) ⊆
        badF basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 1)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (1 : Fin 11).isLt))))) :
    topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar ⊆
      squeezeSurfaceEvent 1 family.toFamily badF := by
  rintro q ⟨h, hbad⟩
  rw [not_and_or, not_not, not_not] at hbad
  have hread : (straightLineRunRecord family q.1 q.2).beta =
      q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 1) :=
    congrFun (straightLineRunReads_eq family q.1 q.2) 1
  have hmem := hcompat q.1 q.2 h (Finset.mem_coe.mpr (by
    rcases hbad with hperm | hlookup
    · exact Finset.mem_union_left _ hperm
    · exact Finset.mem_union_right _ hlookup))
  rw [hread] at hmem
  exact hmem

/-- The `γ` event embeds into the index-`2` squeeze surface. -/
theorem actionGammaFailureEvent_subset_surface
    (badF : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) →
      (Fin 2 → Fp) → Set Fp)
    (hcompat : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(allResolverPermutationGammaBadSet
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (straightLineRunRecord family basis O)
          (topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h)
          actionActiveRows ∪
        allResolverLookupGammaBadSet
          pp.numProofs
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (straightLineRunRecord family basis O)
          (topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h)
          ((actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n -
            (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).blindingFactors
            - 2)) ⊆
        badF basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 2)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (2 : Fin 11).isLt))))) :
    topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar ⊆
      squeezeSurfaceEvent 2 family.toFamily badF := by
  rintro q ⟨h, hbad⟩
  rw [not_and_or, not_not, not_not] at hbad
  have hread : (straightLineRunRecord family q.1 q.2).gamma =
      q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 2) :=
    congrFun (straightLineRunReads_eq family q.1 q.2) 2
  have hmem := hcompat q.1 q.2 h (Finset.mem_coe.mpr (by
    rcases hbad with hperm | hlookup
    · exact Finset.mem_union_left _ hperm
    · exact Finset.mem_union_right _ hlookup))
  rw [hread] at hmem
  exact hmem

/-- The `x`/`y` event embeds into the union of the index-`4` and index-`3` squeeze surfaces. -/
theorem actionXYFailureEvent_subset_surfaces
    (badFX : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) →
      (Fin 4 → Fp) → Set Fp)
    (badFY : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) →
      (Fin 3 → Fp) → Set Fp)
    (hcompatX : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(szBadSet
        (combineConstraints
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).fixedCols
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).adviceCols
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).instanceCols
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).gates
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).sets
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).chunks
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).lookups
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).beta
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).gamma
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).delta
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).theta
          (straightLineRunRecord family basis O).y
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).chunkLen
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).l0
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).lLast
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).lBlind -
          topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h
              CommitmentId.vanishingH *
            (X ^ (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n - 1))) ⊆
        badFX basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (4 : Fin 11).isLt)))))
    (hcompatY : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      {v : Fp | ∃ j, v ∈ szBadSet
        (foldSplitWitness
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).constraints
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n j)} ⊆
        badFY basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 3)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (3 : Fin 11).isLt))))) :
    topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar ⊆
      squeezeSurfaceEvent 4 family.toFamily badFX ∪
        squeezeSurfaceEvent 3 family.toFamily badFY := by
  rintro q ⟨h, hbad⟩
  rw [not_and_or, not_not] at hbad
  rcases hbad with hx | hy
  · have hread : (straightLineRunRecord family q.1 q.2).x =
        q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 4) :=
      congrFun (straightLineRunReads_eq family q.1 q.2) 4
    have hmem := hcompatX q.1 q.2 h (Finset.mem_coe.mpr hx)
    rw [hread] at hmem
    exact Set.mem_union_left _ hmem
  · rw [not_forall] at hy
    obtain ⟨j, hj⟩ := hy
    rw [not_not] at hj
    have hread : (straightLineRunRecord family q.1 q.2).y =
        q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 3) :=
      congrFun (straightLineRunReads_eq family q.1 q.2) 3
    have hmem := hcompatY q.1 q.2 h ⟨j, hj⟩
    rw [hread] at hmem
    exact Set.mem_union_right _ hmem

/-- **The surface-form fusion.**  Every event bound is discharged from the squeeze machinery:
the caller supplies a prefix-determined cover for each exclusion set, prefix-determinism at the
five squeeze indices, and a per-challenge measure apiece, and the bundle-statement failure
probability is

`compressed + (Q+1)·(εx + εy) + (Q+1)·εβ + (Q+1)·εγ + (Q+1)·εθ`. -/
theorem actionNoStatementOrRelation_prob_le_of_surfaces
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → T)
    (badFX : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → (Fin 4 → Fp) → Set Fp)
    (badFY : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → (Fin 3 → Fp) → Set Fp)
    (badFBeta : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → (Fin 1 → Fp) → Set Fp)
    (badFGamma : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → (Fin 2 → Fp) → Set Fp)
    (badFTheta : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → (Fin 0 → Fp) → Set Fp)
    (hcompatX : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(szBadSet
        (combineConstraints
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).fixedCols
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).adviceCols
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).instanceCols
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).gates
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).sets
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).chunks
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).lookups
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).beta
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).gamma
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).delta
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).theta
          (straightLineRunRecord family basis O).y
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).chunkLen
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).l0
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).lLast
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).lBlind -
          topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h
              CommitmentId.vanishingH *
            (X ^ (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n - 1))) ⊆
        badFX basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (4 : Fin 11).isLt)))))
    (hcompatY : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      {v : Fp | ∃ j, v ∈ szBadSet
        (foldSplitWitness
          (topLevelRunModel actionCircuit pp family static inputs hvk hI hchar basis O h).constraints
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n j)} ⊆
        badFY basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 3)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (3 : Fin 11).isLt)))))
    (hcompatBeta : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(allResolverPermutationBetaBadSet
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h)
          actionActiveRows ∪
        allResolverLookupBetaBadSet
          pp.numProofs
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (straightLineRunRecord family basis O)
          (topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h)
          ((actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n -
            (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).blindingFactors
            - 2)) ⊆
        badFBeta basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 1)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (1 : Fin 11).isLt)))))
    (hcompatGamma : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(allResolverPermutationGammaBadSet
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (straightLineRunRecord family basis O)
          (topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h)
          actionActiveRows ∪
        allResolverLookupGammaBadSet
          pp.numProofs
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (straightLineRunRecord family basis O)
          (topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h)
          ((actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n -
            (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).blindingFactors
            - 2)) ⊆
        badFGamma basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 2)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (2 : Fin 11).isLt)))))
    (hcompatTheta : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(TopLevelLookup.thetaBadSet actionCircuit pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)
          (topLevelRunPolynomial actionCircuit pp family static inputs hvk hI hchar basis O h)) ⊆
        badFTheta basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 0)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (0 : Fin 11).isLt)))))
    (hdetX : PrefixDeterminedAt family.toFamily 4)
    (hdetY : PrefixDeterminedAt family.toFamily 3)
    (hdetBeta : PrefixDeterminedAt family.toFamily 1)
    (hdetGamma : PrefixDeterminedAt family.toFamily 2)
    (hdetTheta : PrefixDeterminedAt family.toFamily 0)
    {compressedBound epsX epsY epsBeta epsGamma epsTheta : ENNReal}
    (hcompressed : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) ≤ compressedBound)
    (hbadX : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badFX basis t nu) ≤ epsX)
    (hbadY : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badFY basis t nu) ≤ epsY)
    (hbadBeta : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badFBeta basis t nu) ≤ epsBeta)
    (hbadGamma : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badFGamma basis t nu) ≤ epsGamma)
    (hbadTheta : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badFTheta basis t nu) ≤ epsTheta) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintSemanticFailureEvent
            (topLevelStatementOrRelationDecoded actionCircuit pp family inputs))
      ≤ compressedBound +
          (((family.Q + 1 : ℕ) * epsX + (family.Q + 1 : ℕ) * epsY) +
            ((family.Q + 1 : ℕ) * epsBeta +
              ((family.Q + 1 : ℕ) * epsGamma + (family.Q + 1 : ℕ) * epsTheta))) := by
  refine actionNoStatementOrRelation_prob_le_of_compressed_bound pp family static inputs
    hvk hI hchar query hcompressed ?_ ?_ ?_ ?_
  · calc (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype _)).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar)
        ≤ (independentProductPMF (orchardGeneratorROSetup query)
          (PMF.uniformOfFintype _)).toOuterMeasure
            (((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
              squeezeSurfaceEvent 4 family.toFamily badFX) ∪
              ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
                squeezeSurfaceEvent 3 family.toFamily badFY)) := by
          refine MeasureTheory.measure_mono ?_
          rw [← Set.preimage_union]
          exact Set.preimage_mono
            (actionXYFailureEvent_subset_surfaces pp family static inputs hvk hI hchar
              badFX badFY hcompatX hcompatY)
      _ ≤ (family.Q + 1 : ℕ) * epsX + (family.Q + 1 : ℕ) * epsY :=
          (MeasureTheory.measure_union_le _ _).trans (add_le_add
            (squeezeSurfaceEvent_prob_le 4 query family.toFamily badFX
              (hstab_of_prefixDeterminedAt family.toFamily 4 hdetX) hbadX)
            (squeezeSurfaceEvent_prob_le 3 query family.toFamily badFY
              (hstab_of_prefixDeterminedAt family.toFamily 3 hdetY) hbadY))
  · exact le_trans
      (MeasureTheory.measure_mono (Set.preimage_mono
        (actionBetaFailureEvent_subset_surface pp family static inputs hvk hI hchar
          badFBeta hcompatBeta)))
      (squeezeSurfaceEvent_prob_le 1 query family.toFamily badFBeta
        (hstab_of_prefixDeterminedAt family.toFamily 1 hdetBeta) hbadBeta)
  · exact le_trans
      (MeasureTheory.measure_mono (Set.preimage_mono
        (actionGammaFailureEvent_subset_surface pp family static inputs hvk hI hchar
          badFGamma hcompatGamma)))
      (squeezeSurfaceEvent_prob_le 2 query family.toFamily badFGamma
        (hstab_of_prefixDeterminedAt family.toFamily 2 hdetGamma) hbadGamma)
  · exact le_trans
      (MeasureTheory.measure_mono (Set.preimage_mono
        (actionThetaFailureEvent_subset_surface pp family static inputs hvk hI hchar
          badFTheta hcompatTheta)))
      (squeezeSurfaceEvent_prob_le 0 query family.toFamily badFTheta
        (hstab_of_prefixDeterminedAt family.toFamily 0 hdetTheta) hbadTheta)

end ActionTerminal

end Zcash.Snark
