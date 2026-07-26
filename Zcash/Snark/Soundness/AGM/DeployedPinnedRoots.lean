import Zcash.Snark.Soundness.AGM.DeployedRootDecode
import Zcash.Snark.Soundness.AGM.OnlineMembers
import Zcash.Snark.Soundness.Composition.DeployedRuntime
import Zcash.Snark.Soundness.Forking.PinnedRoots

/-!
# The deployed prefix-pinned AGM root family

This module gives the explicit adapter from rewind-free algebraic batch data to
`PinnedRootFamily`.  The only additional family condition is causal: the corresponding explicit
root set must factor through the transcript prefix before its squeeze.  The generic probability
layer consumes that prefix-indexed set directly, with no caller-supplied rerun equality.  The bad
sets themselves are exactly the two IPA shift polynomials and the deployed `x4`, `x3`, `x2`, and
per-set `x1` polynomials.
-/

namespace Zcash.Snark

open Classical Polynomial
open scoped ENNReal

local instance vestaInhabitedDeployedPinnedRoots : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

attribute [local irreducible] deployedX4PairCount deployedSetQueries
  x4BatchCommitments deployedSetMemberCommitments

/-- Traverse a finite family of computed sum outcomes from left to right.  Either every entry
supplies its left-hand value, or the first right-hand value is returned as data.  In particular,
this does not search a proposition asserting that some right-hand value exists. -/
def finForallOrRelationWitness {n : Nat} {A : Fin n -> Type*} {R : Type*}
    (outcome : forall i, A i ⊕' R) : (forall i, A i) ⊕' R := by
  induction n with
  | zero =>
      exact PSum.inl fun i => Fin.elim0 i
  | succ n ih =>
      cases hhead : outcome 0 with
      | inr relation => exact PSum.inr relation
      | inl head =>
          cases htail : ih (fun i => outcome i.succ) with
          | inr relation => exact PSum.inr relation
          | inl tail => exact PSum.inl (Fin.cases head tail)

/-- Output type of the challenge-read wrapper used by the composition. -/
abbrev WrappedAlgebraicOutput (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :=
  AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) ×
    (Fin (11 + shape.k) -> Fp)

/-- The eleven pre-IPA answers recorded by the wrapped adversary. -/
def wrappedPreIpaReads {family : ComputedAlgebraicFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    (pnu : WrappedAlgebraicOutput family basis) : Fin 11 -> Fp :=
  fun i => pnu.2 (Fin.castAdd shape.k i)

/-- The challenge record relevant to multiopen assembly.  IPA-round challenges do not occur in
this layer, so fixing them to zero matches `AlgebraicWfProof.multiopen_repr` exactly. -/
def wrappedPreIpaRecord {family : ComputedAlgebraicFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    (pnu : WrappedAlgebraicOutput family basis) : Challenges shape.k Fp :=
  chRecord (wrappedPreIpaReads pnu) (fun _ => 0)

/-- The wrapped output's pre-IPA answers are the composition's `runReads`. -/
theorem wrappedPreIpaReads_run (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :
    wrappedPreIpaReads ((wrappedAdversary family basis).run O) = runReads family basis O := by
  funext i
  simp only [wrappedPreIpaReads, wrappedAdversary, OracleComp.run_withReads, runReads, runProof]
  exact congrArg O (Fin.append_left _ _ i)

/-- Rewind-free deployed batches tied to the current wrapped output's canonical aggregate
coordinates. -/
structure DeployedBatchWitness (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family basis) where
  fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)
  canonical : CanonicalOnlineMultiopenCoordinates pnu.1 fixedRepresentations
  membersCovered : DeployedMembersCovered (family.vk basis) (family.instanceCommitment basis)
    pnu.1.algebraicProof fixedRepresentations
  batches : DeployedAlgebraicBatches (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
    (wrappedPreIpaRecord pnu)
    (pnu.1.aMulti (wrappedPreIpaReads pnu))
    (pnu.1.multiU (wrappedPreIpaReads pnu))
    (pnu.1.multiBlind (wrappedPreIpaReads pnu))
  memberCoeffs : forall i
      (hi : i < deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 (wrappedPreIpaRecord pnu)),
    (batches.x1 i hi).coeffs =
      (deployedMemberRepresentationsOfCovered pnu.1 fixedRepresentations membersCovered
        (wrappedPreIpaReads pnu) i hi).coeffs
  memberU : forall i
      (hi : i < deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 (wrappedPreIpaRecord pnu)),
    (batches.x1 i hi).uComp =
      (deployedMemberRepresentationsOfCovered pnu.1 fixedRepresentations membersCovered
        (wrappedPreIpaReads pnu) i hi).uComp
  memberW : forall i
      (hi : i < deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 (wrappedPreIpaRecord pnu)),
    (batches.x1 i hi).wComp =
      (deployedMemberRepresentationsOfCovered pnu.1 fixedRepresentations membersCovered
        (wrappedPreIpaReads pnu) i hi).wComp

/-- Algebraic unbatching either supplies every deployed batch or returns a concrete augmented-basis
relation. -/
abbrev DeployedRootOutcomeProvider (family : ComputedAlgebraicFSFamily shape) :=
  forall (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp),
    DeployedBatchWitness family basis ((wrappedAdversary family basis).run O) ⊕'
      AugmentedRelationWitness (F := Fp)
        (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w

/-- Distinct offline interpolation points for recovering the represented `x4` columns.  The
current challenge is included explicitly, so decoding returns the actual aggregate coordinates. -/
structure DeployedX4InterpolationData
    (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family basis) where
  points : Fin (deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
    pnu.1.proof.1
    (chRecord (wrappedPreIpaReads pnu) (fun _ => 0)) + 1) -> Fp
  pointsInjective : Function.Injective points
  current : Fin (deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
    pnu.1.proof.1
    (chRecord (wrappedPreIpaReads pnu) (fun _ => 0)) + 1)
  currentPoint : points current = wrappedPreIpaReads pnu 8

/-- The deployed shape has enough field elements for offline interpolation whenever its fixed
point-set arity plus one fits in `Fp`.  The construction permutes an arbitrary embedding so that
its first point is the execution's actual `x4` challenge. -/
def deployedX4InterpolationDataOfCapacity
    (family : ComputedAlgebraicFSFamily shape)
    (hcapacity : shape.numPointSets + 1 <= Fintype.card Fp)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family basis) :
    DeployedX4InterpolationData family basis pnu := by
  let count := deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
    pnu.1.proof.1
    (chRecord (wrappedPreIpaReads pnu) (fun _ => 0))
  have hcount : count + 1 <= Fintype.card Fp := by
    exact (Nat.add_le_add_right
      (deployedX4PairCount_le_numPointSets (family.vk basis)
        (family.instanceCommitment basis) pnu.1.proof.1
        (chRecord (wrappedPreIpaReads pnu) (fun _ => 0))) 1).trans hcapacity
  let embedding : Fin (count + 1) ↪ Fp :=
    { toFun := fun i => (i.val : Fp)
      inj' := fun i j hij => Fin.ext (CharP.natCast_injOn_Iio Fp scalarFieldOrder
        (by simpa only [card_Fp] using i.isLt.trans_le hcount)
        (by simpa only [card_Fp] using j.isLt.trans_le hcount)
        hij) }
  let current : Fin (count + 1) := ⟨0, Nat.zero_lt_succ count⟩
  let swap := Equiv.swap (embedding current) (wrappedPreIpaReads pnu 8)
  refine
    { points := fun i => swap (embedding i)
      pointsInjective := swap.injective.comp embedding.injective
      current := current
      currentPoint := ?_ }
  simp [swap]

/-- Construct the complete deployed batch-or-relation outcome from the representations carried by
the actual online AGM execution.  This is an offline algebraic decode: `aMulti` is evaluated at
distinct ghost `x4` values, while every within-set member is resolved from a point representation
that was already available before `x1`.  No accepting execution is rewound. -/
noncomputable def deployedRootOutcomeOfOnline
    (family : ComputedOnlineMemberFSFamily shape)
    (hcapacity : shape.numPointSets + 1 <= Fintype.card Fp) :
    DeployedRootOutcomeProvider family.toFamily := by
  intro basis O
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let p := pnu.1
  let nu := wrappedPreIpaReads pnu
  have hp : p = (family.adversary basis).run O := by
    exact wrappedAdversary_run_fst family.toFamily basis O
  have hcovered : DeployedMembersCovered (family.vk basis)
      (family.instanceCommitment basis) p.algebraicProof
      (family.fixedRepresentations basis) := by
    rw [hp]
    exact family.membersCovered basis O
  have hcanonical : CanonicalOnlineMultiopenCoordinates p
      (family.fixedRepresentations basis) := by
    rw [hp]
    exact family.canonical basis O
  let interpolation :=
    deployedX4InterpolationDataOfCapacity family.toFamily hcapacity basis pnu
  let x4Batch := deployedX4BatchOfRepresentations p nu interpolation.points
    interpolation.pointsInjective interpolation.current interpolation.currentPoint
  let count := deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
    p.proof.1 (wrappedPreIpaRecord pnu)
  let x1Result := fun i : Fin count =>
    deployedX1BatchOfCoveredWithSourceOrRelation p (family.fixedRepresentations basis) hcovered nu
      x4Batch i i.isLt
  cases hall : finForallOrRelationWitness x1Result with
  | inr relation => exact PSum.inr relation
  | inl results =>
      let x1 := fun (i : Nat) (hi : i < count) => (results ⟨i, hi⟩).batch
      have hx1Coeffs : forall i (hi : i < count),
          (x1 i hi).coeffs =
            (deployedMemberRepresentationsOfCovered p
              (family.fixedRepresentations basis) hcovered nu i hi).coeffs := by
        intro i hi
        exact (results ⟨i, hi⟩).coeffs_eq
      have hx1U : forall i (hi : i < count),
          (x1 i hi).uComp =
            (deployedMemberRepresentationsOfCovered p
              (family.fixedRepresentations basis) hcovered nu i hi).uComp := by
        intro i hi
        exact (results ⟨i, hi⟩).uComp_eq
      have hx1W : forall i (hi : i < count),
          (x1 i hi).wComp =
            (deployedMemberRepresentationsOfCovered p
              (family.fixedRepresentations basis) hcovered nu i hi).wComp := by
        intro i hi
        exact (results ⟨i, hi⟩).wComp_eq
      exact PSum.inl
        { fixedRepresentations := family.fixedRepresentations basis
          canonical := hcanonical
          membersCovered := hcovered
          batches :=
            { x4 := x4Batch
              x1 := x1 }
          memberCoeffs := hx1Coeffs
          memberU := hx1U
          memberW := hx1W }

/-- Squeeze index used by one root event: `xi`, `z`, `x4`, `x3`, `x2`, and the union of all
`x1` roots. -/
def deployedRootChallengeIndex (i : Fin 6) : Fin 11 :=
  if i.val = 0 then 9 else if i.val = 1 then 10 else if i.val = 2 then 8
  else if i.val = 3 then 7 else if i.val = 4 then 6 else 5

/-- The oracle point of one deployed root event. -/
noncomputable def deployedRootPoint (family : ComputedAlgebraicFSFamily shape)
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    (pnu : WrappedAlgebraicOutput family basis) (i : Fin 6) :=
  algebraicFullPrefixesPre family.init pnu.1 (deployedRootChallengeIndex i)

/-- Reading a deployed root event's point returns the corresponding recorded challenge. -/
theorem deployedRootPoint_run (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (i : Fin 6) :
    O (deployedRootPoint family ((wrappedAdversary family basis).run O) i) =
      runReads family basis O (deployedRootChallengeIndex i) := by
  simp only [deployedRootPoint, wrappedAdversary_run_fst, runReads, runProof]

/-- Direct budget of one deployed root event. -/
noncomputable def deployedRootEventBudget (shape : Shape)
    (i : Fin 6) : ENNReal :=
  if i.val = 0 then 1 / Fintype.card Fp
  else if i.val = 1 then 1 / Fintype.card Fp
  else if i.val = 2 then
    ((shape.numPointSets + 1 : Nat) : ENNReal) / Fintype.card Fp
  else if i.val = 3 then
    ((max (2 ^ shape.k) (queryBudget shape) + 2 * queryBudget shape : Nat) : ENNReal) /
      Fintype.card Fp
  else if i.val = 4 then
    ((shape.numPointSets * queryBudget shape : Nat) : ENNReal) / Fintype.card Fp
  else
    ((shape.numPointSets * queryBudget shape * queryBudget shape : Nat) : ENNReal) /
      Fintype.card Fp

/-- The exact bad-root set for one event.  A relation outcome needs no bad-root charge because it
is already a successful algebraic extraction. -/
noncomputable def deployedRootBad (family : ComputedAlgebraicFSFamily shape)
    (outcome : DeployedRootOutcomeProvider family)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (_pnu : WrappedAlgebraicOutput family basis)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (i : Fin 6) : Set Fp :=
  let pnu := (wrappedAdversary family basis).run O
  match outcome basis O with
  | PSum.inr _ => ∅
  | PSum.inl witness =>
      let p := pnu.1
      let nu := wrappedPreIpaReads pnu
      let ch := wrappedPreIpaRecord pnu
      let batches := witness.batches
      if i.val = 0 then
        ↑(szBadSet (ipaShiftXiPolynomial
          (commitGen (evalVector shape.k ch.x3) (p.aMulti nu) -
            multiopenValue (family.vk basis) (family.instanceCommitment basis) p.proof.1 ch)
          (commitGen (evalVector shape.k ch.x3) p.s)))
      else if i.val = 1 then
        ↑(szBadSet (ipaShiftZPolynomial
          (commitGen (evalVector shape.k ch.x3) (p.aMulti nu) -
            multiopenValue (family.vk basis) (family.instanceCommitment basis) p.proof.1 ch)
          (p.multiU nu) p.sU (commitGen (evalVector shape.k ch.x3) p.s) ch.xi))
      else if i.val = 2 then
        deployedX4RootSet (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) p.proof.1 ch batches
      else if i.val = 3 then
        deployedX3RootSet (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) p.proof.1 ch batches
      else if i.val = 4 then
        deployedX2RootSet (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) p.proof.1 ch batches
      else
        deployedX1AllRootSet (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) p.proof.1 ch batches

/-- Every explicit bad set has its advertised direct Schwartz--Zippel price. -/
theorem deployedRootBad_measure_le (family : ComputedAlgebraicFSFamily shape)
    (outcome : DeployedRootOutcomeProvider family)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family basis)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (i : Fin 6) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        (deployedRootBad family outcome basis pnu O i) <= deployedRootEventBudget shape i := by
  let actual := (wrappedAdversary family basis).run O
  change (PMF.uniformOfFintype Fp).toOuterMeasure
      (deployedRootBad family outcome basis actual O i) <= deployedRootEventBudget shape i
  cases hout : outcome basis O with
  | inl witness =>
    simp only [deployedRootBad, hout]
    by_cases h0 : i.val = 0
    · simpa [h0, deployedRootEventBudget, uniformChallenge] using
        ipaShiftXi_badSet_measure_le
          (commitGen (evalVector shape.k (wrappedPreIpaRecord actual).x3)
              (actual.1.aMulti (wrappedPreIpaReads actual)) -
            multiopenValue (family.vk basis) (family.instanceCommitment basis)
              actual.1.proof.1 (wrappedPreIpaRecord actual))
          (commitGen (evalVector shape.k (wrappedPreIpaRecord actual).x3) actual.1.s)
    by_cases h1 : i.val = 1
    · simpa [h0, h1, deployedRootEventBudget, uniformChallenge] using
        ipaShiftZ_badSet_measure_le
          (commitGen (evalVector shape.k (wrappedPreIpaRecord actual).x3)
              (actual.1.aMulti (wrappedPreIpaReads actual)) -
            multiopenValue (family.vk basis) (family.instanceCommitment basis)
              actual.1.proof.1 (wrappedPreIpaRecord actual))
          (actual.1.multiU (wrappedPreIpaReads actual)) actual.1.sU
          (commitGen (evalVector shape.k (wrappedPreIpaRecord actual).x3) actual.1.s)
          (wrappedPreIpaRecord actual).xi
    by_cases h2 : i.val = 2
    · simpa [h0, h1, h2, deployedRootEventBudget, uniformChallenge] using
        deployedX4RootSet_measure_le_shape (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) actual.1.proof.1
          (wrappedPreIpaRecord actual) witness.batches
    by_cases h3 : i.val = 3
    · simpa [h0, h1, h2, h3, deployedRootEventBudget, uniformChallenge] using
        deployedX3RootSet_measure_le_shape (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) actual.1.proof.1
          (wrappedPreIpaRecord actual) witness.batches
    by_cases h4 : i.val = 4
    · simpa [h0, h1, h2, h3, h4, deployedRootEventBudget, uniformChallenge] using
        deployedX2RootSet_measure_le_shape (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) actual.1.proof.1
          (wrappedPreIpaRecord actual) witness.batches
    · simpa [h0, h1, h2, h3, h4, deployedRootEventBudget, uniformChallenge] using
        deployedX1AllRootSet_measure_le (ursOfAugmentedBasis shape.k basis) rfl
          (family.vk basis) (family.instanceCommitment basis) actual.1.proof.1
          (wrappedPreIpaRecord actual) witness.batches
  | inr relation => simp [deployedRootBad, hout, deployedRootEventBudget]

/-- The event budgets sum to the conservative shape budget. -/
theorem deployedRootEventBudget_sum_le (shape : Shape) :
    (∑ i : Fin 6, deployedRootEventBudget shape i) <=
      algebraicRootBudget shape shape.k := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num [deployedRootEventBudget, algebraicRootBudget]
  simp only [div_eq_mul_inv]
  ring_nf
  exact le_rfl

/-- The exact causal condition for deployed root data: two executions with the same transcript
prefix before a squeeze induce the same bad-root set for that squeeze.

This is strictly a prefix-factorization property.  It neither compares hindsight-selected AGM
representations after changing a challenge nor treats a final-output equality as chronology. -/
def DeployedRootPrefixDetermined (family : ComputedAlgebraicFSFamily shape)
    (outcome : DeployedRootOutcomeProvider family) : Prop :=
  forall basis (i : Fin 6) O O',
    deployedRootPoint family ((wrappedAdversary family basis).run O) i =
        deployedRootPoint family ((wrappedAdversary family basis).run O') i ->
      deployedRootBad family outcome basis ((wrappedAdversary family basis).run O) O i =
        deployedRootBad family outcome basis ((wrappedAdversary family basis).run O') O' i

/-- Attach a deployed bad-root set to its transcript prefix.  On an unreachable prefix the set is
empty; on a reachable prefix it is taken from one execution reaching that prefix.  Prefix
determinism makes the choice observationally irrelevant. -/
noncomputable def deployedRootBadAt (family : ComputedAlgebraicFSFamily shape)
    (outcome : DeployedRootOutcomeProvider family)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (i : Fin 6)
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k)) : Set Fp :=
  if h : exists O,
      deployedRootPoint family ((wrappedAdversary family basis).run O) i = t then
    let O := Classical.choose h
    deployedRootBad family outcome basis ((wrappedAdversary family basis).run O) O i
  else ∅

/-- Every prefix-indexed deployed root set inherits the direct root budget of the corresponding
explicit polynomial. -/
theorem deployedRootBadAt_measure_le (family : ComputedAlgebraicFSFamily shape)
    (outcome : DeployedRootOutcomeProvider family)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (i : Fin 6)
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k)) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        (deployedRootBadAt family outcome basis i t) <= deployedRootEventBudget shape i := by
  classical
  unfold deployedRootBadAt
  split
  · exact deployedRootBad_measure_le family outcome basis
      ((wrappedAdversary family basis).run (Classical.choose ‹_›))
      (Classical.choose ‹_›) i
  · simp

/-- A prefix-determined family agrees with its prefix-indexed bad set on every actual run. -/
theorem deployedRootBadAt_point
    (family : ComputedAlgebraicFSFamily shape)
    (outcome : DeployedRootOutcomeProvider family)
    (hprefix : DeployedRootPrefixDetermined family outcome)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (i : Fin 6)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :
    deployedRootBadAt family outcome basis i
        (deployedRootPoint family ((wrappedAdversary family basis).run O) i) =
      deployedRootBad family outcome basis ((wrappedAdversary family basis).run O) O i := by
  classical
  unfold deployedRootBadAt
  split
  · apply hprefix basis i (Classical.choose ‹_›) O
    exact Classical.choose_spec ‹_›
  · exfalso
    apply ‹¬ _›
    exact ⟨O, rfl⟩

/-- Constructive chronology certificate for the six deployed root events.  A schedule supplies
the bad set as data indexed by the transcript prefix, together with its direct measure bound and
its equality to the algebraically derived set on every actual run.  The probability layer consumes
this object directly; it no longer stores a free final-output invariance proposition. -/
structure DeployedRootPrefixSchedule (family : ComputedAlgebraicFSFamily shape)
    (outcome : DeployedRootOutcomeProvider family) where
  badAt : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> (i : Fin 6) ->
    BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Set Fp
  measure_le : forall basis i t,
    (PMF.uniformOfFintype Fp).toOuterMeasure (badAt basis i t) <=
      deployedRootEventBudget shape i
  at_point : forall basis i O,
    badAt basis i (deployedRootPoint family ((wrappedAdversary family basis).run O) i) =
      deployedRootBad family outcome basis ((wrappedAdversary family basis).run O) O i

/-- Compatibility adapter from the older equality-style chronology premise.  New concrete
families should preferably construct `DeployedRootPrefixSchedule` at the transcript stage where
each bad set is fixed. -/
noncomputable def DeployedRootPrefixSchedule.ofPrefixDetermined
    (family : ComputedAlgebraicFSFamily shape)
    (outcome : DeployedRootOutcomeProvider family)
    (hprefix : DeployedRootPrefixDetermined family outcome) :
    DeployedRootPrefixSchedule family outcome where
  badAt := deployedRootBadAt family outcome
  measure_le := deployedRootBadAt_measure_le family outcome
  at_point := deployedRootBadAt_point family outcome hprefix

/-- An online AGM family carrying a concrete batch-or-relation outcome whose exact root data
factors through the transcript prefix before each squeeze.  The structure stores the outcome as
data, but does not by itself prove that a particular constructor computes it. -/
structure ComputedDeployedRootFSFamily (shape : Shape)
    extends ComputedOnlineMemberFSFamily shape where
  outcome : DeployedRootOutcomeProvider toComputedAlgebraicFSFamily
  schedule : DeployedRootPrefixSchedule toComputedAlgebraicFSFamily outcome

/-- Mathematical compatibility adapter using the offline Vandermonde decoder.  This constructor is
intentionally `noncomputable`: it proves the batch-or-relation dichotomy, but does not by itself
instantiate an executable DLOG adversary.  A concrete-security capstone must instead supply the
same outcome through a computable direct-coordinate implementation.

The sole remaining multiopen-specific proof is that the exact root data factors through the
preceding transcript prefix; the outcome itself is no longer caller-supplied.

The exact deployed root sets also read ordinary proof-string scalars and grouping data.  The
final-output `OracleComp` interface does not encode when those fields were emitted, so deriving
their chronology from output equality would be unsound.  The compatibility constructor below
accepts the old factorization theorem and packages it as the concrete schedule consumed by the
probability layer.

TODO(#96): replace the compatibility adapter by direct algebraic columns, construct
`DeployedRootPrefixSchedule` from the deployed Rust transcript stages, and compose the resulting
computable constraint endpoint into the final concrete `constraintsBadAccept` capstone.  #96 must
complete that replacement before claiming a concrete executable DLOG solver. -/
noncomputable def ComputedDeployedRootFSFamily.ofOnline
    (family : ComputedOnlineMemberFSFamily shape)
    (hcapacity : shape.numPointSets + 1 <= Fintype.card Fp)
    (hprefix : DeployedRootPrefixDetermined family.toFamily
      (deployedRootOutcomeOfOnline family hcapacity)) :
    ComputedDeployedRootFSFamily shape where
  toComputedOnlineMemberFSFamily := family
  outcome := deployedRootOutcomeOfOnline family hcapacity
  schedule := DeployedRootPrefixSchedule.ofPrefixDetermined family.toFamily
    (deployedRootOutcomeOfOnline family hcapacity) hprefix

/-- Schedule-aware mathematical adapter.  Supplying the schedule closes chronology, but the
Vandermonde-based outcome remains noncomputable for the reason documented on `ofOnline`. -/
noncomputable def ComputedDeployedRootFSFamily.ofScheduledOnline
    (family : ComputedOnlineMemberFSFamily shape)
    (hcapacity : shape.numPointSets + 1 <= Fintype.card Fp)
    (schedule : DeployedRootPrefixSchedule family.toFamily
      (deployedRootOutcomeOfOnline family hcapacity)) :
    ComputedDeployedRootFSFamily shape where
  toComputedOnlineMemberFSFamily := family
  outcome := deployedRootOutcomeOfOnline family hcapacity
  schedule := schedule

namespace ComputedDeployedRootFSFamily

/-- Forget the tighter root data. -/
abbrev toFamily (family : ComputedDeployedRootFSFamily shape) :
    ComputedAlgebraicFSFamily shape := family.toComputedAlgebraicFSFamily

/-- The complete relation producer used by the rewind-free deployed layer.

The recursive extractor's `relationFinder` already preserves both its direct relation branch and
the clean-opening collision branch.  The only additional relation introduced by algebraic
multiopen unbatching is the `outcome` relation.  Keeping both branches in one data-returning finder
is essential: demoting the latter to the bare proposition `HasNontrivialRelation` would make a
terminal `witness ∨ relation` predicate vacuous in a prime-order group and would not charge the
new branch to DLOG.

This declaration is computable relative to `family.outcome`.  Instantiating `family` with either
noncomputable compatibility constructor above does not establish an executable DLOG solver; #96
must supply a computable direct-coordinate outcome before applying a concrete DLOG assumption. -/
def deployedRelationFinder (family : ComputedDeployedRootFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis coins =>
    match family.toFamily.relationFinder basis coins with
    | some relation => some relation
    | none =>
        match family.outcome basis coins.1 with
        | PSum.inl _ => none
        | PSum.inr relation =>
            some (augmentedBasis_ursOfAugmentedBasis shape.k basis ▸
              relation.toAlgebraicRelationWitness)

/-- The complete deployed relation event: the combined finder returns an explicit relation on this
run.  Its concrete executability has the same relative boundary as `deployedRelationFinder`. -/
def deployedRelationEvent (family : ComputedDeployedRootFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins) :=
  {p | (family.deployedRelationFinder p.1 p.2).isSome}

/-- Conditional textbook single-instance DLOG pricing for every relation branch introduced by the
recursive and rewind-free multiopen extractors.  The hypothesis applies to the concrete finder
stored in `family`; using a noncomputable compatibility-constructed family does not discharge that
premise.  Once the finder is computably instantiated, the only reduction loss here is the existing
augmented-basis cardinality factor. -/
theorem deployedRelation_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedDeployedRootFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.deployedRelationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) -> Fp) × family.toFamily.Coins)).toOuterMeasure
        (relSetWithCoins B family.deployedRelationFinder)
      <= Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound :=
  relationWithCoins_prob_le_of_textbookDL B family.deployedRelationFinder hDL

/-- Transfer the complete relation event across a uniform-URS basis identification. -/
theorem deployedRelation_prob_eq_of_uniformURS {Omega : Type*} (setup : PMF Omega)
    (B : VestaG) (family : ComputedDeployedRootFSFamily shape)
    (basisOf : Omega -> AugmentedIndex (2 ^ shape.k) -> VestaG)
    (hURS : OrchardUniformURSIdentification setup shape.k B basisOf) :
    (independentProductPMF setup
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹' family.deployedRelationEvent) =
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) -> Fp) × family.toFamily.Coins)).toOuterMeasure
        (relSetWithCoins B family.deployedRelationFinder) := by
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
      p.toOuterMeasure family.deployedRelationEvent) hprod
  change ((independentProductPMF setup coinPMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure family.deployedRelationEvent =
    ((independentProductPMF
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF).map
        (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure
          family.deployedRelationEvent at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  calc
    _ = (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF).toOuterMeasure
          ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' family.deployedRelationEvent) := hmeasure
    _ = (PMF.uniformOfFintype
          ((AugmentedIndex (2 ^ shape.k) -> Fp) × family.toFamily.Coins)).toOuterMeasure
          (relSetWithCoins B family.deployedRelationFinder) := by
      rw [independentProductPMF_uniform]
      congr 1
      ext p
      simp only [Set.mem_preimage, deployedRelationEvent, Set.mem_setOf_eq, relSetWithCoins,
        Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Generator-random-oracle form of the complete deployed relation bound. -/
theorem deployedRelation_prob_le_of_generatorRO_textbookDL
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.deployedRelationFinder bound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.deployedRelationEvent)
      <= Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound := by
  rw [family.deployedRelation_prob_eq_of_uniformURS
    (orchardGeneratorROSetup query) B (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery)]
  exact family.deployedRelation_prob_le_of_textbookDL B hDL

/-- The concrete deployed root events, ready for the additive coupling theorem. -/
noncomputable def pinnedRoots (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    PinnedRootFamily (wrappedAdversary family.toFamily basis) 6 where
  event i :=
    { point := fun pnu => deployedRootPoint family.toFamily pnu i
      badAt := family.schedule.badAt basis i
      budget := deployedRootEventBudget shape i
      measure_le := family.schedule.measure_le basis i }

/-- The six good-root facts exposed when the concrete root family does not land. -/
structure DeployedGoodRoots (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O)) : Prop where
  xi : wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O) 9 ∉
    deployedRootBad family.toFamily family.outcome basis
      ((wrappedAdversary family.toFamily basis).run O) O 0
  z : wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O) 10 ∉
    deployedRootBad family.toFamily family.outcome basis
      ((wrappedAdversary family.toFamily basis).run O) O 1
  x4 : wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O) 8 ∉
    deployedRootBad family.toFamily family.outcome basis
      ((wrappedAdversary family.toFamily basis).run O) O 2
  x3 : wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O) 7 ∉
    deployedRootBad family.toFamily family.outcome basis
      ((wrappedAdversary family.toFamily basis).run O) O 3
  x2 : wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O) 6 ∉
    deployedRootBad family.toFamily family.outcome basis
      ((wrappedAdversary family.toFamily basis).run O) O 4
  x1 : wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O) 5 ∉
    deployedRootBad family.toFamily family.outcome basis
      ((wrappedAdversary family.toFamily basis).run O) O 5

/-- Non-landing of the concrete family is exactly goodness of all six explicit root sets. -/
theorem goodRoots_of_not_landing (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O))
    (_hout : family.outcome basis O =
      PSum.inl witness)
    (hnot : ¬(family.pinnedRoots basis).Landing O) :
    DeployedGoodRoots family basis O witness := by
  have hgood (i : Fin 6) : ¬((family.pinnedRoots basis).event i).Landing O := by
    intro hi
    exact hnot ⟨i, hi⟩
  have hroot (i : Fin 6) :
      wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O)
          (deployedRootChallengeIndex i) ∉
        deployedRootBad family.toFamily family.outcome basis
          ((wrappedAdversary family.toFamily basis).run O) O i := by
    have hi := hgood i
    change O (deployedRootPoint family.toFamily
        ((wrappedAdversary family.toFamily basis).run O) i) ∉
      family.schedule.badAt basis i
        (deployedRootPoint family.toFamily
          ((wrappedAdversary family.toFamily basis).run O) i) at hi
    rw [family.schedule.at_point basis i O] at hi
    have hpoint := deployedRootPoint_run family.toFamily basis O i
    rw [hpoint] at hi
    simpa [wrappedPreIpaReads_run] using hi
  refine { xi := ?_, z := ?_, x4 := ?_, x3 := ?_, x2 := ?_, x1 := ?_ }
  · simpa [deployedRootChallengeIndex] using hroot (0 : Fin 6)
  · simpa [deployedRootChallengeIndex] using hroot (1 : Fin 6)
  · simpa [deployedRootChallengeIndex] using hroot (2 : Fin 6)
  · simpa [deployedRootChallengeIndex] using hroot (3 : Fin 6)
  · simpa [deployedRootChallengeIndex] using hroot (4 : Fin 6)
  · simpa [deployedRootChallengeIndex] using hroot (5 : Fin 6)

/-- The root family's total direct budget is `algebraicRootBudget`. -/
theorem pinnedRoots_budget_le (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    (∑ i : Fin 6, ((family.pinnedRoots basis).event i).budget) <=
      algebraicRootBudget shape shape.k :=
  deployedRootEventBudget_sum_le shape

end ComputedDeployedRootFSFamily

end Zcash.Snark
