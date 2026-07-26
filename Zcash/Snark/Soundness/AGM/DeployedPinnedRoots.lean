import Zcash.Snark.Soundness.AGM.DeployedRootDecode
import Zcash.Snark.Soundness.AGM.OnlineMembers
import Zcash.Snark.Soundness.Composition.DeployedRuntime
import Zcash.Snark.Soundness.Forking.PinnedRoots

/-!
# The deployed prefix-pinned AGM root family

This module gives the explicit adapter from rewind-free algebraic batch data to
`PinnedRootFamily`.  The only additional family condition is causal: recomputing the adversary
after replacing one squeeze answer must leave the corresponding explicit root set unchanged.
The bad sets themselves are not abstract; they are exactly the two IPA shift polynomials and the
deployed `x4`, `x3`, `x2`, and per-set `x1` polynomials.
-/

namespace Zcash.Snark

open Classical Polynomial
open scoped ENNReal

local instance vestaInhabitedDeployedPinnedRoots : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

attribute [local irreducible] deployedX4PairCount deployedSetQueries
  x4BatchCommitments deployedSetMemberCommitments

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
  batches : DeployedAlgebraicBatches (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
    (wrappedPreIpaRecord pnu)
    (pnu.1.aMulti (wrappedPreIpaReads pnu))
    (pnu.1.multiU (wrappedPreIpaReads pnu))
    (pnu.1.multiBlind (wrappedPreIpaReads pnu))

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
noncomputable def deployedX4InterpolationDataOfCapacity
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
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_fin] using hcount))
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
  let interpolation :=
    deployedX4InterpolationDataOfCapacity family.toFamily hcapacity basis pnu
  let x4Batch := deployedX4BatchOfRepresentations p nu interpolation.points
    interpolation.pointsInjective interpolation.current interpolation.currentPoint
  let x1Result := fun (i : Nat)
      (hi : i < deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
        p.proof.1
        (wrappedPreIpaRecord pnu)) =>
    deployedX1BatchOfCoveredOrRelation p (family.fixedRepresentations basis) hcovered nu
      x4Batch i hi
  by_cases hrelation : exists i hi, exists relation, x1Result i hi = PSum.inr relation
  · let i := Classical.choose hrelation
    have hiExists := Classical.choose_spec hrelation
    let hi := Classical.choose hiExists
    have relationExists := Classical.choose_spec hiExists
    let relation := Classical.choose relationExists
    exact PSum.inr relation
  · let x1 := fun (i : Nat)
        (hi : i < deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
          p.proof.1
          (wrappedPreIpaRecord pnu)) =>
        match hresult : x1Result i hi with
        | PSum.inl batch => batch
        | PSum.inr relation => False.elim (hrelation ⟨i, hi, relation, hresult⟩)
    exact PSum.inl
      { batches :=
          { x4 := x4Batch
            x1 := x1 } }

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

/-- A computed online AGM family with a concrete batch-or-relation outcome and proofs that each
explicit root set is pinned before its own squeeze. -/
structure ComputedDeployedRootFSFamily (shape : Shape)
    extends ComputedOnlineMemberFSFamily shape where
  outcome : DeployedRootOutcomeProvider toComputedAlgebraicFSFamily
  rootPinned : forall basis (i : Fin 6) O v,
    deployedRootBad toComputedAlgebraicFSFamily outcome basis
        ((wrappedAdversary toComputedAlgebraicFSFamily basis).run
          (Function.update O
            (deployedRootPoint toComputedAlgebraicFSFamily
              ((wrappedAdversary toComputedAlgebraicFSFamily basis).run O) i) v))
        (Function.update O
          (deployedRootPoint toComputedAlgebraicFSFamily
            ((wrappedAdversary toComputedAlgebraicFSFamily basis).run O) i) v) i =
      deployedRootBad toComputedAlgebraicFSFamily outcome basis
        ((wrappedAdversary toComputedAlgebraicFSFamily basis).run O) O i

/-- Upgrade an online, member-covered AGM family using the derived offline batch-or-relation
decoder.  The sole remaining multiopen-specific proof is causal root pinning; the outcome itself is
no longer caller-supplied.

`OnlineMultiopenPinned` alone intentionally does not discharge `hrootPinned`.  It pins the AGM
representations named by that interface, while the exact deployed root sets also read ordinary
proof-string scalars and grouping data.  The final-output `OracleComp` interface does not encode
when those fields were emitted, so deriving their chronology would be unsound.  A concrete family
must provide this equality from a strengthened online transcript interface (whose schedule is then
matched to the Rust transcript order). -/
noncomputable def ComputedDeployedRootFSFamily.ofOnline
    (family : ComputedOnlineMemberFSFamily shape)
    (hcapacity : shape.numPointSets + 1 <= Fintype.card Fp)
    (hrootPinned : forall basis (i : Fin 6) O v,
      deployedRootBad family.toFamily (deployedRootOutcomeOfOnline family hcapacity) basis
          ((wrappedAdversary family.toFamily basis).run
            (Function.update O
              (deployedRootPoint family.toFamily
                ((wrappedAdversary family.toFamily basis).run O) i) v))
          (Function.update O
            (deployedRootPoint family.toFamily
              ((wrappedAdversary family.toFamily basis).run O) i) v) i =
        deployedRootBad family.toFamily (deployedRootOutcomeOfOnline family hcapacity) basis
          ((wrappedAdversary family.toFamily basis).run O) O i) :
    ComputedDeployedRootFSFamily shape where
  toComputedOnlineMemberFSFamily := family
  outcome := deployedRootOutcomeOfOnline family hcapacity
  rootPinned := hrootPinned

namespace ComputedDeployedRootFSFamily

/-- Forget the tighter root data. -/
abbrev toFamily (family : ComputedDeployedRootFSFamily shape) :
    ComputedAlgebraicFSFamily shape := family.toComputedAlgebraicFSFamily

/-- The concrete deployed root events, ready for the additive coupling theorem. -/
noncomputable def pinnedRoots (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    PinnedRootFamily (wrappedAdversary family.toFamily basis) 6 where
  event i :=
    { point := fun pnu => deployedRootPoint family.toFamily pnu i
      bad := fun pnu O => deployedRootBad family.toFamily family.outcome basis pnu O i
      budget := deployedRootEventBudget shape i
      pinned := family.rootPinned basis i
      measure_le := fun pnu O =>
        deployedRootBad_measure_le family.toFamily family.outcome basis pnu O i }

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
      deployedRootBad family.toFamily family.outcome basis
        ((wrappedAdversary family.toFamily basis).run O) O i at hi
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
