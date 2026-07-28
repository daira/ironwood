import Zcash.Snark.Soundness.AGM.StraightLineIpa
import Zcash.Snark.Soundness.Composition.DeployedRuntime
import Zcash.Snark.Soundness.Forking.PinnedRoots

/-!
# Pinned IPA-round roots for the straight-line AGM extractor

`StraightLineIpa.lean` proves the deterministic one-run dichotomy.  This module exposes its
quadratic round events through `PinnedRootFamily`.

The final-output `OracleComp` interface does not record when an AGM representation was emitted.
Consequently `StraightLineIpaOnlineTrace` is the stronger interface boundary here: it exposes a
pre-squeeze polynomial, connects it to the final `AlgebraicWfProof`, and derives
`StraightLineIpaSqueezeInvariance` from its own-squeeze invariance.  Chronology is never inferred
merely from the final proof value.
-/

namespace Zcash.Snark

open Classical Polynomial
open scoped ENNReal

local instance vestaInhabitedStraightLinePinnedRoots : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- The ordinary transcript prefix hashed for one IPA-round challenge. -/
def straightLineIpaRootPoint (family : ComputedAlgebraicFSFamily shape)
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    (p : AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis))
    (j : Fin shape.k) :=
  algebraicFullPrefixes family.init p j

/-- The quadratic bad set computed from the representations and earlier challenges of one run. -/
noncomputable def straightLineIpaRootBad (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (p : AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (j : Fin shape.k) : Set Fp :=
  szBadSet (p.straightLineIpaRootPolynomial
    (fun i => O (algebraicFullPrefixesPre family.init p i))
    (fun r => O (algebraicFullPrefixes family.init p r)) j)

/-- Reprogramming a round's own squeeze answer leaves its prefix-fixed discrepancy polynomial
unchanged. -/
def StraightLineIpaSqueezeInvariance (family : ComputedAlgebraicFSFamily shape) : Prop :=
  forall (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (j : Fin shape.k)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (v : Fp),
    let actual := (family.adversary basis).run O
    let point := straightLineIpaRootPoint family actual j
    let updated := Function.update O point v
    straightLineIpaRootBad family basis ((family.adversary basis).run updated)
        updated j =
      straightLineIpaRootBad family basis actual O j

/-- Representation-carrying trace exposed before each IPA squeeze.  `rootPolynomialBefore` is
computed from the AGM representations emitted up to that stage; `agrees` connects it to the final
proof value, while `invariant` states that changing the not-yet-seen squeeze answer cannot change
the staged polynomial.  This is the chronology interface—the final `AlgebraicWfProof` alone does
not provide it. -/
structure StraightLineIpaOnlineTrace (family : ComputedAlgebraicFSFamily shape) where
  rootPolynomialBefore :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> Fin shape.k ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) -> Polynomial Fp
  agrees : forall (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (j : Fin shape.k)
      (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp),
    rootPolynomialBefore basis j O =
      ((family.adversary basis).run O).straightLineIpaRootPolynomial
        (fun i => O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O) i))
        (fun r => O (algebraicFullPrefixes family.init
          ((family.adversary basis).run O) r)) j
  invariant : forall (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (j : Fin shape.k)
      (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (v : Fp),
    rootPolynomialBefore basis j
        (Function.update O (straightLineIpaRootPoint family
          ((family.adversary basis).run O) j) v) =
      rootPolynomialBefore basis j O

/-- The staged representation trace derives the pinned-squeeze property used by probability
pricing. -/
theorem StraightLineIpaOnlineTrace.toSqueezeInvariance
    (trace : StraightLineIpaOnlineTrace family) :
    StraightLineIpaSqueezeInvariance family := by
  intro basis j O v
  dsimp only
  let actual := (family.adversary basis).run O
  let point := straightLineIpaRootPoint family actual j
  let updated := Function.update O point v
  calc
    straightLineIpaRootBad family basis ((family.adversary basis).run updated) updated j =
        szBadSet (trace.rootPolynomialBefore basis j updated) := by
      unfold straightLineIpaRootBad
      congr 1
      exact (trace.agrees basis j updated).symm
    _ = szBadSet (trace.rootPolynomialBefore basis j O) := by
      rw [trace.invariant basis j O v]
    _ = straightLineIpaRootBad family basis actual O j := by
      unfold straightLineIpaRootBad
      congr 1
      exact trace.agrees basis j O

/-- An algebraic FS family whose IPA representations carry an online squeeze trace. -/
structure ComputedStraightLineIpaFSFamily (shape : Shape)
    extends ComputedAlgebraicFSFamily shape where
  ipaTrace : StraightLineIpaOnlineTrace toComputedAlgebraicFSFamily

namespace ComputedStraightLineIpaFSFamily

/-- Forget the online IPA chronology evidence. -/
abbrev toFamily (family : ComputedStraightLineIpaFSFamily shape) :
    ComputedAlgebraicFSFamily shape := family.toComputedAlgebraicFSFamily

/-- Derived squeeze invariance; unlike a bare final-output assumption, this passes through the
staged representation trace stored by the family. -/
theorem ipaSqueezeInvariance (family : ComputedStraightLineIpaFSFamily shape) :
    StraightLineIpaSqueezeInvariance family.toFamily :=
  family.ipaTrace.toSqueezeInvariance

/-- Every straight-line IPA round root set costs at most two field elements. -/
theorem straightLineIpaRootBad_measure_le (family : ComputedStraightLineIpaFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (p : AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (j : Fin shape.k) :
    uniformChallenge.toOuterMeasure
        (straightLineIpaRootBad family.toFamily basis p O j) <=
      2 / (Fintype.card Fp : ENNReal) := by
  unfold straightLineIpaRootBad
  exact le_trans (uniformChallenge_szBadSet _) <| ENNReal.div_le_div_right
    (by exact_mod_cast ipaDiscrepancyPolynomialAt_natDegree_le
      (p.straightLineInitialDiscrepancy
        (fun i => O (algebraicFullPrefixesPre family.init p i)))
      (p.straightLineRoundDiscrepancies
        (fun i => O (algebraicFullPrefixesPre family.init p i)))
      (List.ofFn fun r => O (algebraicFullPrefixes family.init p r)) j.val) _

/-- The `shape.k` pinned quadratic events for the straight-line IPA layer. -/
noncomputable def pinnedIpaRoots (family : ComputedStraightLineIpaFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    PinnedRootFamily (family.adversary basis) shape.k where
  event j :=
    { point := fun pnu => straightLineIpaRootPoint family.toFamily pnu j
      bad := fun pnu O => straightLineIpaRootBad family.toFamily basis pnu O j
      budget := 2 / (Fintype.card Fp : ENNReal)
      measure_le := fun pnu O => family.straightLineIpaRootBad_measure_le basis pnu O j
      pinned := fun O v => family.ipaSqueezeInvariance basis j O v }

/-- The total direct IPA-round root budget is `2k / |Fp|`. -/
theorem pinnedIpaRoots_budget (family : ComputedStraightLineIpaFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    (∑ j : Fin shape.k, ((family.pinnedIpaRoots basis).event j).budget) =
      shape.k * (2 / (Fintype.card Fp : ENNReal)) := by
  simp [pinnedIpaRoots]

/-- Additive probability price of all straight-line IPA-round roots. -/
theorem pinnedIpaRoots_landing_measure_le
    (family : ComputedStraightLineIpaFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    (PMF.uniformOfFintype
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)).toOuterMeasure
        {O | (family.pinnedIpaRoots basis).Landing O} <=
      (family.Q + 1 : Nat) *
        (shape.k * (2 / (Fintype.card Fp : ENNReal))) := by
  calc
    _ <= (family.Q + 1 : Nat) *
        ∑ j : Fin shape.k, ((family.pinnedIpaRoots basis).event j).budget :=
      (family.pinnedIpaRoots basis).landing_measure_le (family.queryBound basis)
    _ = _ := by rw [family.pinnedIpaRoots_budget basis]

/-- View an augmented `(g,U,W)` relation as a relation over the original public basis. -/
def straightLineCanonicalRelation
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    (relation : AugmentedRelationWitness (F := Fp)
      (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w) :
    AlgebraicRelationWitness (F := Fp) basis := by
  simpa only [augmentedBasis_ursOfAugmentedBasis] using relation.toAlgebraicRelationWitness

/-- The one-run IPA relation finder.  It executes the algebraic adversary once, returns the
explicit relation branch, and leaves quadratic-root runs to `pinnedIpaRoots`. -/
def straightLineIpaRelationFinder (family : ComputedStraightLineIpaFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    let p := (family.adversary basis).run O
    let nu : Fin 11 -> Fp := fun i => O (algebraicFullPrefixesPre family.init p i)
    let chi : Fin shape.k -> Fp := fun j => O (algebraicFullPrefixes family.init p j)
    if hattack : fullAlgebraicBindingAttackZ basis (family.vk basis)
        (family.instanceCommitment basis) p nu chi then
      match p.straightLineBindingAttackZIndexedRootOrRelation nu chi hattack with
      | PSum.inl _ => none
      | PSum.inr relation => some (straightLineCanonicalRelation relation)
    else none

/-- The one-run relation branch reduces to textbook DLOG with the usual programmed-slot loss. -/
theorem straightLineIpaRelation_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedStraightLineIpaFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.straightLineIpaRelationFinder bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (relSetWithCoins B family.straightLineIpaRelationFinder) <=
      bound + 1 / Fintype.card Fp :=
  relationWithCoins_prob_le_of_textbookDL B family.straightLineIpaRelationFinder hDL

/-- Every accepted false opening with `z ≠ 0` either lands in a pinned IPA quadratic or makes the
one-run relation finder return a concrete relation. -/
theorem pinnedIpaRoots_landing_or_relation
    (family : ComputedStraightLineIpaFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (hattack : fullAlgebraicBindingAttackZ basis (family.vk basis)
      (family.instanceCommitment basis) (runProof family.toFamily basis O)
      (runReads family.toFamily basis O) (runRounds family.toFamily basis O)) :
    (family.pinnedIpaRoots basis).Landing O ∨
      (family.straightLineIpaRelationFinder basis O).isSome := by
  let p := runProof family.toFamily basis O
  let nu := runReads family.toFamily basis O
  let chi := runRounds family.toFamily basis O
  cases hsplit : p.straightLineBindingAttackZIndexedRootOrRelation nu chi hattack with
  | inr relation =>
      apply Or.inr
      simp [straightLineIpaRelationFinder, p, nu, chi, hattack, hsplit]
  | inl root =>
      apply Or.inl
      obtain ⟨j, hroot⟩ := root
      refine ⟨j, ?_⟩
      change O (straightLineIpaRootPoint family.toFamily
          ((family.adversary basis).run O) j) ∈
        straightLineIpaRootBad family.toFamily basis
          ((family.adversary basis).run O) O j
      unfold straightLineIpaRootPoint straightLineIpaRootBad
      exact hroot

/-- Scalar-basis/random-oracle pairs on which the one-run algebraic proof is a false accepted
opening with `z ≠ 0`. -/
def straightLineBindingAttackZSet (B : VestaG)
    (family : ComputedStraightLineIpaFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  {q |
    let basis := scalarBasis B q.1
    fullAlgebraicBindingAttackZ basis (family.vk basis)
      (family.instanceCommitment basis) (runProof family.toFamily basis q.2)
      (runReads family.toFamily basis q.2) (runRounds family.toFamily basis q.2)}

/-- The straight-line binding-attack set is contained in the union of pinned quadratic landings
and the explicit one-run relation event. -/
theorem straightLineBindingAttackZSet_subset
    (B : VestaG) (family : ComputedStraightLineIpaFSFamily shape) :
    family.straightLineBindingAttackZSet B <=
      {q | (family.pinnedIpaRoots (scalarBasis B q.1)).Landing q.2} ∪
        (relSetWithCoins B family.straightLineIpaRelationFinder :
          Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
            (BTranscript Fp VestaG
              (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))) := by
  intro q hattack
  rcases family.pinnedIpaRoots_landing_or_relation (scalarBasis B q.1) q.2 hattack with
    hroot | hrelation
  · exact Or.inl hroot
  · apply Or.inr
    simpa [relSetWithCoins] using hrelation

/-- One-run AGM binding at `z ≠ 0`: DLOG plus the programmed-slot loss and `2k` pinned IPA roots,
with no recursive AFK or truncation term. -/
theorem straightLineBindingAttackZ_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedStraightLineIpaFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.straightLineIpaRelationFinder bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineBindingAttackZSet B) <=
      (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (bound + 1 / Fintype.card Fp) := by
  let rootSet : Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    {q | (family.pinnedIpaRoots (scalarBasis B q.1)).Landing q.2}
  let relationSet : Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    relSetWithCoins B family.straightLineIpaRelationFinder
  have hroot : (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        rootSet <=
      (family.Q + 1 : Nat) *
        (shape.k * (2 / (Fintype.card Fp : ENNReal))) := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (family.pinnedIpaRoots (scalarBasis B logs)).Landing O})
    intro logs
    exact family.pinnedIpaRoots_landing_measure_le (scalarBasis B logs)
  have hrelation : (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        relationSet <= bound + 1 / Fintype.card Fp := by
    exact family.straightLineIpaRelation_prob_le_of_textbookDL B hDL
  refine le_trans (MeasureTheory.measure_mono
    (family.straightLineBindingAttackZSet_subset B)) ?_
  exact le_trans (MeasureTheory.measure_union_le rootSet relationSet)
    (add_le_add hroot hrelation)

/-- The full false-opening event, including the separately priced `z = 0` slice. -/
def straightLineBindingAttackSet (B : VestaG)
    (family : ComputedStraightLineIpaFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  {q |
    let basis := scalarBasis B q.1
    fsWinsFull (family.adversary basis)
      (fullAlgebraicBindingAttack basis (family.vk basis)
        (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2}

/-- The `z = 0` portion of the full straight-line binding event. -/
def straightLineBindingZeroSet (B : VestaG)
    (family : ComputedStraightLineIpaFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  {q |
    let basis := scalarBasis B q.1
    fsWinsFull (family.adversary basis)
      (fullAlgebraicBindingAttack basis (family.vk basis)
        (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2 ∧
    q.2 (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run q.2) 10) = 0}

/-- A full binding attack is either the nonzero-`z` event or the adaptive zero slice. -/
theorem straightLineBindingAttackSet_subset
    (B : VestaG) (family : ComputedStraightLineIpaFSFamily shape) :
    family.straightLineBindingAttackSet B <=
      family.straightLineBindingAttackZSet B ∪ family.straightLineBindingZeroSet B := by
  intro q hattack
  let basis := scalarBasis B q.1
  by_cases hz : q.2 (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run q.2) 10) = 0
  · exact Or.inr ⟨hattack, hz⟩
  · exact Or.inl ⟨hattack, hz⟩

/-- The adaptive `z = 0` slice costs one field element with the standard query loss. -/
theorem straightLineBindingZero_prob_le
    (B : VestaG) (family : ComputedStraightLineIpaFSFamily shape) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineBindingZeroSet B) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) := by
  apply uniformOfFintype_prod_fiber_bound_right
    (fun logs =>
      let basis := scalarBasis B logs
      {O | fsWinsFull (family.adversary basis)
          (fullAlgebraicBindingAttack basis (family.vk basis)
            (family.instanceCommitment basis))
          (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) O ∧
        O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O) 10) = 0})
  intro logs
  let basis := scalarBasis B logs
  exact fsAdvantageFull_zero_slice_le (family.adversary basis)
    (fullAlgebraicBindingAttack basis (family.vk basis)
      (family.instanceCommitment basis))
    (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) 10
    (family.queryBound basis)

/-- Straight-line AGM binding capstone.  Compared with the recursive capstone, the extraction
term is the additive `2k` IPA-root budget; there is no AFK expectation or Markov tail. -/
theorem straightLineBindingAttack_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedStraightLineIpaFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.straightLineIpaRelationFinder bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineBindingAttackSet B) <=
      (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (bound + 1 / Fintype.card Fp) := by
  refine le_trans (MeasureTheory.measure_mono
    (family.straightLineBindingAttackSet_subset B)) ?_
  refine le_trans (MeasureTheory.measure_union_le
    (family.straightLineBindingAttackZSet B) (family.straightLineBindingZeroSet B)) ?_
  calc
    _ <= ((family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (bound + 1 / Fintype.card Fp)) +
        (family.Q + 1 : Nat) * (1 / Fintype.card Fp) :=
      add_le_add (family.straightLineBindingAttackZ_prob_le_of_textbookDL B hDL)
        (family.straightLineBindingZero_prob_le B)
    _ = _ := by ring

end ComputedStraightLineIpaFSFamily

end Zcash.Snark
