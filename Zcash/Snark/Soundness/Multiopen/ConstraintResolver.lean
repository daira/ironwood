import Mathlib
import Zcash.Snark.Soundness.LookupInstantiation
import Zcash.Snark.Soundness.Multiopen.NodeBinding

/-!
# Routing decoded multiopen members into constraint polynomials

`OpenedMemberDecode` recovers one polynomial for every member of every deployed point set, while
the constraint layer names polynomials by `CommitmentId`.  This file is the small adapter between
those two views:

* `DeployedMemberSlot` is a valid `(point set, member)` position in the deployed grouping;
* `decodedPolynomialResolver` turns a partial `CommitmentId` routing into the total resolver used
  by `constraintModelOfResolver` (unrouted identifiers map to zero);
* `decodedPolynomialResolver_opens_or_relation` converts member-node binding and routing
  faithfulness into the uniform assembled-query opening fact, retaining the binding reduction's
  `HasNontrivialRelation` alternative;
* `eval_lookupEntriesOfDecodedResolver_or_relation` feeds that fact directly into the lookup
  instantiation layer.

The adapter is generic in the verification key and proof string.  It does not select a concrete
Ironwood verification key or duplicate the nested-fork probability argument that produces
member-node binding.
-/

namespace Zcash.Snark

open Polynomial

set_option maxHeartbeats 20000

variable {G : Type*} [AddCommGroup G] [Module Fp G]
variable {shape : Shape} (instanceCommitment : Fin shape.numProofs → ℕ → G)

/-- A valid position in an abstract list of member lists.  Keeping this small dependent index
generic avoids unfolding the deployed verifier while elaborating the structure itself. -/
structure MemberSlot (setCount : ℕ) (memberCount : ℕ → ℕ) where
  setIndex : ℕ
  setIndex_lt : setIndex < setCount
  memberIndex : Fin (memberCount setIndex)

/-- A valid decoded member position in the deployed multiopen grouping. -/
abbrev DeployedMemberSlot [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) :=
  MemberSlot
    (deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch)
    (fun i =>
      (deployedSetQueries (instanceCommitment := instanceCommitment) vk ps ch i).length)

/-- The polynomial decoded at a valid deployed member slot. -/
noncomputable def decodedMemberPolynomial [DecidableEq G] [Inhabited G]
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments (instanceCommitment := instanceCommitment) urs hk vk ps ch)
      (x4BatchEvals (instanceCommitment := instanceCommitment) vk ps ch) a₀ pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch),
      OpenedMemberDecode (instanceCommitment := instanceCommitment)
        urs hk vk ps ch pbatch i hi)
    (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch) :
    Polynomial Fp :=
  coeffsToPoly
    ((memberDecode slot.setIndex slot.setIndex_lt).cols slot.memberIndex)

/-- Resolve a commitment identity to its decoded member polynomial.  The resolver is total because
the constraint model is total; identities outside the routed query block use the zero polynomial. -/
noncomputable def decodedPolynomialResolver [DecidableEq G] [Inhabited G]
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments (instanceCommitment := instanceCommitment) urs hk vk ps ch)
      (x4BatchEvals (instanceCommitment := instanceCommitment) vk ps ch) a₀ pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch),
      OpenedMemberDecode (instanceCommitment := instanceCommitment)
        urs hk vk ps ch pbatch i hi)
    (route : CommitmentId →
      Option (DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)) :
    CommitmentId → Polynomial Fp :=
  fun id =>
    match route id with
    | some slot =>
        decodedMemberPolynomial (instanceCommitment := instanceCommitment)
          urs hk vk ps ch memberDecode slot
    | none => 0

/-- The claimed value stored by the deployed grouping for a member at a point of its point set. -/
noncomputable def deployedMemberClaim [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)
    (point : Fp) : Fp :=
  ((deployedSetQueries (instanceCommitment := instanceCommitment) vk ps ch
      slot.setIndex).getD (slot.memberIndex : ℕ) (.point 0, [])).2.getD
    (((constructIntermediateSets
      (assembleQueries vk instanceCommitment ps ch)).points.getD slot.setIndex []).idxOf point) 0

/-- Generic routing evidence for a claimed opening.  Like `MemberSlot`, this stays independent of
the deployed definitions so its projections elaborate without unfolding the verifier. -/
structure RoutedClaim {Slot Id Point Value : Type*}
    (route : Id → Option Slot) (id : Id) (point : Point) (value : Value)
    (pointMem : Slot → Point → Prop) (claim : Slot → Point → Value) where
  slot : Slot
  route_eq : route id = some slot
  point_mem : pointMem slot point
  claim_eq : claim slot point = value

/-- Routing evidence for one verifier query: its commitment ID selects a decoded member, its point
belongs to that member's point set, and the grouped claimed value there is the query's value. -/
abbrev DeployedQueryRoute [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (route : CommitmentId →
      Option (DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch))
    (q : VerifierQuery shape.k Fp G) :=
  RoutedClaim route q.commId q.point q.eval
    (fun slot point =>
      point ∈ deployedSetPts (instanceCommitment := instanceCommitment)
        vk ps ch slot.setIndex)
    (deployedMemberClaim (instanceCommitment := instanceCommitment) vk ps ch)

/-- If every routed member is node-bound, the decoded resolver opens every query in `queries`;
otherwise the existing augmented-basis relation branch is retained. -/
theorem decodedPolynomialResolver_opens_or_relation [DecidableEq G] [Inhabited G]
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments (instanceCommitment := instanceCommitment) urs hk vk ps ch)
      (x4BatchEvals (instanceCommitment := instanceCommitment) vk ps ch) a₀ pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch),
      OpenedMemberDecode (instanceCommitment := instanceCommitment)
        urs hk vk ps ch pbatch i hi)
    (route : CommitmentId →
      Option (DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch))
    (queries : List (VerifierQuery shape.k Fp G))
    (hrouted : ∀ q ∈ queries,
      DeployedQueryRoute (instanceCommitment := instanceCommitment) vk ps ch route q)
    (hbind : ∀
      (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)
      (point : Fp),
      point ∈ deployedSetPts (instanceCommitment := instanceCommitment) vk ps ch slot.setIndex →
      (decodedMemberPolynomial (instanceCommitment := instanceCommitment)
          urs hk vk ps ch memberDecode slot).eval point
          = deployedMemberClaim (instanceCommitment := instanceCommitment)
              vk ps ch slot point
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w) :
    (∀ q ∈ queries,
      (decodedPolynomialResolver (instanceCommitment := instanceCommitment)
        urs hk vk ps ch memberDecode route q.commId).eval q.point = q.eval)
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  classical
  by_cases hrel : HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
  · exact Or.inr hrel
  · refine Or.inl (fun q hq => ?_)
    have hroute := hrouted q hq
    have hb := hbind hroute.slot q.point hroute.point_mem
    rw [decodedPolynomialResolver, hroute.route_eq]
    exact (hb.resolve_right hrel).trans hroute.claim_eq

/-- The decoded-member bridge specialized to the lookup instantiation: either all coherent lookup
entries evaluate to the proof's five claimed lookup values, or commitment binding has produced a
nontrivial augmented-basis relation. -/
theorem eval_lookupEntriesOfDecodedResolver_or_relation
    [DecidableEq G] [Inhabited G]
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments (instanceCommitment := instanceCommitment) urs hk vk ps ch)
      (x4BatchEvals (instanceCommitment := instanceCommitment) vk ps ch) a₀ pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch),
      OpenedMemberDecode (instanceCommitment := instanceCommitment)
        urs hk vk ps ch pbatch i hi)
    (route : CommitmentId →
      Option (DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch))
    (hrouted : ∀ q ∈ assembleQueries vk instanceCommitment ps ch,
      DeployedQueryRoute (instanceCommitment := instanceCommitment) vk ps ch route q)
    (hbind : ∀
      (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch)
      (point : Fp),
      point ∈ deployedSetPts (instanceCommitment := instanceCommitment) vk ps ch slot.setIndex →
      (decodedMemberPolynomial (instanceCommitment := instanceCommitment)
          urs hk vk ps ch memberDecode slot).eval point
          = deployedMemberClaim (instanceCommitment := instanceCommitment)
              vk ps ch slot point
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (p : Fin shape.numProofs) :
    (lookupEntriesOfResolver vk
        (decodedPolynomialResolver (instanceCommitment := instanceCommitment)
          urs hk vk ps ch memberDecode route) p).map
        (fun lk => (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2))
        = subProofLookups vk ps p
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases decodedPolynomialResolver_opens_or_relation
      (instanceCommitment := instanceCommitment)
      urs hk vk ps ch memberDecode route
      (assembleQueries vk instanceCommitment ps ch) hrouted hbind with hopen | hrel
  · exact Or.inl (eval_lookupEntriesOfResolver_of_assembleQueries
      vk instanceCommitment ps ch
      (decodedPolynomialResolver (instanceCommitment := instanceCommitment)
        urs hk vk ps ch memberDecode route) p hopen)
  · exact Or.inr hrel

end Zcash.Snark
