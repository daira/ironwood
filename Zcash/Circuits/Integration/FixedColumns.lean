import Zcash.Snark.Soundness.InstanceCommitment
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation

/-!
# Fixed-column commitment provenance

The verifier's fixed columns are commitments in the verifying key, while the
multiopen extractor returns augmented monomial-basis openings. This module crosses
that representation boundary without assuming commitment binding: a routed decoded
fixed polynomial is the keygen row polynomial, or the two openings compute a
nontrivial relation among the augmented URS generators.

The result is generic in the fixed row vector and its Lagrange commitment key.
`TopLevelCircuit` keygen supplies those vectors; the Action endpoint only selects
the circuit-owned instance.
-/

namespace Zcash.Snark

open Polynomial

set_option maxHeartbeats 20000

variable {G : Type*} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

namespace CanonicalMemberConstraintRelation

variable
    {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k}
    {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G}
    {ch : Challenges shape.k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi}
    {hblinding : vk.blindingFactors < vk.n}
    {y : Fp} {hpoly : Polynomial Fp} {deg : ℕ}

/--
A canonically routed fixed-column opening is the polynomial interpolating its
keygen rows, or it exhibits an augmented commitment relation.

`hcommit` is the circuit-keygen side of the boundary: the fixed commitment stored
in the derived VK is the Lagrange commitment to `rows` with Halo 2's default blind
`1`. It is independent of the proof and can be established once for the generic
`TopLevelCircuit.toVerifierKey` construction.
-/
theorem fixedColumn_eq_rowPolynomial_or_relation
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg)
    (column : ℕ)
    (key : LagrangeCommitmentKey urs vk.omega)
    (rows : List Fp)
    (hcommit :
      vk.fixedCommitment column =
        key.commitInstance rows 1)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) => vk.omega ^ (i : ℕ))
    (hquery : ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = .fixedCol column) :
    relation.polynomial (.fixedCol column) =
        instanceRowPolynomial (2 ^ urs.k) vk.omega rows ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  classical
  obtain ⟨q, hq, hqid⟩ := hquery
  have routed :=
    assembledQueryMemberRoute_faithful
      (instanceCommitment := instanceCommitment)
      vk ps ch relation.groupingCount relation.noDuplicateQueries q hq
  have routedFixed :
      relation.route (.fixedCol column) = some routed.slot := by
    rw [← hqid]
    exact routed.route_eq
  have hid :
      (deployedSetCommIds (instanceCommitment := instanceCommitment)
        vk ps ch routed.slot.setIndex).getD
          (routed.slot.memberIndex : ℕ) .vanishingH =
        .fixedCol column := by
    apply assembledQueryMemberRoute_id
      (instanceCommitment := instanceCommitment)
      vk ps ch relation.groupingCount relation.noDuplicateQueries
      (.fixedCol column) routed.slot
    simpa [CanonicalMemberConstraintRelation.route] using routedFixed
  have href :=
    deployedMemberRef_eq_fixedCommitment
      (instanceCommitment := instanceCommitment)
      vk ps ch relation.groupingCount routed.slot column hid
  let decoded :=
    memberDecode routed.slot.setIndex routed.slot.setIndex_lt
  have hopen :
      commit urs (decoded.cols routed.slot.memberIndex) +
          decoded.uComp routed.slot.memberIndex • urs.u +
          decoded.wComp routed.slot.memberIndex • urs.w =
        key.commitInstance rows 1 := by
    calc
      commit urs (decoded.cols routed.slot.memberIndex) +
            decoded.uComp routed.slot.memberIndex • urs.u +
            decoded.wComp routed.slot.memberIndex • urs.w =
          ((deployedSetQueries
              (instanceCommitment := instanceCommitment)
              vk ps ch routed.slot.setIndex).getD
            (routed.slot.memberIndex : ℕ) (.point 0, [])).1.eval
              ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ :=
        decoded.commitment routed.slot.memberIndex
      _ = vk.fixedCommitment column := by
        rw [href]
        rfl
      _ = key.commitInstance rows 1 := hcommit
  have hbound :=
    coeffsToPoly_eq_instanceRowPolynomial_or_relation
      key rows 1
      (decoded.cols routed.slot.memberIndex)
      (decoded.uComp routed.slot.memberIndex)
      (decoded.wComp routed.slot.memberIndex)
      hrows hopen
  rcases hbound with heq | hrelation
  · apply Or.inl
    rw [CanonicalMemberConstraintRelation.polynomial,
      decodedPolynomialResolver, routedFixed]
    exact heq
  · exact Or.inr hrelation

end CanonicalMemberConstraintRelation

end Zcash.Snark
