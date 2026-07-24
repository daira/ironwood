import Zcash.Snark.Soundness.CanonicalConstraintModel
import Zcash.Snark.Soundness.ConstraintSatisfaction
import Zcash.Snark.Soundness.Multiopen.ConstraintResolver

/-!
# Canonical decoded-member constraint relation

The older member capstone accepts fixed columns, permutation sets/chunks, lookups,
and selector polynomials as independent arguments. That is useful for decomposing
the verifier proof, but it is too weak as the semantic handoff to a formal circuit:
those arguments could describe a different constraint model.

This relation retains the decoded batch witness and derives one polynomial resolver
from the deployed query grouping. The complete `ConstraintPolyModel` is then built
canonically from that resolver and the accepted verification key. It is bundle-wide:
one constraint identity covers every proof member, with no selected proof index.
-/

namespace Zcash.Snark

open Polynomial

set_option maxHeartbeats 20000

variable {G : Type*} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
The deterministic semantic payload expected from the extraction/probability stack.

All constraint-bearing polynomials come from `memberDecode` through the canonical
assembled-query route. In particular, fixed columns and the permutation/lookup
families are not caller-supplied.
-/
structure CanonicalMemberConstraintRelation
    {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi)
    (hblinding : vk.blindingFactors < vk.n)
    (y : Fp) (hpoly : Polynomial Fp) (deg : ℕ) : Prop where
  groupingCount :
    deployedX4PairCount
      (instanceCommitment := instanceCommitment)
      vk ps ch =
      (constructIntermediateSets
        (assembleQueries vk instanceCommitment ps ch)).sets.length
  noDuplicateQueries :
    hasDuplicateCommitmentPoint
      (assembleQueries vk instanceCommitment ps ch) = false
  satisfiesCircuit :
    let route :=
      assembledQueryMemberRoute
        (instanceCommitment := instanceCommitment)
        vk ps ch groupingCount noDuplicateQueries
    let poly :=
      decodedPolynomialResolver
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch memberDecode route
    let model :=
      canonicalConstraintModelOfPermutationResolver
        vk ch poly hblinding
    model.CircuitSat y hpoly deg a

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

/-- The unique commitment-ID route selected by the deployed grouping. -/
noncomputable def route
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg) :
    CommitmentId →
      Option (DeployedMemberSlot
        (instanceCommitment := instanceCommitment)
        vk ps ch) :=
  assembledQueryMemberRoute
    (instanceCommitment := instanceCommitment)
    vk ps ch relation.groupingCount relation.noDuplicateQueries

/-- The decoded polynomial resolver determined by the relation's member openings. -/
noncomputable def polynomial
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg) :
    CommitmentId → Polynomial Fp :=
  decodedPolynomialResolver
    (instanceCommitment := instanceCommitment)
    urs hk vk ps ch memberDecode relation.route

/-- The complete verifier-native constraint model determined by the relation. -/
noncomputable def model
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg) :
    ConstraintPolyModel shape.numProofs :=
  canonicalConstraintModelOfPermutationResolver
    vk ch relation.polynomial hblinding

/--
A good folding challenge splits the canonical bundle-wide identity into the exact
family-separated satisfaction record consumed by gate, permutation, and lookup
semantics.
-/
theorem constraintSatisfaction
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg)
    (hn : deg ≠ 0)
    (hgoodY : ∀ j,
      y ∉ szBadSet
        (foldSplitWitness relation.model.constraints deg j)) :
    ConstraintSatisfaction relation.model deg := by
  apply ConstraintSatisfaction.of_circuitSatViaConstraints
    relation.model y hpoly a hn
  · exact relation.satisfiesCircuit
  · exact hgoodY

end CanonicalMemberConstraintRelation

end Zcash.Snark
