import Zcash.Snark.VkCommit.Derivation
import Zcash.Snark.Soundness.Multiopen.ConstraintResolver
import Zcash.Snark.Soundness.TopLevelAssignment
import Zcash.Circuits.Action.TopLevel

/-!
# Decoded assignments for the circuit-derived Action key

This is the only Action-specific assignment constructor. It does not accept an
arbitrary verifying key: both the verifier-side decoder and the returned generic
`TopLevelAssignment` are fixed by the real closed Action circuit and the supplied
URS.
-/

namespace Zcash.Snark

open Halo2 Polynomial
open Zcash.Circuits.Action

set_option maxHeartbeats 20000

namespace TopLevelAssignment

/--
Build one generic top-level Action assignment from the deployed decoded-member
resolver, using the Action circuit's derived verifying key.

`hshapeK` records that the protocol shape names the same domain exponent as the
closed circuit. It is retained as an explicit construction premise because the
current `Shape` type does not derive its `k` field from the verifying key.
-/
noncomputable def ofActionDecodedMembers
    {shape : Shape} {G : Type}
    [AddCommGroup G] [Module Fp G] [DecidableEq G] [Inhabited G]
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (urs : URS G) (hk : shape.k = urs.k)
    (_hshapeK :
      shape.k = orchardActionTopLevelCircuit.domainExponent)
    (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments
        (instanceCommitment := instanceCommitment)
        urs hk (VkCommit.derivedActionVk shape urs) ps ch)
      (x4BatchEvals
        (instanceCommitment := instanceCommitment)
        (VkCommit.derivedActionVk shape urs) ps ch)
      a₀ pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          (VkCommit.derivedActionVk shape urs) ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk (VkCommit.derivedActionVk shape urs)
        ps ch pbatch i hi)
    (route : CommitmentId →
      Option (DeployedMemberSlot
        (instanceCommitment := instanceCommitment)
        (VkCommit.derivedActionVk shape urs) ps ch))
    (proofIndex : Fin shape.numProofs) :
    TopLevelAssignment orchardActionTopLevelCircuit
      shape.numProofs proofIndex where
  polynomial :=
    decodedPolynomialResolver
      (instanceCommitment := instanceCommitment)
      urs hk (VkCommit.derivedActionVk shape urs)
      ps ch memberDecode route

end TopLevelAssignment

end Zcash.Snark
