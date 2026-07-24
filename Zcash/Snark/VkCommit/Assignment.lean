import Zcash.Snark.VkCommit.Pipeline
import Zcash.Snark.Soundness.Multiopen.ConstraintResolver
import Zcash.Snark.Soundness.TopLevelAssignment
import Zcash.Circuits.Action.TopLevel

/-!
# Decoded assignments for the circuit-derived Action key

This is the only Action-specific assignment constructor. It does not accept an
arbitrary verifying key: both the verifier-side decoder and the returned generic
`TopLevelAssignment` are fixed by the real closed Action circuit, its proof
parameters, and the supplied URS.
-/

namespace Zcash.Snark

open Halo2 Polynomial
open Zcash.Circuits.Action

set_option maxHeartbeats 20000

namespace TopLevelAssignment

/--
Build one generic top-level Action assignment from the deployed decoded-member
resolver, using the Action circuit's derived verifying key.

The proof shape and verifying key are both derived from the same
`orchardActionTopLevelCircuit`. The only remaining size equality says that the
supplied URS uses that derived domain exponent.
-/
noncomputable def ofActionDecodedMembers
    {G : Type}
    [AddCommGroup G] [Module Fp G] [DecidableEq G] [Inhabited G]
    (pp : VkCommit.ProofParams)
    (urs : URS G)
    (hk :
      (pp.mergeDerived orchardActionTopLevelCircuit).k = urs.k)
    (instanceCommitment :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
        ℕ → G)
    (ps : ProofString
      (pp.mergeDerived orchardActionTopLevelCircuit) Fp G)
    (ch : Challenges
      (pp.mergeDerived orchardActionTopLevelCircuit).k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments
        (instanceCommitment := instanceCommitment)
        urs hk
        (orchardActionTopLevelCircuit.toVerifierKey pp urs) ps ch)
      (x4BatchEvals
        (instanceCommitment := instanceCommitment)
        (orchardActionTopLevelCircuit.toVerifierKey pp urs) ps ch)
      a₀ pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          (orchardActionTopLevelCircuit.toVerifierKey pp urs) ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk
        (orchardActionTopLevelCircuit.toVerifierKey pp urs)
        ps ch pbatch i hi)
    (route : CommitmentId →
      Option (DeployedMemberSlot
        (instanceCommitment := instanceCommitment)
        (orchardActionTopLevelCircuit.toVerifierKey pp urs) ps ch))
    (proofIndex :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs) :
    TopLevelAssignment orchardActionTopLevelCircuit
      (pp.mergeDerived orchardActionTopLevelCircuit).numProofs proofIndex where
  polynomial :=
    decodedPolynomialResolver
      (instanceCommitment := instanceCommitment)
      urs hk
      (orchardActionTopLevelCircuit.toVerifierKey pp urs)
      ps ch memberDecode route

end TopLevelAssignment

end Zcash.Snark
