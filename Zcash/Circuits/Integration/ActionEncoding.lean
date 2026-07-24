import Zcash.Circuits.Action.Statement
import Zcash.Snark.Soundness.ActionStatement
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Zcash.Snark.Soundness.TopLevelCircuit
import Zcash.Snark.VkCommit.Pipeline

/-!
# Canonical decoded relation to the Orchard Action statement

This is the Action-specific end of the Clean/Ironwood boundary. The decoded-member
relation and constraint splitting remain verifier-native. The only circuit-specific
steps here are applying the closed Action circuit's soundness theorem and identifying
its ten public instance rows.
-/

namespace Zcash.Snark

open Halo2 Polynomial
open Zcash.Circuits
open Zcash.Circuits.Action
open VkCommit

set_option maxHeartbeats 20000

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
The canonical bundle-wide decoded relation implies the concrete Orchard Action
bundle statement once the generic polynomial-to-Clean reconstruction supplies the
authoritative operation constraints.

There is no free proposition `S` and no `hencodes` premise. The remaining
`reconstruct` argument is precisely the unfinished generic representation bridge,
not an Action semantic assumption.
-/
theorem actionBundleStatement_of_canonicalRelation
    (pp : VkCommit.ProofParams) (urs : URS G)
    (hk :
      (pp.mergeDerived orchardActionTopLevelCircuit).k = urs.k)
    (instanceCommitment :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
        ℕ → G)
    (ps : ProofString
      (pp.mergeDerived orchardActionTopLevelCircuit) Fp G)
    (ch : Challenges
      (pp.mergeDerived orchardActionTopLevelCircuit).k Fp)
    (vk : VerifyingKey
      (pp.mergeDerived orchardActionTopLevelCircuit) Fp G)
    (hvk :
      vk = orchardActionTopLevelCircuit.toVerifierKey pp urs)
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
    (hbound : orchardActionTopLevelCircuit.domainExponent < 33)
    (hblinding :
      vk.blindingFactors < vk.n)
    (hpoly : Polynomial Fp)
    (relation :
      CanonicalMemberConstraintRelation
        urs hk vk
        instanceCommitment ps ch pU pW a batchOpenings memberDecode
        hblinding ch.y hpoly vk.n)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness relation.model.constraints
          vk.n j))
    (inputs :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
        PublicInputs)
    (hsize :
      10 ≤ 2 ^ orchardActionTopLevelCircuit.domainExponent)
    (hinstance : ∀
      proofIndex :
        Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs,
      relation.polynomial
          (.instanceCol proofIndex
            (Circuit.configure
              Specs.Sinsemilla.orchardGenerators {}).1.primary.index) =
        instanceRowPolynomial
          (2 ^ orchardActionTopLevelCircuit.domainExponent)
          (Zcash.Snark.omegaOf
            orchardActionTopLevelCircuit.domainExponent)
          (inputs proofIndex).rows)
    (reconstruct : ∀ proofIndex,
      ConstraintSatisfaction relation.model
          vk.n →
        Halo2.Constraints orchardActionTopLevelCircuit.placement
          (TopLevelAssignment.environment
            ({ polynomial := relation.polynomial } :
              TopLevelAssignment orchardActionTopLevelCircuit
                (pp.mergeDerived orchardActionTopLevelCircuit).numProofs
                proofIndex))
          (orchardActionTopLevelCircuit.operations 0) 0) :
    BundleStatement Specs.Sinsemilla.orchardGenerators orchardBases inputs := by
  have hn :
      vk.n ≠ 0 := by
    rw [hvk]
    change 2 ^ orchardActionTopLevelCircuit.domainExponent ≠ 0
    positivity
  have hsatisfaction :=
    relation.constraintSatisfaction hn hgoodY
  intro proofIndex
  let assignment :
      TopLevelAssignment orchardActionTopLevelCircuit
        (pp.mergeDerived orchardActionTopLevelCircuit).numProofs
        proofIndex :=
    { polynomial := relation.polynomial }
  have hconstraints :
      Halo2.Constraints orchardActionTopLevelCircuit.placement
        assignment.environment
        (orchardActionTopLevelCircuit.operations 0) 0 := by
    exact reconstruct proofIndex hsatisfaction
  have htop :
      orchardActionTopLevelCircuit.Statement 0
        assignment.placedEnvironment := by
    apply orchardActionTopLevelCircuit.soundness
    · exact assignment.synthesisWellFormed hbound
    · exact hconstraints
  have hstatement :=
    statement_of_topLevelStatement
      Specs.Sinsemilla.orchardGenerators orchardBases
      orchardActionTopLevelCircuit rfl 0
      assignment.placedEnvironment htop
  have hpublic :
      PublicInputs.ofEnvironment
          (Circuit.configure
            Specs.Sinsemilla.orchardGenerators {}).1
          assignment.environment =
        inputs proofIndex := by
    apply actionPublicInputs_of_instanceRowPolynomial
      assignment
      (Circuit.configure
        Specs.Sinsemilla.orchardGenerators {}).1
      (inputs proofIndex) hsize
    · exact hinstance proofIndex
    · exact TopLevelAssignment.domainRowsInjective hbound
  change
    Statement Specs.Sinsemilla.orchardGenerators orchardBases
      (PublicInputs.ofEnvironment
        (Circuit.configure
          Specs.Sinsemilla.orchardGenerators {}).1
        assignment.environment) at hstatement
  rwa [hpublic] at hstatement
