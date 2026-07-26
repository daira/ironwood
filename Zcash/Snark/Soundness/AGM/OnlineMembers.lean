import Zcash.Snark.Soundness.AGM.DeployedCoordinateDecode
import Zcash.Snark.Soundness.AGM.DeployedX1

/-!
# Prefix-covered deployed member representations

The within-set `x1` batch consists of actual query commitments.  Each such commitment must resolve
to either a prover-emitted algebraic point fixed before `x1`, or a verifier-fixed represented
point.  This file states that concrete coverage predicate and turns it into the exact
`AlgebraicColumnRepresentations` consumed by `deployedX1AlgebraicBatchOrRelation`.
-/

namespace Zcash.Snark

open Classical

local instance vestaInhabitedOnlineMembers : Inhabited VestaG := ⟨0⟩

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}

attribute [local irreducible] deployedSetQueries deployedX4PairCount
  deployedSetMemberCommitments

/-- Every query commitment routed into a deployed point set has a representation in the online
multiopen source.  The source's prover points are emitted before `x1`; `fixed` is basis-dependent
but oracle-independent. -/
def DeployedMembersCovered
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) : Prop :=
  forall nu : Fin 11 -> Fp,
    forall i : Nat, i < deployedX4PairCount vk instanceCommitment aps.erase
        (chRecord nu (fun _ => 0)) ->
      forall m : Fin (deployedSetQueries vk instanceCommitment aps.erase
        (chRecord nu (fun _ => 0)) i).length,
        ∃ ap ∈ aps.multiopenAssemblySource fixed,
          ap.point = deployedSetMemberCommitments (ursOfAugmentedBasis shape.k basis) rfl
            vk instanceCommitment aps.erase (chRecord nu (fun _ => 0)) i m

/-- Resolve each covered deployed member commitment to the augmented AGM coordinates carried by
its source point. -/
noncomputable def deployedMemberRepresentationsOfCovered
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : DeployedMembersCovered vk instanceCommitment p.algebraicProof fixed)
    (nu : Fin 11 -> Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0))) :
    AlgebraicColumnRepresentations (ursOfAugmentedBasis shape.k basis)
      (deployedSetMemberCommitments (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) i) := by
  let sourcePoint : Fin (deployedSetQueries vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) i).length -> AlgebraicPoint (F := Fp) basis :=
    fun m => Classical.choose (hcovered nu i hi m)
  have hsourcePoint : forall m,
      (sourcePoint m).point = deployedSetMemberCommitments
        (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0)) i m := by
    intro m
    exact (Classical.choose_spec (hcovered nu i hi m)).2
  refine
    { coeffs := fun m => (sourcePoint m).gPart
      uComp := fun m => (sourcePoint m).coeffs AugmentedIndex.u
      wComp := fun m => (sourcePoint m).coeffs AugmentedIndex.w
      commitment := ?_ }
  intro m
  exact (AlgebraicPoint.point_eq_components (sourcePoint m)).symm.trans (hsourcePoint m)

/-- The exact deployed within-set `x1` batch, obtained from online-covered member coordinates.
Any mismatch with the already decoded `x4` aggregate is returned as an explicit augmented-basis
relation. -/
noncomputable def deployedX1BatchOfCoveredOrRelation
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : DeployedMembersCovered vk instanceCommitment p.algebraicProof fixed)
    (nu : Fin 11 -> Fp)
    (x4Batch : AlgebraicPowerBatch (ursOfAugmentedBasis shape.k basis)
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
        (chRecord nu (fun _ => 0)))
      (p.aMulti nu) (p.multiU nu) (p.multiBlind nu) (nu 8))
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0))) :
    AlgebraicPowerBatch (ursOfAugmentedBasis shape.k basis)
        (deployedSetMemberCommitments (ursOfAugmentedBasis shape.k basis) rfl
          vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) i)
        (x4Batch.coeffs ⟨deployedX4PairCount vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0)) - 1 - i, by omega⟩)
        (x4Batch.uComp ⟨deployedX4PairCount vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0)) - 1 - i, by omega⟩)
        (x4Batch.wComp ⟨deployedX4PairCount vk instanceCommitment p.proof.1
          (chRecord nu (fun _ => 0)) - 1 - i, by omega⟩)
        (nu 5) ⊕'
      AugmentedRelationWitness (F := Fp)
        (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w :=
  deployedX1AlgebraicBatchOrRelation (ursOfAugmentedBasis shape.k basis) rfl
    vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) x4Batch i hi
    (deployedMemberRepresentationsOfCovered p fixed hcovered nu i hi)

/-- Add the exact deployed-member coverage evidence to the online multiopen family.  Keeping this
as a second refinement avoids changing the existing computed-family API while the tighter path is
developed. -/
structure ComputedOnlineMemberFSFamily (shape : Shape)
    extends ComputedOnlineMultiopenFSFamily shape where
  membersCovered : forall basis O,
    DeployedMembersCovered (vk basis) (instanceCommitment basis)
      ((adversary basis).run O).algebraicProof
      (fixedRepresentations basis)

namespace ComputedOnlineMemberFSFamily

/-- Forget only member-coverage evidence. -/
abbrev toOnlineFamily (family : ComputedOnlineMemberFSFamily shape) :
    ComputedOnlineMultiopenFSFamily shape := family.toComputedOnlineMultiopenFSFamily

/-- Forget all tighter multiopen evidence. -/
abbrev toFamily (family : ComputedOnlineMemberFSFamily shape) :
    ComputedAlgebraicFSFamily shape := family.toOnlineFamily.toFamily

end ComputedOnlineMemberFSFamily

end Zcash.Snark
