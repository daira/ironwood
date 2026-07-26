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

/-- A commitment reference is covered by online representations: a plain point is present
directly, while an MSM has representations for every appended point it combines. -/
def CommitmentRefCovered
    (source : List (AlgebraicPoint (F := Fp) basis)) :
    CommitmentRef shape.k Fp VestaG -> Prop
  | .point P => ∃ ap ∈ source, ap.point = P
  | .msm m => ∀ pr ∈ m.other, ∃ ap ∈ source, ap.point = pr.2

/-- Every query commitment routed into a deployed point set is structurally covered by the online
multiopen source.  This includes MSM-valued references such as the folded vanishing-`h`
commitment; their evaluated group point need not itself appear as a source point. -/
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
        CommitmentRefCovered (aps.multiopenAssemblySource fixed)
          ((deployedSetQueries vk instanceCommitment aps.erase
            (chRecord nu (fun _ => 0)) i).getD (m : Nat) (.point 0, [])).1

/-- AGM coordinates for the group value of one structurally covered commitment reference. -/
structure CoveredCommitmentRepresentation
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (c : CommitmentRef shape.k Fp VestaG) where
  coeffs : Fin (2 ^ shape.k) -> Fp
  uComp : Fp
  wComp : Fp
  commitment :
    commit (ursOfAugmentedBasis shape.k basis) coeffs +
        uComp • (ursOfAugmentedBasis shape.k basis).u +
        wComp • (ursOfAugmentedBasis shape.k basis).w =
      c.eval (ursOfAugmentedBasis shape.k basis)

/-- Resolve a covered point directly, or combine the representations carried by an MSM-valued
commitment reference. -/
noncomputable def coveredCommitmentRepresentation
    (source : List (AlgebraicPoint (F := Fp) basis))
    (c : CommitmentRef shape.k Fp VestaG)
    (hcovered : CommitmentRefCovered source c) :
    CoveredCommitmentRepresentation basis c := by
  cases c with
  | point P =>
      let ap := Classical.choose hcovered
      refine
        { coeffs := ap.gPart
          uComp := ap.coeffs AugmentedIndex.u
          wComp := ap.coeffs AugmentedIndex.w
          commitment := ?_ }
      simpa only [CommitmentRef.eval] using
        (AlgebraicPoint.point_eq_components ap).symm.trans
          (Classical.choose_spec hcovered).2
  | msm m =>
      let represented := RepresentedMsm.ofCoveredList m source hcovered
      refine
        { coeffs := m.gScalars + repsGPart represented.reps
          uComp := m.uScalar + repsU represented.reps
          wComp := m.wScalar + repsW represented.reps
          commitment := ?_ }
      simpa only [CommitmentRef.eval] using
        (Msm.eval_repr m represented.reps represented.covers).symm

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
  let memberRef : Fin (deployedSetQueries vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) i).length -> CommitmentRef shape.k Fp VestaG :=
    fun m => ((deployedSetQueries vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0)) i).getD (m : Nat) (.point 0, [])).1
  let represented : forall m, CoveredCommitmentRepresentation basis (memberRef m) :=
    fun m => coveredCommitmentRepresentation
      (p.algebraicProof.multiopenAssemblySource fixed) (memberRef m)
      (hcovered nu i hi m)
  refine
    { coeffs := fun m => (represented m).coeffs
      uComp := fun m => (represented m).uComp
      wComp := fun m => (represented m).wComp
      commitment := ?_ }
  intro m
  simpa only [memberRef, deployedSetMemberCommitments_apply] using
    (represented m).commitment

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
