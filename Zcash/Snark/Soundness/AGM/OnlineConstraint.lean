import Zcash.Snark.Soundness.AGM.DeployedConstraintSupply
import Zcash.Snark.Soundness.AGM.DeployedPinnedRoots

/-!
# Constraint supply from retained online AGM provenance

This adapter builds the pre-`x` constraint polynomial from the exact representation list carried by
`DeployedBatchWitness`.  Plain members agree definitionally with the successful `x1` unbatch; the
only remaining disagreement branch is the explicit quotient-piece collision returned by
`decodedQuotientEqReassembledOrRelationWitness`.
-/

namespace Zcash.Snark

open Classical Polynomial

variable {shape : Shape}

local instance vestaInhabitedOnlineConstraint : Inhabited VestaG := ⟨0⟩

/-- The deterministic pre-`x` representation source retained by one deployed batch witness. -/
def deployedConstraintSource (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu) :
    List (AlgebraicPoint (F := Fp) basis) :=
  pnu.1.algebraicProof.multiopenAssemblySource witness.fixedRepresentations

/-- Polynomial of the first online representation of a committed point. -/
noncomputable def deployedConstraintPointPolynomial
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu) (P : VestaG) : Polynomial Fp :=
  onlinePointPolynomial (deployedConstraintSource family basis pnu witness) P

/-- Coordinates of one quotient-piece commitment from the same deterministic source. -/
def deployedConstraintPieceCoordinates
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (i : Fin shape.numQuotientPieces) : (Fin (2 ^ shape.k) -> Fp) × Fp × Fp :=
  onlinePointCoordinates (deployedConstraintSource family basis pnu witness)
    (pnu.1.algebraicProof.hPieces i).point

/-- Every quotient piece is covered by the retained pre-`x` source. -/
theorem deployedConstraintPieceCovered
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (i : Fin shape.numQuotientPieces) :
    CommitmentRefCovered (deployedConstraintSource family basis pnu witness)
      (.point (pnu.1.algebraicProof.hPieces i).point) :=
  ⟨pnu.1.algebraicProof.hPieces i,
    pnu.1.algebraicProof.hPiece_mem_multiopenAssemblySource witness.fixedRepresentations i,
    rfl⟩

/-- The online quotient-piece coordinates open the emitted quotient-piece commitment. -/
theorem deployedConstraintPieceCoordinates_open
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (i : Fin shape.numQuotientPieces) :
    commit (ursOfAugmentedBasis shape.k basis)
        (deployedConstraintPieceCoordinates family basis pnu witness i).1 +
      (deployedConstraintPieceCoordinates family basis pnu witness i).2.1 •
          (ursOfAugmentedBasis shape.k basis).u +
      (deployedConstraintPieceCoordinates family basis pnu witness i).2.2 •
          (ursOfAugmentedBasis shape.k basis).w = pnu.1.proof.1.hPieces i := by
  simpa [deployedConstraintPieceCoordinates, deployedConstraintSource] using
    onlinePointCoordinates_commitment
      (deployedConstraintSource family basis pnu witness)
      (pnu.1.algebraicProof.hPieces i).point
      (deployedConstraintPieceCovered family basis pnu witness i)

/-- Retained source provenance pins every plain decoded member to its pre-`x` polynomial without a
new relation branch. -/
theorem deployedConstraint_memberPoly_eq_online
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (decoded : DeployedAlgebraicDecode (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu)) (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decoded.batches = witness.batches)
    {i : Nat} (hi : i < deployedX4PairCount (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 (wrappedPreIpaRecord pnu))
    (m : Fin (deployedSetQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).length) {P : VestaG}
    (hP : ((deployedSetQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).getD (m : Nat) (.point 0, [])).1 =
      .point P) :
    decoded.memberPoly i hi m =
      deployedConstraintPointPolynomial family basis pnu witness P := by
  unfold DeployedAlgebraicDecode.memberPoly deployedConstraintPointPolynomial
  rw [hbatches]
  rw [congrFun (witness.memberCoeffs i hi) m]
  exact congrArg coeffsToPoly
    (deployedMemberRepresentationsOfCovered_coeffs_point pnu.1
      witness.fixedRepresentations witness.membersCovered (wrappedPreIpaReads pnu)
      i hi m P hP)

/-- Concrete constraint outcome built from the actual online AGM source.  No arbitrary chosen
opening occurs in this function. -/
noncomputable def deployedOnlineConstraintOutcomeOfDecode
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (decoded : DeployedAlgebraicDecode (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu)) (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decoded.batches = witness.batches)
    (checks : DeployedConstraintChecks (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu))
    (hAdvLen : shape.numAdviceQueries <= (family.vk basis).adviceQueryLayout.length)
    (hInstLen : shape.numInstanceQueries <= (family.vk basis).instanceQueryLayout.length)
    (hFixedLen : shape.numFixedQueries <= (family.vk basis).fixedQueryLayout.length)
    (homega : (family.vk basis).omega ^ (family.vk basis).n = 1)
    (hn : ((family.vk basis).n : Fp) ≠ 0)
    (hxgood : (wrappedPreIpaRecord pnu).x ∉ szBadSet
      (committedPreXConstraintDifference
        (deployedConstraintPointPolynomial family basis pnu witness)
        (fun i => coeffsToPoly
          (deployedConstraintPieceCoordinates family basis pnu witness i).1)
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu))) :
    DeployedConstraintWitness (ursOfAugmentedBasis shape.k basis) rfl
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
        (pnu.1.multiU (wrappedPreIpaReads pnu)) (pnu.1.multiBlind (wrappedPreIpaReads pnu)) ⊕'
      AugmentedRelationWitness (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w :=
  deployedConstraintOutcomeOfDecode (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
    (wrappedPreIpaRecord pnu) decoded
    (deployedConstraintPointPolynomial family basis pnu witness)
    (fun i => (deployedConstraintPieceCoordinates family basis pnu witness i).1)
    (fun i => (deployedConstraintPieceCoordinates family basis pnu witness i).2.1)
    (fun i => (deployedConstraintPieceCoordinates family basis pnu witness i).2.2)
    (fun i => coeffsToPoly
      (deployedConstraintPieceCoordinates family basis pnu witness i).1)
    (deployedConstraintPieceCoordinates_open family basis pnu witness) (fun _ => rfl)
    (deployedConstraint_memberPoly_eq_online family basis pnu witness decoded hbatches)
    checks hAdvLen hInstLen hFixedLen homega hn hxgood

/-- Run-level provider shape consumed by the composite probability theorem.  `none` means the
decode or pre-`x` premises were unavailable; `some` retains either the constraint witness or the
explicit relation produced by the online adapter. -/
abbrev DeployedConstraintOutcomeProvider (family : ComputedDeployedRootFSFamily shape) :=
  forall (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins),
    let pnu := (wrappedAdversary family.toFamily basis).run coins.1
    Option (DeployedConstraintWitness (ursOfAugmentedBasis shape.k basis) rfl
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
        (pnu.1.multiU (wrappedPreIpaReads pnu)) (pnu.1.multiBlind (wrappedPreIpaReads pnu)) ⊕'
      AugmentedRelationWitness (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)

/-- Explicit algebraic relation finder induced by the right branch of a constraint provider. -/
def deployedConstraintFinderOfOutcome (family : ComputedDeployedRootFSFamily shape)
    (provider : DeployedConstraintOutcomeProvider family) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis coins =>
    match provider basis coins with
    | some (PSum.inr relation) =>
        some (augmentedBasis_ursOfAugmentedBasis shape.k basis ▸
          relation.toAlgebraicRelationWitness)
    | _ => none

/-- Successful left branch of the run-level constraint provider. -/
def deployedConstraintDecodedOfOutcome (family : ComputedDeployedRootFSFamily shape)
    (provider : DeployedConstraintOutcomeProvider family)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins) : Prop :=
  ∃ witness, provider basis coins = some (PSum.inl witness)

end Zcash.Snark
