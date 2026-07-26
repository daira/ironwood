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
  pnu.1.algebraicProof.preX1AssemblySource witness.fixedRepresentations

/-- Polynomial of the first online representation of a committed point. -/
def deployedConstraintPointPolynomial
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
    pnu.1.algebraicProof.hPiece_mem_preX1AssemblySource witness.fixedRepresentations i,
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

/-- The reassembled quotient MSM is covered directly by the pre-`x` quotient-piece
representations.  This proof does not select a routed member or an opening witness. -/
theorem deployedConstraintVanishingCovered
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu) :
    CommitmentRefCovered (deployedConstraintSource family basis pnu witness)
      (.msm (vanishingHCommitment shape.k
        ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
        (List.ofFn pnu.1.proof.1.hPieces))) := by
  intro pr hpr
  have hpoint : pr.2 ∈ (vanishingHCommitment shape.k
      ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
      (List.ofFn pnu.1.proof.1.hPieces)).otherPoints := by
    rw [Msm.otherPoints]
    exact List.mem_map.mpr ⟨pr, hpr, rfl⟩
  have hpiece := mem_otherPoints_vanishingHCommitment
    ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
    (List.ofFn pnu.1.proof.1.hPieces) pr.2 hpoint
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpiece
  refine ⟨pnu.1.algebraicProof.hPieces i,
    pnu.1.algebraicProof.hPiece_mem_preX1AssemblySource witness.fixedRepresentations i, ?_⟩
  exact hi.symm

/-- Quotient-piece representations retained in the online pre-`x` source. -/
def deployedConstraintPieceRepresentations
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu) :
    AlgebraicColumnRepresentations (ursOfAugmentedBasis shape.k basis)
      pnu.1.proof.1.hPieces :=
  { coeffs := fun i => (deployedConstraintPieceCoordinates family basis pnu witness i).1
    uComp := fun i => (deployedConstraintPieceCoordinates family basis pnu witness i).2.1
    wComp := fun i => (deployedConstraintPieceCoordinates family basis pnu witness i).2.2
    commitment := deployedConstraintPieceCoordinates_open family basis pnu witness }

/-- Computed comparison between the online representation of the reassembled quotient MSM and
the power sum of the online quotient-piece representations.  A disagreement returns its actual
augmented-basis coefficients; it is never recovered from `HasNontrivialRelation` or `Nonempty`. -/
def deployedConstraintQuotientAgreementOrRelation
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu) :
    let urs := ursOfAugmentedBasis shape.k basis
    let xn := (wrappedPreIpaRecord pnu).x ^ (family.vk basis).n
    let represented := coveredCommitmentRepresentation
      (deployedConstraintSource family basis pnu witness)
      (.msm (vanishingHCommitment shape.k xn (List.ofFn pnu.1.proof.1.hPieces)))
      (deployedConstraintVanishingCovered family basis pnu witness)
    let pieces := deployedConstraintPieceRepresentations family basis pnu witness
    (represented.coeffs = ∑ i, xn ^ (i : Nat) • pieces.coeffs i ∧
      represented.uComp = ∑ i, xn ^ (i : Nat) * pieces.uComp i ∧
      represented.wComp = ∑ i, xn ^ (i : Nat) * pieces.wComp i) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  let urs := ursOfAugmentedBasis shape.k basis
  let xn := (wrappedPreIpaRecord pnu).x ^ (family.vk basis).n
  let msm := vanishingHCommitment shape.k xn (List.ofFn pnu.1.proof.1.hPieces)
  let represented := coveredCommitmentRepresentation
    (deployedConstraintSource family basis pnu witness) (.msm msm)
    (deployedConstraintVanishingCovered family basis pnu witness)
  let pieces := deployedConstraintPieceRepresentations family basis pnu witness
  let pieceCoeffs := ∑ i, xn ^ (i : Nat) • pieces.coeffs i
  let pieceU := ∑ i, xn ^ (i : Nat) * pieces.uComp i
  let pieceW := ∑ i, xn ^ (i : Nat) * pieces.wComp i
  have hvanishing : msm.eval urs =
      ∑ i : Fin shape.numQuotientPieces, xn ^ (i : Nat) • pnu.1.proof.1.hPieces i := by
    simpa [msm] using vanishingHCommitment_eval urs xn (List.ofFn pnu.1.proof.1.hPieces)
  have hrepresented : commit urs represented.coeffs + represented.uComp • urs.u +
      represented.wComp • urs.w =
        ∑ i : Fin shape.numQuotientPieces, xn ^ (i : Nat) • pnu.1.proof.1.hPieces i :=
    represented.commitment.trans hvanishing
  have hpieces : commit urs pieceCoeffs + pieceU • urs.u + pieceW • urs.w =
      ∑ i : Fin shape.numQuotientPieces, xn ^ (i : Nat) • pnu.1.proof.1.hPieces i :=
    pieces.power_commitment xn
  have hcollision : commitGen urs.g represented.coeffs + represented.uComp • urs.u +
      represented.wComp • urs.w =
      commitGen urs.g pieceCoeffs + pieceU • urs.u + pieceW • urs.w := by
    rw [← commit_eq_commitGen, ← commit_eq_commitGen, hrepresented, hpieces]
  exact separateOrRelationWitness urs.g urs.u urs.w represented.coeffs pieceCoeffs
    represented.uComp pieceU represented.wComp pieceW hcollision

/-- Relation-only projection of the online quotient comparison.  This is the executable finder
charged to DLOG by the composite theorem; success certificates and bad-`x` proofs are deliberately
absent from its input. -/
def deployedConstraintQuotientFinder
    (family : ComputedDeployedRootFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis coins =>
    let pnu := (wrappedAdversary family.toFamily basis).run coins.1
    match family.outcome basis coins.1 with
    | PSum.inr _ => none
    | PSum.inl witness =>
        match deployedConstraintQuotientAgreementOrRelation family basis pnu witness with
        | PSum.inl _ => none
        | PSum.inr relation =>
            some (augmentedBasis_ursOfAugmentedBasis shape.k basis ▸
              relation.toAlgebraicRelationWitness)

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

/-- At the routed vanishing-quotient slot, the decoded batch retains all three deterministic
online coordinates, not just the polynomial coefficients. -/
theorem deployedConstraint_vanishing_components_eq_online
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
      pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).length)
    (hcommit : ((deployedSetQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).getD (m : Nat) (.point 0, [])).1 =
      .msm (vanishingHCommitment shape.k
        ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
        (List.ofFn pnu.1.proof.1.hPieces))) :
    let represented := coveredCommitmentRepresentation
      (deployedConstraintSource family basis pnu witness)
      (.msm (vanishingHCommitment shape.k
        ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
        (List.ofFn pnu.1.proof.1.hPieces)))
      (deployedConstraintVanishingCovered family basis pnu witness)
    (decoded.batches.x1 i hi).coeffs m = represented.coeffs ∧
      (decoded.batches.x1 i hi).uComp m = represented.uComp ∧
      (decoded.batches.x1 i hi).wComp m = represented.wComp := by
  let represented := coveredCommitmentRepresentation
    (deployedConstraintSource family basis pnu witness)
    (.msm (vanishingHCommitment shape.k
      ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
      (List.ofFn pnu.1.proof.1.hPieces)))
    (deployedConstraintVanishingCovered family basis pnu witness)
  have hmember := deployedMemberRepresentationsOfCovered_components pnu.1
    witness.fixedRepresentations witness.membersCovered (wrappedPreIpaReads pnu) i hi m
    (.msm (vanishingHCommitment shape.k
      ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
      (List.ofFn pnu.1.proof.1.hPieces))) hcommit
    (deployedConstraintVanishingCovered family basis pnu witness)
  have hcoeffs : (decoded.batches.x1 i hi).coeffs m = represented.coeffs := by
    rw [hbatches]
    exact (congrFun (witness.memberCoeffs i hi) m).trans hmember.1
  have hu : (decoded.batches.x1 i hi).uComp m = represented.uComp := by
    rw [hbatches]
    exact (congrFun (witness.memberU i hi) m).trans hmember.2.1
  have hw : (decoded.batches.x1 i hi).wComp m = represented.wComp := by
    rw [hbatches]
    exact (congrFun (witness.memberW i hi) m).trans hmember.2.2
  exact ⟨hcoeffs, hu, hw⟩

/-- Any quotient relation returned by the decoded constraint adapter is the same relation returned
by the standalone online quotient comparison.  This is the bridge that lets the probability layer
charge the relation-only executable finder rather than the success-certificate provider. -/
theorem deployedConstraint_quotient_relation_eq_online
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
      pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).length)
    (hcommit : ∀ d₀, ((deployedSetQueries (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).getD
        (m : Nat) d₀).1 = .msm (vanishingHCommitment shape.k
          ((wrappedPreIpaRecord pnu).x ^ (family.vk basis).n)
          (List.ofFn pnu.1.proof.1.hPieces)))
    (relation : AugmentedRelationWitness (F := Fp)
      (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w)
    (hrelation : decoded.quotientEvalEqCommittedPreXOrRelationWitness
      (fun j => (deployedConstraintPieceCoordinates family basis pnu witness j).1)
      (fun j => (deployedConstraintPieceCoordinates family basis pnu witness j).2.1)
      (fun j => (deployedConstraintPieceCoordinates family basis pnu witness j).2.2)
      (fun j => coeffsToPoly
        (deployedConstraintPieceCoordinates family basis pnu witness j).1)
      (deployedConstraintPieceCoordinates_open family basis pnu witness) (fun _ => rfl)
      hi m hcommit = PSum.inr relation) :
    deployedConstraintQuotientAgreementOrRelation family basis pnu witness =
      PSum.inr relation := by
  have hcomponents := deployedConstraint_vanishing_components_eq_online family basis pnu witness
    decoded hbatches hi m (hcommit (.point 0, []))
  unfold DeployedAlgebraicDecode.quotientEvalEqCommittedPreXOrRelationWitness at hrelation
  unfold deployedConstraintQuotientAgreementOrRelation
  simp only
  rw [← hcomponents.1, ← hcomponents.2.1, ← hcomponents.2.2]
  simpa only using hrelation

/-- Concrete constraint outcome built from the actual online AGM source.  No arbitrary chosen
opening occurs in this function. -/
def deployedOnlineConstraintOutcomeOfDecode
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

/-- Project any relation branch of the full constraint outcome onto the standalone online
quotient comparison. -/
theorem deployedOnlineConstraintOutcome_relation_eq_online
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
        (wrappedPreIpaRecord pnu)))
    (relation : AugmentedRelationWitness (F := Fp)
      (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w)
    (hout : deployedOnlineConstraintOutcomeOfDecode family basis pnu witness decoded hbatches
      checks hAdvLen hInstLen hFixedLen homega hn hxgood = PSum.inr relation) :
    deployedConstraintQuotientAgreementOrRelation family basis pnu witness =
      PSum.inr relation := by
  simp only [deployedOnlineConstraintOutcomeOfDecode, deployedConstraintOutcomeOfDecode,
    bindOrRelationWitness] at hout
  exact hout

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
