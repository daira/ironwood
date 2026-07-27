import Zcash.Circuits.Integration.ActionEncoding
import Zcash.Circuits.Integration.ActionGateCoherence
import Zcash.Snark.Soundness.TopLevelTerminal
import Mathlib.Util.AssertNoSorry

/-!
# Action public-instance commitment provenance

The verifier's public-instance commitment is determined by the supplied Action rows
and the monomial URS. This module constructs the compatible Lagrange key directly
from that URS, defines the verifier commitment, and specializes the Action semantic
endpoint so neither the key nor its commitment equation is an external premise.
-/

namespace Zcash.Snark

open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action

namespace ActionInstanceCommitment

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/-- The canonical Lagrange commitment key derived from a monomial URS and domain
generator. Each row generator is, by construction, the monomial commitment to the
corresponding interpolating basis polynomial. -/
noncomputable def instanceKey
    (pp : ProofParams) (urs : URS G) :
    LagrangeCommitmentKey urs
      (actionCircuit.toVerifierKey pp urs).omega where
  generators := fun i =>
    commit urs
      (polynomialCoefficients (2 ^ urs.k)
        (rowPolynomial
          (actionCircuit.toVerifierKey pp urs).omega
          (Pi.single i (1 : Fp))))
  generator_eq := fun _ => rfl

/-- The verifier-derived commitment family for the Action circuit's declared public
instance rows. Column serialization is derived from `actionCircuit.publicInputLayout`. -/
noncomputable def commitment
    (pp : ProofParams) (urs : URS G) {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInputs Fp) :
    Fin numProofs → ℕ → G :=
  fun proofIndex column =>
    (instanceKey pp urs).commitInstance
      (actionCircuit.publicInputRows
        (inputs proofIndex) ⟨column⟩) 1

omit [DecidableEq G] in
@[simp] theorem commitment_column
    (pp : ProofParams) (urs : URS G) {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInputs Fp)
    (proofIndex : Fin numProofs) (column : Column .instance) :
    commitment pp urs inputs proofIndex column.index =
      (instanceKey pp urs).commitInstance
        (actionCircuit.publicInputRows
          (inputs proofIndex) column) 1 :=
  rfl

assert_no_sorry commitment_column

omit [DecidableEq G] in
/-- Every declared public column commitment is the monomial-URS commitment to its
layout-derived row polynomial, with Halo 2's default blind. -/
theorem commitment_column_eq_commit
    (pp : ProofParams) (urs : URS G) {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInputs Fp)
    (proofIndex : Fin numProofs) (column : Column .instance) :
    commitment pp urs inputs proofIndex column.index =
      commit urs
          (instanceCoefficients (2 ^ urs.k)
            (actionCircuit.toVerifierKey pp urs).omega
            (actionCircuit.publicInputRows
              (inputs proofIndex) column)) +
        urs.w := by
  rw [commitment_column,
    LagrangeCommitmentKey.commitInstance_eq, one_smul]

assert_no_sorry commitment_column_eq_commit

/--
Construct the Action circuit's component-level correctness package for the
canonical polynomial assignment selected by an accepting run.

This is the circuit-owned adapter consumed by the generic top-level Vesta
capstone. It exposes gate, fixed/selector, copy, and lookup facts, but no Action
statement.
-/
noncomputable def topLevelCorrectnessOfAcceptedCircuitSat
    (pp : ProofParams) (urs : URS G)
    (hk :
      (pp.mergeDerived actionCircuit).k = urs.k)
    (inputs :
      Fin (pp.mergeDerived actionCircuit).numProofs →
        PublicInputs Fp)
    (ps : ProofString
      (pp.mergeDerived actionCircuit) Fp G)
    (ch : Challenges
      (pp.mergeDerived actionCircuit).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := commitment pp urs inputs)
          urs hk (actionCircuit.toVerifierKey pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := commitment pp urs inputs)
          (actionCircuit.toVerifierKey pp urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := commitment pp urs inputs)
          (actionCircuit.toVerifierKey pp urs) ps ch),
      OpenedMemberDecode
        (instanceCommitment := commitment pp urs inputs)
        urs hk (actionCircuit.toVerifierKey pp urs)
        ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts urs hk
        (actionCircuit.toVerifierKey pp urs)
        (commitment pp urs inputs) ps ch)
    (hpoly : Polynomial Fp)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding :=
          ActionPermutationDomain.blindingFactors_lt pp urs)
        haccepts).CircuitSat
          ch.y hpoly
          (actionCircuit.toVerifierKey pp urs).n a)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).constraints
          (actionCircuit.toVerifierKey pp urs).n j))
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        (actionCircuit.toVerifierKey pp urs)
        ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        actionActiveRows)
    (lookupExclusions :
      TopLevelLookupCoherence.TopLevelLookupChallengeExclusions
        actionCircuit pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)) :
    TopLevelCircuitCorrectness
      actionCircuit pp urs ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := memberDecode) haccepts)
      (FlatCell actionNumPermCols actionDomainSize)
      (HasNontrivialRelation (F := Fp) urs.g urs.u urs.w) := by
  let relation :=
    CanonicalMemberConstraintRelation.ofAcceptedCircuitSat
      haccepts hsatisfied
  have hpolynomial :
      relation.polynomial =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts := by
    rfl
  have hcorrect :=
    Zcash.Snark.actionTopLevelCircuitCorrectness
      pp urs hk (commitment pp urs inputs) ps ch pU pW a
      batchOpenings memberDecode hpoly relation
      (by
        simpa only [
          CanonicalMemberConstraintRelation.model,
          hpolynomial] using hgoodY)
      (by simpa only [hpolynomial] using permutationExclusions)
      (by simpa only [hpolynomial] using lookupExclusions)
  simpa only [hpolynomial] using hcorrect

assert_no_sorry topLevelCorrectnessOfAcceptedCircuitSat

/--
Present the generic statement of the accepted Action top-level circuit as the
external Action bundle statement.

Acceptance fixes the canonical instance-column route. Public-instance commitment
binding either identifies that polynomial with the supplied Action rows or yields
the shared augmented-basis relation.
-/
theorem action_bundleStatement_or_relation_of_accepted_topLevelBundleStatement
    (pp : ProofParams) (urs : URS G)
    (hk :
      (pp.mergeDerived actionCircuit).k = urs.k)
    (inputs :
      Fin (pp.mergeDerived actionCircuit).numProofs →
        PublicInputs Fp)
    (ps : ProofString
      (pp.mergeDerived actionCircuit) Fp G)
    (ch : Challenges
      (pp.mergeDerived actionCircuit).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := commitment pp urs inputs)
          urs hk (actionCircuit.toVerifierKey pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := commitment pp urs inputs)
          (actionCircuit.toVerifierKey pp urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := commitment pp urs inputs)
          (actionCircuit.toVerifierKey pp urs) ps ch),
      OpenedMemberDecode
        (instanceCommitment := commitment pp urs inputs)
        urs hk (actionCircuit.toVerifierKey pp urs)
        ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts urs hk
        (actionCircuit.toVerifierKey pp urs)
        (commitment pp urs inputs) ps ch)
    (htop :
      TopLevelBundleStatement actionCircuit pp
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)) :
    BundleStatement inputs ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  by_cases hrelation :
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
  · exact Or.inr hrelation
  · have hrows :=
      actionRowsInjectiveAtUrs pp urs hk
    have hencoding : ∀ proofIndex,
        let assignment : TopLevelAssignment actionCircuit
            (pp.mergeDerived actionCircuit).numProofs proofIndex :=
          { polynomial :=
              CanonicalMemberConstraintRelation.acceptedPolynomial
                (memberDecode := memberDecode) haccepts }
        assignment.PublicInputEncoding (inputs proofIndex) := by
      intro proofIndex
      let assignment : TopLevelAssignment actionCircuit
          (pp.mergeDerived actionCircuit).numProofs proofIndex :=
        { polynomial :=
            CanonicalMemberConstraintRelation.acceptedPolynomial
              (memberDecode := memberDecode) haccepts }
      change assignment.PublicInputEncoding (inputs proofIndex)
      apply TopLevelAssignment.publicInputEncoding_of_publicInputRowPolynomials
          (assignment := assignment)
          (inputs proofIndex)
      · intro index
        let column :=
          (actionCircuit.publicInputLayout.cells index).1
        obtain ⟨instanceRotation, hregistered⟩ :=
          actionCircuit.exists_rotation_mem_instanceQueries_of_publicInputLayout_cell
            index
        have hbound :=
          CanonicalMemberConstraintRelation.acceptedInstanceColumn_eq_rowPolynomial_or_relation
              (pU := pU) (pW := pW) (a := a)
              (batchOpenings := batchOpenings)
              (memberDecode := memberDecode)
              haccepts proofIndex column.index
              (instanceKey pp urs)
              (actionCircuit.publicInputRows
                (inputs proofIndex) column) 1
              (commitment_column pp urs inputs proofIndex column)
              hrows
              (instanceQuery_of_layout
                (actionCircuit.toVerifierKey pp urs)
                (commitment pp urs inputs) ps ch proofIndex
                column.index instanceRotation
                (actionCircuit.toVerifierKey_instanceQueryCount
                  pp urs)
                (QueryLayouts.instanceQueryLayout_of_constraintSystem
                  actionCircuit pp urs column
                  instanceRotation hregistered))
        have hrowPolynomial := hbound.resolve_right hrelation
        change
          CanonicalMemberConstraintRelation.acceptedPolynomial
                (memberDecode := memberDecode) haccepts
              (.instanceCol proofIndex column.index) =
            instanceRowPolynomial (2 ^ urs.k)
              (Zcash.Arithmetic.omegaOf
                actionCircuit.domainExponent)
              (actionCircuit.publicInputRows
                (inputs proofIndex) column) at hrowPolynomial
        simpa only [← hk, column] using hrowPolynomial
      · exact TopLevelAssignment.domainRowsInjective
          ActionPermutationDomain.domainExponent_lt
    have hpublic :=
      TopLevelBundleStatement.of_publicInputEncoding
        actionCircuit pp
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        inputs hencoding htop
    apply Or.inl
    intro proofIndex
    exact hpublic proofIndex

assert_no_sorry action_bundleStatement_or_relation_of_accepted_topLevelBundleStatement


/--
The deterministic `hencodes` handoff for an accepting verifier run.

The caller supplies satisfaction of the constraint model canonically routed from
that same accepting run. This theorem constructs
`CanonicalMemberConstraintRelation` internally and applies the closed Action
endpoint; no free relation, constraint family, or statement proposition remains.
-/
theorem action_bundleStatement_or_relation_of_acceptedModel_circuitSat
    (pp : ProofParams) (urs : URS G)
    (hk :
      (pp.mergeDerived actionCircuit).k = urs.k)
    (inputs :
      Fin (pp.mergeDerived actionCircuit).numProofs →
        PublicInputs Fp)
    (ps : ProofString
      (pp.mergeDerived actionCircuit) Fp G)
    (ch : Challenges
      (pp.mergeDerived actionCircuit).k Fp)
    (vk : VerifyingKey
      (pp.mergeDerived actionCircuit) Fp G)
    (hvk :
      vk = actionCircuit.toVerifierKey pp urs)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := commitment pp urs inputs)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := commitment pp urs inputs)
          vk ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := commitment pp urs inputs)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := commitment pp urs inputs)
        urs hk vk ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts urs hk vk
        (commitment pp urs inputs) ps ch)
    (hblinding :
      vk.blindingFactors < vk.n)
    (hpoly : Polynomial Fp)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts).CircuitSat
          ch.y hpoly vk.n a)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).constraints
          vk.n j))
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        (actionCircuit.toVerifierKey pp urs)
        ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        actionActiveRows)
    (lookupExclusions :
      TopLevelLookupCoherence.TopLevelLookupChallengeExclusions
        actionCircuit pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)) :
    BundleStatement inputs ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  subst vk
  let relation :=
    CanonicalMemberConstraintRelation.ofAcceptedCircuitSat
      haccepts hsatisfied
  have hpolynomial :
      relation.polynomial =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts := by
    rfl
  have hgoodY' : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness relation.model.constraints
          (actionCircuit.toVerifierKey pp urs).n j) := by
    simpa only [
      CanonicalMemberConstraintRelation.model,
      hpolynomial] using hgoodY
  have hcorrect :=
    actionTopLevelCircuitCorrectness
      pp urs hk (commitment pp urs inputs) ps ch pU pW a
      batchOpenings memberDecode hpoly relation hgoodY'
      (by simpa only [hpolynomial] using permutationExclusions)
      (by simpa only [hpolynomial] using lookupExclusions)
  have hn :
      (actionCircuit.toVerifierKey pp urs).n ≠ 0 := by
    change 2 ^ actionCircuit.domainExponent ≠ 0
    positivity
  have hsatisfaction :=
    relation.constraintSatisfaction hn hgoodY'
  have htop :=
    topLevelBundleStatement_or_bad_of_constraintSatisfaction
      hblinding hsatisfaction hcorrect
  rcases htop with htop | hrelation
  · exact action_bundleStatement_or_relation_of_accepted_topLevelBundleStatement
      pp urs hk inputs ps ch pU pW a batchOpenings memberDecode haccepts htop
  · exact Or.inr hrelation

assert_no_sorry action_bundleStatement_or_relation_of_acceptedModel_circuitSat

end ActionInstanceCommitment

end Zcash.Snark
