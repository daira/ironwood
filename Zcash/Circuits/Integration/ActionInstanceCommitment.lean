import Zcash.Circuits.Integration.ActionEncoding
import Zcash.Circuits.Integration.ActionGateCoherence
import Zcash.Circuits.Integration.TopLevelInstanceCommitment
import Zcash.Snark.Soundness.TopLevelTerminal
import Mathlib.Util.AssertNoSorry

/-!
# Action accepted-model specialization

Generic public-instance commitment provenance lives in
`TopLevelInstanceCommitment`. This module retains the Action correctness constructor
and deterministic accepted-model specialization that consume it.
-/

namespace Zcash.Snark

open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action

namespace ActionInstanceCommitment

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

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
          (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
          urs hk (actionCircuit.toVerifierKey pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
          (actionCircuit.toVerifierKey pp urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
          (actionCircuit.toVerifierKey pp urs) ps ch),
      OpenedMemberDecode
        (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
        urs hk (actionCircuit.toVerifierKey pp urs)
        ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts urs hk
        (actionCircuit.toVerifierKey pp urs)
        (actionCircuit.instanceCommitment pp urs inputs) ps ch)
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
      pp urs hk (actionCircuit.instanceCommitment pp urs inputs) ps ch pU pW a
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
          (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
          vk ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := actionCircuit.instanceCommitment pp urs inputs)
        urs hk vk ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts urs hk vk
        (actionCircuit.instanceCommitment pp urs inputs) ps ch)
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
      pp urs hk (actionCircuit.instanceCommitment pp urs inputs) ps ch pU pW a
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
  · simpa only [BundleStatement] using
      (TopLevelInstanceCommitment.statements_or_relation_of_accepted_topLevelBundleStatement
        actionCircuit pp urs hk inputs ps ch pU pW a batchOpenings
        memberDecode haccepts
        ActionPermutationDomain.domainExponent_lt htop)
  · exact Or.inr hrelation

assert_no_sorry action_bundleStatement_or_relation_of_acceptedModel_circuitSat

end ActionInstanceCommitment

end Zcash.Snark
