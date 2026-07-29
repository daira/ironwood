import Zcash.Circuits.Integration.TopLevelCorrectness
import Zcash.Circuits.Integration.TopLevelInstanceCommitment
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.TopLevelAssignment
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation

/-!
# Generic top-level circuit soundness terminal

This module is the core soundness endpoint for a Clean `TopLevelCircuit`. It
turns satisfaction of the verifier-native canonical constraint model into the
circuit's own statement for every proof in the bundle, and binds that statement
to the public inputs supplied to an accepting verifier.

The Clean/Ironwood representation work remains exposed as named component
conditions.  In particular, `TopLevelCircuitCorrectness` does not contain the
desired statement or an opaque encoding implication.
-/

namespace Zcash.Snark

open Halo2 Polynomial

universe u v w

def TopLevelTerminalOutcome
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams)
    (poly : CommitmentId → Polynomial Fp)
    (Bad : Type) : Type :=
  TopLevelBundleStatement top pp poly ⊕' Bad

private def bindOutcome {A : Sort u} {B : Sort v} {R : Sort w}
    (outcome : A ⊕' R) (next : A → B ⊕' R) : B ⊕' R :=
  match outcome with
  | .inl value => next value
  | .inr bad => .inr bad

def topLevelBundleStatement_or_bad_of_components
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    {ch : Challenges (pp.mergeDerived top).k Fp}
    {poly : CommitmentId → Polynomial Fp}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (satisfaction :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly)
        (top.toVerifierKey pp urs).n)
    (gates : TopLevelGateCoherence top)
    (fixedEncoding : ∀ proofIndex,
      TopLevelFixedEncoding top pp urs poly proofIndex)
    (fixed : ∀ proofIndex,
      TopLevelFixed top pp urs poly proofIndex)
    (copies : ∀ proofIndex,
      TopLevelCopies top pp urs poly cell Bad proofIndex)
    (lookups : ∀ proofIndex,
      TopLevelLookups top pp urs ch poly proofIndex) :
    TopLevelTerminalOutcome top pp poly Bad := by
  exact
    finForallOrRelationWitness
      (A := fun proofIndex =>
        let assignment :
            TopLevelAssignment top
              (pp.mergeDerived top).numProofs proofIndex :=
          { polynomial := poly }
        top.Statement
          (top.extractPublicInput
            (top.environment assignment.proofAssignment)))
      fun proofIndex =>
        (TopLevelAssignment.bridgeWitness_of_components
            proofIndex satisfaction gates
            (fixedEncoding proofIndex)
            (fixed proofIndex).1 (fixed proofIndex).2
            (copies proofIndex) (lookups proofIndex)).statement_or_bad

/--
Canonical constraint satisfaction plus the component-level circuit correctness
package implies the circuit-owned statement for every proof, preserving the one
shared exceptional event.
-/
def topLevelBundleStatement_or_bad_of_constraintSatisfaction
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    {ch : Challenges (pp.mergeDerived top).k Fp}
    {poly : CommitmentId → Polynomial Fp}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (satisfaction :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly)
        (top.toVerifierKey pp urs).n)
    (correctness :
      TopLevelCircuitCorrectness top pp urs ch poly cell Bad) :
    TopLevelTerminalOutcome top pp poly Bad := by
  classical
  let fixedEncodingOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelFixedEncoding top pp urs poly proofIndex)
      correctness.fixedEncoding
  let fixedOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelFixed top pp urs poly proofIndex)
      correctness.fixed
  let copiesOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelCopies top pp urs poly cell Bad proofIndex)
      correctness.copies
  let lookupsOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelLookups top pp urs ch poly proofIndex)
      correctness.lookups
  exact bindOutcome fixedEncodingOutcome fun hfixedEncoding =>
    bindOutcome fixedOutcome fun hfixed =>
      bindOutcome copiesOutcome fun hcopies =>
        bindOutcome lookupsOutcome fun hlookups =>
          topLevelBundleStatement_or_bad_of_components
            satisfaction correctness.gates
            hfixedEncoding hfixed hcopies hlookups

assert_no_sorry topLevelBundleStatement_or_bad_of_constraintSatisfaction

variable
    {G : Type} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (hk : (pp.mergeDerived top).k = urs.k)
    (inputs : Fin (pp.mergeDerived top).numProofs → PublicInput Fp)
    (ps : ProofString (pp.mergeDerived top) Fp G)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          urs hk (top.toVerifierKey pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          (top.toVerifierKey pp urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          (top.toVerifierKey pp urs) ps ch),
      OpenedMemberDecode
        (instanceCommitment := top.instanceCommitment pp urs inputs)
        urs hk (top.toVerifierKey pp urs)
        ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts urs hk
        (top.toVerifierKey pp urs)
        (top.instanceCommitment pp urs inputs) ps ch)

/--
Satisfaction of the canonical model selected by an accepting verifier run,
together with the circuit's named correctness package, yields its statements at
the public inputs supplied to the verifier.
-/
def topLevelStatements_or_relation_of_circuitSat
    (hpoly : Polynomial Fp)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding :=
          top.toVerifierKey_blindingFactors_lt_n pp urs) haccepts).CircuitSat
          ch.y hpoly (top.toVerifierKey pp urs).n a)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              top.toVerifierKey_blindingFactors_lt_n pp urs)
            haccepts).constraints
          (top.toVerifierKey pp urs).n j))
    {cell : Type} [DecidableEq cell] [Fintype cell]
    (correctness :
      TopLevelCircuitCorrectness top pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        cell
        (NontrivialRelation (F := Fp) urs.g urs.u urs.w)) :
    (∀ proofIndex, top.Statement (inputs proofIndex)) ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let relation :=
    CanonicalMemberConstraintRelation.ofAcceptedCircuitSat
      haccepts hsatisfied
  have hpolynomial :
      relation.polynomial =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts := by
    rfl
  have hn :
      (top.toVerifierKey pp urs).n ≠ 0 := by
    change 2 ^ top.domainExponent ≠ 0
    positivity
  have hsatisfaction :=
    relation.constraintSatisfaction hn
      (by
        simpa only [
          CanonicalMemberConstraintRelation.model,
          hpolynomial] using hgoodY)
  have htop :=
    topLevelBundleStatement_or_bad_of_constraintSatisfaction
      (top := top) (pp := pp) (urs := urs) (ch := ch)
      (cell := cell)
      (by simpa only [hpolynomial] using hsatisfaction)
      correctness
  rcases htop with htop | hrelation
  · exact
      TopLevelInstanceCommitment.statements_or_relation_of_accepted_topLevelBundleStatement
        top pp urs hk inputs ps ch pU pW a batchOpenings memberDecode
        haccepts correctness.gates.domainExponent_lt htop
  · exact PSum.inr hrelation

assert_no_sorry topLevelStatements_or_relation_of_circuitSat

end Zcash.Snark
