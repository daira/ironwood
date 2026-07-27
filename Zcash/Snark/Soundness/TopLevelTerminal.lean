import Zcash.Circuits.Integration.TopLevelCorrectness
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.TopLevelAssignment
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation

/-!
# Generic top-level circuit soundness terminal

This module is the core soundness endpoint for a Clean `TopLevelCircuit`.  It
turns satisfaction of the verifier-native canonical constraint model into the
circuit's own statement for every proof in the bundle.

The Clean/Ironwood representation work remains exposed as named component
conditions.  In particular, `TopLevelCircuitCorrectness` does not contain the
desired statement or an opaque encoding implication.
-/

namespace Zcash.Snark

open Halo2 Polynomial

set_option maxHeartbeats 20000

set_option cleanup.letToHave false in
/--
Canonical constraint satisfaction plus the component-level circuit correctness
package implies the circuit-owned statement for every proof, preserving the one
shared exceptional event.
-/
noncomputable def topLevelBundleStatement_or_bad_of_constraintSatisfaction
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    {ch : Challenges (pp.mergeDerived top).k Fp}
    {poly : CommitmentId → Polynomial Fp}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (hblinding :
      (top.toVerifierKey pp urs).blindingFactors <
        (top.toVerifierKey pp urs).n)
    (satisfaction :
      ConstraintSatisfaction
        (canonicalConstraintModelOfPermutationResolver
          (top.toVerifierKey pp urs) ch poly hblinding)
        (top.toVerifierKey pp urs).n)
    (correctness :
      TopLevelCircuitCorrectness top pp urs ch poly cell Bad) :
    TopLevelBundleStatement top pp poly ⊕' Bad := by
  classical
  refine bindOrRelationWitness
    (finForallOrRelationWitness
      (A := fun proofIndex : Fin (pp.mergeDerived top).numProofs =>
        top.Statement (top.extractPublicInput
          ({ polynomial := poly } :
            TopLevelAssignment top (pp.mergeDerived top).numProofs proofIndex).environment))
      fun proofIndex => ?_)
    (fun h => h)
  rcases correctness.fixed proofIndex with hfixed | hbad
  swap
  · exact PSum.inr hbad
  rcases correctness.fixedEncoding proofIndex with hfixedEncoding | hbad
  swap
  · exact PSum.inr hbad
  rcases correctness.copies proofIndex with hcopies | hbad
  swap
  · exact PSum.inr hbad
  rcases correctness.lookups proofIndex with hlookups | hbad
  swap
  · exact PSum.inr hbad
  let assignment :
      TopLevelAssignment top (pp.mergeDerived top).numProofs proofIndex :=
    { polynomial := poly }
  -- Ascribed to the form `ofTopLevelCanonical` expects. Left to unification, matching
  -- `Fin (2 ^ top.domainExponent)` against `Fin (top.toVerifierKey pp urs).n` diverges.
  have hrows : Function.Injective
      fun row : Fin (top.toVerifierKey pp urs).n =>
        (top.toVerifierKey pp urs).omega ^ (row : ℕ) :=
    TopLevelAssignment.domainRowsInjective
      (top := top) correctness.gates.domainExponent_lt
  have hroot :=
    TopLevelAssignment.domainRoot
      (top := top) correctness.gates.domainExponent_lt
  have bridge :
      FullCircuitBridge top.placement
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations) 0 cell Bad :=
    FullCircuitBridge.ofTopLevelCanonical (cell := cell) (Bad := Bad)
      correctness.gates ch poly proofIndex hblinding satisfaction
      hrows hroot hfixed.1 hfixed.2 hcopies hlookups
  let assignment :
      TopLevelAssignment top (pp.mergeDerived top).numProofs proofIndex :=
    { polynomial := poly }
  have henvironment :=
    assignment.resolverEnvironment_eq_environment
      pp urs hfixedEncoding
  have canonicalBridge :
      FullCircuitBridge top.placement assignment.environment
        top.operations 0 cell Bad := by
    rw [← henvironment]
    exact bridge
  exact
    FullCircuitBridge.topLevelSoundness_or_bad
      top assignment.proofAssignment canonicalBridge

assert_no_sorry topLevelBundleStatement_or_bad_of_constraintSatisfaction

end Zcash.Snark
