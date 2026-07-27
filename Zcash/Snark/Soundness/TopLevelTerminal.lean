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

/-! ## Why this file disables `cleanup.letToHave`

`topLevelBundleStatement_or_bad_of_constraintSatisfaction` was a `theorem` concluding
`… ∨ Bad`. Carrying the break as data made it a `noncomputable def` concluding `… ⊕' Bad`,
and that alone made it fail to elaborate — `(deterministic) timeout at 'whnf'`, reported
against the declaration name, and unaffected by raising `maxHeartbeats` to two million.

The cause is not in the proof. `Meta.letToHave` is a post-elaboration pass that rewrites
nondependent `let` into `have` in definition *values*. It is skipped for theorems and for
declarations whose type is a `Prop`, so it never ran here before; a `Type`-valued `def`
switches it on. Under a `let` it re-typechecks the body from scratch, outside the
elaborator's unification context. That re-check re-derives the domain equality at the
`hrows` argument of `ofTopLevelCanonical` — `Fin (2 ^ top.domainExponent)` against
`Fin (top.toVerifierKey pp urs).n` — down a path where `whnf` attacks the `2 ^ …` side and
unfolds `top.domainExponent` into `minimalKForRows` and on into `FormalCircuit.synthesize`,
i.e. it tries to run the Clean circuit compiler on an abstract `top`. That does not
terminate on a symbolic circuit, which is why no heartbeat budget helps. The kernel is not
involved: it checks the same equality without trouble.

**This is a hazard for the rest of the breaks-as-data conversion, not a quirk of this file.**
Any declaration moved from `Prop` to `Type` whose proof combines a tactic `let` with a
unification-heavy defeq below it can hit the same pass. The alternatives, if disabling the
pass is unwelcome, are to keep such facts ascribed and *above* every `let`, or to avoid the
`let` entirely.

Diagnosis credit: traced with `trace.profiler` and `set_option diagnostics true`, which
showed `TopLevelCircuit.formalCircuit` unfolding 62,561 times.
-/

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
  -- Ascribed to the form `ofTopLevelCanonical` expects, so the domain equality is settled
  -- here rather than at the argument position. Not sufficient on its own — see the note on
  -- `cleanup.letToHave` above, which is what actually makes this declaration elaborate.
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
