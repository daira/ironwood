import Zcash.Circuits.TopLevelKeygen
import Zcash.Snark.Soundness.ResolverGates
import Zcash.Snark.Soundness.ResolverQueryEnvironment
import Zcash.Snark.Soundness.SelectorCoherence

/-!
# Generic top-level gate bridge

This module packages the static facts that connect a closed formal circuit's own
keygen derivation to a verifier key.  The package is circuit-independent: the
incoming `FormalCircuit.toVerifyingKey` construction should produce it generically.

Given that static package and realization of the circuit-derived packed selector
rows by the decoded fixed polynomials, every enabled circuit gate receives the
polynomial witness consumed by the generic constraint-satisfaction split.
-/

namespace Zcash.Snark

open Halo2 Polynomial
open Zcash.Circuits

set_option maxHeartbeats 20000

/--
Static coherence between a top-level circuit's own keygen data and a verifier key.

No placement, operation stream, selector map, or pinned constraint system is supplied
by the caller: all four are derived from `top`.  The remaining fields are validity
certificates and field equalities that `FormalCircuit.toVerifyingKey` is expected to
expose. Gate/lookup registration coherence is absent because the circuit-derived
constraint system closes the raw configure result under synthesis by construction.
-/
structure TopLevelGateCoherence
    {shape : Shape} {G : Type*}
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (vk : VerifyingKey shape Fp G) : Prop where
  gatesWellFormed : top.constraintSystem.GatesWellFormed
  gateSelectorsAllocated :
    top.constraintSystem.GateSelectorsAllocated
  gates :
    (PinnedConstraintSystem.derive
      top.constraintSystem top.selectorMap).gates =
        vk.gates.map RichExpression.ofExpr
  adviceQueryLayout :
    (PinnedConstraintSystem.derive
      top.constraintSystem top.selectorMap).adviceQueryLayout =
        vk.adviceQueryLayout
  fixedQueryLayout :
    (PinnedConstraintSystem.derive
      top.constraintSystem top.selectorMap).fixedQueryLayout =
        vk.fixedQueryLayout
  instanceQueryLayout :
    (PinnedConstraintSystem.derive
      top.constraintSystem top.selectorMap).instanceQueryLayout =
        vk.instanceQueryLayout
  adviceQueryCount :
    vk.adviceQueryLayout.length = shape.numAdviceQueries
  fixedQueryCount :
    vk.fixedQueryLayout.length = shape.numFixedQueries
  instanceQueryCount :
    vk.instanceQueryLayout.length = shape.numInstanceQueries
  omega_ne_zero : vk.omega ≠ 0
  selectorDegree :
    csDegree top.constraintSystem < scalarFieldOrder

namespace TopLevelGateCoherence

variable
    {shape : Shape} {G : Type*}
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]
    {top : TopLevelCircuit Fp ConfigInput Config Output}
    {vk : VerifyingKey shape Fp G}

/--
The final pinned query state interprets the resolver feeds, and restricts to the
intermediate gate-erasure state because lookup erasure only appends query entries.
-/
theorem resolverInterpretsGates
    (coherence : TopLevelGateCoherence top vk)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex : Fin shape.numProofs) (usableRows row : ℕ) :
    Interprets
      (eraseGates
        ((flatGates top.constraintSystem).map
          (substSelectorMap top.selectorMap.lookup))
        (queryWalkInit top.selectorMap
          top.constraintSystem)).2
      (fun query =>
        (fixedQueryFeedOfResolver vk poly query).eval
          (vk.omega ^ row))
      (fun query =>
        (adviceQueryFeedOfResolver vk poly proofIndex query).eval
          (vk.omega ^ row))
      (fun query =>
        (instanceQueryFeedOfResolver vk poly proofIndex query).eval
          (vk.omega ^ row))
      (Query.eval
        (resolverEnvironment vk poly proofIndex usableRows)
        (fun _ => 0) row) := by
  have hfinal := resolverQueryFeeds_interpret
    vk poly proofIndex usableRows (fun _ => 0) row
    coherence.omega_ne_zero
    (pinnedQueryState
      (PinnedConstraintSystem.derive
        top.constraintSystem top.selectorMap))
    (by
      simpa [pinnedQueryState] using
        coherence.adviceQueryLayout)
    (by
      simpa [pinnedQueryState] using
        coherence.fixedQueryLayout)
    (by
      simpa [pinnedQueryState] using
        coherence.instanceQueryLayout)
    coherence.adviceQueryCount
    coherence.fixedQueryCount
    coherence.instanceQueryCount
  apply hfinal.mono
  exact
    PinnedConstraintSystem.derive_queryState_extends_gates
      top.constraintSystem top.selectorMap

/--
Every enabled constraint in the top-level operation stream has the corresponding
resolver gate polynomial witness.
-/
noncomputable def polynomialWitness
    (coherence : TopLevelGateCoherence top vk)
    (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (sets : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) ×
        List (Polynomial Fp × Polynomial Fp)))
    (l0 lLast lBlind : Polynomial Fp)
    (proofIndex : Fin shape.numProofs) (usableRows : ℕ)
    (hfixed : SelectorActivationsRealized top.selectorMap
      top.selectorActivations
      (resolverEnvironment vk poly proofIndex usableRows))
    (enabled : EnabledGate Fp)
    (henabled :
      enabled ∈ operationEnabledGates (top.operations 0) 0)
    (constraint : Constraint Fp)
    (hconstraint : constraint ∈ enabled.gate.constraints) :
    EnabledGate.PolynomialWitness
      (constraintModelOfResolver vk ch poly sets chunks
        l0 lLast lBlind)
      proofIndex vk.omega top.placement
      (resolverEnvironment vk poly proofIndex usableRows)
      enabled constraint := by
  have hgate : enabled.gate ∈ top.constraintSystem.gates :=
    OperationsKeygenCoherent.gate
      top.keygenCoherent henabled
  have hselector :
      enabled.gate.selector.index <
        top.constraintSystem.numSelectors :=
    coherence.gateSelectorsAllocated.gate hgate
  have hlookupSome :
      (top.selectorMap.lookup
        enabled.gate.selector.index).isSome = true := by
    simpa [TopLevelCircuit.selectorMap] using
      deriveSelCompressMap_lookup_isSome_of_lt
        top.constraintSystem
        (2 ^ top.domainExponent)
        top.selectorActivations hselector
  have hlookupPresent :
      (top.selectorMap.lookup
        enabled.gate.selector.index).isSome := by
    simpa using hlookupSome
  let compressed :=
    Classical.choose
      (Option.isSome_iff_exists.mp hlookupPresent)
  have hcompressed :
      top.selectorMap.lookup enabled.gate.selector.index =
        some compressed :=
    Classical.choose_spec
      (Option.isSome_iff_exists.mp hlookupPresent)
  have hroots :
      SelectorRootsWellFormed top.selectorMap := by
    change SelectorRootsWellFormed
      (deriveSelCompressMap top.constraintSystem
        (2 ^ top.domainExponent) top.selectorActivations)
    exact selectorRootsWellFormed_deriveSelCompressMap
        top.constraintSystem
        (2 ^ top.domainExponent)
        top.selectorActivations coherence.selectorDegree
  have hcoverage :
      ∀ expression ∈ flatGates top.constraintSystem,
        expression.selectorsCovered
          (fun selector =>
            (top.selectorMap.lookup selector).isSome) = true := by
    simpa [TopLevelCircuit.selectorMap] using
      gateSelectorsCovered_deriveSelCompressMap
        top.constraintSystem
        (2 ^ top.domainExponent)
        top.selectorActivations
        coherence.gateSelectorsAllocated
  have hgates :
      (PinnedConstraintSystem.derive
        top.constraintSystem top.selectorMap).gates =
          vk.gates.map RichExpression.ofExpr := by
    exact coherence.gates
  have hinterpret := coherence.resolverInterpretsGates
    poly proofIndex usableRows
    (top.placement enabled.region + enabled.row)
  have hscale :
      (selReplacement compressed).eval
        (Query.eval
          (resolverEnvironment vk poly proofIndex usableRows)
          (fun _ => 0)
          (top.placement enabled.region + enabled.row)) ≠ 0 := by
    apply selectorScale_ne_zero_of_enabledGate
      top.selectorMap top.regionStarts (top.operations 0) 0
      (resolverEnvironment vk poly proofIndex usableRows)
      (fun _ => 0) hroots
    · exact hfixed
    · exact henabled
    · exact hcompressed
  exact enabledGatePolynomialWitnessOfResolver
    vk top.constraintSystem top.selectorMap ch poly sets chunks
    l0 lLast lBlind proofIndex top.placement usableRows
    enabled constraint hgate hconstraint
    coherence.gatesWellFormed hgates hcoverage
    compressed hcompressed hinterpret hscale

/--
Deployed gate divisibility therefore supplies the complete gate component of the
top-level circuit's Clean constraints.
-/
theorem constraints
    (coherence : TopLevelGateCoherence top vk)
    (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (sets : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) ×
        List (Polynomial Fp × Polynomial Fp)))
    (l0 lLast lBlind : Polynomial Fp)
    (proofIndex : Fin shape.numProofs) (usableRows n : ℕ)
    (satisfaction :
      ConstraintSatisfaction
        (constraintModelOfResolver vk ch poly sets chunks
          l0 lLast lBlind) n)
    (domain : ∀ row : ℕ, (vk.omega ^ row) ^ n = 1)
    (hfixed : SelectorActivationsRealized top.selectorMap
      top.selectorActivations
      (resolverEnvironment vk poly proofIndex usableRows)) :
    CircuitConstraintFamily.constraints .gate top.placement
      (resolverEnvironment vk poly proofIndex usableRows)
      (top.operations 0) 0 := by
  apply gate_constraints_of_polynomial_witnesses
    (constraintModelOfResolver vk ch poly sets chunks
      l0 lLast lBlind)
    proofIndex vk.omega top.placement
    (resolverEnvironment vk poly proofIndex usableRows)
    (top.operations 0) 0 satisfaction domain
  intro enabled henabled constraint hconstraint
  exact coherence.polynomialWitness
    ch poly sets chunks l0 lLast lBlind proofIndex usableRows
    hfixed enabled henabled constraint hconstraint

end TopLevelGateCoherence

end Zcash.Snark
