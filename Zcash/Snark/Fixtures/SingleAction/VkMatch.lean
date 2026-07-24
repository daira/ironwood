import Zcash.Snark.Fixtures.SingleAction.Fixture
import Zcash.Snark.Core.Domain
import Zcash.Snark.Keygen.Pipeline
import Zcash.Circuits.Action.TopLevel
import Clean.Halo2.TopLevelKeygen
import Mathlib.Util.AssertNoSorry

/-!
# VK equality: the capture is the derived Action circuit

The captured verifying key's constraint-system fields — gates, the three query
layouts, the permutation columns and chunks, the lookup expression families, and the
domain/permutation scalars — are computed equal to the ones derived end to end from
the ported `Action.Circuit.configure` (`TopLevelCircuit.pinnedCS` and friends: the
configure-recorded query registration, the synthesize mirror → V1 floor-planner
placement → `compress_selectors` selector map, and the derived minimal domain
exponent). The derivation has no fixture inputs left; the Rust-dumped `actionSelMap`
survives only as a cross-check in `TestSelMapDerivation`.

The pinned comparison is stated as a record-update equality
(`capturedPinnedView = actionPinnedCs`): the derived pinned record with every
CAPTURED family overridden by the capture's value. The upstream fixture exporter does
not emit the pinned-CS metadata (`numFixedColumns`, `numAdviceColumns`,
`numSelectors`, `constants`, `minimumDegree`), so those five fields carry over from
the derived record and are not independently cross-checked here — their load-bearing
consequences are pinned elsewhere: wrong counts or constants change the derived fixed
columns and fail the commitment certificate (`Keygen/Certificate.lean`), and
`chunkLen` (the one consequence of `minimumDegree` the verifier uses) is compared
directly below. Per-field theorems split the same equality so a regeneration drift
names the diverging field.

The query-registration order is recorded by `configure` itself (Clean's
configure-time query registration: each gate's `queriedCells` in Rust closure order),
so the equality certifies the circuit's own recorded order against the capture — no
fixed-point caveat: a wrong per-gate list shifts the derived layouts and fails here.
Compiler-trust boundary: like the fingerprint match, these are `native_decide` facts
about one concrete capture, never general theorems (see `TrustBoundary` in this
directory for the discipline).
-/

namespace Zcash.Snark.Fixture

open Halo2
open Zcash.Circuits.Action (orchardActionTopLevelCircuit)

/-- The pinned CS derived from the closed Action circuit — the
`TopLevelCircuit.pinnedCS` method (Clean's `FormalCircuit.toPinnedCS`): query order
from the circuit's own configure-recorded registration (see the module docstring), at
the derived domain size (`TopLevelCircuit.domainExponent`, the keygen fit condition —
no domain constant survives as an input either). -/
def actionPinnedCs : PinnedConstraintSystem Fp :=
  orchardActionTopLevelCircuit.pinnedCS

/-- The capture's permutation columns, in raw column space. The captured
`vk.permutationChunks` stores the verifier view — `ColumnRef`s in QUERY-INDEX space
(`ColumnRef.resolve` reads the eval arrays by query index) — so each ref resolves to
its column through the captured query layouts (permutation queries are always
cur-rotation, so the lookup is exact). -/
def capturedPermutationColumns : List Halo2.AnyColumn :=
  vk.permutationChunks.flatten.map fun p =>
    match p.1 with
    | .advice qi => ⟨.advice, (vk.adviceQueryLayout.getD qi (0, 0)).1⟩
    | .fixed qi => ⟨.fixed, (vk.fixedQueryLayout.getD qi (0, 0)).1⟩
    | .instance qi => ⟨.instance, (vk.instanceQueryLayout.getD qi (0, 0)).1⟩

/-- The derived pinned record with every CAPTURED family overridden by the capture's
value: the captured gate/lookup expressions are verifier-typed `Zcash.Snark.Expr`, so
they convert at the boundary (`RichExpression.ofExpr`); the lookup families are the
`Fin`-function views re-listed. Equality with `actionPinnedCs` pins exactly the
captured data (the five uncaptured metadata fields are carried over — see the module
docstring). -/
def capturedPinnedView : PinnedConstraintSystem Fp :=
  { actionPinnedCs with
    numInstanceColumns := capturedNumInstanceColumns
    gates := vk.gates.map RichExpression.ofExpr
    adviceQueryLayout := vk.adviceQueryLayout
    fixedQueryLayout := vk.fixedQueryLayout
    instanceQueryLayout := vk.instanceQueryLayout
    permutationColumns := capturedPermutationColumns
    lookupInputExprs := (List.ofFn vk.lookupInputExprs).map (·.map RichExpression.ofExpr)
    lookupTableExprs := (List.ofFn vk.lookupTableExprs).map (·.map RichExpression.ofExpr) }

/-- **The capture is the derived Action circuit** (pinned CS), and the derivation is
well-formed: the domain exponent computes to orchard's pinned `K = 11`
(`circuit.rs:76`) and no `queriedCells` entry poisoned the registration. One bundled
`native_decide` — separate per-fact theorems would re-evaluate the shared selector-map
and projection work once each; the field/fact splits below are `congrArg` projections
of this single evaluation. -/
theorem capturedPinnedView_eq_derived_and_wellFormed :
    (capturedPinnedView, orchardActionTopLevelCircuit.domainExponent,
      orchardActionTopLevelCircuit.constraintSystem.invalidQueriedCells.isEmpty,
      (flatGates orchardActionTopLevelCircuit.constraintSystem).all
        (·.selectorsCovered (fun i => (orchardActionTopLevelCircuit.selMapDerived.lookup i).isSome)))
      = (actionPinnedCs, 11, true, true) := by native_decide

/-- **The capture is the derived Action circuit** (pinned CS, captured families). -/
theorem capturedPinnedView_eq_derived : capturedPinnedView = actionPinnedCs := by
  have h := capturedPinnedView_eq_derived_and_wellFormed
  simp only [Prod.mk.injEq] at h
  exact h.1

/-- The derived domain exponent is orchard's pinned `K = 11` (`circuit.rs:76`). -/
theorem actionK_eq : orchardActionTopLevelCircuit.domainExponent = 11 := by
  have h := capturedPinnedView_eq_derived_and_wellFormed
  simp only [Prod.mk.injEq] at h
  exact h.2.1

/-- Every hand-listed `queriedCells` entry was a well-formed query atom (the poison
list is empty) — the registration recorded exactly the per-gate lists. -/
theorem action_queriedCells_wellFormed :
    orchardActionTopLevelCircuit.constraintSystem.invalidQueriedCells.isEmpty := by
  have h := capturedPinnedView_eq_derived_and_wellFormed
  simp only [Prod.mk.injEq] at h
  exact h.2.2.1

/-- The selector-compression map covers every selector atom of every Action gate — the
coverage side condition of `PinnedConstraintSystem.derive_gates_eval`. -/
theorem action_gates_selectorsCovered :
    ((flatGates orchardActionTopLevelCircuit.constraintSystem).all
      (·.selectorsCovered (fun i => (orchardActionTopLevelCircuit.selMapDerived.lookup i).isSome)))
      = true := by
  have h := capturedPinnedView_eq_derived_and_wellFormed
  simp only [Prod.mk.injEq] at h
  exact h.2.2.2

/-- **The captured verifying key's gates are the derived Action circuit's.** The
verifying key holds `Zcash.Snark.Expr` gates and the derivation holds
`Halo2.RichExpression` gates, so the equality is stated through the boundary
conversion `RichExpression.ofExpr`. -/
theorem vk_gates_eq_derived :
    vk.gates.map RichExpression.ofExpr = actionPinnedCs.gates :=
  congrArg PinnedConstraintSystem.gates capturedPinnedView_eq_derived

theorem vk_adviceQueryLayout_eq_derived :
    vk.adviceQueryLayout = actionPinnedCs.adviceQueryLayout :=
  congrArg PinnedConstraintSystem.adviceQueryLayout capturedPinnedView_eq_derived

theorem vk_fixedQueryLayout_eq_derived :
    vk.fixedQueryLayout = actionPinnedCs.fixedQueryLayout :=
  congrArg PinnedConstraintSystem.fixedQueryLayout capturedPinnedView_eq_derived

theorem vk_instanceQueryLayout_eq_derived :
    vk.instanceQueryLayout = actionPinnedCs.instanceQueryLayout :=
  congrArg PinnedConstraintSystem.instanceQueryLayout capturedPinnedView_eq_derived

theorem vk_lookupInputExprs_eq_derived :
    (List.ofFn vk.lookupInputExprs).map (·.map RichExpression.ofExpr)
      = actionPinnedCs.lookupInputExprs :=
  congrArg PinnedConstraintSystem.lookupInputExprs capturedPinnedView_eq_derived

theorem vk_lookupTableExprs_eq_derived :
    (List.ofFn vk.lookupTableExprs).map (·.map RichExpression.ofExpr)
      = actionPinnedCs.lookupTableExprs :=
  congrArg PinnedConstraintSystem.lookupTableExprs capturedPinnedView_eq_derived

theorem permutationColumns_eq :
    capturedPermutationColumns = actionPinnedCs.permutationColumns :=
  congrArg PinnedConstraintSystem.permutationColumns capturedPinnedView_eq_derived

theorem numInstanceColumns_eq :
    capturedNumInstanceColumns = actionPinnedCs.numInstanceColumns :=
  congrArg PinnedConstraintSystem.numInstanceColumns capturedPinnedView_eq_derived

/-! ## The VK's domain and permutation scalars, derived

The captured `vk`'s scalar fields — previously transcribed constants — are all
computable from the circuit: `omega`/`n` from the derived domain exponent
(`TopLevelCircuit.domainExponent`), `blindingFactors` from the configure-recorded
advice queries, `delta` a pasta constant, `chunkLen` from the ported `cs.degree()`,
and `permutationChunks` the recorded permutation columns chunked by it. -/

/-- ONE bundled `native_decide` for the scalars and the permutation chunks (separate
theorems would re-evaluate the shared selector-map/projection work once each; the
nesting `((…), chunks)` rather than a flat 6-tuple is what instance synthesis accepts). -/
theorem vk_scalars_and_chunks_derived :
    ((vk.omega, vk.n, vk.blindingFactors, vk.delta, vk.chunkLen), vk.permutationChunks)
      = ((omegaOf orchardActionTopLevelCircuit.domainExponent,
            2 ^ orchardActionTopLevelCircuit.domainExponent,
            orchardActionTopLevelCircuit.constraintSystem.blindingFactors, deltaFp,
            orchardActionTopLevelCircuit.constraintSystem.chunkLen),
          Keygen.permutationChunksOf orchardActionTopLevelCircuit.selMapDerived
            orchardActionTopLevelCircuit.constraintSystem) := by
  native_decide

theorem vk_scalars_derived :
    (vk.omega, vk.n, vk.blindingFactors, vk.delta, vk.chunkLen)
      = (omegaOf orchardActionTopLevelCircuit.domainExponent,
          2 ^ orchardActionTopLevelCircuit.domainExponent,
          orchardActionTopLevelCircuit.constraintSystem.blindingFactors, deltaFp,
          orchardActionTopLevelCircuit.constraintSystem.chunkLen) := by
  have h := vk_scalars_and_chunks_derived
  simp only [Prod.mk.injEq] at h ⊢
  exact h.1

theorem vk_permutationChunks_derived :
    vk.permutationChunks
      = Keygen.permutationChunksOf orchardActionTopLevelCircuit.selMapDerived
        orchardActionTopLevelCircuit.constraintSystem := by
  have h := vk_scalars_and_chunks_derived
  simp only [Prod.mk.injEq] at h
  exact h.2

assert_no_sorry capturedPinnedView_eq_derived
assert_no_sorry action_gates_selectorsCovered
assert_no_sorry action_queriedCells_wellFormed
assert_no_sorry actionK_eq
assert_no_sorry vk_scalars_and_chunks_derived

end Zcash.Snark.Fixture
