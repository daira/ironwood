import Zcash.Snark.Fixtures.SingleAction.VkCsData
import Zcash.Bridge.VkProjection
import Mathlib.Util.AssertNoSorry

/-!
# Pinned-CS equality: the capture is the derived Action circuit

Two `PinnedConstraintSystem` values: `capturedPinnedCs`, read off the capture's
CS-data dump, and `actionPinnedCs`, derived from the ported `Action.Circuit.configure`.
`capturedPinnedCs_eq_derived` computes them equal; the per-field theorems split the
same equality so a regeneration drift names the diverging field.

The derivation has no fixture inputs left: the selector-compression map is COMPUTED
circuit-side (`actionSelMapDerived`, `Bridge/VkProjection.lean` — synthesize mirror →
V1 floor-planner placement → activations → `compress_selectors`; the Rust-dumped
`actionSelMap` survives only as a cross-check in `TestSelMapDerivation`), and the
query-registration order is recorded by `configure` itself (Clean's configure-time
query registration: each gate's `queriedCells` in Rust closure order). The equality
therefore certifies the circuit's own recorded order against the capture — no
fixed-point caveat: a wrong per-gate list shifts the derived layouts and fails here.

This module deliberately imports only the capture's `VkCsData` (plain field/ℕ data) —
not the full fixture with its point captures — so the checks build in seconds;
`VkMatch` restates the result for the `vk` record. Compiler-trust boundary: like the
fingerprint match, these are `native_decide` facts about one concrete capture, never
general theorems (see `TrustBoundary` in this directory for the discipline).
-/

namespace Zcash.Snark.Fixture

open Bridge
open Circuits.Fixtures

/-- The capture's permutation columns, in raw column space. The capture's
`vkPermutationChunks` stores the verifier view — `ColumnRef`s in QUERY-INDEX space
(`ColumnRef.resolve` reads the eval arrays by query index) — so each ref resolves to
its column through the captured query layouts (permutation queries are always
cur-rotation, so the lookup is exact). -/
def capturedPermutationColumns : List Halo2.AnyColumn :=
  vkPermutationChunks.flatten.map fun p =>
    match p.1 with
    | .advice qi => ⟨.advice, (vkAdviceQueryLayout.getD qi (0, 0)).1⟩
    | .fixed qi => ⟨.fixed, (vkFixedQueryLayout.getD qi (0, 0)).1⟩
    | .instance qi => ⟨.instance, (vkInstanceQueryLayout.getD qi (0, 0)).1⟩

/-- The capture's CS data, as the pinned record. -/
def capturedPinnedCs : PinnedConstraintSystem where
  numFixedColumns := vkNumFixedColumns
  numAdviceColumns := vkNumAdviceColumns
  numInstanceColumns := vkNumInstanceColumns
  numSelectors := vkNumSelectors
  gates := vkGates
  adviceQueryLayout := vkAdviceQueryLayout
  fixedQueryLayout := vkFixedQueryLayout
  instanceQueryLayout := vkInstanceQueryLayout
  permutationColumns := capturedPermutationColumns
  lookupInputExprs := vkLookupInputExprs
  lookupTableExprs := vkLookupTableExprs
  constants := vkConstants
  minimumDegree := vkMinimumDegree

/-- The pinned CS derived from the ported Action circuit — query order from the
circuit's own configure-recorded registration (see the module docstring), at the
derived domain size `2^actionK` (`minimalK`, the keygen fit condition — no domain
constant survives as an input either). -/
def actionPinnedCs : PinnedConstraintSystem :=
  .derive actionCS (actionSelMapDerived (2 ^ actionK))

/-- **The capture is the derived Action circuit** (pinned CS), and the derivation is
well-formed: the domain exponent computes to orchard's pinned `K = 11`
(`circuit.rs:76`) and no `queriedCells` entry poisoned the registration. One bundled
`native_decide` — separate per-fact theorems would re-evaluate the shared selector-map
and projection work once each; the field/fact splits below are `congrArg` projections
of this single evaluation. -/
theorem capturedPinnedCs_eq_derived_and_wellFormed :
    (capturedPinnedCs, actionK, actionCS.invalidQueriedCells.isEmpty)
      = (actionPinnedCs, 11, true) := by native_decide

/-- **The capture is the derived Action circuit** (pinned CS). -/
theorem capturedPinnedCs_eq_derived : capturedPinnedCs = actionPinnedCs := by
  have h := capturedPinnedCs_eq_derived_and_wellFormed
  simp only [Prod.mk.injEq] at h
  exact h.1

/-- The derived domain exponent is orchard's pinned `K = 11` (`circuit.rs:76`). -/
theorem actionK_eq : actionK = 11 := by
  have h := capturedPinnedCs_eq_derived_and_wellFormed
  simp only [Prod.mk.injEq] at h
  exact h.2.1

/-- Every hand-listed `queriedCells` entry was a well-formed query atom (the poison
list is empty) — the registration recorded exactly the per-gate lists. -/
theorem action_queriedCells_wellFormed : actionCS.invalidQueriedCells.isEmpty := by
  have h := capturedPinnedCs_eq_derived_and_wellFormed
  simp only [Prod.mk.injEq] at h
  exact h.2.2

theorem gates_eq : capturedPinnedCs.gates = actionPinnedCs.gates :=
  congrArg PinnedConstraintSystem.gates capturedPinnedCs_eq_derived

theorem adviceQueryLayout_eq :
    capturedPinnedCs.adviceQueryLayout = actionPinnedCs.adviceQueryLayout :=
  congrArg PinnedConstraintSystem.adviceQueryLayout capturedPinnedCs_eq_derived

theorem fixedQueryLayout_eq :
    capturedPinnedCs.fixedQueryLayout = actionPinnedCs.fixedQueryLayout :=
  congrArg PinnedConstraintSystem.fixedQueryLayout capturedPinnedCs_eq_derived

theorem instanceQueryLayout_eq :
    capturedPinnedCs.instanceQueryLayout = actionPinnedCs.instanceQueryLayout :=
  congrArg PinnedConstraintSystem.instanceQueryLayout capturedPinnedCs_eq_derived

theorem lookupInputExprs_eq :
    capturedPinnedCs.lookupInputExprs = actionPinnedCs.lookupInputExprs :=
  congrArg PinnedConstraintSystem.lookupInputExprs capturedPinnedCs_eq_derived

theorem lookupTableExprs_eq :
    capturedPinnedCs.lookupTableExprs = actionPinnedCs.lookupTableExprs :=
  congrArg PinnedConstraintSystem.lookupTableExprs capturedPinnedCs_eq_derived

theorem constants_eq : capturedPinnedCs.constants = actionPinnedCs.constants :=
  congrArg PinnedConstraintSystem.constants capturedPinnedCs_eq_derived

theorem minimumDegree_eq :
    capturedPinnedCs.minimumDegree = actionPinnedCs.minimumDegree :=
  congrArg PinnedConstraintSystem.minimumDegree capturedPinnedCs_eq_derived

theorem permutationColumns_eq :
    capturedPinnedCs.permutationColumns = actionPinnedCs.permutationColumns :=
  congrArg PinnedConstraintSystem.permutationColumns capturedPinnedCs_eq_derived

/-- The selector-compression map covers every selector atom of every Action gate — the
coverage side condition of `PinnedConstraintSystem.derive_gates_eval`. -/
theorem action_gates_selectorsCovered :
    ((flatGates actionCS).all
      (·.selectorsCovered (fun i => ((actionSelMapDerived (2 ^ actionK)).lookup i).isSome)))
      = true := by
  native_decide

assert_no_sorry capturedPinnedCs_eq_derived
assert_no_sorry action_gates_selectorsCovered
assert_no_sorry action_queriedCells_wellFormed
assert_no_sorry actionK_eq

end Zcash.Snark.Fixture
