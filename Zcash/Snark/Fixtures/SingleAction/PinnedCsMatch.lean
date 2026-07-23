import Zcash.Snark.Fixtures.SingleAction.VkCsData
import Zcash.Bridge.VkProjection
import Mathlib.Util.AssertNoSorry

/-!
# Pinned-CS equality: the capture is the derived Action circuit

Two `PartialPinnedConstraintSystem` values: `capturedPinnedCs`, read off the capture's
CS-data dump, and `actionPinnedCs`, derived from the ported `Action.Circuit.configure`.
`capturedPinnedCs_eq_derived` computes them equal; the per-field theorems split the
same equality so a regeneration drift names the diverging field.

The derivation's keygen witnesses: the selector-compression map is the Rust dump
(`actionSelMap`), and the registration seed is the capture's own layouts — the
fixed-point form: the equality then says the capture is consistent with the circuit
under its own query-registration order, which pins the semantics (the layouts the
consumers read are the ones the equality certifies). Both witnesses become computed,
circuit-side data in the planned keygen ports (see the
`PartialPinnedConstraintSystem` module docstring).

This module deliberately imports only the capture's `VkCsData` (plain field/ℕ data) —
not the full fixture with its point captures — so the checks build in seconds;
`VkMatch` restates the result for the `vk` record. Compiler-trust boundary: like the
fingerprint match, these are `native_decide` facts about one concrete capture, never
general theorems (see `TrustBoundary` in this directory for the discipline).
-/

namespace Zcash.Snark.Fixture

open Bridge
open Circuits.Fixtures

/-- The capture's CS data, as the pinned record. -/
def capturedPinnedCs : PartialPinnedConstraintSystem where
  gates := vkGates
  adviceQueryLayout := vkAdviceQueryLayout
  fixedQueryLayout := vkFixedQueryLayout
  instanceQueryLayout := vkInstanceQueryLayout
  lookupInputExprs := vkLookupInputExprs
  lookupTableExprs := vkLookupTableExprs

/-- The pinned CS derived from the ported Action circuit, at the capture's
registration order (fixed-point form; see the module docstring). -/
def actionPinnedCs : PartialPinnedConstraintSystem :=
  .derive actionCS
    (csSeed vkAdviceQueryLayout vkFixedQueryLayout vkInstanceQueryLayout) actionSelMap

theorem gates_eq : capturedPinnedCs.gates = actionPinnedCs.gates := by native_decide

theorem adviceQueryLayout_eq :
    capturedPinnedCs.adviceQueryLayout = actionPinnedCs.adviceQueryLayout := by native_decide

theorem fixedQueryLayout_eq :
    capturedPinnedCs.fixedQueryLayout = actionPinnedCs.fixedQueryLayout := by native_decide

theorem instanceQueryLayout_eq :
    capturedPinnedCs.instanceQueryLayout = actionPinnedCs.instanceQueryLayout := by native_decide

theorem lookupInputExprs_eq :
    capturedPinnedCs.lookupInputExprs = actionPinnedCs.lookupInputExprs := by native_decide

theorem lookupTableExprs_eq :
    capturedPinnedCs.lookupTableExprs = actionPinnedCs.lookupTableExprs := by native_decide

/-- **The capture is the derived Action circuit** (pinned CS). -/
theorem capturedPinnedCs_eq_derived : capturedPinnedCs = actionPinnedCs := by native_decide

/-- The selector-compression map covers every selector atom of every Action gate — the
coverage side condition of `PartialPinnedConstraintSystem.derive_gates_eval`. -/
theorem action_gates_selectorsCovered :
    ((flatGates actionCS).all
      (·.selectorsCovered (fun i => (actionSelMap.lookup i).isSome))) = true := by
  native_decide

assert_no_sorry capturedPinnedCs_eq_derived
assert_no_sorry action_gates_selectorsCovered

end Zcash.Snark.Fixture
