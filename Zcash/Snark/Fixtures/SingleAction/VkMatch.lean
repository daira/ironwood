import Zcash.Snark.Fixtures.SingleAction.Fixture
import Zcash.Snark.Fixtures.SingleAction.PinnedCsMatch

/-!
# VK equality, verifying-key form

The record-level pinned equality lives in `PinnedCsMatch` — the pinned record carries
counts and constants the runtime `VerifyingKey` does not. This module links the
captured verifying key's own CS fields to the derived record, the forms downstream
consumers use (`VerifyingKey.gates_eval_of_gates_eq`, the decode-side layout reads):
the record's fields are the `VkCsData` definitions, so only the `Fin`-function views of
the lookup expression lists need re-flattening.
-/

namespace Zcash.Snark.Fixture

open Bridge
open Circuits.Fixtures

theorem vk_lookupInputs_ofFn : List.ofFn vk.lookupInputExprs = vkLookupInputExprs := by
  native_decide

theorem vk_lookupTables_ofFn : List.ofFn vk.lookupTableExprs = vkLookupTableExprs := by
  native_decide

/-- **The captured verifying key's gates are the derived Action circuit's.** -/
theorem vk_gates_eq_derived : vk.gates = actionPinnedCs.gates :=
  congrArg PartialPinnedConstraintSystem.gates capturedPinnedCs_eq_derived

theorem vk_adviceQueryLayout_eq_derived :
    vk.adviceQueryLayout = actionPinnedCs.adviceQueryLayout :=
  congrArg PartialPinnedConstraintSystem.adviceQueryLayout capturedPinnedCs_eq_derived

theorem vk_fixedQueryLayout_eq_derived :
    vk.fixedQueryLayout = actionPinnedCs.fixedQueryLayout :=
  congrArg PartialPinnedConstraintSystem.fixedQueryLayout capturedPinnedCs_eq_derived

theorem vk_instanceQueryLayout_eq_derived :
    vk.instanceQueryLayout = actionPinnedCs.instanceQueryLayout :=
  congrArg PartialPinnedConstraintSystem.instanceQueryLayout capturedPinnedCs_eq_derived

theorem vk_lookupInputExprs_eq_derived :
    List.ofFn vk.lookupInputExprs = actionPinnedCs.lookupInputExprs :=
  vk_lookupInputs_ofFn.trans
    (congrArg PartialPinnedConstraintSystem.lookupInputExprs capturedPinnedCs_eq_derived)

theorem vk_lookupTableExprs_eq_derived :
    List.ofFn vk.lookupTableExprs = actionPinnedCs.lookupTableExprs :=
  vk_lookupTables_ofFn.trans
    (congrArg PartialPinnedConstraintSystem.lookupTableExprs capturedPinnedCs_eq_derived)

assert_no_sorry vk_gates_eq_derived

end Zcash.Snark.Fixture
