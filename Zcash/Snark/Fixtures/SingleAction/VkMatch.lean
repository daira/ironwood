import Zcash.Snark.Fixtures.SingleAction.Fixture
import Zcash.Snark.Fixtures.SingleAction.PinnedCsMatch

/-!
# VK equality, verifying-key form

Restates the pinned-CS equality (`PinnedCsMatch`) for the captured `vk` record: the
record's CS fields are the `VkCsData` definitions, so only the `Fin`-function views of
the lookup expression lists need re-flattening.
-/

namespace Zcash.Snark.Fixture

open Bridge

theorem vk_lookupInputs_ofFn : List.ofFn vk.lookupInputExprs = vkLookupInputExprs := by
  native_decide

theorem vk_lookupTables_ofFn : List.ofFn vk.lookupTableExprs = vkLookupTableExprs := by
  native_decide

theorem vk_pinnedCs_eq_captured : vk.pinnedCs = capturedPinnedCs := by
  simp only [Snark.VerifyingKey.pinnedCs, capturedPinnedCs, vk_lookupInputs_ofFn,
    vk_lookupTables_ofFn]
  rfl

/-- **The captured verifying key pins the derived Action circuit** (pinned CS). -/
theorem vk_pinnedCs_eq_derived : vk.pinnedCs = actionPinnedCs :=
  vk_pinnedCs_eq_captured.trans capturedPinnedCs_eq_derived

assert_no_sorry vk_pinnedCs_eq_derived

end Zcash.Snark.Fixture
