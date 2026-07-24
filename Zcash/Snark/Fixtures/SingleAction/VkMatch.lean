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
open Halo2

theorem vk_lookupInputs_ofFn : List.ofFn vk.lookupInputExprs = vkLookupInputExprs := by
  native_decide

theorem vk_lookupTables_ofFn : List.ofFn vk.lookupTableExprs = vkLookupTableExprs := by
  native_decide

/-- **The captured verifying key's gates are the derived Action circuit's.** The verifying
key holds `Zcash.Snark.Expr` gates and the derivation holds `Halo2.RichExpression` gates, so
the equality is stated through the boundary conversion `RichExpression.ofExpr`. -/
theorem vk_gates_eq_derived :
    vk.gates.map RichExpression.ofExpr = actionPinnedCs.gates :=
  congrArg PinnedConstraintSystem.gates capturedPinnedCs_eq_derived

theorem vk_adviceQueryLayout_eq_derived :
    vk.adviceQueryLayout = actionPinnedCs.adviceQueryLayout :=
  congrArg PinnedConstraintSystem.adviceQueryLayout capturedPinnedCs_eq_derived

theorem vk_fixedQueryLayout_eq_derived :
    vk.fixedQueryLayout = actionPinnedCs.fixedQueryLayout :=
  congrArg PinnedConstraintSystem.fixedQueryLayout capturedPinnedCs_eq_derived

theorem vk_instanceQueryLayout_eq_derived :
    vk.instanceQueryLayout = actionPinnedCs.instanceQueryLayout :=
  congrArg PinnedConstraintSystem.instanceQueryLayout capturedPinnedCs_eq_derived

theorem vk_lookupInputExprs_eq_derived :
    (List.ofFn vk.lookupInputExprs).map (·.map RichExpression.ofExpr)
      = actionPinnedCs.lookupInputExprs := by
  rw [vk_lookupInputs_ofFn]
  exact congrArg PinnedConstraintSystem.lookupInputExprs capturedPinnedCs_eq_derived

theorem vk_lookupTableExprs_eq_derived :
    (List.ofFn vk.lookupTableExprs).map (·.map RichExpression.ofExpr)
      = actionPinnedCs.lookupTableExprs := by
  rw [vk_lookupTables_ofFn]
  exact congrArg PinnedConstraintSystem.lookupTableExprs capturedPinnedCs_eq_derived

/-! ## The VK's domain and permutation scalars, derived

The captured `vk`'s scalar fields — previously transcribed constants — are all
computable from the circuit: `omega`/`n` from the derived domain exponent `actionK`
(`minimalK`), `blindingFactors` from the configure-recorded advice queries, `delta` a
pasta constant, `chunkLen` from the ported `cs.degree()`, and `permutationChunks` the
recorded permutation columns chunked by it. -/

/-- ONE bundled `native_decide` for the scalars and the permutation chunks (separate
theorems would re-evaluate the shared selector-map/projection work once each; the
nesting `((…), chunks)` rather than a flat 6-tuple is what instance synthesis accepts). -/
theorem vk_scalars_and_chunks_derived :
    ((vk.omega, vk.n, vk.blindingFactors, vk.delta, vk.chunkLen), vk.permutationChunks)
      = ((omegaOf actionK, 2 ^ actionK, actionCS.blindingFactors, deltaFp,
            actionCS.chunkLen),
          permutationChunksOf (actionSelMapDerived (2 ^ actionK)) actionCS) := by
  native_decide

theorem vk_scalars_derived :
    (vk.omega, vk.n, vk.blindingFactors, vk.delta, vk.chunkLen)
      = (omegaOf actionK, 2 ^ actionK, actionCS.blindingFactors, deltaFp,
          actionCS.chunkLen) := by
  have h := vk_scalars_and_chunks_derived
  simp only [Prod.mk.injEq] at h ⊢
  exact h.1

theorem vk_permutationChunks_derived :
    vk.permutationChunks
      = permutationChunksOf (actionSelMapDerived (2 ^ actionK)) actionCS := by
  have h := vk_scalars_and_chunks_derived
  simp only [Prod.mk.injEq] at h
  exact h.2

assert_no_sorry vk_gates_eq_derived
assert_no_sorry vk_scalars_and_chunks_derived

end Zcash.Snark.Fixture
