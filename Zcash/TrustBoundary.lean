import Zcash.Security.KeyBinding.Instance
import Zcash.Security.KeyBinding.Probability
import Zcash.Security.Common.Birthday
import Zcash.Security.BindingSignature.Orchard
import Zcash.Security.BindingSignature.Sapling
import Zcash.Meta.AxiomCheck

/-!
# Trust boundary, build-checked

The library-wide census that makes the trust claims build-time checks rather than prose: a change
that widens a declaration's trusted base — a `sorry` reached through some dependency, an unexpected
axiom, or `native_decide` where none was permitted — fails this file rather than passing silently.

Two commands from `Zcash.Meta.AxiomCheck`, per the breaks-as-computed-data discipline (see
`Zcash.Security.RandomOracle`):

* **Computed break reductions** get `assert_computable`: the declaration is a plain `def` — not a
  theorem, not marked `noncomputable` — with axioms bounded by `propext` / `Quot.sound`.
  `+choice` additionally permits `Classical.choice`; with the plain-`def` check this asserts
  choice enters only through erased `Prop` certificate fields, so the break data cannot have been
  conjured from mere propositional existence.
* **Theorems** get `assert_axioms`, an upper bound at the standard tier
  (`propext` / `Classical.choice` / `Quot.sound`). Both commands reject `sorryAx`.
-/

open Zcash.Security.KeyBinding Zcash.Security.RandomOracle Zcash.Security.Birthday
open Zcash.Security.Ledger Zcash.Security.BindingSignature
open Zcash.Meta

/-! ## Key binding — computed break reductions -/

assert_computable Zcash.Security.RandomOracle.CollisionUpToSign.ofOpeningBreak +choice
assert_computable Zcash.Security.RandomOracle.CollisionUpToSign.ofBreak +choice

/-! ## Key binding — theorems -/

assert_axioms Zcash.Security.KeyBinding.Extractor.card_ivk_ge
assert_axioms Zcash.Security.KeyBinding.commit_scalar_pm
assert_axioms Zcash.Security.KeyBinding.rivk_eq_finalOracle
assert_axioms Zcash.Security.KeyBinding.sameIvk_finalOracle_pm
assert_axioms Zcash.Security.KeyBinding.openingBreak_finalOracle_pm
assert_axioms Zcash.Security.KeyBinding.break_finalOracle_pm
assert_axioms Zcash.Security.KeyBinding.residual_of_finalQuery_eq
assert_axioms Zcash.Security.KeyBinding.nk_pinned
assert_axioms Zcash.Security.KeyBinding.ak_pinned
assert_axioms Zcash.Security.KeyBinding.qk_or_sk_pinned
assert_axioms Zcash.Security.KeyBinding.collision_mem_shifted_pm
assert_axioms Zcash.Security.KeyBinding.toInterface

/-! ## Birthday bound -/

assert_axioms Zcash.Security.Birthday.card_shifted_pm_collision_le
assert_axioms Zcash.Security.Birthday.shifted_pm_collision_fraction_le
assert_axioms Zcash.Security.Birthday.birthday_closed_form

/-! ## Key binding — whole-table random-oracle model -/

assert_computable Zcash.Security.KeyBinding.finalQueryEquiv
assert_axioms Zcash.Security.KeyBinding.eval_restrict
assert_axioms Zcash.Security.KeyBinding.pair_shifted_collision_measure_le
assert_axioms Zcash.Security.KeyBinding.finset_shifted_collision_measure_le
assert_axioms Zcash.Security.KeyBinding.ofBreak_queries
assert_axioms Zcash.Security.KeyBinding.break_measure_le
assert_computable Zcash.Security.KeyBinding.badList
assert_axioms Zcash.Security.KeyBinding.mem_badList
assert_axioms Zcash.Security.KeyBinding.badList_measure_le
assert_axioms Zcash.Security.KeyBinding.escapesWithHistory
assert_axioms Zcash.Security.KeyBinding.escapesWithHistory_measure_le
assert_axioms Zcash.Security.KeyBinding.CollidesDuring
assert_axioms Zcash.Security.KeyBinding.CollidesDuring.of_pair
assert_axioms Zcash.Security.KeyBinding.sum_two_mul_add
assert_axioms Zcash.Security.KeyBinding.collidesDuring_measure_le
assert_axioms Zcash.Security.KeyBinding.queries_pair_collision_measure_le
assert_computable Zcash.Security.KeyBinding.derivQueries
assert_axioms Zcash.Security.KeyBinding.break_measure_le_adaptive
assert_axioms Zcash.Security.KeyBinding.break_measure_le_of_queryBound
assert_axioms Zcash.Security.KeyBinding.toOuterMeasure_bind_le
assert_axioms Zcash.Security.KeyBinding.break_measure_le_mixture
assert_axioms Zcash.Security.KeyBinding.uniformOfFintype_prod
assert_computable Zcash.Security.KeyBinding.evalEquiv
assert_axioms Zcash.Security.KeyBinding.uniform_triple_eval
assert_axioms Zcash.Security.KeyBinding.break_measure_le_product
assert_axioms Zcash.Security.toInterface_break_measure_le

/-! ## Ledger-layer break reductions

These data-producing reductions rest on `propext` and `Quot.sound` only — no `Classical.choice`
even in erased positions, which is the strict (flagless) `assert_computable` tier. -/

assert_computable Collision.upToSign
assert_computable Merkle.collisionOfWrongLeaf
assert_computable noteCommitBreakOfNe

/-! ## Binding-signature relation reductions

Unlike the ledger break reductions, these depend on `Classical.choice` (`+choice`). It enters
only through erased `Prop` certificate fields (the arithmetic side proofs); the relation
coefficients themselves are direct terms of the inputs, and the plain-`def` check means the data
cannot have been conjured from mere propositional existence. -/

assert_computable NontrivialRelation.ofImbalance +choice
assert_computable NontrivialRelation.ofBundleModImbalance +choice
assert_computable NontrivialRelation.ofBundleIntImbalance +choice
assert_computable NontrivialRelation.ofOrchardImbalance +choice
assert_computable NontrivialRelation.ofSaplingImbalance +choice
