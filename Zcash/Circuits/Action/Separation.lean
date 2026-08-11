import Mathlib.Util.AssertNoSorry
import Zcash.Circuits.Action.CircuitPreIronwood
import Zcash.Circuits.Action.Spec

/-!
# The pre-ironwood contract omits the cross-address policy

The NU 6.3 upgrade adds exactly one clause to the Action statement: the cross-address
binding.  This file pins that localization, machine-checked at the deployed generators and
bases:

* `preIronwood_synthesize_eq_base` — the pre-ironwood circuit is *definitionally*
  `synthesizeBase` alone: it never runs the `synthCrossAddressChecks` region the ironwood
  `synthesize` appends (`Circuit.lean`).
* `specPost_iff_base_and_crossAddress` — the ironwood contract `SpecPost` is exactly the
  base statement `SpecBase` conjoined with the cross-address clause, so the two differ in
  precisely that clause.
* `preIronwood_spec_omits_crossAddress` — the pre-ironwood contract `Spec` guarantees only
  `SpecBase` (plus its output-carrying rows), never the cross-address clause.
* `crossAddressBinding_nontrivial` — that clause is a genuine restriction: a witness with the
  flag set and distinct old/new diversified bases falsifies it.

Together these localize the entire post-NU 6.3 policy to the one clause the old key cannot
enforce; height-based key selection is the deployed obligation that keeps the old key from
being chosen after activation (`book/src/design/action-circuit.md`).

Not established here: a *satisfying* pre-ironwood witness that violates the clause — i.e.
`¬ ∀ wit, SpecBase G B wit → crossAddressBinding wit`.  A concrete such witness must open the
honest `Commit^ivk`/note/nullifier chains, whose `[ivk]·g_d` and Poseidon-scalar terms are
~255-bit `nsmul`s that `native_decide` cannot evaluate; that separation is left as the
remaining step.
-/

namespace Zcash.Circuits.Action.Separation

open Halo2
open Circuit
open Specs.Sinsemilla (Generators)

variable (G : Generators) (B : Bases) (W : Witnesses Fp) (cfg : Config)

/-- **The pre-ironwood circuit is `synthesizeBase` alone.**  Definitionally equal — the ironwood
`synthCrossAddressChecks` region is absent, so no constraint of the pre-NU 6.3 key depends on
`disableCrossAddress`. -/
theorem preIronwood_synthesize_eq_base :
    CircuitPreIronwood.synthesize G B W cfg = synthesizeBase G B W cfg := rfl

/-- The post-NU 6.3 cross-address binding, as a standalone clause: a nonzero
`disableCrossAddress` forces both new-note address components to equal the old note's. -/
def crossAddressBinding (wit : ActionData) : Prop :=
  wit.disableCrossAddress ≠ 0 → wit.gdOld = wit.gdNew ∧ wit.pkdOld = wit.pkdNew

/-- **The ironwood contract is the base contract plus exactly the cross-address clause.**  The two
statements separate in precisely this conjunct. -/
theorem specPost_iff_base_and_crossAddress (wit : ActionData) :
    SpecPost G B () () wit ↔ SpecBase G B wit ∧ crossAddressBinding wit := Iff.rfl

/-- **The pre-ironwood contract omits the cross-address clause.**  Its guarantee is `SpecBase`
(with the output-carrying rows); nothing in it constrains the cross-address relation, so a prover
bound only by the old key is free on it. -/
theorem preIronwood_spec_omits_crossAddress
    (out : Value AddressPoints Fp) (wit : ActionData)
    (h : Spec G B () out wit) : SpecBase G B wit := h.1

/-- **The cross-address clause is a real restriction.**  A witness carrying `disableCrossAddress = 1`
with distinct old/new diversified bases falsifies it — so conjoining it in `SpecPost` genuinely
narrows the accepted set relative to `SpecBase`.  (`merkleQ`/`ivkQ` are two distinct deployed
domain points, used here only as a convenient pair of unequal on-curve points.) -/
theorem crossAddressBinding_nontrivial :
    ∃ wit : ActionData, wit.disableCrossAddress ≠ 0 ∧ ¬ crossAddressBinding wit := by
  refine ⟨{ (default : ActionData) with
      disableCrossAddress := 1, gdOld := orchardBases.merkleQ, gdNew := orchardBases.ivkQ },
    one_ne_zero, ?_⟩
  intro hbind
  have hne : orchardBases.merkleQ ≠ orchardBases.ivkQ := by native_decide
  exact hne (hbind one_ne_zero).1

assert_no_sorry preIronwood_synthesize_eq_base
assert_no_sorry specPost_iff_base_and_crossAddress
assert_no_sorry preIronwood_spec_omits_crossAddress
assert_no_sorry crossAddressBinding_nontrivial

end Zcash.Circuits.Action.Separation
