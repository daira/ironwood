import Zcash.Snark.Fixtures.SingleAction.Fixture
import Mathlib.Util.AssertNoSorry

/-!
# Checked trust boundary of the fingerprint match

This module is built by CI (it belongs to the `FixtureCheck` lake target) and turns the trust boundary of
the captured fingerprint match into *checked*, build-time obligations. It complements — it does not
duplicate — the computability guarantee that the match already carries: `fingerprint_matches` is proved by
`native_decide`, which compiles and *runs* the Lean verifier `assemble` on the captured proof, so building
`FixtureCheck` already fails if anything on the assembled-MSM path is `noncomputable` (Lean's own
per-definition, whole-path determination). What a build does *not* otherwise pin down is whether the
theorem rests on a `sorry` reached through some dependency, or on an unexpected axiom. Those are
what this module rules out.

Both checks below follow Lean's elaborated dependency graph (via `Lean.collectAxioms`), so they see holes
anywhere in the transitive closure — including the `Soundness/` proof layer and Mathlib — which a
syntactic scan of the verifier sources cannot.

* `assert_no_sorry` — fails the build if the named constant transitively depends on `sorryAx`. Applied to
  `fingerprint_matches` (the captured match) and `assemble` (the verifier assembly it runs).
* `#print axioms` pinned by `#guard_msgs` — freezes the exact axiom set `fingerprint_matches` rests on, so
  a newly introduced axiom changes the set and fails the build. The
  pinned set records `fingerprint_matches._native.native_decide.ax_1_1`, the compiler-trust axiom that
  `native_decide` generates for this theorem (this Lean version emits a per-declaration native axiom rather
  than the global `Lean.ofReduceBool`): pinning it documents that the one place compiler trust enters is
  this concrete numeric fixture, never a general theorem. The other three (`propext`, `Classical.choice`,
  `Quot.sound`) are the standard classical-logic axioms every Mathlib development uses.
-/

open Zcash.Snark Zcash.Snark.Fixture

-- No `sorry` reaches the captured match or the verifier assembly it runs (whole dependency graph).
assert_no_sorry fingerprint_matches
assert_no_sorry assemble

-- `whitespace := lax` collapses all whitespace, so the pin is insensitive to how
-- `#print axioms` line-wraps the list (a formatting artifact of the axiom-name lengths).
/-- info: 'Zcash.Snark.Fixture.fingerprint_matches' depends on axioms: [propext, Classical.choice, Quot.sound, fingerprint_matches._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms fingerprint_matches
