import Zcash.Snark.Fixtures.MultiAction.Fixture
import Zcash.Meta.AxiomCheck

/-!
# Checked trust boundary of the concrete multi-action fixture

The multi-action analog of `Fixtures.SingleAction.TrustBoundary`, and checked the same way: CI
bounds the trusted base of the concrete coordinate validation, verifier fingerprint match, and
executable Vesta MSM identity, and pins the exact axiom set of the two `native_decide` claims.

* `assert_axioms` (from `Zcash.Meta.AxiomCheck`) — bounds the trusted base at the standard tier,
  rejecting `sorryAx` and any unexpected axiom, walking the whole elaborated dependency graph
  (`Lean.collectAxioms`) rather than a syntactic scan. `+native` on the captured fixtures that run
  through `native_decide`.
* `#print axioms` pinned by `#guard_msgs` — freezes the exact axiom set, so a newly introduced
  axiom fails the build. As in the single-action sibling, this is the case the pinned form is
  reserved for: for a concrete numeric fixture the exact axiom set *is* the claim, documenting that
  compiler trust enters here and nowhere else.
-/

open Zcash.Snark Zcash.Snark.Fixture2

assert_axioms capturedPointCoordinatesValid_eq_true +native
assert_axioms capturedInit_startsWith_vkTranscriptRepr +native
assert_axioms fingerprint_matches +native
assert_axioms capturedMsm_eval_eq_zero +native
assert_axioms assembledMsm_eval_eq_zero +native
assert_axioms Msm.evalNat
assert_axioms assemble

-- `whitespace := lax` collapses all whitespace, so the pin is insensitive to how
-- `#print axioms` line-wraps the list (a formatting artifact of the axiom-name lengths).
/-- info: 'Zcash.Snark.Fixture2.fingerprint_matches' depends on axioms: [propext, Classical.choice, Quot.sound, fingerprint_matches._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms fingerprint_matches

/-- info: 'Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound, capturedMsm_eval_eq_zero._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms capturedMsm_eval_eq_zero
