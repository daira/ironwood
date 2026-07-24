import Zcash.Snark.Fixtures.SingleAction.Fixture
import Zcash.Meta.AxiomCheck

/-!
# Checked trust boundary of the concrete fingerprint fixture

This module is built by CI (it belongs to the `FixtureCheck` lake target) and turns the trust boundary of
the concrete captured fingerprint into *checked*, build-time obligations. Besides the
coefficient-and-point match, the generated fixture validates every Vesta coordinate, binds the captured
transcript prefix to the canonical VK representation emitted by Rust, and computes both the captured and
Lean-assembled MSMs to the Vesta identity.

Both checks below follow Lean's elaborated dependency graph (via `Lean.collectAxioms`), so they see holes
anywhere in the transitive closure — including the `Soundness/` proof layer and Mathlib — which a
syntactic scan of the verifier sources cannot.

* `assert_axioms` (from `Zcash.Meta.AxiomCheck`) — bounds the trusted base at the standard tier and so
  rejects `sorryAx` and any unexpected axiom, walking the whole dependency graph. Applied to every
  captured fixture (`+native` for the `native_decide` ones) and to `assemble` (the verifier assembly it
  runs).
* `#print axioms` pinned by `#guard_msgs` — freezes the exact axiom set each captured claim rests on, so
  a newly introduced axiom changes the set and fails the build. The
  pinned sets record `..._native.native_decide.ax_1_1`, the compiler-trust axiom that
  `native_decide` generates for each theorem (this Lean version emits a per-declaration native axiom rather
  than the global `Lean.ofReduceBool`): pinning it documents that the one place compiler trust enters is
  this concrete numeric fixture, never a general theorem. The other three (`propext`, `Classical.choice`,
  `Quot.sound`) are the standard classical-logic axioms every Mathlib development uses.

`instance_commitments_derived` and `capturedPublicInstances_within_lagrange` are pinned alongside
`fingerprint_matches`: they carry the *derivation* of the instance commitments from the captured public
inputs (ironwood#65), which is the trust this fixture buys in place of taking the commitments as opaque
captured points. The derivation's supporting data and functions (`capturedUrsGLagrange`,
`capturedPublicInstances`, `commitLagrange`, `derivedInstanceCommitment`) are bounded too, so the
`native_decide` claims cannot be narrowed by quietly widening what they range over.
-/

open Zcash.Snark Zcash.Snark.Fixture

-- Every captured fixture and the verifier assembly it runs are bounded at the standard tier — no
-- `sorry`, no unexpected axiom (whole dependency graph). The `native_decide` fixtures carry the
-- compiler-trust axiom, permitted by `+native` and pinned exactly by the `#print axioms` guards below.
assert_axioms fingerprint_matches +native
assert_axioms capturedPointCoordinatesValid_eq_true +native
assert_axioms capturedInit_startsWith_vkTranscriptRepr +native
assert_axioms capturedMsm_eval_eq_zero +native
assert_axioms assembledMsm_eval_eq_zero +native
assert_axioms Msm.evalNat
assert_axioms assemble

-- The instance-commitment derivation: the two captured claims, plus the data and functions they
-- range over. The latter are flagless — they are ordinary definitions, so compiler trust must not
-- reach them; only the two claims about them may spend it.
assert_axioms instance_commitments_derived +native
assert_axioms capturedPublicInstances_within_lagrange +native
assert_axioms capturedUrsGLagrange
assert_axioms capturedPublicInstances
assert_axioms commitLagrange
assert_axioms derivedInstanceCommitment

-- `whitespace := lax` collapses all whitespace, so the pin is insensitive to how
-- `#print axioms` line-wraps the list (a formatting artifact of the axiom-name lengths).
/-- info: 'Zcash.Snark.Fixture.fingerprint_matches' depends on axioms: [propext, Classical.choice, Quot.sound, fingerprint_matches._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms fingerprint_matches

/-- info: 'Zcash.Snark.Fixture.capturedMsm_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound, capturedMsm_eval_eq_zero._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms capturedMsm_eval_eq_zero

/-- info: 'Zcash.Snark.Fixture.instance_commitments_derived' depends on axioms: [propext, Classical.choice, Quot.sound, instance_commitments_derived._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms instance_commitments_derived

/-- info: 'Zcash.Snark.Fixture.capturedPublicInstances_within_lagrange' depends on axioms: [propext, Classical.choice, Quot.sound, capturedPublicInstances_within_lagrange._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms capturedPublicInstances_within_lagrange
