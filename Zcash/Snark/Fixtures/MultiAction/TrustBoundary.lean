import Zcash.Snark.Fixtures.MultiAction.Fixture
import Zcash.Snark.Fixtures.MultiAction.Degree
import Zcash.Snark.Fixtures.MultiAction.StaticChecks
import Zcash.Snark.Fixtures.MultiAction.Schedule
import Zcash.Snark.Fixtures.MultiAction.KnowledgeError
import Zcash.Meta.AxiomCheck

/-!
# Checked trust boundary of the concrete multi-action fixture

The multi-action analog of `Fixtures.SingleAction.TrustBoundary`, and checked the same way: CI
bounds the trusted base of the concrete coordinate validation, verifier fingerprint match, executable
Vesta MSM identity, and instance-commitment derivation, and pins the exact axiom set of the
`native_decide` claims among them.

* `assert_axioms` (from `Zcash.Meta.AxiomCheck`) — bounds the trusted base at the standard tier,
  rejecting `sorryAx` and any unexpected axiom, walking the whole elaborated dependency graph
  (`Lean.collectAxioms`) rather than a syntactic scan. `+native` on the captured fixtures that run
  through `native_decide`.
* `#print axioms` pinned by `#guard_msgs` — freezes the exact axiom set, so a newly introduced
  axiom fails the build. As in the single-action sibling, this is the case the pinned form is
  reserved for: for a concrete numeric fixture the exact axiom set *is* the claim, documenting that
  compiler trust enters here and nowhere else.

The instance-commitment derivation (`instance_commitments_derived`,
`capturedPublicInstances_within_lagrange`) is pinned on the same footing, together with the data and
functions it ranges over; see the single-action sibling for why this is the fixture's new trust
surface.
-/

open Zcash.Snark Zcash.Snark.Fixture2

assert_axioms capturedPointCoordinatesValid_eq_true +native
assert_axioms capturedInit_startsWith_vkTranscriptRepr +native
assert_axioms fingerprint_matches +native
assert_axioms capturedMsm_eval_eq_zero +native
assert_axioms assembledMsm_eval_eq_zero +native
assert_axioms Zcash.Arithmetic.Msm.evalNat
assert_axioms assemble
-- The captured key's degree budget: one literal (`20470`) dominates every constraint family,
-- so the `x`-squeeze schedule's `epsilonX` is the concrete `20470 / |𝔽|` at this key.
assert_axioms vk_gates_degree_le +native
assert_axioms vk_chunk_width_le +native
assert_axioms vk_lookup_input_degree_le +native
assert_axioms vk_lookup_table_degree_le +native
assert_axioms vk_quotient_tail_le +native
-- The captured key's static checks: the query layouts cover the shape's counts, `ω` has order
-- dividing `n`, and `n` does not vanish in `𝔽` — packaged for any family carrying this key.
assert_axioms vk_advice_layout_length +native
assert_axioms vk_instance_layout_length +native
assert_axioms vk_fixed_layout_length +native
assert_axioms vk_omega_order +native
assert_axioms vk_n_cast_ne_zero +native
assert_axioms deployedConstraintStaticChecks_of_captured +native
-- The `x`-squeeze schedule at the captured key: the degree caps discharged, so `epsilonX` is
-- the concrete `20470 / |𝔽|`; the squeeze-pinning premise passes through as the named input.
assert_axioms deployedConstraintXSqueezeSchedule_captured +native
-- The deployed knowledge-error bound at the captured key: the rewind-free capstone with the
-- static checks and degree caps discharged, so the bad-`x` term is the concrete
-- `(Q + 1) · 20470 / |𝔽|` and the multiopen term is the additive root budget.
assert_axioms orchard_deployed_knowledge_error_captured +native

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
/-- info: 'Zcash.Snark.Fixture2.fingerprint_matches' depends on axioms: [propext, Classical.choice, Quot.sound, fingerprint_matches._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms fingerprint_matches

/-- info: 'Zcash.Snark.Fixture2.capturedMsm_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound, capturedMsm_eval_eq_zero._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms capturedMsm_eval_eq_zero

/-- info: 'Zcash.Snark.Fixture2.instance_commitments_derived' depends on axioms: [propext, Classical.choice, Quot.sound, instance_commitments_derived._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms instance_commitments_derived

/-- info: 'Zcash.Snark.Fixture2.capturedPublicInstances_within_lagrange' depends on axioms: [propext, Classical.choice, Quot.sound, capturedPublicInstances_within_lagrange._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms capturedPublicInstances_within_lagrange
