import Zcash.Meta.AxiomCheck

/-!
# Regression tests for the environment-level endpoint census

Forged declarations exercising `Zcash.Meta.EndpointCensus`: endpoint-named theorems, axioms, and
opaque declarations with no census entry must be discovered from the elaborated environment, and
one that a census entry pinned must not be reported.  The declarations are deliberate forgeries,
so they live in this test-only library, out of the production `Zcash` import graph — which is also why
`unpinnedEndpoints` excludes `Zcash.Meta.Tests` by default and the discovery assertion below
opts back in.
-/

namespace Zcash.Meta.Tests.EndpointCensus

/-- A forged endpoint: matches the naming convention, censused nowhere. -/
theorem orchard_action_forged_prob_le : True := trivial

/-- A forged axiom endpoint: declaration kind must not bypass the environment census. -/
axiom orchard_action_forged_axiom_prob_le : True

/-- A forged opaque endpoint: declaration kind must not bypass the environment census. -/
opaque orchard_action_forged_opaque_prob_le : True := trivial

/-- A pinned endpoint: the census entry below records it, removing it from the unpinned set. -/
theorem orchard_action_pinned_prob_le : True := trivial

assert_axioms Zcash.Meta.Tests.EndpointCensus.orchard_action_pinned_prob_le

-- Discovery: with the test exclusion lifted, exactly the three forged endpoints are unpinned —
-- the pinned sibling was recorded by its census entry above.  Keeping the expected set explicit
-- makes a declaration-kind regression fail closed.
run_cmd do
  let bad := Zcash.Meta.unpinnedEndpoints (← Lean.getEnv) (excludeTests := false)
  let expected := #[``orchard_action_forged_axiom_prob_le,
    ``orchard_action_forged_opaque_prob_le, ``orchard_action_forged_prob_le].qsort Lean.Name.lt
  unless bad == expected do
    Lean.throwError m!"expected exactly the forged theorem/axiom/opaque endpoints unpinned, got \
      {bad.toList}; expected {expected.toList}"

-- The deployed configuration excludes this forged-declaration library, so the command passes
-- even with the forgery in scope.
assert_endpoint_census

end Zcash.Meta.Tests.EndpointCensus
