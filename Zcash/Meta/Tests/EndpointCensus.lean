import Zcash.Meta.AxiomCheck

/-!
# Regression tests for the environment-level endpoint census

Forged declarations exercising `Zcash.Meta.EndpointCensus`: an endpoint-named theorem with no
census entry must be discovered from the elaborated environment, and one that a census entry
pinned must not be reported.  The declarations are deliberate forgeries, so they live in this
test-only library, out of the production `Zcash` import graph — which is also why
`unpinnedEndpoints` excludes `Zcash.Meta.Tests` by default and the discovery assertion below
opts back in.
-/

namespace Zcash.Meta.Tests.EndpointCensus

/-- A forged endpoint: matches the naming convention, censused nowhere. -/
theorem orchard_action_forged_prob_le : True := trivial

/-- A pinned endpoint: the census entry below records it, removing it from the unpinned set. -/
theorem orchard_action_pinned_prob_le : True := trivial

assert_axioms Zcash.Meta.Tests.EndpointCensus.orchard_action_pinned_prob_le

-- Discovery: with the test exclusion lifted, exactly the forged endpoint is unpinned — the
-- pinned sibling was recorded by its census entry above.
run_cmd do
  let bad := Zcash.Meta.unpinnedEndpoints (← Lean.getEnv) (excludeTests := false)
  unless bad == #[``orchard_action_forged_prob_le] do
    Lean.throwError "expected exactly the forged endpoint unpinned, got {bad.toList}"

-- The deployed configuration excludes this forged-declaration library, so the command passes
-- even with the forgery in scope.
assert_endpoint_census

end Zcash.Meta.Tests.EndpointCensus
