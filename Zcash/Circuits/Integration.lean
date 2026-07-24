import Zcash.Circuits.Integration.ExprRich
import Zcash.Circuits.Integration.ActionEncoding
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Integration.PermutationColumns
import Zcash.Circuits.Integration.PermutationReplay
import Zcash.Circuits.Integration.InstanceColumns
import Zcash.Circuits.Integration.LookupProjection
import Zcash.Circuits.Integration.QueryLayouts
import Zcash.Circuits.Integration.TopLevelLookups
import Zcash.Snark.Soundness.ActionStatement
import Zcash.Snark.Soundness.CircuitIntegration
import Zcash.Snark.Soundness.FixedLayout
import Zcash.Snark.Soundness.TopLevelCircuit
import Zcash.Snark.Soundness.TopLevelGates

/-!
# Clean-to-Ironwood integration

Aggregator for the implementation boundary between Clean formal circuits and the
Ironwood verifier/soundness model. Until the boundary refactor finishes moving the
files physically into this directory, this module deliberately imports their current
locations under `Zcash.Snark.Soundness`.

Keep pure verifier-native constraint, permutation, and lookup mathematics in
`Zcash.Snark`; only modules that translate between Clean and Ironwood belong here.
-/
