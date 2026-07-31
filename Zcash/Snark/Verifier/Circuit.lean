import Zcash.Snark.Verifier.ConstraintSystem
import Zcash.Circuits.Integration.VerifierCS

/-!
# Verifier circuit compatibility import

The verifier constraint-system type now lives in
`Zcash.Snark.Verifier.ConstraintSystem`, while the concrete circuit translation
lives at the circuit-integration boundary in
`Zcash.Circuits.Integration.VerifierCS`.

This module preserves the original import path.
-/
