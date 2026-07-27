import Clean.Halo2.TopLevelKeygen
import Zcash.Circuits.Integration.CircuitIntegration

/-!
# Generic SNARK-to-top-level-circuit endpoint

`FullCircuitBridge` reconstructs Clean's authoritative operation constraints from the
separated gate, copy, lookup, and fixed arguments.  A fitting `TopLevelCircuit`
closes its own environment contract.  This module composes those two generic
boundaries; no Action-specific circuit, placement, or statement appears here.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

namespace FullCircuitSatisfaction

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/-- Exact full operation satisfaction implies the circuit-owned semantic statement. -/
theorem topLevelSoundness
    (top : TopLevelCircuit Fp Config PublicInput)
    (env : Placed Environment Fp)
    (hwellFormed :
      SynthesisWellFormed env.env top.operations)
    (hsatisfied :
      FullCircuitSatisfaction env.place env.env top.operations 0) :
    top.Statement (top.extractPublicInput env.env) := by
  apply top.statement_soundness env hwellFormed
  exact FullCircuitSatisfaction.constraints hsatisfied

end FullCircuitSatisfaction

namespace FullCircuitBridge

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Prop}

/--
The generic semantic last mile: reconstructed full constraints imply the top-level
circuit's own statement, preserving the bridge's shared exceptional event.
-/
theorem topLevelSoundness_or_bad
    (top : TopLevelCircuit Fp Config PublicInput)
    (env : Placed Environment Fp)
    (hwellFormed :
      SynthesisWellFormed env.env top.operations)
    (bridge : FullCircuitBridge env.place env.env
      top.operations 0 cell Bad) :
    top.Statement (top.extractPublicInput env.env) ∨ Bad := by
  rcases bridge.satisfaction_or_bad with hsatisfied | hbad
  · exact Or.inl (hsatisfied.topLevelSoundness top env hwellFormed)
  · exact Or.inr hbad

end FullCircuitBridge

end Zcash.Snark
