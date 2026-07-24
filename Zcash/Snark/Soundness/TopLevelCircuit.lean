import Zcash.Circuits.TopLevelKeygen
import Zcash.Snark.Soundness.CircuitIntegration

/-!
# Generic SNARK-to-top-level-circuit endpoint

`FullCircuitBridge` reconstructs Clean's authoritative operation constraints from the
separated gate, copy, lookup, and fixed arguments.  A fitting `TopLevelCircuit`
closes its own environment contract.  This module composes those two generic
boundaries; no Action-specific circuit, placement, or statement appears here.
-/

namespace Zcash.Snark

open Halo2
open Zcash.Circuits

set_option maxHeartbeats 20000

namespace FullCircuitSatisfaction

variable
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]

/-- Exact full operation satisfaction implies the circuit-owned semantic statement. -/
theorem topLevelSoundness
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (i : RegionIndex) (env : Placed Environment Fp)
    (hwellFormed :
      SynthesisWellFormed env.env (top.operations i))
    (hsatisfied :
      FullCircuitSatisfaction env.place env.env (top.operations i) i) :
    top.Statement i env := by
  apply top.soundness i env hwellFormed
  exact FullCircuitSatisfaction.constraints hsatisfied

end FullCircuitSatisfaction

namespace FullCircuitBridge

variable
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Prop}

/--
The generic semantic last mile: reconstructed full constraints imply the top-level
circuit's own statement, preserving the bridge's shared exceptional event.
-/
theorem topLevelSoundness_or_bad
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (i : RegionIndex) (env : Placed Environment Fp)
    (hwellFormed :
      SynthesisWellFormed env.env (top.operations i))
    (bridge : FullCircuitBridge env.place env.env
      (top.operations i) i cell Bad) :
    top.Statement i env ∨ Bad := by
  rcases bridge.satisfaction_or_bad with hsatisfied | hbad
  · exact Or.inl (hsatisfied.topLevelSoundness top i env hwellFormed)
  · exact Or.inr hbad

end FullCircuitBridge

end Zcash.Snark
