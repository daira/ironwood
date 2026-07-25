import Zcash.Circuits.Integration.LookupSelectorRows
import Zcash.Circuits.Action.TopLevel

/-!
# Action lookup-selector rows

This is the thin Action-specific instantiation of the generic packed-selector row
bridge. Singleton packing, required-cell realization, and expression-level projection
remain generic; this module merely supplies Action's shared fixed coherence.
-/

namespace Zcash.Snark

open Halo2
open Zcash.Circuits.Action

set_option maxHeartbeats 20000

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [Inhabited G]

/--
The Action fixed-row boundary realizes the exact packed-selector rows needed by
every enabled lookup. No proof-specific verifier data enters this statement.
-/
theorem actionLookupInputSelectorLeafRowsExact
    {pp : Keygen.ProofParams} {urs : URS G}
    (coherence :
      TopLevelFixedCoherence orchardActionTopLevelCircuit pp urs)
    (lookup : EnabledLookup Fp)
    (henabled :
      lookup ∈ operationEnabledLookups
        (orchardActionTopLevelCircuit.operations 0) 0) :
    lookup.InputSelectorLeafRowsExact
      orchardActionTopLevelCircuit coherence.rows := by
  apply EnabledLookup.inputSelectorLeafRowsExact_of_realizes
    orchardActionTopLevelCircuit coherence.rows lookup henabled
  intro column row value hentry
  have hrealized := coherence.realizes column row value hentry
  exact ⟨hrealized.2.1, hrealized.2.2⟩

end Zcash.Snark
