import Zcash.Circuits.Action.TopLevel
import Mathlib.Util.AssertNoSorry

/-!
# Closed Action public-instance layout facts

This small module isolates the concrete query-registration computation used by the
public-instance commitment adapter.
-/

namespace Zcash.Snark

open Halo2
open Zcash.Circuits
open Zcash.Circuits.Action (orchardActionTopLevelCircuit)

namespace ActionInstanceCommitment

/-- The configured primary Action instance column is present at rotation zero in the
synthesis-closed constraint system. -/
theorem primaryRegistered :
    ((Action.Circuit.configure
          Specs.Sinsemilla.orchardGenerators {}).1.primary,
        (0 : Rotation)) ∈
      orchardActionTopLevelCircuit.constraintSystem.instanceQueries := by
  native_decide

assert_no_sorry primaryRegistered

end ActionInstanceCommitment

end Zcash.Snark
