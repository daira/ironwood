import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.ActionConstraintBoundsCompute
import Mathlib.Util.AssertNoSorry

/-!
# Closed computations for the Action permutation layout

This small module isolates the native computation certificates used by the semantic
Action permutation-domain package.  Every statement is against keygen data derived
from `actionCircuit`, never the captured verifying-key fixture.
-/

namespace Zcash.Snark

open Zcash.Circuits.Action (actionCircuit)

namespace ActionPermutationDomain

/-- The circuit-derived Action domain exponent is within Pasta's supported range. -/
theorem domainExponent_lt :
    actionCircuit.domainExponent < 33 :=
  ActionConstraintBounds.domainExponent_lt

/-- The Action permutation-column prefix fits easily inside `deltaFp`'s
certified order. This residual concrete count awaits a configure law bounding the
derived equality-enabled column list. -/
theorem permutationColumnCount_eq :
    actionCircuit.permutationColumnCount =
      15 := by
  native_decide

/-- The Action circuit configures exactly one instance column. -/
theorem numInstanceColumns_eq :
    actionCircuit.constraintSystem.numInstanceColumns = 1 := by
  native_decide

/-- Every instance query in the Action circuit's pinned layout names the single
configured instance column. -/
theorem instanceQueryLayout_columns_lt :
    ∀ entry ∈ actionCircuit.instanceQueryLayout, entry.1 < 1 := by
  native_decide

assert_no_sorry domainExponent_lt
assert_no_sorry permutationColumnCount_eq

end ActionPermutationDomain

end Zcash.Snark
