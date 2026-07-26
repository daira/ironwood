import Zcash.Arithmetic.Field

/-!
# Compatibility shim: the scalar field under `Zcash.Snark`

Compatibility shim for the generated fixture captures, which are byte-locked; delete when the
captures are next regenerated.

The field itself now lives in `Zcash.Arithmetic.Field`; the captures spell it `Fp` under
`open Zcash.Snark`, so that one name is re-exported here. No editable module depends on this
shim.
-/

namespace Zcash.Snark

export Zcash.Arithmetic (Fp)

end Zcash.Snark
