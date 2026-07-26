import Zcash.Arithmetic.Group

/-!
# Compatibility shim: the uniform reference string under `Zcash.Snark`

Compatibility shim for the generated fixture captures, which are byte-locked; delete when the
captures are next regenerated.

`URS` now lives in `Zcash.Arithmetic.Group`; the captures spell it bare under
`open Zcash.Snark`, so that one name is re-exported here. No editable module depends on this
shim.
-/

namespace Zcash.Snark

export Zcash.Arithmetic (URS)

end Zcash.Snark
