import Zcash.Arithmetic.Msm

/-!
# Compatibility shim: the fingerprint MSM under `Zcash.Snark`

Compatibility shim for the generated fixture captures, which are byte-locked; delete when the
captures are next regenerated.

`Msm` now lives in `Zcash.Arithmetic.Msm`; the captures spell it bare under `open Zcash.Snark`,
so that one name is re-exported here. Its operations (`evalNat` in particular) reach the
captures through generalized field notation on the structure itself, which resolves in
`Zcash.Arithmetic.Msm` and needs no alias. No editable module depends on this shim.
-/

namespace Zcash.Snark

export Zcash.Arithmetic (Msm)

end Zcash.Snark
