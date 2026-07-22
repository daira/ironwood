import Zcash.Security.KeyBinding.Basic
import Zcash.Security.Ledger.Statement

/-!
# Bridging the concrete key-binding layer to the games' `KeyBindingInterface`

The deliberate contact point between the concrete key-binding development
(`Zcash.Security.KeyBinding`: the `Witness`, the factored condition `KB = KBOpening ∧ KBDerivation`,
and `Break`) and the games-facing view (`Zcash.Security.Ledger.KeyBindingInterface`). The games see
only the projections and the `break_of_nk_ne` guarantee; here we discharge that guarantee from
`nk_pinned`.
-/

namespace Zcash.Security

open Zcash.Security.KeyBinding Zcash.Security.Ledger

variable {G F AK NK SK QK : Type*}

/-- The concrete key-binding witness, viewed through the games' `KeyBindingInterface`. -/
def KeyBinding.toInterface
    [AddCommGroup G] [Field F] [Field AK] [Module F G]
    (Extract : G → AK) (S : G) (hfn : AK → NK → F) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → NK) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → AK → NK → F) (Hrivk_int : F → AK → NK → F) :
    KeyBindingInterface (KeyBinding.Witness G F AK NK SK QK) G AK NK where
  ivk w := w.ivk
  nk w := w.nk
  akP w := w.akP
  KB := KeyBinding.KB Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int
  Break := KeyBinding.Break Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int
  break_of_nk_ne {_w₁ _w₂} h₁ h₂ hivk hne := by
    by_contra hnb
    exact hne (KeyBinding.nk_pinned Extract S hfn Ggen Hask Hnk Hrivk_legacy
      Hrivk_ext Hrivk_int h₁ h₂ hivk hnb)

end Zcash.Security
