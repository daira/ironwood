import Zcash.Security.KeyBinding
import Zcash.Security.Ledger.Statement

/-!
# Bridging the concrete key-binding layer to the games' `KeyBindingInterface`

The deliberate contact point between Layer A (`Zcash.Security.KeyBinding`: the concrete `Witness`,
the factored condition `KB = KBOpening ∧ KBDerivation`, and `Break`) and Layer B
(`Zcash.Security.Ledger.KeyBindingInterface`: the games-facing view). The games see only the
projections and the `break_of_nk_ne` guarantee; here we discharge that guarantee from Layer A's
`nk_pinned`.
-/

namespace Zcash.Security

open Zcash.Security.KeyBinding Zcash.Security.Ledger

variable {G F B SK QK : Type*}

/-- Layer A's concrete key-binding witness, viewed through Layer B's `KeyBindingInterface`. -/
def KeyBinding.toInterface
    [AddCommGroup G] [Field F] [Field B] [Module F G]
    (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F) :
    KeyBindingInterface (KeyBinding.Witness G F B SK QK) G B where
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
