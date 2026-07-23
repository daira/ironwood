import Zcash.Security.KeyBinding.Basic
import Zcash.Security.KeyBinding.Probability
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

open Zcash.Security.KeyBinding Zcash.Security.Ledger Zcash.Security.RandomOracle Zcash.Snark

variable {G F IVK AK NK SK QK : Type*}

/-- The concrete key-binding witness, viewed through the games' `KeyBindingInterface`. -/
def KeyBinding.toInterface
    [AddCommGroup G] [Field F] [Field IVK] [Module F G]
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → F) (Ggen : G)
    (H : Oracles F AK NK SK QK) :
    KeyBindingInterface (KeyBinding.Witness G F IVK AK NK SK QK) G IVK NK where
  ivk w := w.ivk
  nk w := w.nk
  akP w := w.akP
  KB := KeyBinding.KB Extract S hfn Ggen H
  Break := KeyBinding.Break Extract S hfn Ggen H
  break_of_nk_ne {_w₁ _w₂} h₁ h₂ hivk hne := by
    by_contra hnb
    exact hne (KeyBinding.nk_pinned Extract S hfn Ggen H h₁ h₂ hivk hnb)


/-- The probabilistic key-binding bound, delivered at the games' interface: over the
adversary's private randomness (any distribution `p`) and the five independent oracle
tables, a bounded-query machine's output witnesses exhibit the interface's `Break` with
probability at most `(n+4)·(n+3)/|F|`. `toInterface` interprets `Break` as
`KeyBinding.Break` definitionally, so the games' `∨ kv.Break` branches inherit the bound
directly. -/
theorem toInterface_break_measure_le {ι : Type*}
    [AddCommGroup G] [Field F] [Field IVK] [Module F G] [NoZeroSMulDivisors F G]
    [Fintype QK] [Fintype SK] [Fintype AK] [Fintype NK] [Fintype F] [Nonempty NK]
    [DecidableEq QK] [DecidableEq SK] [DecidableEq AK] [DecidableEq NK] [DecidableEq F]
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → F) (Ggen : G)
    (hExt : ∀ P R : G, Extract.toIVK P = Extract.toIVK R ↔ P =± R) (hS : S ≠ 0) (p : PMF ι)
    {A : ι → OracleComp (FinalQuery QK SK AK NK F) F
      (KeyBinding.Witness G F IVK AK NK SK QK × KeyBinding.Witness G F IVK AK NK SK QK)}
    {n : ℕ} (hQ : ∀ i, (A i).QueryBound n) :
    ((p.bind fun i => (PMF.uniformOfFintype (SK → F)).bind fun Hask =>
        (PMF.uniformOfFintype (SK → NK)).bind fun Hnk =>
          (PMF.uniformOfFintype (SK → F)).bind fun Hleg =>
            (PMF.uniformOfFintype (QK → AK → NK → F)).bind fun Hext =>
              (PMF.uniformOfFintype (F → AK → NK → F)).map fun Hint =>
                (i, Hask, Hnk, FinalQuery.eval Hleg Hext Hint))).toOuterMeasure
        {x : ι × (SK → F) × (SK → NK) × (FinalQuery QK SK AK NK F → F) |
          (KeyBinding.toInterface Extract S hfn Ggen
              ⟨x.2.1, x.2.2.1, fun sk => x.2.2.2 (.legacy sk),
                fun qk ak nk => x.2.2.2 (.ext qk ak nk),
                fun rivk_ext ak nk => x.2.2.2 (.int rivk_ext ak nk)⟩).Break
            ((A x.1).run x.2.2.2).1 ((A x.1).run x.2.2.2).2}
      ≤ ((n + 4) * (n + 3) : ℕ) / Fintype.card F :=
  KeyBinding.break_measure_le_product Extract S hfn Ggen hExt hS p hQ


end Zcash.Security
