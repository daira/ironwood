import Zcash.Security.KeyBinding.Basic
import Zcash.Security.KeyBinding.Probability
import Zcash.Security.Ledger.Statement

/-!
# Bridging the concrete key-binding layer to the games' `KeyBindingInterface`

The deliberate contact point between the concrete key-binding development
(`Zcash.Security.KeyBinding`: the `Witness`, the factored condition `KB = KBOpening ∧ KBDerivation`,
and `Break`) and the games-facing view (`Zcash.Security.Ledger.KeyBindingInterface`). The games see
only the projections and the `break_of_nk_ne` / `break_of_akP_ne` guarantees; here we discharge
them from the break projection (`nk` differing directly; `akP` via `toAK_pm`, since the projection
quotients the y-sign).
-/

namespace Zcash.Security

open Zcash.Security.KeyBinding Zcash.Security.Ledger Zcash.Security.RandomOracle Zcash.Snark

variable {G IVK AK NK RIVK ASK QK SK : Type*}

/-- The concrete key-binding witness, viewed through the games' `KeyBindingInterface`. -/
def KeyBinding.toInterface
    [AddCommGroup G] [Field IVK] [Field RIVK] [Module RIVK G] [SMul ASK G]
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G)
    (H : Oracles AK NK RIVK ASK QK SK) :
    KeyBindingInterface (KeyBinding.Witness G IVK AK NK RIVK QK SK) G IVK NK where
  ivk w := w.ivk
  nk w := w.nk
  akP w := w.akP
  KB := KeyBinding.KB Extract S hfn Ggen H
  Break := KeyBinding.Break Extract S hfn Ggen H
  break_of_nk_ne {_w₁ _w₂} h₁ h₂ hivk hne :=
    ⟨h₁, h₂, hivk, fun heq => hne (congrArg BreakProj.nk heq)⟩
  break_of_akP_ne {_w₁ _w₂} h₁ h₂ hivk hne :=
    ⟨h₁, h₂, hivk, fun heq => hne ((Extract.toAK_pm _ _).mp (congrArg BreakProj.ak heq))⟩


/-- The probabilistic key-binding bound, delivered at the games' interface: over the
adversary's private randomness (any distribution `p`) and the five independent oracle
tables, a bounded-query machine — receiving the sampled `H^ask`/`H^nk` tables and querying
the combined rivk table — has output witnesses exhibiting the interface's `Break` with
probability at most `(n+4)·(n+3)/|F|`. `toInterface` interprets `Break` as
`KeyBinding.Break` definitionally, so the games' `∨ kv.Break` branches inherit the bound
directly. -/
theorem toInterface_break_measure_le {ι : Type*}
    [AddCommGroup G] [Field IVK] [Field RIVK] [Module RIVK G] [NoZeroSMulDivisors RIVK G]
    [SMul ASK G] [Fintype AK] [Fintype NK] [Fintype RIVK] [Fintype ASK] [Fintype QK]
    [Fintype SK] [Nonempty NK] [Nonempty ASK]
    [DecidableEq AK] [DecidableEq NK] [DecidableEq RIVK] [DecidableEq QK] [DecidableEq SK]
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G) (hS : S ≠ 0) (p : PMF ι)
    {A : ι → (SK → ASK) → (SK → NK) → OracleComp (FinalQuery AK NK RIVK QK SK) RIVK
      (KeyBinding.Witness G IVK AK NK RIVK QK SK × KeyBinding.Witness G IVK AK NK RIVK QK SK)}
    {n : ℕ} (hQ : ∀ i Hask Hnk, (A i Hask Hnk).QueryBound n) :
    ((p.bind fun i => (PMF.uniformOfFintype (SK → ASK)).bind fun Hask =>
        (PMF.uniformOfFintype (SK → NK)).bind fun Hnk =>
          (PMF.uniformOfFintype (SK → RIVK)).bind fun Hleg =>
            (PMF.uniformOfFintype (QK → AK → NK → RIVK)).bind fun Hext =>
              (PMF.uniformOfFintype (RIVK → AK → NK → RIVK)).map fun Hint =>
                (i, Hask, Hnk, FinalQuery.eval Hleg Hext Hint))).toOuterMeasure
        (setOf fun (i, Hask, Hnk, O) =>
          (KeyBinding.toInterface Extract S hfn Ggen
              ⟨Hask, Hnk, fun sk => O (.legacy sk),
                fun qk ak nk => O (.ext qk ak nk),
                fun rivk_ext ak nk => O (.int rivk_ext ak nk)⟩).Break
            ((A i Hask Hnk).run O).1 ((A i Hask Hnk).run O).2)
      ≤ ((n + 4) * (n + 3) : ℕ) / Fintype.card RIVK :=
  KeyBinding.break_measure_le_product Extract S hfn Ggen hS p hQ


end Zcash.Security
