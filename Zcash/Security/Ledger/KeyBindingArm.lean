import Mathlib
import Zcash.Security.KeyBinding.Instance
import Zcash.Security.Ledger.Balance
import Zcash.Security.Ledger.SpendAuthority

-- This lint enforces Mathlib's minimal-hypothesis style, from which we deliberately depart.
set_option linter.unusedSectionVars false

/-!
# The key-binding arm's ε, discharged in the oracle model

The capstone layer bounds each game's break arms by named ε hypotheses. This module
discharges the Balance-subset key-binding arm in the key-binding oracle model:
`(n + 4) · (n + 3) / |RIVK|` for any `n`-query-bounded adversary — the bound of
`toInterface_break_measure_le`, inherited at an unchanged query count because the
reduction makes no oracle queries.

The adversary is pair-annotated: an oracle machine producing a ledger together with a
candidate witness pair. It cannot run the reduction itself — `balanceSubsetOrBreak`
consumes a validity proof whose meaning depends on the sampled oracle (through the
sampled interface `kvAt`), and an oracle machine's result type cannot depend on the
table it is run against. The bad event ties the annotation to the reduction instead:
the output ledger is valid, and the reduction at that validity lands in the
key-binding arm with exactly the output pair (`BalanceBreak.kbPair`). Proof
irrelevance makes the tie independent of which validity proof the event exhibits.
That event is contained in "the output pair breaks the sampled interface", so the
key-binding bound applies to the composite machine that returns the pair.

Spend Authority's key-binding arm is discharged the same way
(`spendAuthority_keyBindingArm_measure_le`): the victim's key witness is a theorem
parameter — the `Witness` type is oracle-independent — while its `KB` certificate,
whose meaning is oracle-dependent, moves inside the event, and the break data's own
fields supply the pair.
-/

namespace Zcash.Security.Ledger.Model

open Zcash.Security.KeyBinding Zcash.Snark

-- A shared universe for the oracle-model types, so the sampling experiment can be
-- written in `do`-notation: `PMF`'s monad instance fixes one universe for the whole
-- block, which the independent `Type*` universes could not satisfy.
universe u
variable {G IVK AK NK RIVK ASK QK SK : Type u}
variable {RHO PSI MHASH MENC MSG SIG : Type*}

section OracleModel

variable [AddCommGroup G] [Field IVK] [Field RIVK] [Module RIVK G]
  [NoZeroSMulDivisors RIVK G] [SMul ASK G]
  [Fintype AK] [Fintype NK] [Fintype RIVK] [Fintype ASK] [Fintype QK] [Fintype SK]
  [Nonempty NK] [Nonempty ASK]
  [DecidableEq AK] [DecidableEq NK] [DecidableEq RIVK] [DecidableEq QK] [DecidableEq SK]
  [DecidableEq G] [DecidableEq RHO] [DecidableEq PSI] [DecidableEq MHASH]
  [DecidableEq MENC]

/-- The games-facing key-binding interface at a sampled oracle assignment: the two
sampled key tables plus the three components of the combined `rivk` oracle. -/
abbrev kvAt (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G)
    (Hask : SK → ASK) (Hnk : SK → NK) (O : FinalQuery AK NK RIVK QK SK → RIVK) :
    KeyBindingInterface (KeyBinding.Witness G IVK AK NK RIVK QK SK) G IVK NK :=
  KeyBinding.toInterface Extract S hfn Ggen
    ⟨Hask, Hnk, fun sk => O (.legacy sk),
      fun qk ak nk => O (.ext qk ak nk),
      fun rivk_ext ak nk => O (.int rivk_ext ak nk)⟩

/-- **The key-binding arm's ε, discharged.** For any `n`-query-bounded ledger adversary
in the key-binding oracle model, the probability that its output ledger is valid and the
Balance-subset reduction lands in the key-binding arm is at most
`(n + 4) · (n + 3) / |RIVK|`. The adversary outputs only a ledger; the arm's witness pair
is recovered from that ledger by the oracle-free `kbPairOf` (`balanceSubsetOrBreak_kbPair`
identifies it with the reduction's own pair), so the composite that returns the pair makes
no queries beyond the adversary's own and `toInterface_break_measure_le` applies unchanged.
`kbPairOf` is `Option`-valued (`findPair` may find no duplicate) while the bound's machine
must return a concrete pair, so the composite collapses it with `Option.getD default`; the
default is furnished by `[Inhabited (Witness …)]`, present at the concrete instantiation. On
every sample of the bounded event `kbPairOf` is `some`, so the default is never used. -/
theorem balanceSubset_keyBindingArm_measure_le {ι : Type u}
    [Inhabited (KeyBinding.Witness G IVK AK NK RIVK QK SK)]
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G) (hS : S ≠ 0)
    (p : PMF ι)
    (P : Primitives RIVK G IVK NK RHO PSI MHASH MENC MSG SIG)
    (issuance : ℕ → ℕ) (maxActions : ℕ) (i : ℕ)
    {LA : ι → (SK → ASK) → (SK → NK) →
      OracleComp (FinalQuery AK NK RIVK QK SK) RIVK
        (Ledger (KeyBinding.Witness G IVK AK NK RIVK QK SK) RIVK G RHO PSI MHASH MENC
            MSG SIG P.depth)}
    {n : ℕ} (hQ : ∀ j Hask Hnk, (LA j Hask Hnk).QueryBound n) :
    ((kbExperiment p)).toOuterMeasure
        (setOf fun (j, Hask, Hnk, O) =>
          ∃ hval : ValidLedger P (kvAt Extract S hfn Ggen Hask Hnk O)
              issuance maxActions ((LA j Hask Hnk).run O),
            ∃ w₁ w₂ h, balanceSubsetOrBreak hval i
              = PSum.inr (BalanceBreak.keyBinding w₁ w₂ h))
      ≤ ((n + 4) * (n + 3) : ℕ) / Fintype.card RIVK := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (toInterface_break_measure_le Extract S hfn Ggen hS p
      (A := fun j Hask Hnk => (LA j Hask Hnk).bind fun L => .pure ((kbPairOf L i).getD default))
      (n := n) (fun j Hask Hnk => ?_))
  · rintro ⟨j, Hask, Hnk, O⟩ ⟨hval, w₁, w₂, h, heq⟩
    simp only [Set.mem_setOf_eq, OracleComp.run_bind, OracleComp.run_pure]
    have hkp : kbPairOf ((LA j Hask Hnk).run O) i = some (w₁, w₂) := by
      have := balanceSubsetOrBreak_kbPair hval i heq
      simpa [BalanceBreak.kbPair] using this.symm
    rw [hkp]
    exact h
  · exact OracleComp.queryBound_bind (hQ j Hask Hnk)
      fun L => OracleComp.QueryBound.pure _ 0

/-- **The Spend Authority key-binding arm's ε, discharged.** For any
`n`-query-bounded pair-annotated ledger adversary in the key-binding oracle model,
the probability that its output ledger is valid and the Spend Authority reduction —
at some Action spending a note addressed to the victim `wV` over an unsigned
sighash — lands in the key-binding arm with exactly its output pair is at most
`(n + 4) · (n + 3) / |RIVK|`. -/
theorem spendAuthority_keyBindingArm_measure_le {ι : Type u}
    (Extract : Extractor G IVK AK) (S : G) (hfn : AK → NK → RIVK) (Ggen : G) (hS : S ≠ 0)
    (p : PMF ι)
    (P : Primitives RIVK G IVK NK RHO PSI MHASH MENC MSG SIG)
    (issuance : ℕ → ℕ) (maxActions : ℕ)
    (wV : KeyBinding.Witness G IVK AK NK RIVK QK SK) (Signed : MSG → Prop)
    {LA : ι → (SK → ASK) → (SK → NK) →
      OracleComp (FinalQuery AK NK RIVK QK SK) RIVK
        (Ledger (KeyBinding.Witness G IVK AK NK RIVK QK SK) RIVK G RHO PSI MHASH MENC
            MSG SIG P.depth
          × (KeyBinding.Witness G IVK AK NK RIVK QK SK
            × KeyBinding.Witness G IVK AK NK RIVK QK SK))}
    {n : ℕ} (hQ : ∀ j Hask Hnk, (LA j Hask Hnk).QueryBound n) :
    ((kbExperiment p)).toOuterMeasure
        (setOf fun (j, Hask, Hnk, O) =>
          ∃ hval : ValidLedger P (kvAt Extract S hfn Ggen Hask Hnk O)
              issuance maxActions ((LA j Hask Hnk).run O).1,
            ∃ tx, ∃ htx : tx ∈ ((LA j Hask Hnk).run O).1, ∃ a, ∃ ha : a ∈ tx.actions,
              ∃ hKB : (kvAt Extract S hfn Ggen Hask Hnk O).KB wV,
                ∃ hrecv : a.w.note_old.pkd
                    = P.emb ((kvAt Extract S hfn Ggen Hask Hnk O).ivk wV)
                      • a.w.note_old.gd,
                  ∃ hfresh : ¬ Signed tx.sighash,
                    ∃ b, spendAuthorityOrBreak hval htx ha hKB hrecv hfresh = PSum.inr b
                      ∧ b.w₁ = ((LA j Hask Hnk).run O).2.1
                      ∧ b.w₂ = ((LA j Hask Hnk).run O).2.2)
      ≤ ((n + 4) * (n + 3) : ℕ) / Fintype.card RIVK := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (toInterface_break_measure_le Extract S hfn Ggen hS p
      (A := fun j Hask Hnk => (LA j Hask Hnk).bind fun out => .pure out.2)
      (n := n) (fun j Hask Hnk => ?_))
  · rintro ⟨j, Hask, Hnk, O⟩
      ⟨hval, tx, htx, a, ha, hKB, hrecv, hfresh, b, heq, hw₁, hw₂⟩
    simp only [Set.mem_setOf_eq, OracleComp.run_bind, OracleComp.run_pure]
    rw [← hw₁, ← hw₂]
    exact b.h
  · exact OracleComp.queryBound_bind (hQ j Hask Hnk)
      fun out => OracleComp.QueryBound.pure out.2 0

end OracleModel

end Zcash.Security.Ledger.Model
