import Mathlib
import Zcash.Security.Ledger.Model

/-!
# Spend Authority: forgery or break

The deterministic core of the Spend Authority game. Suppose an action spends a note
addressed to a key witness `wV` (its `pk_d` is `emb (ivk wV) • g_d`), in a transaction
whose sighash the holder of `wV` never signed. Then the ledger's own data computes one
of two things. If the action's verification key matches `akP wV` up to sign, the
action's signature is a `SpendAuthForgery`: a verifying signature under a randomization
of `± akP wV`, over an unsigned message. If it does not match even up to sign, the two
key witnesses share an `ivk` (receivability pins it) but not their `akP`, and
`break_of_akP_ne` turns that into a key-binding break.

The sign matters because `ak` is consumed as a single extracted coordinate, so the
statement pins `ak^ℙ` only up to its y-sign. A forgery therefore carries a `negated`
flag, and the unforgeability hypothesis for the randomized signature scheme must cover
both `akV` and `-akV`. That is a factor-of-2 security loss, fine with ~2^253 ±-fibres
remaining.

What stays outside this layer: unforgeability of the randomized signature scheme itself
(a named hypothesis; this layer produces the forgery object it consumes), and the
probability accounting of the key-binding break (the key-binding layer's bound).
-/

namespace Zcash.Security.Ledger.Model

open scoped Zcash.Security.RandomOracle

variable {F : Type*}
variable {G : Type*}
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}

section Validity

variable [Field F] [AddCommGroup G] [Module F G]
variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- A spend-authorization forgery against the verification key `akV`, as data: a
verifying signature under a randomization of `akV` or of `-akV` (recorded by `negated`),
over a message outside `Signed` — the messages the key's holder actually signed. This is
the object the named unforgeability hypothesis for the ±-randomized signature scheme
consumes. -/
structure SpendAuthForgery (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG)
    (akV : G) (Signed : MSG → Prop) where
  negated : Bool
  α : F
  rk : G
  msg : MSG
  sig : SIG
  rk_eq : rk = P.randomizePublic α (cond negated (-akV) akV)
  verifies : P.spendAuthVerify rk msg sig
  fresh : ¬ Signed msg

/-- A key-binding break between two exhibited witnesses, as data. -/
structure KeyBindingBreakData (kv : KeyBindingInterface KW G IVK NK) where
  w₁ : KW
  w₂ : KW
  h : kv.Break w₁ w₂

/-- Receivability pins `ivk`: a satisfied spend of a note addressed to `ivkV`
(`pk_d = emb ivkV • g_d`) has that `ivk` on its key witness. The one-witness form of
`ivk_pinned`, by the same module algebra. -/
theorem ivk_eq_of_receivable [NoZeroSMulDivisors F G]
    {inst : ActionInstance G MHASH RHO}
    {w : ActionWitness KW F G RHO PSI MHASH MENC P.depth}
    (h : ActionSatisfied P kv inst w) {ivkV : IVK}
    (hrecv : w.note_old.pkd = P.emb ivkV • w.note_old.gd) :
    kv.ivk w.kw = ivkV := by
  have hs : P.emb (kv.ivk w.kw) • w.note_old.gd = P.emb ivkV • w.note_old.gd := by
    rw [← h.pkd_eq, hrecv]
  have hz : (P.emb (kv.ivk w.kw) - P.emb ivkV) • w.note_old.gd = 0 := by
    rw [sub_smul, hs, sub_self]
  rcases smul_eq_zero.mp hz with hc | hgd0
  · exact P.emb_injective (sub_eq_zero.mp hc)
  · exact absurd hgd0 h.gd_ne

/-- **The Spend Authority core, per action.** A satisfied action spending a note
addressed to the key witness `wV`, whose signature verifies over a message the holder of
`wV` never signed, computes a forgery against `akP wV` — or a key-binding break. The
branch compares the action's `akP` with `± akP wV`: on a match the action's `rk` is a
randomization of `± akP wV` and the action's signature is the forgery; otherwise the two
key witnesses share `ivk` (receivability) but not `akP` up to sign, a break. -/
def spendAuthForgeryOrBreak [DecidableEq G] [NoZeroSMulDivisors F G]
    {inst : ActionInstance G MHASH RHO}
    {w : ActionWitness KW F G RHO PSI MHASH MENC P.depth}
    (h : ActionSatisfied P kv inst w) {wV : KW} (hKB : kv.KB wV)
    (hrecv : w.note_old.pkd = P.emb (kv.ivk wV) • w.note_old.gd)
    {msg : MSG} {sig : SIG} (hver : P.spendAuthVerify inst.rk msg sig)
    {Signed : MSG → Prop} (hfresh : ¬ Signed msg) :
    SpendAuthForgery P (kv.akP wV) Signed ⊕' KeyBindingBreakData kv :=
  if hak : kv.akP w.kw = kv.akP wV then
    .inl ⟨false, w.α, inst.rk, msg, sig, by rw [h.rk_eq, hak]; rfl, hver, hfresh⟩
  else if hakn : kv.akP w.kw = -kv.akP wV then
    .inl ⟨true, w.α, inst.rk, msg, sig, by rw [h.rk_eq, hakn]; rfl, hver, hfresh⟩
  else
    .inr ⟨w.kw, wV, kv.break_of_akP_ne h.key_binding hKB
      (ivk_eq_of_receivable h hrecv) fun hpm => hpm.elim hak hakn⟩

/-- **Spend Authority.** In a valid ledger, an action spending a note addressed to the
key witness `wV`, in a transaction whose sighash the holder of `wV` never signed,
computes a spend-authorization forgery against `akP wV` — or a key-binding break.
Statement satisfaction and signature verification come from validity; the reduction is
`spendAuthForgeryOrBreak`. -/
def spendAuthorityOrBreak [DecidableEq G] [NoZeroSMulDivisors F G]
    (hval : ValidLedger P kv issuance maxActions ledger)
    {tx : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth} (htx : tx ∈ ledger)
    {a : Action KW F G RHO PSI MHASH MENC SIG P.depth} (ha : a ∈ tx.actions)
    {wV : KW} (hKB : kv.KB wV)
    (hrecv : a.w.note_old.pkd = P.emb (kv.ivk wV) • a.w.note_old.gd)
    {Signed : MSG → Prop} (hfresh : ¬ Signed tx.sighash) :
    SpendAuthForgery P (kv.akP wV) Signed ⊕' KeyBindingBreakData kv :=
  spendAuthForgeryOrBreak (hval.satisfied tx htx a ha) hKB hrecv
    (hval.sig_verifies tx htx a ha) hfresh

end Validity

end Zcash.Security.Ledger.Model
