import Mathlib
import Zcash.Security.Ledger.Balance

/-!
# Spendability: the Faerie-Gold core and persistence

Two deterministic pieces of the Spendability game. The Faerie-Gold core says nullifiers
pin note tuples: two satisfied spends with distinct openings and equal revealed
nullifiers compute a break — a `NoteCommitBreak` when their derive-inputs coincide (the
same commitment opened two ways), and otherwise a `NullifierCollision`, two distinct
inputs on which `deriveNullifier` agrees. The collision is terminal vocabulary here:
nothing in this development reduces it further. The intended deployed discharge is a
named DL/Pedersen-hash hypothesis; for the Recovery Statement, ZIP 2005's Spendability
theorem reduces it to an `H^rcm` ±-collision.

Persistence says a transaction valid immediately after `ledger` stays valid when
appended to any valid extension `ledger'`: anchors persist because prefix roots do
(`rootAfter_prefix`), satisfaction and signatures are per-transaction, and the only live
conditions are nullifier freshness and the boundary conjuncts (capacity and transparent
nonnegativity), which appear as hypotheses. The roadblock inversion (`respendOrBreak`)
classifies what can consume a nullifier first: an action revealing the same nullifier
either re-spends the same opening (the case Spend Authority handles) or computes a
break.

Key binding plays no role at this layer: `nk` is carried inside the collision data, and
ZIP 2005's nf-pinning conditioning belongs to the Recovery instantiation's
probabilistic layer, not here.
-/

namespace Zcash.Security.Ledger.Model

variable {F : Type*}
variable {G : Type*}
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*} {d : ℕ}

/-- Nullifiers of an appended ledger split at the append. -/
theorem nullifiers_append (l₁ l₂ : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) :
    nullifiers (l₁ ++ l₂) = nullifiers l₁ ++ nullifiers l₂ := by
  simp [nullifiers, List.flatMap_append]

section Validity

variable [Field F] [AddCommGroup G] [Module F G]
variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {ledger ledger' : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth}
variable {T : Tx KW F G RHO PSI MHASH MENC MSG SIG P.depth}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- A nullifier-derivation collision, as data: two distinct derive-inputs on which
`deriveNullifier` agrees. Terminal vocabulary — nothing in this development reduces it
further; the intended deployed hypothesis is discrete-log independence of the nullifier
base 𝒦^Orchard from the note-commitment bases. -/
structure NullifierCollision (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG) where
  nk₁ : NK
  ρ₁ : RHO
  ψ₁ : PSI
  cm₁ : G
  nk₂ : NK
  ρ₂ : RHO
  ψ₂ : PSI
  cm₂ : G
  ne : (nk₁, ρ₁, ψ₁, cm₁) ≠ (nk₂, ρ₂, ψ₂, cm₂)
  eq : P.deriveNullifier nk₁ ρ₁ ψ₁ cm₁ = P.deriveNullifier nk₂ ρ₂ ψ₂ cm₂

/-- **The Faerie-Gold core.** Two satisfied spends with distinct openings and equal
revealed nullifiers compute a break: when the derive-inputs coincide the same
commitment has two openings, and when they differ they are themselves the collision. -/
def faerieGoldCore [DecidableEq G] [DecidableEq NK] [DecidableEq RHO] [DecidableEq PSI]
    {inst₁ inst₂ : ActionInstance G MHASH RHO}
    {w₁ w₂ : ActionWitness KW F G RHO PSI MHASH MENC P.depth}
    (h₁ : ActionSatisfied P kv inst₁ w₁) (h₂ : ActionSatisfied P kv inst₂ w₂)
    (hne : (w₁.rcm_old, w₁.note_old) ≠ (w₂.rcm_old, w₂.note_old))
    (hnf : inst₁.nf_old = inst₂.nf_old) :
    NoteCommitBreak P ⊕' NullifierCollision P :=
  if hin : (kv.nk w₁.kw, w₁.note_old.ρ, w₁.note_old.ψ, w₁.cm_old)
      = (kv.nk w₂.kw, w₂.note_old.ρ, w₂.note_old.ψ, w₂.cm_old) then
    .inl (by
      simp only [Prod.mk.injEq] at hin
      exact noteCommitBreakOfNe h₁ h₂ (congrArg P.extract hin.2.2.2) hne)
  else
    .inr ⟨_, _, _, _, _, _, _, _, hin, by
      rw [← h₁.nf_old_eq, ← h₂.nf_old_eq]
      exact hnf⟩

/-- **The roadblock inversion.** An action revealing the same nullifier as a satisfied
spend either re-spends the same opening (the case Spend Authority handles) or computes
a break. -/
def respendOrBreak [DecidableEq F] [DecidableEq G] [DecidableEq NK] [DecidableEq RHO]
    [DecidableEq PSI]
    {inst₁ inst₂ : ActionInstance G MHASH RHO}
    {w₁ w₂ : ActionWitness KW F G RHO PSI MHASH MENC P.depth}
    (h₁ : ActionSatisfied P kv inst₁ w₁) (h₂ : ActionSatisfied P kv inst₂ w₂)
    (hnf : inst₁.nf_old = inst₂.nf_old) :
    ((w₁.rcm_old, w₁.note_old) = (w₂.rcm_old, w₂.note_old))
      ⊕' (NoteCommitBreak P ⊕' NullifierCollision P) :=
  if h : (w₁.rcm_old, w₁.note_old) = (w₂.rcm_old, w₂.note_old) then .inl h
  else .inr (faerieGoldCore h₁ h₂ h hnf)

/-- **Persistence.** A transaction valid immediately after `ledger` remains valid when
appended to any valid extension `ledger'`, given that its nullifiers are still fresh
and the boundary conjuncts hold for the appended ledger. Anchors persist because prefix
roots do; satisfaction, signatures, and the action bound are per-transaction. -/
theorem validLedger_append
    (hval' : ValidLedger P kv issuance maxActions ledger')
    (hpre : ledger <+: ledger')
    (hvalT : ValidLedger P kv issuance maxActions (ledger ++ [T]))
    (hfresh : ∀ a ∈ T.actions, a.inst.nf_old ∉ nullifiers ledger')
    (hcap : (leafList (ledger' ++ [T])).length ≤ 2 ^ P.depth)
    (htrans : ∀ i : ℕ, 0 ≤ transparentPoolBalance issuance (ledger' ++ [T]) i) :
    ValidLedger P kv issuance maxActions (ledger' ++ [T]) := by
  have hTmem : T ∈ ledger ++ [T] := by simp
  have hmem : ∀ tx ∈ ledger' ++ [T], tx ∈ ledger' ∨ tx = T := by
    intro tx htx
    rcases List.mem_append.mp htx with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  refine ⟨?_, ?_, ?_, hcap, ?_, htrans, ?_⟩
  · intro tx htx a ha
    rcases hmem tx htx with h | rfl
    · exact hval'.satisfied tx h a ha
    · exact hvalT.satisfied tx hTmem a ha
  · rw [nullifiers_append]
    refine List.nodup_append.mpr ⟨hval'.nf_nodup, ?_, ?_⟩
    · have h := hvalT.nf_nodup
      rw [nullifiers_append] at h
      exact (List.nodup_append.mp h).2.1
    · intro x hx y hy
      obtain ⟨a, ha, rfl⟩ : ∃ a ∈ T.actions, a.inst.nf_old = y := by
        simpa [nullifiers] using hy
      exact fun heq => hfresh a ha (heq ▸ hx)
  · intro i a hai
    by_cases hi : (i : ℕ) < ledger'.length
    · have hget : (ledger' ++ [T]).get i = ledger'.get ⟨(i : ℕ), hi⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left hi]
      rw [hget] at hai
      obtain ⟨j, hj, hrt⟩ := hval'.anchor_valid ⟨(i : ℕ), hi⟩ a hai
      refine ⟨j, hj, ?_⟩
      rw [rootAfter_prefix P ⟨[T], rfl⟩ (le_trans hj (le_of_lt hi))]
      exact hrt
    · have hieq : (i : ℕ) = ledger'.length := by
        have := i.isLt
        simp only [List.length_append, List.length_singleton] at this
        omega
      have hget : (ledger' ++ [T]).get i = T := by
        simp [List.get_eq_getElem, hieq]
      rw [hget] at hai
      have hTfin : (ledger ++ [T]).get ⟨ledger.length, by simp⟩ = T := by
        simp [List.get_eq_getElem]
      obtain ⟨j, hj, hrt⟩ := hvalT.anchor_valid ⟨ledger.length, by simp⟩ a
        (by rw [hTfin]; exact hai)
      refine ⟨j, ?_, ?_⟩
      · rw [hieq]
        exact le_trans hj hpre.length_le
      · rw [rootAfter_prefix P (⟨[T], rfl⟩ : ledger' <+: ledger' ++ [T])
            (le_trans hj hpre.length_le),
          rootAfter_prefix P hpre hj,
          ← rootAfter_prefix P (⟨[T], rfl⟩ : ledger <+: ledger ++ [T]) hj]
        exact hrt
  · intro tx htx a ha
    rcases hmem tx htx with h | rfl
    · exact hval'.sig_verifies tx h a ha
    · exact hvalT.sig_verifies tx hTmem a ha
  · intro tx htx
    rcases hmem tx htx with h | rfl
    · exact hval'.action_bound tx h
    · exact hvalT.action_bound tx hTmem

end Validity

end Zcash.Security.Ledger.Model
