import Mathlib
import Zcash.Security.Ledger.Merkle

/-!
# The abstract Action statement and its pinning lemmas

This module transcribes the games-relevant conjuncts of an Orchard-shaped Action statement
(Zcash protocol specification §4.17.4) over abstract primitives, as the interface consumed
by the ledger-model security games (Balance, Spendability, Spend Authority). Two intended
instantiations satisfy it:

* the deployed (pre-quantum) Orchard Action statement, where the key-binding condition is
  the bare `Commit^ivk` opening and note-commitment breaks reduce to Sinsemilla/DLR
  relations; and
* the ZIP 2005 Recovery Statement, which adds derivation constraints (`KB_deriv`, the
  `H^rcm`/`H^ψ` checks) so that the same breaks reduce to random-oracle collisions.

The key material is decoupled behind `KeyBindingInterface`: the games see only the
projections (`ivk`, `nk`, `akP`), the key-binding condition `KB` enforced by the statement,
and a `Break` predicate with the guarantee that two `KB`-witnesses sharing an `ivk` but
disagreeing on `nk` are a break. The concrete witness structure, the factoring
`KB = KBOpening ∧ KBDerivation`, and the reduction from `Break` to random-oracle
collisions live in the key-binding layer
(`Zcash/Security/KeyBinding/Basic.lean` for Recovery and
`Zcash/Security/KeyBinding/Pool.lean` for the deployed Action circuit).

The lemmas here are the deterministic pinning steps of the Balance argument:

* `ivk_pinned` — an address `(g_d, pk_d)` determines `ivk` (ZIP 2005's `ivk`-pinning lemma;
  needs only `g_d ≠ 0` and torsion-freeness of the group, no cryptography);
* `nk_eq_or_break` — hence `nk` is determined up to an exhibited key-binding break;
* `noteCommitBreakOfNe` — an `extract`-equal commitment pins the note tuple `(rcm, note)`,
  else this reduction computes a note-commitment break (data, per breaks-as-computed-data);
* `nf_old_eq_or_break` — nullifier determinism: spends of the same note tuple reveal the
  same nullifier, up to an exhibited key-binding break.
-/

namespace Zcash.Security.Ledger

variable {F : Type*} [Field F]
variable {G : Type*} [AddCommGroup G] [Module F G]
variable {IVK NK RHO PSI CMX RT : Type*} {E : Type*} {KW : Type*}

/-- An Orchard-shaped note. Point encodings and type conversions are abstracted away:
`gd` and `pkd` are group elements, `ρ` and `ψ` base-field values, `v` a natural number
(range-bounded by the statement). -/
structure Note (G RHO PSI : Type*) where
  gd : G
  pkd : G
  v : ℕ
  ρ : RHO
  ψ : PSI

/-- The public inputs of an Action that the games consume: the anchor, the revealed
nullifier, the randomized verification key, the net value commitment, and the new note
commitment's extracted coordinate. -/
structure ActionInstance (G RT RHO CMX : Type*) where
  rt : RT
  /-- `⦂ RHO`: nullifiers share ρ's type, forced by ρ-uniqueness (`ρ_new = nf_old`). -/
  nf_old : RHO
  rk : G
  cv_net : G
  cmx_new : CMX

/-- The abstract primitives of an Orchard-shaped shielded protocol. No algebraic structure
is required of the fields themselves; the group algebra enters only through the statement
and lemmas. `emb` is the embedding of base-field values used as scalars
(`[0, q) ⊆ [0, r)` concretely). -/
structure Primitives (F G IVK NK RHO PSI CMX RT E : Type*) where
  valueBound : ℕ
  emb : IVK → F
  emb_injective : Function.Injective emb
  extract : G → CMX
  noteCommit : F → Note G RHO PSI → Option G
  /-- Nullifiers share ρ's type (`RHO`), forced by ρ-uniqueness (`ρ_new = nf_old`). -/
  deriveNullifier : NK → RHO → PSI → G → RHO
  /-- The raw-encoding Merkle interface: tree nodes are `RT` values, `E` is the raw
  child encoding consumed by the level-personalized compression. -/
  merkle : MerklePrimitives RT E
  leafOf : CMX → RHO → RT
  randomizePublic : F → G → G
  valueCommit : ℤ → F → G

/-- The collision vocabulary associated with the level-personalized Merkle primitive. -/
abbrev MerkleCollision (P : Primitives F G IVK NK RHO PSI CMX RT E) :=
  Merkle.Collision P.merkle

/-- The games-facing view of a key-binding witness type `KW`: projections, the key-binding
condition `KB` enforced by the statement, and a `Break` predicate. `break_of_nk_ne` is the
guarantee the games consume; the key-binding layer instantiates `Break` and discharges it
(reducing breaks onward to random-oracle collisions or DLR relations). This interface is
provisional: its shape is to be revisited against what the Balance and Spendability games
actually consume once they are formalized — in particular `Break` being an opaque `Prop`
limits the games to certificate-level break exhibition. -/
structure KeyBindingInterface (KW G IVK NK : Type*) where
  ivk : KW → IVK
  nk : KW → NK
  akP : KW → G
  KB : KW → Prop
  Break : KW → KW → Prop
  break_of_nk_ne : ∀ {w₁ w₂ : KW}, KB w₁ → KB w₂ →
    ivk w₁ = ivk w₂ → nk w₁ ≠ nk w₂ → Break w₁ w₂

/-- The auxiliary inputs of an Action. `cm_old`/`cm_new` are carried explicitly so that the
statement's commitment checks pin them; `kw` is the key-binding witness. -/
structure ActionWitness (KW F G RHO PSI E : Type*) (d : ℕ) where
  /-- Both raw child encodings at every layer, in leaf-to-root order. -/
  path : Fin d → E × E
  /-- The child encoding selected by the path (`false` = left, `true` = right). -/
  side : Fin d → Bool
  note_old : Note G RHO PSI
  note_new : Note G RHO PSI
  cm_old : G
  cm_new : G
  kw : KW
  α : F
  rcv : F
  rcm_old : F
  rcm_new : F

/-- The games-relevant conjuncts of the Action statement, for instance `inst` and witness
`w`. Both the deployed Orchard Action statement and the ZIP 2005 Recovery Statement
satisfy this interface (the latter enforces strictly more).

TODO: It's unclear how well this will compose with Gregor's approach to the circuit proof.
In particular, should this be `Prop`-only or will we need to apply the break-as-computed-data
pattern here? -/
structure ActionSatisfied (P : Primitives F G IVK NK RHO PSI CMX RT E)
    (kv : KeyBindingInterface KW G IVK NK) (inst : ActionInstance G RT RHO CMX)
    (w : ActionWitness KW F G RHO PSI E P.merkle.depth) : Prop where
  /-- Spend-side commitment integrity: `cm_old` opens `note_old` with `rcm_old`. -/
  commit_old : P.noteCommit w.rcm_old w.note_old = some w.cm_old
  /-- Merkle path validity for nonzero-valued spends. -/
  merkle_path : w.note_old.v ≠ 0 →
    Merkle.Path P.merkle (P.leafOf (P.extract w.cm_old) w.note_old.ρ) inst.rt w.path w.side
  /-- Nullifier integrity. -/
  nf_old_eq : inst.nf_old =
    P.deriveNullifier (kv.nk w.kw) w.note_old.ρ w.note_old.ψ w.cm_old
  /-- The key-binding condition on the key witness. -/
  key_binding : kv.KB w.kw
  /-- Diversified address integrity: `pk_d = [ivk] g_d`. -/
  pkd_eq : w.note_old.pkd = P.emb (kv.ivk w.kw) • w.note_old.gd
  /-- `g_d` is not the zero element. -/
  gd_ne : w.note_old.gd ≠ 0
  /-- Spend authority: `rk` is the `α`-randomization of the verification key. -/
  rk_eq : inst.rk = P.randomizePublic w.α (kv.akP w.kw)
  /-- Output-side commitment integrity: `cm_new` opens `note_new` with `rcm_new`. -/
  commit_new : P.noteCommit w.rcm_new w.note_new = some w.cm_new
  /-- The instance exposes the extracted coordinate of `cm_new`. -/
  cmx_new_eq : inst.cmx_new = P.extract w.cm_new
  /-- ρ-uniqueness: the output note's `ρ` is the spend's nullifier. -/
  ρ_new_eq : w.note_new.ρ = inst.nf_old
  /-- Spent-note value range. -/
  v_old_lt : w.note_old.v < P.valueBound
  /-- Output-note value range. -/
  v_new_lt : w.note_new.v < P.valueBound
  /-- Value commitment integrity over the net value. -/
  cv_net_eq : inst.cv_net = P.valueCommit ((w.note_old.v : ℤ) - (w.note_new.v : ℤ)) w.rcv

/-- A note-commitment break, as data (per the breaks-as-computed-data
convention in `Zcash.Security.RandomOracle`): two distinct `(rcm, note)` tuples whose commitments have
equal extracted coordinates. Computed by the games' reductions; each instantiation reduces
it onward (a Sinsemilla/DLR relation pre-quantum; an `H^rcm` ±-collision for the Recovery
Statement via the Pedersen lift and the `extract` ±-property). -/
structure NoteCommitBreak (P : Primitives F G IVK NK RHO PSI CMX RT E) where
  rcm₁ : F
  n₁ : Note G RHO PSI
  rcm₂ : F
  n₂ : Note G RHO PSI
  cm₁ : G
  cm₂ : G
  ne : (rcm₁, n₁) ≠ (rcm₂, n₂)
  open₁ : P.noteCommit rcm₁ n₁ = some cm₁
  open₂ : P.noteCommit rcm₂ n₂ = some cm₂
  extract_eq : P.extract cm₁ = P.extract cm₂

section Pinning

variable {P : Primitives F G IVK NK RHO PSI CMX RT E}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {inst₁ inst₂ : ActionInstance G RT RHO CMX}
variable {w₁ w₂ : ActionWitness KW F G RHO PSI E P.merkle.depth}

/-- **`ivk`-pinning** (ZIP 2005 `lemma-ivk-pinning`): the address `(g_d, pk_d)` of the
spent note determines `ivk`. Pure module algebra: needs only `g_d ≠ 0`, injectivity of the
scalar embedding, and torsion-freeness of the group (satisfied by a prime-order group). -/
theorem ivk_pinned [NoZeroSMulDivisors F G]
    (h₁ : ActionSatisfied P kv inst₁ w₁) (h₂ : ActionSatisfied P kv inst₂ w₂)
    (hgd : w₁.note_old.gd = w₂.note_old.gd) (hpkd : w₁.note_old.pkd = w₂.note_old.pkd) :
    kv.ivk w₁.kw = kv.ivk w₂.kw := by
  have hs : P.emb (kv.ivk w₁.kw) • w₂.note_old.gd
      = P.emb (kv.ivk w₂.kw) • w₂.note_old.gd := by
    rw [← hgd, ← h₁.pkd_eq, hpkd, h₂.pkd_eq, hgd]
  have hz : (P.emb (kv.ivk w₁.kw) - P.emb (kv.ivk w₂.kw)) • w₂.note_old.gd = 0 := by
    rw [sub_smul, hs, sub_self]
  rcases smul_eq_zero.mp hz with hc | hgd0
  · exact P.emb_injective (sub_eq_zero.mp hc)
  · exact absurd hgd0 h₂.gd_ne

/-- `nk`-pinning up to a break: two satisfied spends of notes with the same address agree
on `nk`, or their key witnesses exhibit a key-binding break. -/
theorem nk_eq_or_break [NoZeroSMulDivisors F G]
    (h₁ : ActionSatisfied P kv inst₁ w₁) (h₂ : ActionSatisfied P kv inst₂ w₂)
    (hgd : w₁.note_old.gd = w₂.note_old.gd) (hpkd : w₁.note_old.pkd = w₂.note_old.pkd) :
    kv.nk w₁.kw = kv.nk w₂.kw ∨ kv.Break w₁.kw w₂.kw := by
  by_cases hnk : kv.nk w₁.kw = kv.nk w₂.kw
  · exact Or.inl hnk
  · exact Or.inr (kv.break_of_nk_ne h₁.key_binding h₂.key_binding
      (ivk_pinned h₁ h₂ hgd hpkd) hnk)

/-- **Note-tuple pinning, as an explicit reduction**: two satisfied spends with
`extract`-equal commitments but distinct note tuples `(rcm_old, note_old)` yield a
note-commitment break. This is the step that converts Merkle-pinned leaves into pinned
notes in the Balance argument; consumers with `DecidableEq` on the tuple case-split and
call this in the ≠ branch. -/
def noteCommitBreakOfNe
    (h₁ : ActionSatisfied P kv inst₁ w₁) (h₂ : ActionSatisfied P kv inst₂ w₂)
    (hx : P.extract w₁.cm_old = P.extract w₂.cm_old)
    (hne : (w₁.rcm_old, w₁.note_old) ≠ (w₂.rcm_old, w₂.note_old)) :
    NoteCommitBreak P :=
  ⟨_, _, _, _, _, _, hne, h₁.commit_old, h₂.commit_old, hx⟩

/-- **Nullifier determinism up to a break** — **nf-pinning** (ZIP 2005 `lemma-nf-pinning`,
consumed by the Spendability argument), as computed data per the breaks-as-computed-data
convention: two satisfied spends of the same note tuple either reveal the same nullifier or
their key witnesses exhibit a key-binding break, with the branch decided on the
nullifier-key comparison. Together with `tuple_eq_or_noteCommitBreak` this is what turns a
repeated spend of a positioned note into a repeated nullifier in the Balance argument. The
nullifier here is a function by definition; the circuit-soundness layer must separately
ensure the deployed circuit computes `DeriveNullifier` deterministically as a function of
`(nk, ρ, ψ, cm)`. -/
def nfOldEqOrBreak [DecidableEq NK] [NoZeroSMulDivisors F G]
    (h₁ : ActionSatisfied P kv inst₁ w₁) (h₂ : ActionSatisfied P kv inst₂ w₂)
    (hrcm : w₁.rcm_old = w₂.rcm_old) (hnote : w₁.note_old = w₂.note_old) :
    (inst₁.nf_old = inst₂.nf_old) ⊕' kv.Break w₁.kw w₂.kw :=
  if hnk : kv.nk w₁.kw = kv.nk w₂.kw then
    .inl (by
      have hcm : w₁.cm_old = w₂.cm_old := by
        have h := h₁.commit_old
        rw [hrcm, hnote, h₂.commit_old] at h
        exact (Option.some.inj h).symm
      rw [h₁.nf_old_eq, h₂.nf_old_eq, hnk, hcm, hnote])
  else
    .inr (kv.break_of_nk_ne h₁.key_binding h₂.key_binding
      (ivk_pinned h₁ h₂ (congrArg Note.gd hnote) (congrArg Note.pkd hnote)) hnk)

end Pinning

end Zcash.Security.Ledger
