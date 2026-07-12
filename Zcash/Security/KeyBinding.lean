import Mathlib
import Zcash.Security.RandomOracle

/-!
# Key binding (Orchard / Ironwood) — Layer A

Formalizes ZIP 2005 §"Security argument for key binding" (`thm-key-binding-rom`) and the `ivk`-pinning
lemma: a verifying Recovery-Statement witness pins the key components (`ak` up to y-sign, `nk`, `qk`)
to `ivk`. Shared intermediate result under Balance (`nk`-pinning), Spendability (`PRF^nf`-pinning), and
Spend authority (`ak`/`qk`-pinning).

The *deterministic reduction* `OpeningBreak ⇒ CollisionUpToSign` is the composable core;
`openingBreak_scalar_pm` below is its algebraic heart. The probabilistic birthday bound
`ε_kb ≤ 3q(q-1)/2r` is a separate concern.

Abstract setting: a prime-order group `G` as an `F`-vector space (`F = ZMod r` the scalar field),
a base field `B` (x-coordinates, `= ZMod q`), and `Extract : G → B` with the ±-property (`hExt`).

`Commitivk` is required to have the Pedersen structure (not opaque), which is what makes the break
reduction provable. Pallas is instantiated last via CompElliptic.
-/

namespace Zcash.Security.KeyBinding

open Zcash.Security.RandomOracle

/-- A Recovery-Statement / Orchard key witness (ZIP 2005 §"key binding"). `use_qsk` is encoded by
which of `sk`/`qk` is `some`; the internal-vs-external `ivk` choice by `rivk`'s value. -/
structure Witness (G F B SK QK : Type*) where
  ivk      : B
  qk       : Option QK
  sk       : Option SK
  akP      : G
  nk       : B
  rivk_ext : F
  rivk     : F

variable {G F B SK QK : Type*}

/-- `ak = Extract(ak^ℙ)`. -/
def ak (Extract : G → B) (w : Witness G F B SK QK) : B := Extract w.akP

/-- The Pedersen-scalar map a `Commitivk` opening reduces to: `(ak, nk, rivk) ↦ h ak nk + rivk`.
An `OpeningBreak` is exhibited as a `CollisionUpToSign` of this map by `commitCollision`. -/
def pedersenScalar [Add F] (hfn : B → B → F) (t : B × B × F) : F := hfn t.1 t.2.1 + t.2.2

/-- The "final input" to the final `rivk`-derivation random oracle (ZIP 2005 key-binding proof):
the query at which `rivk` is that oracle's output, selected by the qk/sk branch and the
external/internal ivk choice. -/
inductive FinalQuery (QK SK B F : Type*) where
  /-- qk-branch, external ivk: `rivk = Hrivk_ext qk ak nk`. -/
  | ext : QK → B → B → FinalQuery QK SK B F
  /-- sk-branch, external ivk: `rivk = Hrivk_legacy sk`. -/
  | legacy : SK → FinalQuery QK SK B F
  /-- internal ivk: `rivk = Hrivk_int rivk_ext ak nk`. -/
  | int : F → B → B → FinalQuery QK SK B F

/-- The combined final `rivk`-derivation random oracle: dispatch each final query to its oracle. -/
def FinalQuery.eval (Hrivk_legacy : SK → F) (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F) :
    FinalQuery QK SK B F → F
  | .ext qk a n => Hrivk_ext qk a n
  | .legacy sk => Hrivk_legacy sk
  | .int re a n => Hrivk_int re a n

section Algebra
variable [AddCommGroup G] [Field F] [Field B] [Module F G] [NoZeroSMulDivisors F G]

/-- The `ivk` commitment as a Pedersen lift (Layer B request):
`Commitivk rivk a n = Extract ((h a n + rivk) • S)`, with `h` abstract-but-non-querying and `S` a
fixed base. Mirrors the `NoteCommit` repair `[H^rcm + f]·R`. -/
def Commitivk (Extract : G → B) (S : G) (hfn : B → B → F) (rivk : F) (a n : B) : B :=
  Extract ((hfn a n + rivk) • S)

omit [Field B] in
/-- Algebraic core: two openings of the same `Commitivk` value force their Pedersen scalars to be
equal or negatives. Uses the `Extract` ±-property and injectivity of `·•S` for `S ≠ 0` (`G` is an
`F`-vector space). This is the deterministic content the whole key-binding reduction rests on. -/
theorem commit_scalar_pm
    (Extract : G → B) (S : G) (hfn : B → B → F)
    (hExt : ∀ P Q : G, Extract P = Extract Q ↔ P = Q ∨ P = -Q) (hS : S ≠ 0)
    {r₁ r₂ : F} {a₁ n₁ a₂ n₂ : B}
    (hcm : Commitivk Extract S hfn r₁ a₁ n₁ = Commitivk Extract S hfn r₂ a₂ n₂) :
    hfn a₁ n₁ + r₁ = hfn a₂ n₂ + r₂ ∨ hfn a₁ n₁ + r₁ = -(hfn a₂ n₂ + r₂) := by
  unfold Commitivk at hcm
  rw [hExt] at hcm
  rcases hcm with hcm | hcm
  · left
    have h0 : (hfn a₁ n₁ + r₁ - (hfn a₂ n₂ + r₂)) • S = 0 := by
      rw [sub_smul, hcm, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hS
  · right
    have hcm' : (hfn a₁ n₁ + r₁) • S = (-(hfn a₂ n₂ + r₂)) • S := by
      rw [neg_smul]; exact hcm
    have h0 : (hfn a₁ n₁ + r₁ - (-(hfn a₂ n₂ + r₂))) • S = 0 := by
      rw [sub_smul, hcm', sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hS

/-- `KBOpening` — the commitment-opening core of the key-binding condition (what Layer B's
statement-validity yields): `ivk` opens as `Commitivk` at `(rivk, ak, nk)`, and `ivk ≠ 0`. -/
def KBOpening (Extract : G → B) (S : G) (hfn : B → B → F) (w : Witness G F B SK QK) : Prop :=
  w.ivk = Commitivk Extract S hfn w.rivk (ak Extract w) w.nk ∧ w.ivk ≠ 0

/-- `OpeningBreak` — a `Commitivk`-opening collision (produced by Layer B's games layer): two valid `KBOpening`
witnesses with the same `ivk` but differing `(ak, nk, rivk)`. -/
def OpeningBreak (Extract : G → B) (S : G) (hfn : B → B → F) (w₁ w₂ : Witness G F B SK QK) : Prop :=
  KBOpening Extract S hfn w₁ ∧ KBOpening Extract S hfn w₂ ∧ w₁.ivk = w₂.ivk ∧
    (ak Extract w₁, w₁.nk, w₁.rivk) ≠ (ak Extract w₂, w₂.nk, w₂.rivk)

/-- The deterministic reduction (composable core): a `OpeningBreak` exhibits distinct `(ak, nk, rivk)`
triples whose Pedersen scalars `h(ak,nk) + rivk` are equal or negatives — a ±-collision of the
commitment's scalar map. Under `KBDerivation` (below) `rivk` is an `H^*` output, turning this into a
random-oracle ±-collision that the birthday bound (Layer C) bounds. -/
theorem openingBreak_scalar_pm
    (Extract : G → B) (S : G) (hfn : B → B → F)
    (hExt : ∀ P Q : G, Extract P = Extract Q ↔ P = Q ∨ P = -Q) (hS : S ≠ 0)
    {w₁ w₂ : Witness G F B SK QK} (hbrk : OpeningBreak Extract S hfn w₁ w₂) :
    (ak Extract w₁, w₁.nk, w₁.rivk) ≠ (ak Extract w₂, w₂.nk, w₂.rivk) ∧
    (hfn (ak Extract w₁) w₁.nk + w₁.rivk = hfn (ak Extract w₂) w₂.nk + w₂.rivk ∨
     hfn (ak Extract w₁) w₁.nk + w₁.rivk = -(hfn (ak Extract w₂) w₂.nk + w₂.rivk)) := by
  obtain ⟨hk₁, hk₂, hivk, hne⟩ := hbrk
  refine ⟨hne, commit_scalar_pm Extract S hfn hExt hS ?_⟩
  -- Commitivk(w₁) = w₁.ivk = w₂.ivk = Commitivk(w₂)
  exact hk₁.1.symm.trans (hivk.trans hk₂.1)

/-- **Breaks as computed data** (per the `RandomOracle` convention): a computable function turning a
`OpeningBreak` into a `CollisionUpToSign` of the Pedersen-scalar map `pedersenScalar hfn`. The colliding
queries are the two `(ak, nk, rivk)` triples read off the witnesses; `openingBreak_scalar_pm` supplies the
distinctness and the ±-equality (both erased `Prop` fields), so the data is genuinely computed, not
extracted from a proof. The onward reduction to an `H^*` random-oracle collision (via `KBDerivation`,
where `rivk` is an oracle output) is per-instantiation, as with `NoteCommitBreak`. -/
def commitCollision
    (Extract : G → B) (S : G) (hfn : B → B → F)
    (hExt : ∀ P Q : G, Extract P = Extract Q ↔ P = Q ∨ P = -Q) (hS : S ≠ 0)
    {w₁ w₂ : Witness G F B SK QK} (hbrk : OpeningBreak Extract S hfn w₁ w₂) :
    RandomOracle.CollisionUpToSign (pedersenScalar hfn) where
  q₁ := (ak Extract w₁, w₁.nk, w₁.rivk)
  q₂ := (ak Extract w₂, w₂.nk, w₂.rivk)
  ne := (openingBreak_scalar_pm Extract S hfn hExt hS hbrk).1
  pm := by simpa [pedersenScalar] using (openingBreak_scalar_pm Extract S hfn hExt hS hbrk).2

end Algebra

section Derivation
variable [AddCommGroup G] [Field F] [Field B] [Module F G]

/-- `BindKeys^sk` (ZIP 2005): the `sk`-branch derivation constraints. -/
def BindKeysSk (Ggen : G) (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (sk : SK) (akP : G) (nk : B) (rivk_ext : F) : Prop :=
  akP = (Hask sk) • Ggen ∧ nk = Hnk sk ∧ rivk_ext = Hrivk_legacy sk

/-- `KBDerivation` — the ZIP 2005 derivation constraints (conjuncts 1–4): the `sk`/`qk` null-structure,
the `Hrivk_ext` / `BindKeys^sk` branch constraints, and `rivk ∈ {rivk_ext, Hrivk_int …}`. -/
def KBDerivation (Extract : G → B) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    (w : Witness G F B SK QK) : Prop :=
  ((w.sk = none) ≠ (w.qk = none)) ∧
  (∀ qk, w.qk = some qk → w.rivk_ext = Hrivk_ext qk (ak Extract w) w.nk) ∧
  (∀ sk, w.sk = some sk → BindKeysSk Ggen Hask Hnk Hrivk_legacy sk w.akP w.nk w.rivk_ext) ∧
  (w.rivk = w.rivk_ext ∨ w.rivk = Hrivk_int w.rivk_ext (ak Extract w) w.nk)

end Derivation

section Full
variable [AddCommGroup G] [Field F] [Field B] [Module F G]

/-- The full key-binding condition: commitment opening (`KBOpening`) and derivation constraints
(`KBDerivation`). -/
def KB (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    (w : Witness G F B SK QK) : Prop :=
  KBOpening Extract S hfn w ∧ KBDerivation Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w

/-- A full key-binding break (ZIP 2005): two valid witnesses with equal `ivk` differing in some
component other than the y-sign of `ak^ℙ` (the projection uses `ak = Extract ak^ℙ`, quotienting the
sign). -/
def Break (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    (w₁ w₂ : Witness G F B SK QK) : Prop :=
  KB Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁ ∧
  KB Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₂ ∧
  w₁.ivk = w₂.ivk ∧
  (w₁.qk, w₁.sk, ak Extract w₁, w₁.nk, w₁.rivk) ≠ (w₂.qk, w₂.sk, ak Extract w₂, w₂.nk, w₂.rivk)

/-- `nk`-pinning (Balance's import): two valid witnesses with the same `ivk` that do **not** form a
key-binding break must share the same nullifier key `nk`. (The probability that a break *does* occur
is the Layer-C birthday bound.) -/
theorem nk_pinned (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w₁ w₂ : Witness G F B SK QK}
    (h₁ : KB Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁)
    (h₂ : KB Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₂)
    (hivk : w₁.ivk = w₂.ivk)
    (hnb : ¬ Break Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁ w₂) :
    w₁.nk = w₂.nk := by
  by_contra hne
  apply hnb
  refine ⟨h₁, h₂, hivk, fun heq => hne ?_⟩
  simpa using congrArg (fun t => t.2.2.2.1) heq

end Full

section Onward
variable [AddCommGroup G] [Field F] [Field B] [Module F G] [DecidableEq F]

/-- The final query of a witness: which final oracle produces its `rivk`, and at what input.
Selected by the external/internal ivk choice (`rivk = rivk_ext`?) and then the qk/sk branch. -/
def finalQueryOf (Extract : G → B) (w : Witness G F B SK QK) : FinalQuery QK SK B F :=
  if w.rivk = w.rivk_ext then
    match w.qk, w.sk with
    | some qk, _ => .ext qk (ak Extract w) w.nk
    | none, some sk => .legacy sk
    | none, none => .int w.rivk_ext (ak Extract w) w.nk
  else
    .int w.rivk_ext (ak Extract w) w.nk

omit [Field B] in
/-- **Final-random-oracle representation** (ZIP 2005 key-binding proof, "Final-random-oracle
structure"): under the derivation constraints, `rivk` is the output of the combined final oracle at
the witness's `finalQueryOf`. This is the deterministic bridge from the Pedersen-scalar collision
(`commitCollision`, over `G(w) = h(ak,nk) + rivk`) to a collision of the actual `H^*` random
oracles. The birthday bound over the final-query space, and the residual `x₁ = x₂` upstream-collision
sub-case, are the probabilistic Layer C. -/
theorem rivk_eq_finalOracle
    (Extract : G → B) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w : Witness G F B SK QK}
    (hd : KBDerivation Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w) :
    w.rivk = (finalQueryOf Extract w).eval Hrivk_legacy Hrivk_ext Hrivk_int := by
  obtain ⟨hxor, hqk, hsk, hrivk⟩ := hd
  unfold finalQueryOf
  by_cases hext : w.rivk = w.rivk_ext
  · rw [if_pos hext]
    rcases hq : w.qk with _ | qk
    · rcases hs : w.sk with _ | sk
      · simp [hq, hs] at hxor
      · simp only [FinalQuery.eval]
        obtain ⟨_, _, hrl⟩ := hsk sk hs
        rw [hext, hrl]
    · simp only [FinalQuery.eval]
      rw [hext, hqk qk hq]
  · rw [if_neg hext]
    simp only [FinalQuery.eval]
    exact hrivk.resolve_left hext

end Onward

section OnwardCollision
variable [AddCommGroup G] [Field F] [Field B] [Module F G] [NoZeroSMulDivisors F G] [DecidableEq F]

/-- **`H^*` ±-collision — the deterministic core of the birthday step.** Composing the
commitment-opening ±-collision (`openingBreak_scalar_pm`) with the final-oracle representation
(`rivk_eq_finalOracle`), an `OpeningBreak` whose witnesses both satisfy the derivation constraints
yields the ZIP 2005 break equation `G₁ = ±G₂` with the *Final-random-oracle structure* substituted:
writing `H^* q := (FinalQuery.eval …) q` for the combined final oracle and `qᵢ := finalQueryOf wᵢ`,
`h(ak₁,nk₁) + H^*(q₁) = ±(h(ak₂,nk₂) + H^*(q₂))`. Each side is thus an `H^*`-output offset by the
constant shift `h(akᵢ,nkᵢ)` (non-querying `h`, independent of `H^*`'s responses) — exactly the
quantity the birthday bound bounds. The distinctness of the final queries (`q₁ ≠ q₂`) and the
residual `x₁ = x₂` sub-cases are the probabilistic Layer C, *not* established here; that is why this
is the ±-equation rather than a full `CollisionUpToSign` (whose `ne` field is that very residual). -/
theorem openingBreak_finalOracle_pm
    (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (hExt : ∀ P Q : G, Extract P = Extract Q ↔ P = Q ∨ P = -Q) (hS : S ≠ 0)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w₁ w₂ : Witness G F B SK QK}
    (hbrk : OpeningBreak Extract S hfn w₁ w₂)
    (hd₁ : KBDerivation Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁)
    (hd₂ : KBDerivation Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₂) :
    hfn (ak Extract w₁) w₁.nk + (finalQueryOf Extract w₁).eval Hrivk_legacy Hrivk_ext Hrivk_int =
      hfn (ak Extract w₂) w₂.nk + (finalQueryOf Extract w₂).eval Hrivk_legacy Hrivk_ext Hrivk_int ∨
    hfn (ak Extract w₁) w₁.nk + (finalQueryOf Extract w₁).eval Hrivk_legacy Hrivk_ext Hrivk_int =
      -(hfn (ak Extract w₂) w₂.nk + (finalQueryOf Extract w₂).eval Hrivk_legacy Hrivk_ext Hrivk_int) := by
  have hpm := (openingBreak_scalar_pm Extract S hfn hExt hS hbrk).2
  rw [rivk_eq_finalOracle Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int hd₁,
      rivk_eq_finalOracle Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int hd₂] at hpm
  exact hpm

end OnwardCollision

end Zcash.Security.KeyBinding
