import Mathlib
import Zcash.Security.Common.RandomOracle

/-!
# Key binding (Orchard / Ironwood)

The deterministic layer of the
[ZIP 2005 key-binding theorem (ROM)](https://zips.z.cash/zip-2005#thm-key-binding-rom): a
verifying Recovery-Statement witness pins the key components — `ak` up to y-sign, `nk`, and the
`qk`/`sk` branch with its key — to `ivk`, unless an explicit break event is computed.

The route, each step proven here:

1. `commit_scalar_pm` — two openings of one `Commitivk` value force their Pedersen scalars equal
   or negated; `CollisionUpToSign.ofOpeningBreak` packages this as computed data.
2. `rivk_eq_finalOracle` — under the derivation constraints, `rivk` is the combined final
   oracle's output at the witness's decoded query.
3. `CollisionUpToSign.ofBreak` — a full `Break` computes a ±-collision of the shifted combined
   oracle at distinct queries; `residual_of_finalQuery_eq` handles coinciding queries.
4. `nk_pinned` / `ak_pinned` / `qk_or_sk_pinned` — without a break, the components agree
   (Balance's and Spend Authorization's imports).

The probabilistic side — producing the computed collision is hard — is the birthday bound
`ε_kb ≤ q(q-1)/r` (`Birthday.lean`). `PRF^nf`-pinning, Spendability's import, is not here yet.

Abstract setting: a prime-order group `G` as an `F`-vector space (`F = ZMod r` the scalar field),
a base field `B` (x-coordinates, `= ZMod q`), and `Extract : G → B` with the ±-property (`hExt`).
`Commitivk` is required to have the Pedersen structure (not opaque), which is what makes the break
reduction provable; no Pallas instantiation is included (the intended concrete route is via
CompElliptic).
-/

namespace Zcash.Security.KeyBinding

open Zcash.Security.RandomOracle

/-- Which key material backs a witness: the `qk`-branch (`use_qsk = true`) or the `sk`-branch
(`use_qsk = false`). A witness carries exactly one of `qk` or `sk`. -/
inductive Branch (QK SK : Type*) where
  /-- qk-branch: `rivk_ext` derives via `Hrivk_ext`. -/
  | qk : QK → Branch QK SK
  /-- sk-branch: the keys derive via `BindKeys^sk`. -/
  | sk : SK → Branch QK SK
  deriving DecidableEq

/-- A Recovery-Statement / Orchard key witness (ZIP 2005 §"key binding"). `use_qsk` is encoded by
the `qk_or_sk` constructor. The internal-vs-external `ivk` choice is encoded by `rivk`'s value,
not a tag (see `finalQueryOf`). -/
structure Witness (G F B SK QK : Type*) where
  ivk      : B
  qk_or_sk : Branch QK SK
  akP      : G
  nk       : B
  rivk_ext : F
  rivk     : F

variable {G F B SK QK : Type*}

/-- The Pedersen-scalar map a `Commitivk` opening reduces to: `(ak, nk, rivk) ↦ h ak nk + rivk`.
An `OpeningBreak` is exhibited as a `CollisionUpToSign` of this map by
`CollisionUpToSign.ofOpeningBreak`. -/
def pedersenScalar [Add F] (hfn : B → B → F) (t : B × B × F) : F :=
  let (ak, nk, rivk) := t
  hfn ak nk + rivk

/-- The "final input" to the final `rivk`-derivation random oracle (ZIP 2005 key-binding proof):
the query at which `rivk` is that oracle's output, selected by the `qk`/`sk` branch and the
external/internal ivk choice. -/
inductive FinalQuery (QK SK B F : Type*) where
  /-- qk-branch, external ivk: `rivk = Hrivk_ext qk ak nk`. -/
  | ext : QK → B → B → FinalQuery QK SK B F
  /-- sk-branch, external ivk: `rivk = Hrivk_legacy sk`. -/
  | legacy : SK → FinalQuery QK SK B F
  /-- internal ivk: `rivk = Hrivk_int rivk_ext ak nk`. -/
  | int : F → B → B → FinalQuery QK SK B F
  deriving DecidableEq

/-- The combined final `rivk`-derivation random oracle: dispatch each final query to its oracle. -/
def FinalQuery.eval (Hrivk_legacy : SK → F) (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F) :
    FinalQuery QK SK B F → F
  | .ext qk ak nk => Hrivk_ext qk ak nk
  | .legacy sk => Hrivk_legacy sk
  | .int rivk_ext ak nk => Hrivk_int rivk_ext ak nk

section Algebra
variable [AddCommGroup G] [Field F] [Field B] [Module F G] [NoZeroSMulDivisors F G]

/-- The `ivk` commitment as a Pedersen lift:
`Commitivk rivk ak nk = Extract ((h ak nk + rivk) • S)`, with `h` abstract-but-non-querying and `S`
a fixed base. Mirrors the `NoteCommit` repair `(H^rcm + f) • R`. -/
def Commitivk (Extract : G → B) (S : G) (hfn : B → B → F) (rivk : F) (ak nk : B) : B :=
  Extract ((hfn ak nk + rivk) • S)

omit [Field B] in
/-- Algebraic core: two openings of the same `Commitivk` value force their Pedersen scalars to be
equal or negatives — the deterministic content the whole key-binding reduction rests on. Proved
from the `Extract` ±-property and injectivity of `· • S` for `S ≠ 0` (`smul_left_injective`;
`G` is an `F`-vector space). -/
theorem commit_scalar_pm
    (Extract : G → B) (S : G) (hfn : B → B → F)
    (hExt : ∀ P Q : G, Extract P = Extract Q ↔ P =± Q) (hS : S ≠ 0)
    {rivk₁ rivk₂ : F} {ak₁ nk₁ ak₂ nk₂ : B}
    (hcm : Commitivk Extract S hfn rivk₁ ak₁ nk₁ = Commitivk Extract S hfn rivk₂ ak₂ nk₂) :
    hfn ak₁ nk₁ + rivk₁ =± hfn ak₂ nk₂ + rivk₂ := by
  unfold Commitivk at hcm
  rw [hExt] at hcm
  rcases hcm with hcm | hcm
  · exact Or.inl (smul_left_injective F hS hcm)
  · refine Or.inr (smul_left_injective F hS ?_)
    show (hfn ak₁ nk₁ + rivk₁) • S = (-(hfn ak₂ nk₂ + rivk₂)) • S
    rw [neg_smul]
    exact hcm

/-- `KBOpening` — the commitment-opening core of the key-binding condition (what statement-validity
yields). -/
structure KBOpening (Extract : G → B) (S : G) (hfn : B → B → F)
    (w : Witness G F B SK QK) : Prop where
  /-- `ivk` opens as `Commitivk` at `(rivk, ak, nk)`. -/
  commit : w.ivk = Commitivk Extract S hfn w.rivk (Extract w.akP) w.nk
  /-- `ivk ≠ 0`. -/
  nonzero : w.ivk ≠ 0

/-- `OpeningBreak` — a `Commitivk`-opening collision (produced by the games layer): two valid
`KBOpening` witnesses with the same `ivk` but differing `(ak, nk, rivk)`. -/
structure OpeningBreak (Extract : G → B) (S : G) (hfn : B → B → F)
    (w₁ w₂ : Witness G F B SK QK) : Prop where
  opening₁ : KBOpening Extract S hfn w₁
  opening₂ : KBOpening Extract S hfn w₂
  ivk_eq : w₁.ivk = w₂.ivk
  /-- The witnesses differ in the opening data. -/
  proj_ne : (Extract w₁.akP, w₁.nk, w₁.rivk) ≠ (Extract w₂.akP, w₂.nk, w₂.rivk)

/-- The deterministic reduction (composable core), as computed data: an `OpeningBreak` exhibits a
±-collision of the Pedersen-scalar map `pedersenScalar hfn`. The colliding queries are the two
`(ak, nk, rivk)` triples read off the witnesses; the break's distinctness and `commit_scalar_pm`
supply the erased `Prop` fields, so the data is genuinely computed, not extracted from a proof.

This is an intermediate certificate, not a break event: `pedersenScalar` is affine in `rivk`, so a
standalone inhabitant is computable outright. The security content is conditional on the
`OpeningBreak` hypothesis; hardness enters per-instantiation, where `rivk` is an `H^*` output
(`KBDerivation`) and the birthday bound applies. -/
def _root_.Zcash.Security.RandomOracle.CollisionUpToSign.ofOpeningBreak
    (Extract : G → B) (S : G) (hfn : B → B → F)
    (hExt : ∀ P Q : G, Extract P = Extract Q ↔ P =± Q) (hS : S ≠ 0)
    {w₁ w₂ : Witness G F B SK QK} (hbrk : OpeningBreak Extract S hfn w₁ w₂) :
    RandomOracle.CollisionUpToSign (pedersenScalar hfn) where
  q₁ := (Extract w₁.akP, w₁.nk, w₁.rivk)
  q₂ := (Extract w₂.akP, w₂.nk, w₂.rivk)
  ne := hbrk.proj_ne
  pm := by
    -- Commitivk(w₁) = w₁.ivk = w₂.ivk = Commitivk(w₂)
    simpa [pedersenScalar] using
      commit_scalar_pm Extract S hfn hExt hS
        (hbrk.opening₁.commit.symm.trans (hbrk.ivk_eq.trans hbrk.opening₂.commit))

end Algebra

section Derivation
variable [AddCommGroup G] [Field F] [Field B] [Module F G]

/-- `BindKeys^sk` (ZIP 2005): the `sk`-branch derivation constraints. -/
structure BindKeysSk (Ggen : G) (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (sk : SK) (akP : G) (nk : B) (rivk_ext : F) : Prop where
  akP_eq : akP = (Hask sk) • Ggen
  nk_eq : nk = Hnk sk
  rivk_ext_eq : rivk_ext = Hrivk_legacy sk

/-- `KBDerivation` — the ZIP 2005 derivation constraints (the `qk_or_sk` branch structure is
enforced by the `Branch` type). -/
structure KBDerivation (Extract : G → B) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    (w : Witness G F B SK QK) : Prop where
  /-- The per-branch constraint: `Hrivk_ext` on the qk-branch, `BindKeys^sk` on the sk-branch. -/
  branch : match w.qk_or_sk with
    | .qk qk => w.rivk_ext = Hrivk_ext qk (Extract w.akP) w.nk
    | .sk sk => BindKeysSk Ggen Hask Hnk Hrivk_legacy sk w.akP w.nk w.rivk_ext
  /-- `rivk ∈ {rivk_ext, Hrivk_int ...}`. -/
  rivk_choice : w.rivk = w.rivk_ext ∨ w.rivk = Hrivk_int w.rivk_ext (Extract w.akP) w.nk

end Derivation

section Full
variable [AddCommGroup G] [Field F] [Field B] [Module F G]

/-- The full key-binding condition: commitment opening and key derivation constraints. -/
structure KB (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    (w : Witness G F B SK QK) : Prop where
  opening : KBOpening Extract S hfn w
  derivation : KBDerivation Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w

/-- The break projection of a witness: the components a key-binding break must differ in. Using
`ak = Extract ak^ℙ` quotients the y-sign of `ak^ℙ`. -/
structure BreakProj (QK SK B F : Type*) where
  qk_or_sk : Branch QK SK
  ak : B
  nk : B
  rivk : F

/-- The break projection, read off a witness. -/
def Witness.breakProj (Extract : G → B) (w : Witness G F B SK QK) : BreakProj QK SK B F :=
  ⟨w.qk_or_sk, Extract w.akP, w.nk, w.rivk⟩

/-- A full key-binding break (ZIP 2005): two valid witnesses with equal `ivk` and differing
break projections. -/
structure Break (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    (w₁ w₂ : Witness G F B SK QK) : Prop where
  kb₁ : KB Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁
  kb₂ : KB Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₂
  ivk_eq : w₁.ivk = w₂.ivk
  /-- The witnesses differ in the break projection. -/
  proj_ne : w₁.breakProj Extract ≠ w₂.breakProj Extract

/-- `nk`-pinning (Balance's import): two valid witnesses with the same `ivk` that do **not** form a
key-binding break must share the same nullifier key `nk`. (The probability that a break *does* occur
is the birthday bound.) -/
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
  exact congrArg BreakProj.nk heq

/-- `ak`-pinning up to y-sign (Spend Authorization's import): two valid witnesses with the same `ivk`
that do *not* form a key-binding break share the same `ak = Extract ak^ℙ` — i.e. `ak^ℙ` is pinned up
to its y-sign, matching the protocol's choice to consume `ak` as a single x-coordinate. -/
theorem ak_pinned (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w₁ w₂ : Witness G F B SK QK}
    (h₁ : KB Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁)
    (h₂ : KB Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₂)
    (hivk : w₁.ivk = w₂.ivk)
    (hnb : ¬ Break Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁ w₂) :
    Extract w₁.akP = Extract w₂.akP := by
  by_contra hne
  apply hnb
  refine ⟨h₁, h₂, hivk, fun heq => hne ?_⟩
  exact congrArg BreakProj.ak heq

/-- `qk`/`sk`-pinning (Spend Authorization's import): two valid witnesses with the same `ivk` that do
*not* form a key-binding break share the same branch — the same `qk` or the same `sk`, including
*which* of the two backs the witness. This is stronger than ZIP 2005's former "`qk` determined by
`ivk` when `qk ≠ ⊥`". -/
theorem qk_or_sk_pinned (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w₁ w₂ : Witness G F B SK QK}
    (h₁ : KB Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁)
    (h₂ : KB Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₂)
    (hivk : w₁.ivk = w₂.ivk)
    (hnb : ¬ Break Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁ w₂) :
    w₁.qk_or_sk = w₂.qk_or_sk := by
  by_contra hne
  apply hnb
  refine ⟨h₁, h₂, hivk, fun heq => hne ?_⟩
  exact congrArg BreakProj.qk_or_sk heq

end Full

section Onward
variable [AddCommGroup G] [Field F] [Field B] [Module F G] [DecidableEq F]

/-- The `rivk_ext`-derivation query of a witness: the query at which the combined final oracle
produces its `rivk_ext`, selected by the branch. Never `.int` (`extQueryOf_ne_int`). -/
def extQueryOf (Extract : G → B) (w : Witness G F B SK QK) : FinalQuery QK SK B F :=
  match w.qk_or_sk with
  | .qk qk => .ext qk (Extract w.akP) w.nk
  | .sk sk => .legacy sk

/-- The final query of a witness: which final oracle produces its `rivk`, and at what input.
Selected by the external/internal ivk choice (`rivk = rivk_ext`?) and then the branch.
The external/internal choice is decoded from the fields, not carried as witness data: at a
fixpoint `Hrivk_int rivk_ext ak nk = rivk_ext`, an internally-derived witness decodes as
external — harmless for `rivk_eq_finalOracle` (which holds either way), but the birthday
accounting must partition query pairs by this decode, not by how the witnesses were
derived. -/
def finalQueryOf (Extract : G → B) (w : Witness G F B SK QK) : FinalQuery QK SK B F :=
  if w.rivk = w.rivk_ext then extQueryOf Extract w
  else .int w.rivk_ext (Extract w.akP) w.nk

omit [Field B] in
/-- **Final-random-oracle representation** (ZIP 2005 key-binding proof, "Final-random-oracle
structure"): under the derivation constraints, `rivk` is the output of the combined final oracle at
the witness's `finalQueryOf`. It bridges the Pedersen-scalar collision
(`CollisionUpToSign.ofOpeningBreak`) to a collision of the actual `H^*` oracles. What remains
probabilistic is only the birthday bound over the final-query space. -/
theorem rivk_eq_finalOracle
    (Extract : G → B) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w : Witness G F B SK QK}
    (hd : KBDerivation Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w) :
    w.rivk = (finalQueryOf Extract w).eval Hrivk_legacy Hrivk_ext Hrivk_int := by
  obtain ⟨hbc, hrivk⟩ := hd
  unfold finalQueryOf extQueryOf
  by_cases hext : w.rivk = w.rivk_ext
  · rw [if_pos hext]
    rcases hb : w.qk_or_sk with qk | sk <;> simp only [hb] at hbc ⊢ <;> simp only [FinalQuery.eval]
    · rw [hext, hbc]
    · rw [hext, hbc.rivk_ext_eq]
  · rw [if_neg hext]
    simp only [FinalQuery.eval]
    exact hrivk.resolve_left hext

/-- The non-querying shift: `hfn` at the query's key data (for `.legacy sk`, `ak`/`nk` are
recovered via `Hask`/`Hnk`, so the shift is a function of the query alone). -/
def shiftOf (Extract : G → B) (Ggen : G) (hfn : B → B → F) (Hask : SK → F) (Hnk : SK → B) :
    FinalQuery QK SK B F → F
  | .ext _ ak nk => hfn ak nk
  | .legacy sk => hfn (Extract ((Hask sk) • Ggen)) (Hnk sk)
  | .int _ ak nk => hfn ak nk

/-- The *shifted* combined final oracle: the `H^*` output offset by the non-querying shift.
The ±-collision a `Break` computes (`CollisionUpToSign.ofBreak`) is of this map — the event
the birthday layer bounds. -/
def shiftedFinalOracle (Extract : G → B) (Ggen : G) (hfn : B → B → F)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    (q : FinalQuery QK SK B F) : F :=
  shiftOf Extract Ggen hfn Hask Hnk q + q.eval Hrivk_legacy Hrivk_ext Hrivk_int

omit [Field B] in
/-- On a witness's `finalQueryOf`, the shifted oracle is the shift plus the `H^*` output — the form
`sameIvk_finalOracle_pm`'s equation is stated in. -/
theorem shiftedFinalOracle_finalQueryOf
    (Extract : G → B) (Ggen : G) (hfn : B → B → F)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w : Witness G F B SK QK}
    (hd : KBDerivation Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w) :
    shiftedFinalOracle Extract Ggen hfn Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int
        (finalQueryOf Extract w)
      = hfn (Extract w.akP) w.nk
          + (finalQueryOf Extract w).eval Hrivk_legacy Hrivk_ext Hrivk_int := by
  obtain ⟨hbc, hrivk⟩ := hd
  unfold finalQueryOf extQueryOf
  by_cases hext : w.rivk = w.rivk_ext
  · rw [if_pos hext]
    rcases hb : w.qk_or_sk with qk | sk <;> simp only [hb] at hbc ⊢
    · simp only [shiftedFinalOracle, shiftOf, FinalQuery.eval]
    · obtain ⟨hakP, hnk, _⟩ := hbc
      simp only [shiftedFinalOracle, shiftOf, FinalQuery.eval, ← hakP, ← hnk]
  · rw [if_neg hext]
    simp only [shiftedFinalOracle, shiftOf, FinalQuery.eval]

end Onward

section OnwardCollision
variable [AddCommGroup G] [Field F] [Field B] [Module F G] [NoZeroSMulDivisors F G] [DecidableEq F]

/-- **Same-`ivk` ±-equation over `H^*`.** Two witnesses opening the same `ivk` (`KBOpening`), both
satisfying the derivation constraints, give the ZIP 2005 break equation with the final-oracle
structure substituted: `h(ak₁,nk₁) + H^*(q₁) = ±(h(ak₂,nk₂) + H^*(q₂))`, where `H^*` is the
combined final oracle (`FinalQuery.eval`) and `qᵢ = finalQueryOf wᵢ`.

No distinctness is needed: the ±-equation holds for *every* same-`ivk` pair, and only the break
notions (`OpeningBreak`, `Break`) carry a distinctness witness. That is why this is a bare
equation rather than a full `CollisionUpToSign`; the `ne` field arrives with
`CollisionUpToSign.ofBreak`'s case split. -/
theorem sameIvk_finalOracle_pm
    (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (hExt : ∀ P Q : G, Extract P = Extract Q ↔ P =± Q) (hS : S ≠ 0)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w₁ w₂ : Witness G F B SK QK}
    (hop₁ : KBOpening Extract S hfn w₁) (hop₂ : KBOpening Extract S hfn w₂)
    (hivk : w₁.ivk = w₂.ivk)
    (hd₁ : KBDerivation Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁)
    (hd₂ : KBDerivation Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₂) :
    hfn (Extract w₁.akP) w₁.nk + (finalQueryOf Extract w₁).eval Hrivk_legacy Hrivk_ext Hrivk_int
      =± hfn (Extract w₂.akP) w₂.nk + (finalQueryOf Extract w₂).eval Hrivk_legacy Hrivk_ext Hrivk_int := by
  have hcm : Commitivk Extract S hfn w₁.rivk (Extract w₁.akP) w₁.nk
      = Commitivk Extract S hfn w₂.rivk (Extract w₂.akP) w₂.nk :=
    hop₁.commit.symm.trans (hivk.trans hop₂.commit)
  have hpm := commit_scalar_pm Extract S hfn hExt hS hcm
  rw [rivk_eq_finalOracle Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int hd₁,
      rivk_eq_finalOracle Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int hd₂] at hpm
  exact hpm

/-- The `H^*` ±-equation from an `OpeningBreak` (the object the games produce): the same-`ivk`
core `sameIvk_finalOracle_pm` applied to the break's two openings. -/
theorem openingBreak_finalOracle_pm
    (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (hExt : ∀ P Q : G, Extract P = Extract Q ↔ P =± Q) (hS : S ≠ 0)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w₁ w₂ : Witness G F B SK QK}
    (hbrk : OpeningBreak Extract S hfn w₁ w₂)
    (hd₁ : KBDerivation Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁)
    (hd₂ : KBDerivation Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₂) :
    hfn (Extract w₁.akP) w₁.nk + (finalQueryOf Extract w₁).eval Hrivk_legacy Hrivk_ext Hrivk_int
      =± hfn (Extract w₂.akP) w₂.nk + (finalQueryOf Extract w₂).eval Hrivk_legacy Hrivk_ext Hrivk_int :=
  sameIvk_finalOracle_pm Extract S hfn Ggen hExt hS Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int
    hbrk.opening₁ hbrk.opening₂ hbrk.ivk_eq hd₁ hd₂

/-- The `H^*` ±-equation from a full key-binding `Break` (break projections differing). The
derivation constraints are already inside the `Break` (via `KB`), and *no* `Break → OpeningBreak`
upgrade is needed: the equation depends only on the openings and `ivk`-equality, never on how the
projections differ. `CollisionUpToSign.ofBreak` builds its case split on this. -/
theorem break_finalOracle_pm
    (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (hExt : ∀ P Q : G, Extract P = Extract Q ↔ P =± Q) (hS : S ≠ 0)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w₁ w₂ : Witness G F B SK QK}
    (hbrk : Break Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁ w₂) :
    hfn (Extract w₁.akP) w₁.nk + (finalQueryOf Extract w₁).eval Hrivk_legacy Hrivk_ext Hrivk_int
      =± hfn (Extract w₂.akP) w₂.nk + (finalQueryOf Extract w₂).eval Hrivk_legacy Hrivk_ext Hrivk_int :=
  sameIvk_finalOracle_pm Extract S hfn Ggen hExt hS Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int
    hbrk.kb₁.opening hbrk.kb₂.opening hbrk.ivk_eq hbrk.kb₁.derivation hbrk.kb₂.derivation

/-- The break projection an *externally-decoded* witness must have, read off its
`rivk_ext`-derivation query (`proj_eq_projOfQuery`); `.int` is not in `extQueryOf`'s image. -/
def projOfQuery (Extract : G → B) (Ggen : G) (Hask : SK → F) (Hnk : SK → B)
    (Hrivk_legacy : SK → F) (Hrivk_ext : QK → B → B → F) :
    FinalQuery QK SK B F → Option (BreakProj QK SK B F)
  | .ext qk ak nk => some ⟨.qk qk, ak, nk, Hrivk_ext qk ak nk⟩
  | .legacy sk => some ⟨.sk sk, Extract ((Hask sk) • Ggen), Hnk sk, Hrivk_legacy sk⟩
  | .int _ _ _ => none

/-- The Branch data of a witness, read off its `rivk_ext`-derivation query
(`branch_eq_branchOfQuery`); `.int` is not in `extQueryOf`'s image. -/
def branchOfQuery : FinalQuery QK SK B F → Option (Branch QK SK)
  | .ext qk _ _ => some (.qk qk)
  | .legacy sk => some (.sk sk)
  | .int _ _ _ => none

omit [AddCommGroup G] [Field F] [Field B] [NoZeroSMulDivisors F G] [DecidableEq F] in
/-- A witness's Branch data is recoverable from its `rivk_ext`-derivation query. -/
theorem branch_eq_branchOfQuery {w : Witness G F B SK QK} (Extract : G → B) :
    some w.qk_or_sk = branchOfQuery (extQueryOf Extract w) := by
  rcases hb : w.qk_or_sk with qk | sk <;> simp [extQueryOf, branchOfQuery, hb]

omit [AddCommGroup G] [Field F] [Field B] [NoZeroSMulDivisors F G] [DecidableEq F] in
/-- A witness's `rivk_ext`-derivation query is never `.int`. -/
theorem extQueryOf_ne_int {w : Witness G F B SK QK} (Extract : G → B) (rivk_ext : F) (ak nk : B) :
    extQueryOf Extract w ≠ .int rivk_ext ak nk := by
  rcases hb : w.qk_or_sk with qk | sk <;> simp [extQueryOf, hb]

omit [Field B] [NoZeroSMulDivisors F G] [DecidableEq F] in
/-- An externally-decoded witness's break projection is recoverable from its `rivk_ext`-derivation
query: the derivation constraints determine every component from the query. -/
theorem proj_eq_projOfQuery
    (Extract : G → B) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w : Witness G F B SK QK}
    (hd : KBDerivation Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w)
    (hext : w.rivk = w.rivk_ext) :
    some (w.breakProj Extract)
      = projOfQuery Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext (extQueryOf Extract w) := by
  obtain ⟨hbc, _⟩ := hd
  rcases hb : w.qk_or_sk with qk | sk <;> simp only [Witness.breakProj, hb] at hbc ⊢ <;>
    simp only [extQueryOf, hb, projOfQuery]
  · rw [hext.trans hbc]
  · obtain ⟨hakP, hnk, hre⟩ := hbc
    rw [hakP, hnk, hext.trans hre]

omit [Field B] [NoZeroSMulDivisors F G] [DecidableEq F] in
/-- A witness's shifted-oracle output at its `rivk_ext`-derivation query is
`hfn (ak, nk) + rivk_ext`: the derivation constraints collapse the per-branch shift to the
witness's own key data. -/
theorem shiftedFinalOracle_extQueryOf
    (Extract : G → B) (Ggen : G) (hfn : B → B → F)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w : Witness G F B SK QK}
    (hd : KBDerivation Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w) :
    shiftedFinalOracle Extract Ggen hfn Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int
        (extQueryOf Extract w)
      = hfn (Extract w.akP) w.nk + w.rivk_ext := by
  obtain ⟨hbc, _⟩ := hd
  rcases hb : w.qk_or_sk with qk | sk <;> simp only [hb] at hbc <;>
    simp only [extQueryOf, hb, shiftedFinalOracle, shiftOf, FinalQuery.eval]
  · rw [← hbc]
  · obtain ⟨hakP, hnk, hre⟩ := hbc
    rw [← hakP, ← hnk, ← hre]

omit [NoZeroSMulDivisors F G] in
/-- **The residual case is deterministic**: if a `Break`'s two final queries coincide, then both
witnesses are internally derived, sharing `(ak, nk, rivk_ext, rivk)` and differing in `qk_or_sk`.
The collision then relocates to the `rivk_ext`-derivation queries, at which the shifted oracle's
outputs are *equal* and the queries are *distinct*. -/
theorem residual_of_finalQuery_eq
    (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w₁ w₂ : Witness G F B SK QK}
    (hbrk : Break Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁ w₂)
    (hq : finalQueryOf Extract w₁ = finalQueryOf Extract w₂) :
    extQueryOf Extract w₁ ≠ extQueryOf Extract w₂ ∧
    shiftedFinalOracle Extract Ggen hfn Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int
        (extQueryOf Extract w₁)
      = shiftedFinalOracle Extract Ggen hfn Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int
        (extQueryOf Extract w₂) := by
  obtain ⟨⟨hop₁, hd₁⟩, ⟨hop₂, hd₂⟩, hivk, hne5⟩ := hbrk
  unfold finalQueryOf at hq
  by_cases hext₁ : w₁.rivk = w₁.rivk_ext
  · rw [if_pos hext₁] at hq
    by_cases hext₂ : w₂.rivk = w₂.rivk_ext
    · -- external × external: the projections coincide, contradicting the break's distinctness
      rw [if_pos hext₂] at hq
      exact absurd (Option.some_inj.mp
        (((proj_eq_projOfQuery Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int
            hd₁ hext₁).trans (by rw [hq])).trans
          (proj_eq_projOfQuery Extract Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int
            hd₂ hext₂).symm)) hne5
    · -- external × internal: constructor clash
      rw [if_neg hext₂] at hq
      exact absurd hq (extQueryOf_ne_int Extract _ _ _)
  · rw [if_neg hext₁] at hq
    by_cases hext₂ : w₂.rivk = w₂.rivk_ext
    · -- internal × external: constructor clash
      rw [if_pos hext₂] at hq
      exact absurd hq.symm (extQueryOf_ne_int Extract _ _ _)
    · -- internal × internal: the genuine residual
      rw [if_neg hext₂] at hq
      simp only [FinalQuery.int.injEq] at hq
      obtain ⟨hre, hak, hnk⟩ := hq
      have hrv : w₁.rivk = w₂.rivk := by
        rw [hd₁.rivk_choice.resolve_left hext₁, hd₂.rivk_choice.resolve_left hext₂, hre, hak,
          hnk]
      refine ⟨fun h => hne5 ?_, ?_⟩
      · -- equal `extQueryOf`s would equate qk_or_sk, hence the whole projections
        have hbr : w₁.qk_or_sk = w₂.qk_or_sk :=
          Option.some_inj.mp ((branch_eq_branchOfQuery (w := w₁) Extract).trans
            ((congrArg branchOfQuery h).trans (branch_eq_branchOfQuery (w := w₂) Extract).symm))
        simp only [Witness.breakProj]
        rw [hbr, hak, hnk, hrv]
      · rw [shiftedFinalOracle_extQueryOf Extract Ggen hfn Hask Hnk Hrivk_legacy Hrivk_ext
            Hrivk_int hd₁,
          shiftedFinalOracle_extQueryOf Extract Ggen hfn Hask Hnk Hrivk_legacy Hrivk_ext
            Hrivk_int hd₂, hak, hnk, hre]

/-- **The ZIP 2005 break event, as a computed random-oracle ±-collision** — the terminal object of
the deterministic layer. A full key-binding `Break` computes a `CollisionUpToSign` of the shifted
combined final oracle at *distinct* queries: the two witnesses' final queries when they differ, or
(the residual case, `residual_of_finalQuery_eq`) the two `rivk_ext`-derivation queries when they
coincide. What the birthday bound then adds is that inhabiting this event is hard: `hfn` is
non-querying, so a fixed shift cannot be steered to manufacture collisions, and ±-colliding the
shifted oracle at distinct queries has probability at most `q(q-1)/r` (`Birthday.lean`). -/
def _root_.Zcash.Security.RandomOracle.CollisionUpToSign.ofBreak
    [DecidableEq QK] [DecidableEq SK] [DecidableEq B]
    (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (hExt : ∀ P Q : G, Extract P = Extract Q ↔ P =± Q) (hS : S ≠ 0)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    {w₁ w₂ : Witness G F B SK QK}
    (hbrk : Break Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁ w₂) :
    RandomOracle.CollisionUpToSign
      (shiftedFinalOracle Extract Ggen hfn Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int
        (QK := QK) (SK := SK)) :=
  if hq : finalQueryOf Extract w₁ = finalQueryOf Extract w₂ then
    { q₁ := extQueryOf Extract w₁
      q₂ := extQueryOf Extract w₂
      ne := (residual_of_finalQuery_eq Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext
        Hrivk_int hbrk hq).1
      pm := Or.inl (residual_of_finalQuery_eq Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext
        Hrivk_int hbrk hq).2 }
  else
    { q₁ := finalQueryOf Extract w₁
      q₂ := finalQueryOf Extract w₂
      ne := hq
      pm := by
        rw [shiftedFinalOracle_finalQueryOf Extract Ggen hfn Hask Hnk Hrivk_legacy Hrivk_ext
              Hrivk_int hbrk.kb₁.derivation,
            shiftedFinalOracle_finalQueryOf Extract Ggen hfn Hask Hnk Hrivk_legacy Hrivk_ext
              Hrivk_int hbrk.kb₂.derivation]
        exact break_finalOracle_pm Extract S hfn Ggen hExt hS Hask Hnk Hrivk_legacy Hrivk_ext
          Hrivk_int hbrk }

omit [Field B] [NoZeroSMulDivisors F G] in
/-- **The bridge to the birthday counting**: the pair of `H^*` outputs at a shifted-oracle
±-collision's queries lies in the shifted ±-collision set that
`Birthday.card_shifted_pm_collision_le` counts, with the shifts read off the queries. Combined
with the collision's `ne` field (distinct queries) this is the per-pair event whose fraction the
birthday layer bounds by `2/|F|`. -/
theorem collision_mem_shifted_pm [Fintype F]
    (Extract : G → B) (Ggen : G) (hfn : B → B → F)
    (Hask : SK → F) (Hnk : SK → B) (Hrivk_legacy : SK → F)
    (Hrivk_ext : QK → B → B → F) (Hrivk_int : F → B → B → F)
    (c : RandomOracle.CollisionUpToSign
      (shiftedFinalOracle Extract Ggen hfn Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int
        (QK := QK) (SK := SK))) :
    (c.q₁.eval Hrivk_legacy Hrivk_ext Hrivk_int, c.q₂.eval Hrivk_legacy Hrivk_ext Hrivk_int)
      ∈ Finset.univ.filter (fun p : F × F =>
          shiftOf Extract Ggen hfn Hask Hnk c.q₁ + p.1
            =± shiftOf Extract Ggen hfn Hask Hnk c.q₂ + p.2) := by
  simpa [shiftedFinalOracle] using c.pm

end OnwardCollision

end Zcash.Security.KeyBinding
