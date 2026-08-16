import Zcash.Common.Oracle.MultiOracleComp
import Zcash.Security.GroupHash.Indiff

/-!
# Two-oracle → one-oracle collapse

The full group-hash indifferentiability game gives the distinguisher two oracles:
a `hash_to_field` oracle returning pairs `(u₀, u₁) : F × F`, and the group hash
`H` returning group elements. In both worlds `H`'s answer is a deterministic
function of the pair at the same message — `H(m) = f u₀ + f u₁`, real by
construction and ideal because the simulator draws the pair from the fibre of
its target (`mem_fibre_self`). So the hash oracle carries nothing that the
pair oracle does not, and the two-oracle game collapses computably to the
one-oracle `IndiffFromRO`.

The collapse is `mapQuery` on the distinguisher: every hash query is
reimplemented as a pair query followed by `hashFromPair`. `mapQuery` lands in a
single-oracle `MultiOracleComp`, which `toOracleComp` carries to the plain
`OracleComp` that `IndiffFromRO` is stated over; `queryBound_mapQuery` folds the
hash budget onto the pair oracle. Fresh per-node sampling answers *distinct*
messages independently, as a random oracle does, so the theorem is stated for
deduplicated distinguishers (`dedup`): a distinguisher that queries the same
message on both oracles must reuse the one pair answer, which `dedup` enforces.

`M` is the message domain; the distinguisher is the query tree itself.
-/

namespace Zcash.Security.GroupHash

open scoped ENNReal
open Zcash.Common

variable {M : Type}
variable {F : Type} {G : Type} [AddCommGroup G]

/-- The two oracles of the full game: `pair` is `hash_to_field`, `hash` is the
group hash. -/
inductive TwoOracle
  | pair
  | hash
  deriving DecidableEq, Fintype

/-- Each oracle's answer type: pairs in `F × F` for `pair`, group elements in
`G` for `hash`. -/
def TwoOracle.answer (F G : Type) : TwoOracle → Type
  | .pair => F × F
  | .hash => G

/-- The two-oracle interface: a pair oracle (`.pair`, answering in `F × F`) and
a hash oracle (`.hash`, answering in `G`), both keyed by messages. -/
def twoSpec (M F G : Type) : OracleSpec TwoOracle :=
  ⟨fun _ => M, TwoOracle.answer F G⟩

/-- The single pair oracle that the two-oracle game collapses onto. -/
def oneSpec (M R : Type*) : OracleSpec Unit := ⟨fun _ => M, fun _ => R⟩

/-- Derive each oracle's answer from one pair answer: the pair oracle returns it
unchanged; the hash oracle returns `f u₀ + f u₁`. -/
def hashFromPair (f : F → G) : ∀ i : TwoOracle, (F × F) → i.answer F G
  | .pair => id
  | .hash => fun p => f p.1 + f p.2

/-- Collapse the hash oracle onto the pair oracle by `mapQuery`. -/
def collapseMap (f : F → G) {α : Type*}
    (B : MultiOracleComp (twoSpec M F G) α) : MultiOracleComp (oneSpec M (F × F)) α :=
  MultiOracleComp.mapQuery (spec := twoSpec M F G) (spec' := oneSpec M (F × F))
    (fun _ => ()) (fun _ => id) (hashFromPair f) B

/-- Bridge a single-oracle `MultiOracleComp` to the plain `OracleComp`. -/
def toOracleComp {R : Type*} {α : Type*} :
    MultiOracleComp (oneSpec M R) α → OracleComp M R α
  | .pure a => .pure a
  | .query _ t k => .query t (fun r => toOracleComp (k r))

/-- The full collapse: a two-oracle distinguisher becomes a pair-only
`OracleComp`, with the hash oracle reimplemented as a pair query plus
`hashFromPair`. -/
def collapse (f : F → G) {α : Type*}
    (B : MultiOracleComp (twoSpec M F G) α) : OracleComp M (F × F) α :=
  toOracleComp (collapseMap f B)

/-- `toOracleComp` transports the single-oracle budget. -/
theorem queryBound_toOracleComp {R α : Type*} {c : MultiOracleComp (oneSpec M R) α}
    {Q : Unit → ℕ} (h : c.QueryBound Q) : (toOracleComp c).QueryBound (Q ()) := by
  induction h with
  | pure a Q => exact .pure a (Q ())
  | @query i t k Q hk ih =>
      cases i
      simp only [toOracleComp, Function.update_self]
      exact .query ih

/-- The collapsed pair-only distinguisher makes at most `Q .pair + Q .hash`
queries — the hash budget folds onto the pair oracle. -/
theorem collapse_queryBound (f : F → G) {α : Type*}
    {B : MultiOracleComp (twoSpec M F G) α} {Q : TwoOracle → ℕ} (hB : B.QueryBound Q) :
    (collapse f B).QueryBound (Q .pair + Q .hash) :=
  queryBound_toOracleComp (MultiOracleComp.queryBound_mapQuery
    (spec := twoSpec M F G) (spec' := oneSpec M (F × F))
    (fun _ => ()) (fun _ => id) (hashFromPair f) hB)

/-- **Two-oracle indifferentiability from the one-oracle bound.** A deduplicated
two-oracle distinguisher with per-oracle budget `Q` distinguishes the real and
ideal worlds by at most `δ`, whenever the one-oracle `IndiffFromRO` holds at the
folded budget `Q .pair + Q .hash`. Both worlds derive the hash answer from the
pair at the same message, so the hash oracle is eliminated by the collapse. -/
theorem twoOracleIndiffFromRO [DecidableEq M] [Fintype F] [DecidableEq F] [Nonempty F]
    [Fintype G] [DecidableEq G] [Nonempty G] (f : F → G) {Q : TwoOracle → ℕ} {δ : ℝ≥0∞}
    (hIndiff : IndiffFromRO f (Q .pair + Q .hash) δ)
    {B : MultiOracleComp (twoSpec M F G) Bool} (hB : B.QueryBound Q) :
    PMFEventBiasLE (((collapse f B).dedup []).runFreshPMF (PMF.uniformOfFintype (F × F)))
        (((collapse f B).dedup []).runFreshPMF (idealLaw f)) δ
      ∧ PMFEventBiasLE (((collapse f B).dedup []).runFreshPMF (idealLaw f))
        (((collapse f B).dedup []).runFreshPMF (PMF.uniformOfFintype (F × F))) δ :=
  hIndiff ((collapse f B).dedup [])
    (OracleComp.dedup_queryBound (collapse_queryBound f hB) [])

end Zcash.Security.GroupHash
