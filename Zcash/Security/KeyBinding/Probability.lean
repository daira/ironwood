import Zcash.Security.KeyBinding.Basic
import Zcash.Security.Common.Birthday
import Zcash.Snark.Soundness.Forking.Probability

/-!
# Key binding in the whole-table random-oracle model (Layer C)

The deterministic key-binding layer ends at a computed event: `CollisionUpToSign.ofBreak` turns
any key-binding `Break` into a ±-collision of the shifted combined final oracle at two distinct
queries, and `collision_mem_shifted_pm` places its output pair in the set `Birthday.lean` counts.
This module adds the probabilistic model that turns those counting facts into a probability
bound.

The model samples the combined final `rivk`-derivation oracle `H^*` as one uniform table
`O : FinalQuery QK SK B F → F`. A uniform table is the same as independent uniform outputs at
every query — the product structure of the uniform measure. (In Markov-category terms `PMF` is a
commutative monad, so samples reorder freely; see Fritz [eprint arXiv:1908.07021] and
`Mathlib.CategoryTheory.MarkovCategory` for the abstract setting.) The three constituent oracles
are the table's restrictions along the `FinalQuery` constructors (`FinalQuery.eval_restrict`).

The remaining data (`Extract`, the bases, `hfn`, `Hask`, `Hnk`) are fixed parameters. The shift
`shiftOf` reads only the query and these parameters, never the sampled table — so a shifted read
of the table at distinct queries is still a uniform pair. (The shift is a deterministic, a.k.a.
copy-preserving, map in the Markov-category sense.) The pair and union lemmas below are stated
for an arbitrary finite query domain and arbitrary shift function, for reuse by the Spendability
`H^rcm` collision.

Results (milestone 1 — a *static* query set, fixed before the table is sampled):

* `pair_shifted_collision_measure_le` — a shifted ±-collision at one distinct query pair has
  probability at most `2/|F|`.
* `finset_shifted_collision_measure_le` — union bound over the `C(q,2)` unordered pairs of a
  query set of size at most `q`: probability at most `q·(q−1)/|F|`.
* `break_measure_le` — the key-binding capstone: an adversary whose witnesses' derivation
  queries land in the static set produces a `Break` with probability at most `q·(q−1)/|F|`
  (ZIP 2005's `ε_kb` at `|F| = r`).

The more realistic adaptive attack model —a bounded-query machine choosing queries after seeing
earlier answers— is the next milestone (issue #68). The fresh-read conditioning it needs is in
`Snark.Soundness.Forking.Probability`, which this module already imports for the uniform-table
lemmas.
-/

namespace Zcash.Security.KeyBinding

open Finset Zcash.Security.RandomOracle Zcash.Security.Birthday Zcash.Snark
open scoped ENNReal

variable {G F B SK QK : Type*}

/-! ## Finiteness of the query space -/

/-- `FinalQuery` as the sum of its constructors' data. -/
def finalQueryEquiv : FinalQuery QK SK B F ≃ (QK × B × B) ⊕ SK ⊕ (F × B × B) where
  toFun
    | .ext qk ak nk => .inl (qk, ak, nk)
    | .legacy sk => .inr (.inl sk)
    | .int rivk_ext ak nk => .inr (.inr (rivk_ext, ak, nk))
  invFun
    | .inl (qk, ak, nk) => .ext qk ak nk
    | .inr (.inl sk) => .legacy sk
    | .inr (.inr (rivk_ext, ak, nk)) => .int rivk_ext ak nk
  left_inv q := by cases q <;> rfl
  right_inv x := by rcases x with ⟨qk, ak, nk⟩ | sk | ⟨rivk_ext, ak, nk⟩ <;> rfl

instance [Fintype QK] [Fintype SK] [Fintype B] [Fintype F] :
    Fintype (FinalQuery QK SK B F) :=
  Fintype.ofEquiv _ finalQueryEquiv.symm

/-- Assembling the combined final oracle from a table's constructor restrictions gives back the
table. -/
theorem eval_restrict (O : FinalQuery QK SK B F → F) :
    FinalQuery.eval (fun sk => O (.legacy sk)) (fun qk ak nk => O (.ext qk ak nk))
      (fun rivk_ext ak nk => O (.int rivk_ext ak nk)) = O := by
  funext q; cases q <;> rfl

/-! ## The per-pair and union bounds, over an arbitrary finite query domain -/

section Generic

variable {Q : Type*} [Fintype Q] [DecidableEq Q] [Field F] [Fintype F] [DecidableEq F]

/-- **Non-adaptive per-pair bound.** For distinct queries `a ≠ b` and any shift `s` fixed
independently of the table, a uniform table's shifted outputs at `a` and `b` ±-collide with
probability at most `2/|F|`: the pair read is uniform on `F × F`
(`uniformOfFintype_map_precomp_injective`), and the shifted collision set has at most
`2·|F|` elements (`card_shifted_pm_collision_le`). -/
theorem pair_shifted_collision_measure_le (s : Q → F) {a b : Q} (hne : a ≠ b) :
    (PMF.uniformOfFintype (Q → F)).toOuterMeasure
        {O : Q → F | s a + O a =± s b + O b}
      ≤ 2 / Fintype.card F := by
  have hφ : Function.Injective (![a, b] : Fin 2 → Q) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hpre : {O : Q → F | s a + O a =± s b + O b}
      = (fun O : Q → F => (piFinTwoEquiv fun _ => F) (O ∘ ![a, b])) ⁻¹'
          {p : F × F | s a + p.1 =± s b + p.2} := rfl
  rw [hpre, ← PMF.toOuterMeasure_map_apply]
  have hmap : (PMF.uniformOfFintype (Q → F)).map
        (fun O : Q → F => (piFinTwoEquiv fun _ => F) (O ∘ ![a, b]))
      = PMF.uniformOfFintype (F × F) := by
    rw [show (fun O : Q → F => (piFinTwoEquiv fun _ => F) (O ∘ ![a, b]))
          = ⇑(piFinTwoEquiv fun _ => F) ∘ (fun O : Q → F => O ∘ ![a, b]) from rfl,
      ← PMF.map_comp, uniformOfFintype_map_precomp_injective _ hφ,
      map_uniformOfFintype_equiv]
  rw [hmap, uniformOfFintype_toOuterMeasure_set]
  have hcard : Nat.card {p : F × F | s a + p.1 =± s b + p.2} ≤ 2 * Fintype.card F := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    exact card_shifted_pm_collision_le (s a) (s b)
  calc (Nat.card {p : F × F | s a + p.1 =± s b + p.2} : ℝ≥0∞) / Fintype.card (F × F)
      ≤ (2 * Fintype.card F : ℕ) / Fintype.card (F × F) := by
        gcongr
    _ = 2 / Fintype.card F := by
        rw [Fintype.card_prod]
        push_cast
        rw [ENNReal.mul_div_mul_right _ _ (by exact_mod_cast Fintype.card_pos.ne')
          (ENNReal.natCast_ne_top _)]

/-- **Non-adaptive union bound.** A query set of size at most `q`, fixed before the table is
sampled, contains a shifted ±-colliding pair with probability at most `q·(q−1)/|F|`: sum the
per-pair bound over the `C(q,2)` unordered pairs (`Finset.powersetCard 2`). -/
theorem finset_shifted_collision_measure_le (s : Q → F) (Qs : Finset Q) {q : ℕ}
    (hq : Qs.card ≤ q) :
    (PMF.uniformOfFintype (Q → F)).toOuterMeasure
        {O : Q → F | ∃ a ∈ Qs, ∃ b ∈ Qs, a ≠ b ∧ s a + O a =± s b + O b}
      ≤ (q * (q - 1) : ℕ) / Fintype.card F := by
  have hsymm : ∀ x y : F, x =± y → y =± x := fun x y h =>
    h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (by rw [h, neg_neg]))
  have hcover : {O : Q → F | ∃ a ∈ Qs, ∃ b ∈ Qs, a ≠ b ∧ s a + O a =± s b + O b}
      ⊆ ⋃ t : ↥(Qs.powersetCard 2),
          {O : Q → F | ∃ a ∈ t.1, ∃ b ∈ t.1, a ≠ b ∧ s a + O a =± s b + O b} := by
    rintro O ⟨a, ha, b, hb, hab, hpm⟩
    refine Set.mem_iUnion.2 ⟨⟨{a, b}, Finset.mem_powersetCard.2 ⟨?_, Finset.card_pair hab⟩⟩,
      ⟨a, ?_, b, ?_, hab, hpm⟩⟩
    · exact Finset.insert_subset ha (Finset.singleton_subset_iff.2 hb)
    · simp
    · simp
  have hpair : ∀ t : ↥(Qs.powersetCard 2),
      (PMF.uniformOfFintype (Q → F)).toOuterMeasure
          {O : Q → F | ∃ a ∈ t.1, ∃ b ∈ t.1, a ≠ b ∧ s a + O a =± s b + O b}
        ≤ 2 / Fintype.card F := by
    rintro ⟨t, ht⟩
    obtain ⟨-, hcard⟩ := Finset.mem_powersetCard.1 ht
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hcard
    refine le_trans (MeasureTheory.measure_mono ?_) (pair_shifted_collision_measure_le s hab)
    rintro O ⟨x, hx, y, hy, hxy, hpm⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hpm
    · exact hsymm _ _ hpm
    · exact absurd rfl hxy
  have hdvd : 2 ∣ q * (q - 1) := by
    rcases q with _ | m
    · simp
    · simpa [Nat.succ_sub_one, mul_comm] using (Nat.even_mul_succ_self m).two_dvd
  have h2 : q * (q - 1) = q.choose 2 * 2 := by
    rw [Nat.choose_two_right, Nat.div_mul_cancel hdvd]
  calc (PMF.uniformOfFintype (Q → F)).toOuterMeasure
        {O : Q → F | ∃ a ∈ Qs, ∃ b ∈ Qs, a ≠ b ∧ s a + O a =± s b + O b}
      ≤ (PMF.uniformOfFintype (Q → F)).toOuterMeasure
          (⋃ t : ↥(Qs.powersetCard 2),
            {O : Q → F | ∃ a ∈ t.1, ∃ b ∈ t.1, a ≠ b ∧ s a + O a =± s b + O b}) :=
        MeasureTheory.measure_mono hcover
    _ ≤ ∑' t : ↥(Qs.powersetCard 2), (PMF.uniformOfFintype (Q → F)).toOuterMeasure
          {O : Q → F | ∃ a ∈ t.1, ∃ b ∈ t.1, a ≠ b ∧ s a + O a =± s b + O b} :=
        MeasureTheory.measure_iUnion_le _
    _ ≤ ∑' _t : ↥(Qs.powersetCard 2), (2 / Fintype.card F : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum hpair
    _ = ((Qs.powersetCard 2).card : ℝ≥0∞) * (2 / Fintype.card F) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ (q.choose 2 : ℝ≥0∞) * (2 / Fintype.card F) := by
        gcongr
        rw [Finset.card_powersetCard]
        exact_mod_cast Nat.choose_le_choose 2 hq
    _ = (q * (q - 1) : ℕ) / Fintype.card F := by
        rw [h2]
        push_cast
        rw [mul_div_assoc]

end Generic

/-! ## The key-binding capstone -/

section Capstone

variable [AddCommGroup G] [Field F] [Field B] [Module F G] [NoZeroSMulDivisors F G]
variable [Fintype QK] [Fintype SK] [Fintype B] [Fintype F]
variable [DecidableEq QK] [DecidableEq SK] [DecidableEq B] [DecidableEq F]

omit [Fintype QK] [Fintype SK] [Fintype B] [Fintype F] in
/-- The queries at which `CollisionUpToSign.ofBreak` exhibits its collision are the witnesses'
derivation queries: the `rivk_ext`-derivation pair in the residual case, the final-query pair
otherwise. Stated over any `c` equal to the computed collision (`hc`), so that a consumer's
`set c := CollisionUpToSign.ofBreak ... with hc` supplies `hc` directly. -/
theorem ofBreak_queries {Extract : G → B} {S : G} {hfn : B → B → F} {Ggen : G}
    {hExt : ∀ P R : G, Extract P = Extract R ↔ P =± R} {hS : S ≠ 0}
    {Hask : SK → F} {Hnk : SK → B} {Hrivk_legacy : SK → F}
    {Hrivk_ext : QK → B → B → F} {Hrivk_int : F → B → B → F}
    {w₁ w₂ : Witness G F B SK QK}
    {hbrk : Break Extract S hfn Ggen Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int w₁ w₂}
    {c : RandomOracle.CollisionUpToSign
      (shiftedFinalOracle Extract Ggen hfn Hask Hnk Hrivk_legacy Hrivk_ext Hrivk_int
        (QK := QK) (SK := SK))}
    (hc : c = CollisionUpToSign.ofBreak Extract S hfn Ggen hExt hS Hask Hnk Hrivk_legacy
      Hrivk_ext Hrivk_int hbrk) :
    (c.q₁ = extQueryOf Extract w₁ ∧ c.q₂ = extQueryOf Extract w₂) ∨
      (c.q₁ = finalQueryOf Extract w₁ ∧ c.q₂ = finalQueryOf Extract w₂) := by
  subst hc
  unfold CollisionUpToSign.ofBreak
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- **Non-adaptive key-binding birthday bound.** Sample the combined final oracle as a uniform
table. An adversary —here, any pair of witness choices depending on the whole table— whose
witnesses' derivation queries lie in a set `Qs` of at most `q` queries *fixed in advance*,
produces a key-binding `Break` with probability at most `q·(q−1)/|F|`. This is ZIP 2005's
`ε_kb` at `|F| = r`. -/
theorem break_measure_le (Extract : G → B) (S : G) (hfn : B → B → F) (Ggen : G)
    (hExt : ∀ P R : G, Extract P = Extract R ↔ P =± R) (hS : S ≠ 0)
    (Hask : SK → F) (Hnk : SK → B)
    (w₁ w₂ : (FinalQuery QK SK B F → F) → Witness G F B SK QK)
    (Qs : Finset (FinalQuery QK SK B F)) {q : ℕ} (hq : Qs.card ≤ q)
    (hqueries : ∀ O, finalQueryOf Extract (w₁ O) ∈ Qs ∧ finalQueryOf Extract (w₂ O) ∈ Qs ∧
      extQueryOf Extract (w₁ O) ∈ Qs ∧ extQueryOf Extract (w₂ O) ∈ Qs) :
    (PMF.uniformOfFintype (FinalQuery QK SK B F → F)).toOuterMeasure
        {O : FinalQuery QK SK B F → F |
          Break Extract S hfn Ggen Hask Hnk
            (fun sk => O (.legacy sk)) (fun qk ak nk => O (.ext qk ak nk))
            (fun rivk_ext ak nk => O (.int rivk_ext ak nk)) (w₁ O) (w₂ O)}
      ≤ (q * (q - 1) : ℕ) / Fintype.card F := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (finset_shifted_collision_measure_le (shiftOf Extract Ggen hfn Hask Hnk) Qs hq)
  intro O hO
  obtain ⟨hf₁, hf₂, he₁, he₂⟩ := hqueries O
  set c := CollisionUpToSign.ofBreak Extract S hfn Ggen hExt hS Hask Hnk _ _ _ hO with hc
  have hq12 := ofBreak_queries hc
  have hpm : shiftOf Extract Ggen hfn Hask Hnk c.q₁ + O c.q₁
      =± shiftOf Extract Ggen hfn Hask Hnk c.q₂ + O c.q₂ := by
    have hp := c.pm
    simpa only [shiftedFinalOracle, eval_restrict] using hp
  refine ⟨c.q₁, ?_, c.q₂, ?_, c.ne, hpm⟩
  · rcases hq12 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> assumption
  · rcases hq12 with ⟨-, h2⟩ | ⟨-, h2⟩ <;> rw [h2] <;> assumption

end Capstone

end Zcash.Security.KeyBinding
