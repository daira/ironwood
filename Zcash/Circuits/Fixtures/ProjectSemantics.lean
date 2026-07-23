import Zcash.Circuits.Fixtures.Project

/-!
# The VK-match projection preserves evaluation

`projectCS` (`Fixtures/Project.lean`) is what the VK-match tests compare against
the Rust dumps: selector compression (`substSelectorMap`), then the query-index walk
that erases `Expression Fp Query` into the verifier's gate AST `Zcash.Snark.Expr`. The
tests establish *syntactic* equality with the dump; this module supplies the *semantic*
half the soundness bridge needs (the reusable VK-correctness step of the Action
integration roadmap):

* `substSelectorMap_eval` — compression is evaluation under a rewritten valuation: each
  selector reads its root-finding replacement instead (`substValuation`).
* `selReplacement_eval` and its corollaries — the replacement's value at a row is
  decided by the packed column: `0` where no member is active (`_of_zero`) or where
  another member's root is written (`_of_other`), nonzero at the selector's own root
  (`_of_root`). This is the algebra that turns "the compressed gate vanishes" into
  "the gated constraint vanishes" at enabled rows.
* `Expression.selectorFree` and `substSelectorMap_selectorFree` — compression under a
  total map leaves no selector atom, so the erasure's junk selector arm is unreachable.
* `eraseExpr_eval` — the query-walk erasure of a selector-free expression evaluates to
  the original, when the evaluation families interpret the walk's final query layout
  (`Interprets`).
* `eraseExpr_substSelectorMap_eval` — the composed per-gate step: the whole projection
  pipeline evaluates to the original Clean gate expression under the
  selector-replacement valuation.
-/

namespace Zcash.Circuits.Fixtures

open Halo2
open Zcash.Snark (Expr)

/-! ## Selector compression is evaluation under a rewritten valuation -/

/-- The valuation `substSelectorMap` simulates: selectors in the map read their
root-finding replacement, everything else reads `v`. -/
def substValuation (m : ℕ → Option SelCompress) (v : Query → Fp) : Query → Fp
  | .selector s => match m s.index with
      | some d => (selReplacement d).eval v
      | none => v (.selector s)
  | q => v q

/-- Selector compression preserves evaluation: the substituted expression at `v` is the
original at `substValuation m v`. -/
theorem substSelectorMap_eval (m : ℕ → Option SelCompress) (v : Query → Fp)
    (e : Expression Fp Query) :
    (substSelectorMap m e).eval v = e.eval (substValuation m v) := by
  induction e with
  | var q =>
      cases q with
      | selector s =>
          cases hm : m s.index with
          | some d => simp only [substSelectorMap, substValuation, hm, Expression.eval]
          | none => simp only [substSelectorMap, substValuation, hm, Expression.eval]
      | fixed c r => rfl
      | advice c r => rfl
      | «instance» c r => rfl
  | const c => rfl
  | add a b iha ihb => simp only [substSelectorMap, Expression.eval, iha, ihb]
  | mul a b iha ihb => simp only [substSelectorMap, Expression.eval, iha, ihb]

/-! ## The root-finding replacement's value

`selReplacement d` is `q · ∏_{i ∈ [1, len], i ≠ root} (i − q)` over the packed column's
query `q`. Keygen writes the active member's root into the packed cell (`0` where no
member is active), so the replacement is nonzero exactly at this selector's own enabled
rows. -/

/-- Closed form of the replacement's value: the packed query's value times the product of
`(i − q)` over the other members' roots. -/
theorem selReplacement_eval (d : SelCompress) (v : Query → Fp) :
    (selReplacement d).eval v
      = v (.fixed ⟨d.packedCol⟩ 0) *
        (((List.range d.combinationLen).filterMap (fun j =>
            if j + 1 = d.assignedRoot then none
            else some (((j + 1 : ℕ) : Fp) - v (.fixed ⟨d.packedCol⟩ 0)))).prod) := by
  have hfold : ∀ (fs : List (Expression Fp Query)) (acc : Expression Fp Query),
      (fs.foldl (· * ·) acc).eval v = acc.eval v * (fs.map (Expression.eval v)).prod := by
    intro fs
    induction fs with
    | nil => intro acc; simp
    | cons f fs ih =>
        intro acc
        rw [List.foldl_cons, ih (acc * f), List.map_cons, List.prod_cons,
          show ((acc * f).eval v) = acc.eval v * f.eval v from rfl]
        ring
  unfold selReplacement
  rw [hfold]
  congr 1
  rw [List.map_filterMap]
  congr 1
  refine List.filterMap_congr fun j _ => ?_
  by_cases hcase : j + 1 = d.assignedRoot
  · simp [hcase]
  · simp only [hcase, ite_false, Option.map_some]
    congr 1
    show (_ : Expression Fp Query).eval v = _
    simp only [Expression.eval, sub_eq_add_neg]
    ring

/-- Where no member of the combination is active the packed cell is `0`, and the
replacement vanishes. -/
theorem selReplacement_eval_of_zero (d : SelCompress) (v : Query → Fp)
    (hq : v (.fixed ⟨d.packedCol⟩ 0) = 0) : (selReplacement d).eval v = 0 := by
  rw [selReplacement_eval, hq, zero_mul]

/-- Where another member (root `i₀ ≠ assignedRoot`, `1 ≤ i₀ ≤ len`) is active, its factor
`(i₀ − q)` kills the replacement. -/
theorem selReplacement_eval_of_other (d : SelCompress) (v : Query → Fp)
    (i₀ : ℕ) (hq : v (.fixed ⟨d.packedCol⟩ 0) = (i₀ : Fp))
    (h1 : 1 ≤ i₀) (hlen : i₀ ≤ d.combinationLen) (hne : i₀ ≠ d.assignedRoot) :
    (selReplacement d).eval v = 0 := by
  rw [selReplacement_eval, hq]
  refine mul_eq_zero_of_right _ (List.prod_eq_zero ?_)
  rw [List.mem_filterMap]
  refine ⟨i₀ - 1, by rw [List.mem_range]; omega, ?_⟩
  have h : i₀ - 1 + 1 = i₀ := by omega
  rw [h, if_neg hne, sub_self]

/-- At the selector's own enabled rows the packed cell holds `assignedRoot`, and the
replacement is nonzero: the root itself is nonzero (`1 ≤ root < p`), and every other
member's factor `(i − root)` is a difference of distinct naturals below `p`. The bound
`combinationLen < p` is vacuously generous (`p ≈ 2²⁵⁴`, combinations are tiny). -/
theorem selReplacement_eval_of_root (d : SelCompress) (v : Query → Fp)
    (hq : v (.fixed ⟨d.packedCol⟩ 0) = (d.assignedRoot : Fp))
    (h1 : 1 ≤ d.assignedRoot) (hlen : d.assignedRoot ≤ d.combinationLen)
    (hp : d.combinationLen < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD) :
    (selReplacement d).eval v ≠ 0 := by
  rw [selReplacement_eval, hq]
  have hcast : ∀ i j : ℕ, i ≤ d.combinationLen → j ≤ d.combinationLen →
      (i : Fp) = (j : Fp) → i = j := by
    intro i j hi hj hij
    have := (ZMod.natCast_eq_natCast_iff' i j _).mp hij
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  refine mul_ne_zero ?_ ?_
  · intro h0
    have : d.assignedRoot = 0 := hcast _ 0 hlen (by omega) (by simpa using h0)
    omega
  · intro h0
    obtain ⟨x, hx, hx0⟩ := List.mem_filterMap.mp (List.prod_eq_zero_iff.mp h0)
    rw [List.mem_range] at hx
    by_cases hroot : x + 1 = d.assignedRoot
    · simp [hroot] at hx0
    · rw [if_neg hroot, Option.some_inj] at hx0
      rw [sub_eq_zero] at hx0
      exact hroot (hcast _ _ (by omega) hlen hx0)

/-! ## Selector-freeness

Post-compression expressions contain no selector atom: compression under a total map
replaces every one by its root-finding polynomial, whose atoms are a fixed query and
constants. `Expression.selectorFree` is the Boolean witness `eraseExpr_eval` consumes to
rule the erasure's junk selector arm unreachable. -/

/-- No `Query.selector` atom occurs in the expression. -/
def _root_.Halo2.Expression.selectorFree {F : Type} : Expression F Query → Bool
  | .var (.selector _) => false
  | .var _ => true
  | .const _ => true
  | .add a b => a.selectorFree && b.selectorFree
  | .mul a b => a.selectorFree && b.selectorFree

private theorem selectorFree_foldl_mul (fs : List (Expression Fp Query))
    (acc : Expression Fp Query) (hacc : acc.selectorFree = true)
    (hfs : ∀ f ∈ fs, f.selectorFree = true) :
    (fs.foldl (· * ·) acc).selectorFree = true := by
  induction fs generalizing acc with
  | nil => exact hacc
  | cons f fs ih =>
      rw [List.foldl_cons]
      refine ih (acc * f) ?_ (fun g hg => hfs g (List.mem_cons_of_mem f hg))
      show (Expression.mul acc f).selectorFree = true
      simp [Expression.selectorFree, hacc, hfs f (List.mem_cons_self ..)]

/-- The root-finding replacement's atoms are a fixed query and constants. -/
theorem selReplacement_selectorFree (d : SelCompress) :
    (selReplacement d).selectorFree = true := by
  unfold selReplacement
  refine selectorFree_foldl_mul _ _ rfl ?_
  intro f hf
  rw [List.mem_filterMap] at hf
  obtain ⟨j, _, hj⟩ := hf
  by_cases hcase : j + 1 = d.assignedRoot
  · simp [hcase] at hj
  · rw [if_neg hcase, Option.some_inj] at hj
    subst hj
    rfl

/-- Compression under a total map leaves no selector atom. -/
theorem substSelectorMap_selectorFree (m : ℕ → Option SelCompress)
    (hm : ∀ i, (m i).isSome) (e : Expression Fp Query) :
    (substSelectorMap m e).selectorFree = true := by
  induction e with
  | var q =>
      cases q with
      | selector sel =>
          cases hs : m sel.index with
          | some d =>
              simp only [substSelectorMap, hs]
              exact selReplacement_selectorFree d
          | none => exact absurd (hm sel.index) (by simp [hs])
      | fixed c r => rfl
      | advice c r => rfl
      | «instance» c r => rfl
  | const c => rfl
  | add a b iha ihb =>
      show (Expression.add _ _).selectorFree = true
      simp [Expression.selectorFree, iha, ihb]
  | mul a b iha ihb =>
      show (Expression.mul _ _).selectorFree = true
      simp [Expression.selectorFree, iha, ihb]

/-! ## The query walk interprets its own layout

`eraseExpr` threads a `QueryState`; the index it hands an atom refers to the layout the
walk *finishes* with (entries are only appended). `Interprets` says the evaluation
families read a layout correctly; `Extends` is the append-only ordering that carries
interpretation back to every intermediate state. -/

/-- `s'` extends `s`: every layout is a prefix. Walk steps only append. -/
def QueryState.Extends (s' s : QueryState) : Prop :=
  s.advice.toList <+: s'.advice.toList ∧ s.fixed.toList <+: s'.fixed.toList ∧
    s.inst.toList <+: s'.inst.toList

theorem QueryState.Extends.refl (s : QueryState) : s.Extends s :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩

/-- Transitivity, staged as `s₃ ⊒ s₂ ⊒ s₁ → s₃ ⊒ s₁`. -/
theorem QueryState.Extends.trans {s₁ s₂ s₃ : QueryState}
    (h₂₁ : s₂.Extends s₁) (h₃₂ : s₃.Extends s₂) : s₃.Extends s₁ :=
  ⟨h₂₁.1.trans h₃₂.1, h₂₁.2.1.trans h₃₂.2.1, h₂₁.2.2.trans h₃₂.2.2⟩

/-- The families `fE`/`aE`/`iE` interpret `s`'s query layouts against the valuation `v`:
index `i` of a layout reads the same value as its registered `(column, rotation)` query. -/
structure Interprets (s : QueryState) (fE aE iE : ℕ → Fp) (v : Query → Fp) : Prop where
  advice : ∀ (i c : ℕ) (r : ℤ), s.advice[i]? = some (c, r) → aE i = v (.advice ⟨c⟩ r)
  fixed : ∀ (i c : ℕ) (r : ℤ), s.fixed[i]? = some (c, r) → fE i = v (.fixed ⟨c⟩ r)
  inst : ∀ (i c : ℕ) (r : ℤ), s.inst[i]? = some (c, r) → iE i = v (.instance ⟨c⟩ r)

private theorem getElem?_of_prefix {l l' : List (ℕ × ℤ)} (h : l <+: l') {i : ℕ}
    {p : ℕ × ℤ} (hp : l[i]? = some p) : l'[i]? = some p := by
  obtain ⟨t, rfl⟩ := h
  have hlt : i < l.length := (List.getElem?_eq_some_iff.mp hp).1
  rwa [List.getElem?_append_left hlt]

/-- Interpretation restricts along `Extends`: prefixes agree entrywise. -/
theorem Interprets.mono {s s' : QueryState} {fE aE iE : ℕ → Fp} {v : Query → Fp}
    (hint : Interprets s' fE aE iE v) (hext : s'.Extends s) : Interprets s fE aE iE v where
  advice i c r h := hint.advice i c r (by
    rw [← Array.getElem?_toList] at h ⊢; exact getElem?_of_prefix hext.1 h)
  fixed i c r h := hint.fixed i c r (by
    rw [← Array.getElem?_toList] at h ⊢; exact getElem?_of_prefix hext.2.1 h)
  inst i c r h := hint.inst i c r (by
    rw [← Array.getElem?_toList] at h ⊢; exact getElem?_of_prefix hext.2.2 h)

/-! ### Registration correctness of the three index lookups -/

private theorem findQuery_spec {arr : Array (ℕ × ℤ)} {c : ℕ} {r : ℤ} {i : ℕ}
    (h : findQuery arr c r = some i) : arr[i]? = some (c, r) := by
  unfold findQuery at h
  obtain ⟨hlt, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
  obtain ⟨h1, h2⟩ := of_decide_eq_true hp
  rw [Array.getElem?_eq_some_iff]
  exact ⟨hlt, Prod.ext h1 h2⟩

private theorem advIdx_spec (s : QueryState) (c : ℕ) (r : ℤ) :
    ((s.advIdx c r).2).advice[(s.advIdx c r).1]? = some (c, r) := by
  unfold QueryState.advIdx
  cases hf : findQuery s.advice c r with
  | some i => simpa using findQuery_spec hf
  | none => simp

private theorem fixIdx_spec (s : QueryState) (c : ℕ) (r : ℤ) :
    ((s.fixIdx c r).2).fixed[(s.fixIdx c r).1]? = some (c, r) := by
  unfold QueryState.fixIdx
  cases hf : findQuery s.fixed c r with
  | some i => simpa using findQuery_spec hf
  | none => simp

private theorem instIdx_spec (s : QueryState) (c : ℕ) (r : ℤ) :
    ((s.instIdx c r).2).inst[(s.instIdx c r).1]? = some (c, r) := by
  unfold QueryState.instIdx
  cases hf : findQuery s.inst c r with
  | some i => simpa using findQuery_spec hf
  | none => simp

private theorem advIdx_extends (s : QueryState) (c : ℕ) (r : ℤ) :
    ((s.advIdx c r).2).Extends s := by
  unfold QueryState.advIdx
  cases findQuery s.advice c r with
  | some i => exact QueryState.Extends.refl s
  | none =>
      exact ⟨by simp only [Array.toList_push]; exact List.prefix_append _ _,
        List.prefix_refl _, List.prefix_refl _⟩

private theorem fixIdx_extends (s : QueryState) (c : ℕ) (r : ℤ) :
    ((s.fixIdx c r).2).Extends s := by
  unfold QueryState.fixIdx
  cases findQuery s.fixed c r with
  | some i => exact QueryState.Extends.refl s
  | none =>
      exact ⟨List.prefix_refl _,
        by simp only [Array.toList_push]; exact List.prefix_append _ _, List.prefix_refl _⟩

private theorem instIdx_extends (s : QueryState) (c : ℕ) (r : ℤ) :
    ((s.instIdx c r).2).Extends s := by
  unfold QueryState.instIdx
  cases findQuery s.inst c r with
  | some i => exact QueryState.Extends.refl s
  | none =>
      exact ⟨List.prefix_refl _, List.prefix_refl _,
        by simp only [Array.toList_push]; exact List.prefix_append _ _⟩

/-! ### Reduction helpers for the guarded `eraseExpr` arms

`eraseExpr`'s later `mul` arms only apply when the subterms do *not* match the earlier
arms; the functional-induction cases carry those guards as hypotheses, and these helpers
turn them into plain unfolding equations by splitting the guarded subterm's head. -/

private theorem eraseExpr_mulConstant (e : Expression Fp Query) (c : Fp) (s : QueryState)
    (he : ∀ c' : Fp, e = .const c' → False) :
    eraseExpr (.mul e (.mul (.const c) (.const 1))) s
      = ((eraseExpr e s).1.product (.constant c), (eraseExpr e s).2) := by
  cases e with
  | const c' => exact absurd rfl (he c')
  | var q => simp only [eraseExpr, if_true]
  | add a b => simp only [eraseExpr, if_true]
  | mul a b => simp only [eraseExpr, if_true]

private theorem eraseExpr_mul_const_mul_const_of_ne_one (e : Expression Fp Query) (c one : Fp)
    (s : QueryState) (he : ∀ c' : Fp, e = .const c' → False) (hone : ¬one = 1) :
    eraseExpr (.mul e (.mul (.const c) (.const one))) s
      = ((eraseExpr e s).1.product
          (eraseExpr (.mul (.const c) (.const one)) (eraseExpr e s).2).1,
         (eraseExpr (.mul (.const c) (.const one)) (eraseExpr e s).2).2) := by
  cases e with
  | const c' => exact absurd rfl (he c')
  | var q => simp only [eraseExpr, if_neg hone]
  | add a b => simp only [eraseExpr, if_neg hone]
  | mul a b => simp only [eraseExpr, if_neg hone]

private theorem eraseExpr_mul_const (e : Expression Fp Query) (c : Fp) (s : QueryState)
    (he : ∀ c' : Fp, e = .const c' → False) :
    eraseExpr (.mul e (.const c)) s
      = ((eraseExpr e s).1.scaled c, (eraseExpr e s).2) := by
  cases e with
  | const c' => exact absurd rfl (he c')
  | var q => simp only [eraseExpr]
  | add a b => simp only [eraseExpr]
  | mul a b => simp only [eraseExpr]

private theorem eraseExpr_mul (a b : Expression Fp Query) (s : QueryState)
    (ha : ∀ c : Fp, a = .const c → False)
    (hb1 : ∀ c one : Fp, b = .mul (.const c) (.const one) → False)
    (hb2 : ∀ c : Fp, b = .const c → False) :
    eraseExpr (.mul a b) s
      = ((eraseExpr a s).1.product (eraseExpr b (eraseExpr a s).2).1,
         (eraseExpr b (eraseExpr a s).2).2) := by
  cases a with
  | const c => exact absurd rfl (ha c)
  | var qa =>
      cases b with
      | const c => exact absurd rfl (hb2 c)
      | var qb => simp only [eraseExpr]
      | add x y => simp only [eraseExpr]
      | mul x y =>
          cases x with
          | const cx =>
              cases y with
              | const cy => exact absurd rfl (hb1 cx cy)
              | var q => simp only [eraseExpr]
              | add _ _ => simp only [eraseExpr]
              | mul _ _ => simp only [eraseExpr]
          | var q => simp only [eraseExpr]
          | add _ _ => simp only [eraseExpr]
          | mul _ _ => simp only [eraseExpr]
  | add xa ya =>
      cases b with
      | const c => exact absurd rfl (hb2 c)
      | var qb => simp only [eraseExpr]
      | add x y => simp only [eraseExpr]
      | mul x y =>
          cases x with
          | const cx =>
              cases y with
              | const cy => exact absurd rfl (hb1 cx cy)
              | var q => simp only [eraseExpr]
              | add _ _ => simp only [eraseExpr]
              | mul _ _ => simp only [eraseExpr]
          | var q => simp only [eraseExpr]
          | add _ _ => simp only [eraseExpr]
          | mul _ _ => simp only [eraseExpr]
  | mul xa ya =>
      cases b with
      | const c => exact absurd rfl (hb2 c)
      | var qb => simp only [eraseExpr]
      | add x y => simp only [eraseExpr]
      | mul x y =>
          cases x with
          | const cx =>
              cases y with
              | const cy => exact absurd rfl (hb1 cx cy)
              | var q => simp only [eraseExpr]
              | add _ _ => simp only [eraseExpr]
              | mul _ _ => simp only [eraseExpr]
          | var q => simp only [eraseExpr]
          | add _ _ => simp only [eraseExpr]
          | mul _ _ => simp only [eraseExpr]

/-- The walk only appends: `eraseExpr`'s output state extends its input state. -/
theorem eraseExpr_extends (e : Expression Fp Query) (s : QueryState) :
    ((eraseExpr e s).2).Extends s := by
  induction e, s using eraseExpr.induct with
  | case1 c s => exact QueryState.Extends.refl s
  | case2 sel s => exact QueryState.Extends.refl s
  | case3 col rot s i s₁ heq =>
      have := advIdx_extends s col.index rot
      simpa [eraseExpr, heq] using this
  | case4 col rot s i s₁ heq =>
      have := fixIdx_extends s col.index rot
      simpa [eraseExpr, heq] using this
  | case5 col rot s i s₁ heq =>
      have := instIdx_extends s col.index rot
      simpa [eraseExpr, heq] using this
  | case6 e s e' s₁ heq ih =>
      simpa only [eraseExpr, if_true, heq] using ih
  | case7 c e s hc e' s₁ heq ih =>
      simpa only [eraseExpr, if_neg hc, heq] using ih
  | case8 e c s he e' s₁ heq ih =>
      rw [eraseExpr_mulConstant e c s he]
      exact ih
  | case9 e c one s he hone e' s₁ heq e'' s₂ heq₂ ih₁ ih₂ =>
      rw [eraseExpr_mul_const_mul_const_of_ne_one e c one s he hone]
      simp only [heq] at ih₁ ⊢
      exact QueryState.Extends.trans ih₁ ih₂
  | case10 e c s he e' s₁ heq ih =>
      rw [eraseExpr_mul_const e c s he]
      exact ih
  | case11 a b s e' s₁ heq e'' s₂ heq₂ ih₁ ih₂ =>
      simp only [eraseExpr]
      simp only [heq] at ih₁ ⊢
      exact QueryState.Extends.trans ih₁ ih₂
  | case12 a b s ha hb1 hb2 e' s₁ heq e'' s₂ heq₂ ih₁ ih₂ =>
      rw [eraseExpr_mul a b s ha hb1 hb2]
      simp only [heq] at ih₁ ⊢
      exact QueryState.Extends.trans ih₁ ih₂

/-- **Erasure preserves evaluation.** If the evaluation families interpret the layout of
any state extending the walk's output — in practice the whole-circuit walk's final state
— then the erased selector-free expression evaluates to the original at `v`. Stepped
through by the walk's own case split; the `Interprets`/`Extends` bookkeeping is what
lets sibling subexpressions share one final layout. -/
theorem eraseExpr_eval (fE aE iE : ℕ → Fp) (v : Query → Fp)
    (e : Expression Fp Query) (s sfin : QueryState)
    (hfree : e.selectorFree = true)
    (hext : sfin.Extends (eraseExpr e s).2)
    (hint : Interprets sfin fE aE iE v) :
    Expr.eval fE aE iE (eraseExpr e s).1 = e.eval v := by
  induction e, s using eraseExpr.induct with
  | case1 c s => rfl
  | case2 sel s => simp [Expression.selectorFree] at hfree
  | case3 col rot s i s₁ heq =>
      show Expr.eval fE aE iE (.advice (s.advIdx col.index rot).1)
        = v (.advice col rot)
      have hspec := advIdx_spec s col.index rot
      have := (hint.mono (by simpa [eraseExpr, heq] using hext)).advice
        (s.advIdx col.index rot).1 col.index rot (by rw [heq] at hspec ⊢; exact hspec)
      simpa using this
  | case4 col rot s i s₁ heq =>
      show Expr.eval fE aE iE (.fixed (s.fixIdx col.index rot).1)
        = v (.fixed col rot)
      have hspec := fixIdx_spec s col.index rot
      have := (hint.mono (by simpa [eraseExpr, heq] using hext)).fixed
        (s.fixIdx col.index rot).1 col.index rot (by rw [heq] at hspec ⊢; exact hspec)
      simpa using this
  | case5 col rot s i s₁ heq =>
      show Expr.eval fE aE iE (.instance (s.instIdx col.index rot).1)
        = v (.instance col rot)
      have hspec := instIdx_spec s col.index rot
      have := (hint.mono (by simpa [eraseExpr, heq] using hext)).inst
        (s.instIdx col.index rot).1 col.index rot (by rw [heq] at hspec ⊢; exact hspec)
      simpa using this
  | case6 e s e' s₁ heq ih =>
      simp only [eraseExpr, if_true] at hext ⊢
      simp only [Expression.selectorFree, Bool.true_and] at hfree
      rw [Expr.eval, ih hfree hext,
        show (Expression.mul (.const (-1)) e).eval v = -1 * e.eval v from rfl]
      ring
  | case7 c e s hc e' s₁ heq ih =>
      simp only [eraseExpr, if_neg hc] at hext ⊢
      simp only [Expression.selectorFree, Bool.true_and] at hfree
      rw [Expr.eval, Expr.eval, ih hfree hext]
      rfl
  | case8 e c s he e' s₁ heq ih =>
      rw [eraseExpr_mulConstant e c s he] at hext ⊢
      simp only [Expression.selectorFree, Bool.and_true] at hfree
      rw [Expr.eval, Expr.eval, ih hfree hext,
        show (Expression.mul e (.mul (.const c) (.const 1))).eval v
          = e.eval v * (c * 1) from rfl]
      ring
  | case9 e c one s he hone e' s₁ heq e'' s₂ heq₂ ih₁ ih₂ =>
      rw [eraseExpr_mul_const_mul_const_of_ne_one e c one s he hone] at hext ⊢
      simp only [heq] at hext ih₁ ⊢
      simp only [Expression.selectorFree, Bool.and_true] at hfree
      simp only [Expr.eval]
      rw [ih₁ hfree (QueryState.Extends.trans (eraseExpr_extends _ _) hext),
        ih₂ rfl hext]
      rfl
  | case10 e c s he e' s₁ heq ih =>
      rw [eraseExpr_mul_const e c s he] at hext ⊢
      simp only [Expression.selectorFree, Bool.and_true] at hfree
      rw [Expr.eval, ih hfree hext]
      rfl
  | case11 a b s e' s₁ heq e'' s₂ heq₂ ih₁ ih₂ =>
      simp only [eraseExpr] at hext ⊢
      simp only [heq] at hext ih₁ ⊢
      simp only [Expression.selectorFree, Bool.and_eq_true] at hfree
      simp only [Expr.eval]
      rw [ih₁ hfree.1 (QueryState.Extends.trans (eraseExpr_extends _ _) hext),
        ih₂ hfree.2 hext]
      rfl
  | case12 a b s ha hb1 hb2 e' s₁ heq e'' s₂ heq₂ ih₁ ih₂ =>
      rw [eraseExpr_mul a b s ha hb1 hb2] at hext ⊢
      simp only [heq] at hext ih₁ ⊢
      simp only [Expression.selectorFree, Bool.and_eq_true] at hfree
      simp only [Expr.eval]
      rw [ih₁ hfree.1 (QueryState.Extends.trans (eraseExpr_extends _ _) hext),
        ih₂ hfree.2 hext]
      rfl

/-! ## The composed per-gate step -/

/-- **The whole projection preserves evaluation**: compress, erase, then evaluate at
families interpreting the walk's layout — the result is the original gate expression at
the selector-replacement valuation. Composition of `eraseExpr_eval` with
`substSelectorMap_eval`; one application per gate polynomial per row is the gate
portion of the Clean-constraints transport. -/
theorem eraseExpr_substSelectorMap_eval (m : ℕ → Option SelCompress)
    (hm : ∀ i, (m i).isSome) (fE aE iE : ℕ → Fp) (v : Query → Fp)
    (p : Expression Fp Query) (s sfin : QueryState)
    (hext : sfin.Extends (eraseExpr (substSelectorMap m p) s).2)
    (hint : Interprets sfin fE aE iE v) :
    Expr.eval fE aE iE (eraseExpr (substSelectorMap m p) s).1
      = p.eval (substValuation m v) := by
  rw [eraseExpr_eval fE aE iE v _ s sfin (substSelectorMap_selectorFree m hm p) hext hint,
    substSelectorMap_eval]

end Zcash.Circuits.Fixtures
