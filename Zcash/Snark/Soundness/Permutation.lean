import Mathlib
import Zcash.Snark.Soundness.GrandProduct

/-!
# Permutation argument soundness

(Towards #14.) The [permutation argument](https://zcash.github.io/halo2/design/proving-system/permutation.html)
proves the copy constraints: cells in the same cycle of the permutation `σ` hold equal values.

Its soundness relies on the grand-product → multiset-of-pairs kernel (`GrandProduct.lean`, `prod_pair_inj`,
giving `{(value c, label c)} = {(value c, label (σ c))}`), and also on the **structural step** proved here,
which turns that multiset identity into the per-cell relation `value c = value (σ c)`.

Here `label c` is the cell's name `δ^j·ω^i` and `σ` is the permutation built from the cycles of
copy-constrained cells. Name distinctness — δ-coset disjointness in the keygen — is exactly the
injectivity of `label` that this step relies on. We do not prove here that the `δ^j·ω^i` encoding
preserves distinctness.

The per-cell relation `value c = value (σ c)` (invariance under *one* step of `σ`) is then lifted to
the full copy-constraint statement — *all cells in a cycle of `σ` are equal* — by
`value_const_on_sameCycle`, which iterates the one-step invariance over the whole orbit.

This file provides `perm_values_eq_iff` (the structural step) and `value_const_on_sameCycle` (the lift
to cycles), composed in `perm_copy_constraints`: from the multiset-of-pairs identity, with `label`
injective, cells in the same σ-cycle hold equal values. What remains for full soundness is the
grand-product ⟹ multiset identity (telescoping the running product over the usable rows, with the
boundary / blinding-row rules) feeding the `h` hypothesis, and the final assembly.
-/

namespace Zcash.Snark

open Finset

/-- Mapping a permutation over the universal multiset leaves it unchanged (`σ` is a bijection of the
index type, so it just reindexes `univ`). -/
theorem univ_val_map_perm {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) :
    Finset.univ.val.map (⇑σ) = Finset.univ.val := by
  simp

/-- **Structural step for the permutation argument.** Cells `ι` carry a `value` and an injective name
`label`. The multiset of `(value, label)` pairs is unchanged by permuting the labels through `σ` if and
only if `value` is constant on each σ-cycle (`value c = value (σ c)` for all `c`) — i.e. the copy
constraints hold.

The grand-product kernel (`prod_pair_inj`) delivers the multiset equality on the left; `label`
injectivity (δ-coset name distinctness) is what turns it into the per-cell relation. This is the
permutation analogue of `Lookup.run_structure`.

* (⟸) value-invariance lets us rewrite each right-hand pair to `(value (σ c), label (σ c))`, which is
  the left-hand map precomposed with `σ`; reindexing `univ` by the bijection `σ` leaves it unchanged.
* (⟹) the pair `(value (σ c), label (σ c))` sits in the left multiset (index `σ c`); the equality
  moves it to the right, where `Multiset.mem_map` yields an index `e` with `label (σ e) = label (σ c)`
  and `value e = value (σ c)`; injectivity of `label` and of `σ` forces `e = c`. -/
theorem perm_values_eq_iff {ι L V : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    {label : ι → L} (hlabel : Function.Injective label) (value : ι → V) :
    Finset.univ.val.map (fun c => (value c, label c))
      = Finset.univ.val.map (fun c => (value c, label (σ c)))
    ↔ ∀ c, value c = value (σ c) := by
  constructor
  · intro h c
    -- the index `σ c` puts `(value (σ c), label (σ c))` in the left multiset
    have hmem : (value (σ c), label (σ c)) ∈
        Finset.univ.val.map (fun c => (value c, label c)) :=
      Multiset.mem_map.mpr ⟨σ c, by simp, rfl⟩
    -- transport it to the right multiset and read off a matching index `e`
    rw [h] at hmem
    obtain ⟨e, _, he⟩ := Multiset.mem_map.mp hmem
    -- `he : (value e, label (σ e)) = (value (σ c), label (σ c))`
    have hee : e = c := σ.injective (hlabel (congrArg Prod.snd he))
    have hval : value e = value (σ c) := congrArg Prod.fst he
    rwa [hee] at hval
  · intro h
    -- value-invariance rewrites the right pairs to `(value (σ c), label (σ c))` …
    have hRHS : Finset.univ.val.map (fun c => (value c, label (σ c)))
        = Finset.univ.val.map (fun c => (value (σ c), label (σ c))) :=
      Multiset.map_congr rfl (fun c _ => by rw [h c])
    -- … which is `(fun c => (value c, label c)) ∘ σ`, so reindexing by `σ` over `univ` closes it
    rw [hRHS, show (fun c => (value (σ c), label (σ c)))
          = (fun c => (value c, label c)) ∘ σ from rfl,
        ← Multiset.map_map, univ_val_map_perm]

/-- A `value` invariant under one application of `σ` is invariant under every integer power of `σ`.
By induction on the exponent: the `value c = value (σ c)` hypothesis also gives invariance under `σ⁻¹`
(`value (σ⁻¹ x) = value (σ (σ⁻¹ x)) = value x`), and the two extend to all of ℤ. (ℕ is logically
sufficient since the permutation is finite, but Mathlib's definition of `SameCycle` uses ℤ to cater
for infinite cases.) -/
theorem value_zpow {ι V : Type*} (σ : Equiv.Perm ι) (value : ι → V)
    (h : ∀ c, value c = value (σ c)) : ∀ (n : ℤ) (x : ι), value ((σ ^ n) x) = value x := by
  have hinv : ∀ x, value (σ⁻¹ x) = value x := by
    intro x; rw [h (σ⁻¹ x)]; simp
  intro n
  induction n using Int.induction_on with
  | zero => intro x; simp
  | succ i ih =>
      intro x
      rw [zpow_add, zpow_one, Equiv.Perm.mul_apply, ih (σ x), ← h x]
  | pred i ih =>
      intro x
      rw [zpow_sub, zpow_one, Equiv.Perm.mul_apply, ih (σ⁻¹ x), hinv x]

/-- **Values are constant on σ-cycles** — the copy-constraint relation in full.

Given the per-cell one-step invariance `value c = value (σ c)` (e.g. from `perm_values_eq_iff`), any two
cells in the same cycle of `σ` (`σ.SameCycle c d`, i.e. `d = σⁱ c` for some `i : ℤ`) hold equal values. -/
theorem value_const_on_sameCycle {ι V : Type*} (σ : Equiv.Perm ι) (value : ι → V)
    (h : ∀ c, value c = value (σ c)) {c d : ι} (hcd : σ.SameCycle c d) :
    value c = value d := by
  obtain ⟨n, rfl⟩ := hcd
  exact (value_zpow σ value h n c).symm

/-- **Soundness of the permutation argument — structural step lifted to cycles** (modulo the
grand-product ⟹ multiset-identity step).

This composes `perm_values_eq_iff` with `value_const_on_sameCycle`: from the multiset-of-pairs identity
delivered by the kernel (`prod_pair_inj`), with `label` injective, any two cells in the same cycle of
`σ` hold equal values — exactly the copy constraints `σ` encodes. -/
theorem perm_copy_constraints {ι L V : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    {label : ι → L} (hlabel : Function.Injective label) (value : ι → V)
    (h : Finset.univ.val.map (fun c => (value c, label c))
       = Finset.univ.val.map (fun c => (value c, label (σ c))))
    {c d : ι} (hcd : σ.SameCycle c d) :
    value c = value d :=
  value_const_on_sameCycle σ value ((perm_values_eq_iff σ hlabel value).mp h) hcd

end Zcash.Snark
