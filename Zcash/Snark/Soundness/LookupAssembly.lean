import Mathlib
import Zcash.Snark.Soundness.Lookup
import Zcash.Snark.Soundness.GrandProductBridge

/-!
# The lookup argument, assembled

`Soundness.Lookup.run_structure` proves the permuted columns' half: every permuted-input value
occurs somewhere in the permuted table. `GrandProductBridge` proves the product half: the running
product identity pins the permuted columns to the real ones — as two separate multiset identities,
since the lookup's two challenges sit on separate columns.

Neither alone says anything about the lookup. Together they do, and this module is that step: an
input value is a permuted-input value, which the run structure places in the permuted table, which
the multiset identities place in the real table.

* `lookup_subset_of_components` — the assembly, `{input} ⊆ {table}`, from the two column identities.
* `lookup_subset_of_prod_eval_eq` — the same with those identities supplied by the verifier's own
  product check and row constraints rather than assumed.
-/

namespace Zcash.Snark

open Polynomial Finset

/-- **The lookup assembly.** Every input value occurs in the table. The input identity moves an input
into the permuted columns, the run structure moves it across to the permuted table, and the table
identity moves it back to the real table. -/
theorem lookup_subset_of_components {ι : Type*} [Fintype ι] {a s inp tbl : ι → Fp}
    (hinp : Finset.univ.val.map a = Finset.univ.val.map inp)
    (htbl : Finset.univ.val.map s = Finset.univ.val.map tbl)
    (hrun : ∀ i, ∃ j, a i = s j) (i : ι) :
    ∃ j, inp i = tbl j := by
  -- the input value is a permuted-input value
  have hmem : inp i ∈ Finset.univ.val.map a := by
    rw [hinp]; exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  obtain ⟨i₀, _, hi₀⟩ := Multiset.mem_map.mp hmem
  -- the run structure sends it to a permuted table entry
  obtain ⟨j, hj⟩ := hrun i₀
  -- which the table identity places in the real table
  have hsmem : s j ∈ Finset.univ.val.map tbl := by
    rw [← htbl]; exact Multiset.mem_map.mpr ⟨j, by simp, rfl⟩
  obtain ⟨j', _, hj'⟩ := Multiset.mem_map.mp hsmem
  exact ⟨j', by rw [← hi₀, hj, ← hj']⟩

open Finset in
/-- **The lookup argument, closed at the verifier's checks.** The product identity is the telescoped
running product; `h0`/`hstep0`/`hstep` are the row constraints on the permuted columns; the two
challenge conditions are the priced root sets. The conclusion is the lookup relation: every input
value appears in the table. -/
theorem lookup_subset_of_prod_eval_eq {n : ℕ} (a s inp tbl : Fin (n + 1) → Fp) (β γ aPrev : Fp)
    (hprod : (∏ i, (β + a i)) * (∏ i, (γ + s i)) = (∏ i, (β + inp i)) * (∏ i, (γ + tbl i)))
    (hgoodγ : γ ∉ szBadSet ((lookupProdDiff (univ.val.map a) (univ.val.map s)
      (univ.val.map inp) (univ.val.map tbl)).map (evalRingHom β)))
    (hgoodβ : ∀ j, β ∉ szBadSet ((lookupProdDiff (univ.val.map a) (univ.val.map s)
      (univ.val.map inp) (univ.val.map tbl)).coeff j))
    (h0 : a 0 = s 0) (hstep0 : a 0 = s 0 ∨ a 0 = aPrev)
    (hstep : ∀ i : Fin n, a i.succ = s i.succ ∨ a i.succ = a i.castSucc) (i : Fin (n + 1)) :
    ∃ j, inp i = tbl j := by
  have hmulti : ((univ.val.map a).map (fun u => β + u)).prod
        * ((univ.val.map s).map (fun u => γ + u)).prod
      = ((univ.val.map inp).map (fun u => β + u)).prod
        * ((univ.val.map tbl).map (fun u => γ + u)).prod := by
    simpa [Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_def] using hprod
  obtain ⟨hain, hstbl⟩ :=
    lookup_multisets_of_diff_eq_zero (lookup_multisets_of_prod_eval_eq hgoodγ hgoodβ hmulti)
  exact lookup_subset_of_components hain hstbl (run_structure a s aPrev h0 hstep0 hstep) i

end Zcash.Snark
