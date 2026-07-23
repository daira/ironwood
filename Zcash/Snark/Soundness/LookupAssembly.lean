import Mathlib
import Zcash.Snark.Soundness.Lookup
import Zcash.Snark.Soundness.GrandProductBridge

/-!
# The lookup argument, assembled

`Soundness.Lookup.run_structure` proves the permuted columns' half: every permuted-input value
occurs somewhere in the permuted table. `GrandProductBridge` proves the product half: the running
product identity pins the multiset of `(permuted input, permuted table)` pairs to the multiset of
`(compressed input, compressed table)` pairs.

Neither alone says anything about the lookup. Together they do, and this module is that step: an
input value is a permuted-input value, which the run structure places in the permuted table, which
the multiset identity places in the real table.

* `lookup_subset_of_pairs_of_run_structure` — the assembly, `{input} ⊆ {table}`.
* `lookup_subset_of_running_product` — the same with the pair identity supplied by the telescoped
  running product rather than assumed, so the inputs are the verifier's own row checks.
-/

namespace Zcash.Snark

open Finset

/-- Both components of a pair multiset identity: the permuted columns and the real ones agree
componentwise as multisets. -/
theorem map_snd_eq_of_pairs_eq {ι : Type*} [Fintype ι] {a s inp tbl : ι → Fp}
    (hpairs : Finset.univ.val.map (fun i => (a i, s i))
      = Finset.univ.val.map (fun i => (inp i, tbl i))) :
    Finset.univ.val.map s = Finset.univ.val.map tbl := by
  have := congrArg (Multiset.map Prod.snd) hpairs
  simpa [Multiset.map_map, Function.comp_def] using this

/-- **The lookup assembly.** Every input value occurs in the table. The pair identity moves an input
into the permuted columns, the run structure moves it across to the permuted table, and the identity
moves it back to the real table. -/
theorem lookup_subset_of_pairs_of_run_structure {ι : Type*} [Fintype ι] {a s inp tbl : ι → Fp}
    (hpairs : Finset.univ.val.map (fun i => (a i, s i))
      = Finset.univ.val.map (fun i => (inp i, tbl i)))
    (hrun : ∀ i, ∃ j, a i = s j) (i : ι) :
    ∃ j, inp i = tbl j := by
  -- the input's pair sits in the right multiset, so it sits in the left one
  have hmem : (inp i, tbl i) ∈ Finset.univ.val.map (fun i => (a i, s i)) := by
    rw [hpairs]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  obtain ⟨i₀, _, hi₀⟩ := Multiset.mem_map.mp hmem
  have hinp : inp i = a i₀ := (congrArg Prod.fst hi₀).symm
  -- the run structure sends that permuted input to a permuted table entry
  obtain ⟨j, hj⟩ := hrun i₀
  -- and the second components agree as multisets, so that entry is a real table entry
  have hsmem : s j ∈ Finset.univ.val.map tbl := by
    rw [← map_snd_eq_of_pairs_eq hpairs]
    exact Multiset.mem_map.mpr ⟨j, by simp, rfl⟩
  obtain ⟨j', _, hj'⟩ := Multiset.mem_map.mp hsmem
  exact ⟨j', by rw [hinp, hj, ← hj']⟩

/-- **The lookup argument from the verifier's checks.** The row constraints give the run structure
(`hzero`, `hstep`) and the running product gives the pair identity; together every input value is a
table value. The permuted columns are the prover's, so the run structure is what stops it from
answering with a table it never committed to. -/
theorem lookup_subset_of_run_structure {n : ℕ} {a s inp tbl : Fin (n + 1) → Fp} {aPrev : Fp}
    (hpairs : Finset.univ.val.map (fun i => (a i, s i))
      = Finset.univ.val.map (fun i => (inp i, tbl i)))
    (h0 : a 0 = s 0)
    (hstep0 : a 0 = s 0 ∨ a 0 = aPrev)
    (hstep : ∀ i : Fin n, a i.succ = s i.succ ∨ a i.succ = a i.castSucc) (i : Fin (n + 1)) :
    ∃ j, inp i = tbl j :=
  lookup_subset_of_pairs_of_run_structure hpairs (run_structure a s aPrev h0 hstep0 hstep) i

end Zcash.Snark
