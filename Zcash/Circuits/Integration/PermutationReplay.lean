import Zcash.Circuits.Integration.PermutationColumns

/-!
# The executable keygen assembly replay is the abstract permutation replay

`Layout.runAssembly` replays halo2's `Assembly::copy` over the derived copy list with
arrays and union-find bookkeeping; the permutation semantics
(`ResolverPermutationCycle.ofKeygenColumns`, `keygenSigmaColumn`) speak about the
abstract swap-composition replay `replayKeygenPermutation`. This module proves they are
the same permutation: the assembly's `mapping` is the abstract permutation's action, and
its `aux` classes are exactly the cycles.

The simulation invariant `Asm.Sim` carries three facts through the copy fold: `mapping`
acts as the permutation, every `aux` entry is an in-cycle representative, and `aux`
entries agree exactly on cycles. The union-find size heuristic needs no invariant — it
only selects which representative survives a merge, and the cycle partition is
representative-agnostic.
-/

namespace Zcash.Snark

open Halo2 Zcash.Circuits.Fixtures.Layout
open Equiv (Perm swap)

set_option maxHeartbeats 400000

/-- A flat permutation-table cell: a permutation column and a row. -/
abbrev FlatCell (numCols n : ℕ) := Fin numCols × Fin n

/-- The `(column, row)` pair the assembly arrays index by. -/
def FlatCell.pair {numCols n : ℕ} (c : FlatCell numCols n) : ℕ × ℕ :=
  ((c.1 : ℕ), (c.2 : ℕ))

theorem FlatCell.pair_injective {numCols n : ℕ} :
    Function.Injective (FlatCell.pair (numCols := numCols) (n := n)) := by
  intro c d h
  simp only [FlatCell.pair, Prod.mk.injEq] at h
  exact Prod.ext_iff.mpr ⟨Fin.ext h.1, Fin.ext h.2⟩

namespace Layout.Asm

open Zcash.Circuits.Fixtures.Layout.Asm

/-- Simulation between an assembly state and an abstract cell permutation. -/
structure Sim {numCols n : ℕ} (a : Asm) (π : Perm (FlatCell numCols n)) : Prop where
  map_eq : ∀ c : FlatCell numCols n,
    getPair a.mapping c.pair = (π c).pair
  aux_rep : ∀ c : FlatCell numCols n, ∃ r : FlatCell numCols n,
    getPair a.aux c.pair = r.pair ∧ π.SameCycle c r
  aux_eq_iff : ∀ c d : FlatCell numCols n,
    (getPair a.aux c.pair = getPair a.aux d.pair ↔ π.SameCycle c d)

/-- `repoint` never touches `mapping`. -/
theorem repoint_mapping (a : Asm) (fuel : ℕ) (i tgt stop : ℕ × ℕ) :
    (repoint a fuel i tgt stop).mapping = a.mapping := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [repoint]
      split
      · rfl
      · exact ih _ _

/-- `repoint` never touches `sizes`. -/
theorem repoint_sizes (a : Asm) (fuel : ℕ) (i tgt stop : ℕ × ℕ) :
    (repoint a fuel i tgt stop).sizes = a.sizes := by
  induction fuel generalizing a i with
  | zero => rfl
  | succ fuel ih =>
      simp only [repoint]
      split
      · rfl
      · exact ih _ _

/-- The rectangular shape invariant of the assembly's cell arrays. -/
def Shaped (numCols n : ℕ) (a : Array (Array (ℕ × ℕ))) : Prop :=
  a.size = numCols ∧ ∀ i, (h : i < a.size) → a[i].size = n

theorem Shaped.setPair {numCols n : ℕ} {a : Array (Array (ℕ × ℕ))}
    (h : Shaped numCols n a) (p : ℕ × ℕ) (v : ℕ × ℕ) :
    Shaped numCols n (setPair a p v) := by
  obtain ⟨hsize, hrow⟩ := h
  refine ⟨by simpa [Zcash.Circuits.Fixtures.Layout.Asm.setPair] using hsize, ?_⟩
  intro i hi
  simp only [Zcash.Circuits.Fixtures.Layout.Asm.setPair, Array.size_modify] at hi
  by_cases hip : p.1 = i
  · subst hip
    simp [Zcash.Circuits.Fixtures.Layout.Asm.setPair, Array.getElem_modify_self, hrow]
  · simp [Zcash.Circuits.Fixtures.Layout.Asm.setPair, Array.getElem_modify_of_ne hip, hrow]

/-- Reading back the just-written cell (the write position must be in shape). -/
theorem getPair_setPair_self {numCols n : ℕ} {a : Array (Array (ℕ × ℕ))}
    (h : Shaped numCols n a) {p : ℕ × ℕ} (hp1 : p.1 < numCols) (hp2 : p.2 < n)
    (v : ℕ × ℕ) :
    getPair (setPair a p v) p = v := by
  obtain ⟨hsize, hrow⟩ := h
  have hp1' : p.1 < a.size := hsize ▸ hp1
  simp [Zcash.Circuits.Fixtures.Layout.Asm.getPair, Zcash.Circuits.Fixtures.Layout.Asm.setPair,
    Array.size_modify, hp1', Array.getElem_modify_self,
    Array.set!, Array.getElem_setIfInBounds_self, hrow _ hp1', hp2]

/-- Reading any other cell is unaffected by the write. -/
theorem getPair_setPair_ne {numCols n : ℕ} {a : Array (Array (ℕ × ℕ))}
    (h : Shaped numCols n a) {p q : ℕ × ℕ} (hpq : q ≠ p) (v : ℕ × ℕ) :
    getPair (setPair a p v) q = getPair a q := by
  obtain ⟨hsize, hrow⟩ := h
  by_cases h1 : q.1 = p.1
  · have h2 : q.2 ≠ p.2 := fun h2 => hpq (Prod.ext_iff.mpr ⟨h1, h2⟩)
    by_cases hq1 : q.1 < a.size
    · have hp1 : p.1 < a.size := h1 ▸ hq1
      simp [Zcash.Circuits.Fixtures.Layout.Asm.getPair, Zcash.Circuits.Fixtures.Layout.Asm.setPair, Array.getElem!_eq_getD, Array.getD,
        Array.size_modify, h1, Array.getElem_modify_self,
        Array.set!, Array.size_setIfInBounds, hp1]
      split
      · exact Array.getElem_setIfInBounds_ne (by assumption) (Ne.symm h2)
      · rfl
    · simp [Zcash.Circuits.Fixtures.Layout.Asm.getPair, Zcash.Circuits.Fixtures.Layout.Asm.setPair, Array.getElem!_eq_getD, Array.getD,
        Array.size_modify, hq1]
  · simp [Zcash.Circuits.Fixtures.Layout.Asm.getPair, Zcash.Circuits.Fixtures.Layout.Asm.setPair, Array.getElem!_eq_getD, Array.getD,
      Array.size_modify, Array.getElem_modify_of_ne (fun h => h1 h.symm)]

/-- `repoint` preserves the aux shape. -/
theorem Shaped.repoint {numCols n : ℕ} {a : Asm}
    (h : Shaped numCols n a.aux) (fuel : ℕ) (i tgt stop : ℕ × ℕ) :
    Shaped numCols n (Zcash.Circuits.Fixtures.Layout.Asm.repoint a fuel i tgt stop).aux := by
  induction fuel generalizing a i with
  | zero => exact h
  | succ fuel ih =>
      simp only [Zcash.Circuits.Fixtures.Layout.Asm.repoint]
      split
      · exact h.setPair i tgt
      · exact ih (h.setPair i tgt) _

/-- The effect of one `repoint` walk: with `mapping` acting as `π`, the walk from
`start` (with stop `stop`, the first later return of the orbit) re-points exactly the
orbit segment `π ^ t · start, t < s`, and leaves every other `aux` entry unchanged. -/
theorem getPair_repoint_aux {numCols n : ℕ} {a : Asm} {π : Perm (FlatCell numCols n)}
    (hshape : Shaped numCols n a.aux)
    (hmap : ∀ c : FlatCell numCols n, getPair a.mapping c.pair = (π c).pair)
    (s : ℕ) (start stop : FlatCell numCols n) (tgt : ℕ × ℕ)
    (hs : (π ^ s) start = stop) (hs1 : 1 ≤ s)
    (hmin : ∀ t, 0 < t → t < s → (π ^ t) start ≠ stop)
    (fuel : ℕ) (hfuel : s ≤ fuel)
    (d : FlatCell numCols n) :
    getPair (Zcash.Circuits.Fixtures.Layout.Asm.repoint a fuel start.pair tgt stop.pair).aux d.pair =
      if ∃ t, t < s ∧ (π ^ t) start = d then tgt else getPair a.aux d.pair := by
  induction s generalizing a start fuel with
  | zero => exact absurd hs1 (by omega)
  | succ s' ih =>
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 :=
        ⟨fuel - 1, by omega⟩
      have hnext : getPair a.mapping start.pair = (π start).pair := hmap start
      by_cases hzero : s' = 0
      · -- one step: the walk immediately returns to `stop`
        subst hzero
        have hstop : π start = stop := by
          simpa [pow_one] using hs
        simp only [Zcash.Circuits.Fixtures.Layout.Asm.repoint, hnext, hstop]
        rw [if_pos (by simp)]
        by_cases hd : d = start
        · subst hd
          rw [if_pos ⟨0, by simp, rfl⟩]
          exact getPair_setPair_self hshape d.1.isLt d.2.isLt tgt
        · rw [if_neg ?_, getPair_setPair_ne hshape ?_ tgt]
          · exact fun h => hd (FlatCell.pair_injective h)
          · rintro ⟨t, ht, hteq⟩
            interval_cases t
            exact hd (by simpa using hteq.symm)
      · -- the walk continues: `π start ≠ stop`, recurse along the orbit
        have hs'1 : 1 ≤ s' := by omega
        have hne : π start ≠ stop := by
          simpa [pow_one] using hmin 1 (by omega) (by omega)
        have hnepair : ((π start).pair == stop.pair) = false := by
          simp only [beq_eq_false_iff_ne]
          exact fun h => hne (FlatCell.pair_injective h)
        simp only [Zcash.Circuits.Fixtures.Layout.Asm.repoint, hnext, hnepair]
        rw [if_neg (by simp)]
        have hs'' : (π ^ s') (π start) = stop := by
          rw [← Equiv.Perm.mul_apply, ← pow_succ]
          exact hs
        have hmin'' : ∀ t, 0 < t → t < s' → (π ^ t) (π start) ≠ stop := by
          intro t ht hts habs
          refine hmin (t + 1) (by omega) (by omega) ?_
          rw [pow_succ, Equiv.Perm.mul_apply]
          exact habs
        have hrec := ih (a := { a with aux := setPair a.aux start.pair tgt })
          (hshape.setPair start.pair tgt) hmap (π start) hs'' hs'1 hmin'' f (by omega) 
        rw [hrec]
        by_cases hd : d = start
        · subst hd
          have hrhs : ∃ t, t < s' + 1 ∧ (π ^ t) d = d := ⟨0, by simp⟩
          rw [if_pos hrhs]
          split
          · rfl
          · exact getPair_setPair_self hshape d.1.isLt d.2.isLt tgt
        · have hpairne : d.pair ≠ start.pair :=
            fun h => hd (FlatCell.pair_injective h)
          have hcond : (∃ t, t < s' ∧ (π ^ t) (π start) = d) ↔
              (∃ t, t < s' + 1 ∧ (π ^ t) start = d) := by
            constructor
            · rintro ⟨t, ht, hteq⟩
              refine ⟨t + 1, by omega, ?_⟩
              rw [pow_succ, Equiv.Perm.mul_apply]
              exact hteq
            · rintro ⟨t, ht, hteq⟩
              match t with
              | 0 => exact absurd (by simpa using hteq.symm) hd
              | t + 1 =>
                  refine ⟨t, by omega, ?_⟩
                  rw [pow_succ, Equiv.Perm.mul_apply] at hteq
                  exact hteq
          rw [getPair_setPair_ne hshape hpairne tgt]
          by_cases hc : ∃ t, t < s' + 1 ∧ (π ^ t) start = d
          · rw [if_pos hc, if_pos (hcond.mpr hc)]
          · rw [if_neg hc, if_neg (fun h => hc (hcond.mp h))]

end Layout.Asm

end Zcash.Snark
