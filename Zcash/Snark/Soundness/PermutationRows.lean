import Mathlib
import Zcash.Snark.Soundness.FoldSplit
import Zcash.Snark.Soundness.GrandProductBridge

/-!
# The verifier's permutation constraints, read row by row

`GrandProductBridge` closes the permutation argument from a one-row recurrence on the running
product. This module produces that recurrence from the verifier's own constraint list, so nothing
about the shape of the checks is assumed.

The route is short once the constraints are individually known to vanish on the domain
(`FoldSplit.constraints_dvd_of_good_y`):

* `eval_eq_zero_of_dvd_vanishing` — a constraint divisible by `Xⁿ − 1` vanishes at every row.
* `permSetPolys` — the running product as a permutation set: this row is `z`, the next row is
  `z` composed with the rotation `ω·X`, which at row `ωⁱ` reads `z(ω^{i+1})`.
* `perm_row_recurrence` — the step rule at row `ωⁱ`, with the row switched on, *is* the recurrence.
* `running_product_start` / `running_product_end` — the boundary rules give `z = 1` at the first row
  and `z ∈ {0, 1}` at the last.
* `name_injective_of_coset` — the identity names `ωⁱ·δ^j` are distinct across cells, from `ω`'s
  order and the `δ`-coset distinctness the keygen chooses `δ` to satisfy.

Everything here is about the deployed `permChunkExpression`, not a restatement of it.
-/

namespace Zcash.Snark

open Polynomial Finset

/-- A constraint that vanishes on the whole domain vanishes at each row. -/
theorem eval_eq_zero_of_dvd_vanishing {n : ℕ} {c : Polynomial Fp}
    (h : (X ^ n - 1 : Polynomial Fp) ∣ c) {r : Fp} (hr : r ^ n = 1) : c.eval r = 0 := by
  obtain ⟨d, rfl⟩ := h
  simp [hr]

/-- The running product as a permutation set: `eval` is this row, `nextEval` is the next row (the
polynomial composed with the rotation `ω·X`), and `lastEval` is supplied by the caller. -/
noncomputable def permSetPolys (omega : Fp) (z : Polynomial Fp)
    (last : Option (Polynomial Fp)) : PermSetEval (Polynomial Fp) :=
  { eval := z, nextEval := z.comp (C omega * X), lastEval := last }

@[simp] theorem permSetPolys_eval (omega : Fp) (z : Polynomial Fp) (last) :
    (permSetPolys omega z last).eval = z := rfl

/-- The next-row component really is the next row: at `ωⁱ` it reads `z(ω^{i+1})`. -/
theorem eval_permSetPolys_nextEval (omega : Fp) (z : Polynomial Fp) (last) (i : ℕ) :
    ((permSetPolys omega z last).nextEval).eval (omega ^ i) = z.eval (omega ^ (i + 1)) := by
  rw [permSetPolys, eval_comp_rotate, pow_succ, mul_comm]

/-- **The step rule is the recurrence.** At a row the verifier has switched on, the deployed
`permChunkExpression` vanishing says exactly that the running product advances by the ratio of the
`σ`-named factors to the identity-named ones. The identity name of column `j` in chunk `c` at row
`ωⁱ` is `ωⁱ·δ^{c·chunkLen + j}`. -/
theorem perm_row_recurrence (omega beta gamma delta : Fp) (chunkLen chunkIndex : ℕ)
    (z : Polynomial Fp) (last : Option (Polynomial Fp))
    (pairs : List (Polynomial Fp × Polynomial Fp)) (lLastP lBlindP : Polynomial Fp) {n : ℕ}
    (hdvd : (X ^ n - 1 : Polynomial Fp) ∣ permChunkExpression (C beta) (C gamma) X (C delta)
      chunkLen chunkIndex (permSetPolys omega z last) pairs lLastP lBlindP)
    {i : ℕ} (hpow : (omega ^ i) ^ n = 1)
    (hactive : 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0) :
    z.eval (omega ^ (i + 1)) * ∏ j ∈ range pairs.length,
        ((pairs.getD j (0, 0)).1.eval (omega ^ i)
          + beta * (pairs.getD j (0, 0)).2.eval (omega ^ i) + gamma)
      = z.eval (omega ^ i) * ∏ j ∈ range pairs.length,
        ((pairs.getD j (0, 0)).1.eval (omega ^ i)
          + beta * (omega ^ i * delta ^ (chunkIndex * chunkLen + j)) + gamma) := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hpow
  rw [permChunkExpression_eq] at hzero
  simp only [eval_mul, eval_sub, eval_prod, eval_add, eval_C, eval_X, eval_one, eval_pow,
    eval_permSetPolys_nextEval, permSetPolys_eval] at hzero
  rcases mul_eq_zero.mp hzero with hbr | hact
  · have := sub_eq_zero.mp hbr
    rw [this]
    exact congrArg _ (prod_congr rfl fun j _ => by ring)
  · exact absurd hact hactive

/-- The first-row rule `ℓ₀·(1 − z) = 0` pins the running product to `1` where `ℓ₀` is nonzero. -/
theorem running_product_start {l0P zP : Polynomial Fp} {n : ℕ}
    (hdvd : (X ^ n - 1 : Polynomial Fp) ∣ l0P * (1 - zP)) {r : Fp} (hr : r ^ n = 1)
    (hl0 : l0P.eval r ≠ 0) : zP.eval r = 1 := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hr
  rw [eval_mul, eval_sub, eval_one] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hl0
  · exact (sub_eq_zero.mp h).symm

/-- The last-row rule `(z² − z)·ℓ_last = 0` leaves the running product at `0` or `1` where
`ℓ_last` is nonzero. -/
theorem running_product_end {lLastP zP : Polynomial Fp} {n : ℕ}
    (hdvd : (X ^ n - 1 : Polynomial Fp) ∣ (zP ^ 2 - zP) * lLastP) {r : Fp} (hr : r ^ n = 1)
    (hlast : lLastP.eval r ≠ 0) : zP.eval r = 0 ∨ zP.eval r = 1 := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hr
  rw [eval_mul, eval_sub, eval_pow] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · have hfac : zP.eval r * (zP.eval r - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  · exact absurd h hlast

/-! ## The identity names are distinct

halo2 names cell `(row i, column j)` by `ωⁱ·δ^j`. Distinctness of those names is what turns the
multiset identity into the per-cell copy constraints, and it rests on two facts about the verifying
key's constants: `ω` generates a subgroup of order `u`, and the powers of `δ` below the column count
lie in distinct cosets of that subgroup. The second is the property halo2's keygen picks `δ` to
have; it is a statement about the concrete key, checkable for a given one, not an assumption about
the proof system. -/

/-- **Name distinctness.** With `ω` of order `u` and the column names in distinct cosets of `⟨ω⟩`,
the cell names `ωⁱ·colName j` separate the cells. -/
theorem name_injective_of_coset {omega : Fp} {u k : ℕ} (colName : Fin k → Fp)
    (hne : ∀ j, colName j ≠ 0) (homega : omega ^ u = 1)
    (horder : ∀ i i' : ℕ, i < u → i' < u → omega ^ i = omega ^ i' → i = i')
    (hcoset : ∀ (j j' : Fin k) (t : ℕ), colName j = omega ^ t * colName j' → j = j') :
    Function.Injective fun c : Fin u × Fin k => omega ^ (c.1 : ℕ) * colName c.2 := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only at h
  -- multiply by `ω^{u−i}` to clear the row factor without dividing
  have hshift : colName j = omega ^ (u - (i : ℕ) + (i' : ℕ)) * colName j' := by
    have hmul := congrArg (fun v => omega ^ (u - (i : ℕ)) * v) h
    simp only at hmul
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_of_lt i.isLt), homega, one_mul] at hmul
    rw [hmul, ← mul_assoc, ← pow_add]
  have hj : j = j' := hcoset _ _ _ hshift
  have hi : (i : ℕ) = (i' : ℕ) := by
    refine horder _ _ i.isLt i'.isLt ?_
    rw [hj] at h
    exact mul_right_cancel₀ (hne j') h
  exact Prod.ext (Fin.ext hi) hj

/-! ## The permutation argument at the deployed constraints

Naming the three families the row reading produces, so the end-to-end statement stays readable: the
committed column value at a cell, the permutation column's value there (the `σ`-side name), and the
identity name `ωⁱ·δ^{offset + j}` halo2 assigns the cell. -/

/-- The committed column's value at row `ωⁱ`, column `j`. -/
noncomputable def rowValue (omega : Fp) (pairs : List (Polynomial Fp × Polynomial Fp)) :
    ℕ → ℕ → Fp := fun i j => (pairs.getD j (0, 0)).1.eval (omega ^ i)

/-- The permutation column's value at row `ωⁱ`, column `j` — the name `σ` sends the cell to. -/
noncomputable def rowSigmaName (omega : Fp) (pairs : List (Polynomial Fp × Polynomial Fp)) :
    ℕ → ℕ → Fp := fun i j => (pairs.getD j (0, 0)).2.eval (omega ^ i)

/-- The identity name halo2 assigns to row `ωⁱ`, column `j` of a chunk starting at `off`. -/
noncomputable def rowName (omega delta : Fp) (off : ℕ) : ℕ → ℕ → Fp :=
  fun i j => omega ^ i * delta ^ (off + j)

open Finset in
/-- **The permutation argument, closed at the deployed constraints.** Every hypothesis is either a
constraint the verifier checks (`hstep`/`hstart`/`hend`, each vanishing on the domain), a fact about
the verifying key's constants (`hrow`/`hactive`/`hl0`/`hlast`/`hnm`), or a challenge avoiding a
priced root set. The conclusion is halo2's copy constraint: cells in the same cycle of `σ` hold
equal values. The surviving branch is a vanishing factor — the running product ended at zero, or a
name collided with a value. -/
theorem deployed_perm_copy_constraints
    (omega beta gamma delta : Fp) (chunkLen chunkIndex : ℕ)
    (z : Polynomial Fp) (last : Option (Polynomial Fp))
    (pairs : List (Polynomial Fp × Polynomial Fp)) (l0P lLastP lBlindP : Polynomial Fp)
    {n u : ℕ} (σ : Equiv.Perm (Fin u × Fin pairs.length))
    (hstep : (X ^ n - 1 : Polynomial Fp) ∣ permChunkExpression (C beta) (C gamma) X (C delta)
      chunkLen chunkIndex (permSetPolys omega z last) pairs lLastP lBlindP)
    (hstart : (X ^ n - 1 : Polynomial Fp) ∣ l0P * (1 - z))
    (hend : (X ^ n - 1 : Polynomial Fp) ∣ (z ^ 2 - z) * lLastP)
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < u, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ u) ≠ 0)
    (hσ : ∀ c : Fin u × Fin pairs.length,
      rowSigmaName omega pairs (c.1 : ℕ) (c.2 : ℕ)
        = rowName omega delta (chunkIndex * chunkLen) ((σ c).1 : ℕ) ((σ c).2 : ℕ))
    (hnm : Function.Injective fun c : Fin u × Fin pairs.length =>
      rowName omega delta (chunkIndex * chunkLen) (c.1 : ℕ) (c.2 : ℕ))
    (hgoodγ : gamma ∉ szBadSet (linProdDiff
      ((cellPairs u pairs.length (rowValue omega pairs)
        (rowSigmaName omega pairs)).map (fun p => p.1 + p.2 * beta))
      ((cellPairs u pairs.length (rowValue omega pairs)
        (rowName omega delta (chunkIndex * chunkLen))).map (fun p => p.1 + p.2 * beta))))
    (hgoodβ : ∀ j, beta ∉ szBadSet ((pairProdDiff
      (cellPairs u pairs.length (rowValue omega pairs) (rowSigmaName omega pairs))
      (cellPairs u pairs.length (rowValue omega pairs)
        (rowName omega delta (chunkIndex * chunkLen)))).coeff j))
    {c d : Fin u × Fin pairs.length} (hcd : σ.SameCycle c d) :
    rowValue omega pairs (c.1 : ℕ) (c.2 : ℕ) = rowValue omega pairs (d.1 : ℕ) (d.2 : ℕ)
      ∨ ∃ p ∈ range u ×ˢ range pairs.length,
          rowValue omega pairs p.1 p.2
            + beta * rowName omega delta (chunkIndex * chunkLen) p.1 p.2 + gamma = 0 := by
  refine perm_copy_constraints_of_running_product (fun i => z.eval (omega ^ i))
    (rowValue omega pairs) (rowName omega delta (chunkIndex * chunkLen))
    (rowSigmaName omega pairs) beta gamma σ hσ hnm ?_ ?_ ?_ hgoodγ hgoodβ hcd
  · intro i hi
    simpa [rowValue, rowSigmaName, rowName, pow_add, mul_assoc, mul_comm, mul_left_comm] using
      perm_row_recurrence omega beta gamma delta chunkLen chunkIndex z last pairs lLastP lBlindP
        hstep (hrow i) (hactive i hi)
  · simpa using running_product_start hstart (hrow 0) hl0
  · exact running_product_end hend (hrow u) hlast

end Zcash.Snark
