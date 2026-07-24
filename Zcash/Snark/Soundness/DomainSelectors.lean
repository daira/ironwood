import Zcash.Snark.Soundness.PolynomialEnvironment

/-!
# Canonical evaluation-domain selector polynomials

Halo 2's permutation and lookup arguments use three circuit-independent Lagrange
polynomials:

* `l₀`, one at the first row and zero elsewhere;
* `l_last`, one at the final usable row and zero elsewhere;
* `l_blind`, one on the rows after `l_last` and zero through the usable rows.

This module defines those polynomials by their domain rows and proves the evaluations
needed by the generic permutation and lookup semantic records. Identifying the
verifier's decoded `l₀`/`l_last`/`l_blind` with these canonical polynomials remains a
multiopen/domain-polynomial provenance step, not a circuit-specific layout fact.
-/

namespace Zcash.Snark

open Polynomial

set_option maxHeartbeats 20000

/-- The Lagrange row selector that is one at `selected` and zero at every other row. -/
noncomputable def rowSelectorPolynomial {n : ℕ}
    (omega : Fp) (selected : Fin n) : Polynomial Fp :=
  rowPolynomial omega (Pi.single selected 1)

/-- The selector that is one exactly on rows strictly after the final usable row. -/
noncomputable def blindSelectorPolynomial {n : ℕ}
    (omega : Fp) (lastUsable : Fin n) : Polynomial Fp :=
  rowPolynomial omega fun row : Fin n =>
    if lastUsable.val < row.val then 1 else 0

/-- A row selector is exactly the corresponding Lagrange basis polynomial. -/
theorem rowSelectorPolynomial_eq_basis {n : ℕ}
    (omega : Fp) (selected : Fin n) :
    rowSelectorPolynomial omega selected =
      Lagrange.basis Finset.univ (fun i : Fin n => omega ^ (i : ℕ)) selected := by
  classical
  rw [rowSelectorPolynomial, rowPolynomial, Lagrange.interpolate_apply]
  rw [Finset.sum_eq_single selected]
  · simp
  · intro row _ hne
    simp [hne]
  · simp

/--
The nodal polynomial of an injectively enumerated size-`n` root-of-unity domain
is the usual vanishing polynomial `Xⁿ - 1`.
-/
theorem domainNodal_eq_vanishing {n : ℕ} {omega : Fp}
    (hn : 0 < n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hroot : omega ^ n = 1) :
    Lagrange.nodal Finset.univ (fun i : Fin n => omega ^ (i : ℕ)) =
      X ^ n - 1 := by
  have hdegree : (1 : Polynomial Fp).degree < (X ^ n : Polynomial Fp).degree := by
    simp [hn]
  apply Polynomial.eq_of_degree_le_of_eval_index_eq Finset.univ hrows.injOn
  · simp
  · rw [Lagrange.degree_nodal, Finset.card_univ, Fintype.card_fin,
      degree_sub_eq_left_of_degree_lt hdegree, degree_pow, degree_X,
      nsmul_eq_mul, mul_one]
  · rw [Lagrange.nodal_monic, leadingCoeff_sub_of_degree_lt hdegree,
      monic_X_pow]
  · intro row hrow
    rw [Lagrange.eval_nodal_at_node
      (s := Finset.univ) (v := fun i : Fin n => omega ^ (i : ℕ)) hrow]
    have hpow : (omega ^ (row : ℕ)) ^ n = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]
    simp [eval_sub, eval_pow, hpow]

/-- The barycentric weight of row `i` in a root-of-unity domain is `ωⁱ / n`. -/
theorem domainNodalWeight_eq {n : ℕ} {omega : Fp}
    (hn : 0 < n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hroot : omega ^ n = 1)
    (hnFp : (n : Fp) ≠ 0)
    (row : Fin n) :
    Lagrange.nodalWeight Finset.univ
        (fun i : Fin n => omega ^ (i : ℕ)) row =
      omega ^ (row : ℕ) / (n : Fp) := by
  have hrowRoot : (omega ^ (row : ℕ)) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ row),
    domainNodal_eq_vanishing hn hrows hroot, derivative_sub,
    derivative_X_pow, derivative_one, sub_zero, eval_mul, eval_C, eval_pow]
  apply inv_eq_of_mul_eq_one_right
  field_simp
  rw [eval_X, mul_comm, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt hn))]
  exact hrowRoot

/--
Away from its selected domain node, a canonical row selector evaluates to the
closed formula used by the deployed verifier.
-/
theorem rowSelectorPolynomial_eval_eq_lagrangeBasisValue
    {n : ℕ} {omega x : Fp}
    (hn : 0 < n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hroot : omega ^ n = 1)
    (hnFp : (n : Fp) ≠ 0)
    (selected : Fin n)
    (hx : x ≠ omega ^ (selected : ℕ)) :
    (rowSelectorPolynomial omega selected).eval x =
      lagrangeBasisValue omega n (x ^ n) x (selected : ℤ) := by
  rw [rowSelectorPolynomial_eq_basis,
    Lagrange.eval_basis_not_at_node (Finset.mem_univ selected) hx,
    domainNodal_eq_vanishing hn hrows hroot,
    domainNodalWeight_eq hn hrows hroot hnFp selected]
  simp only [eval_sub, eval_pow, eval_X, eval_one]
  simp [lagrangeBasisValue, div_eq_mul_inv]
  ring

/-- The same verifier formula, expressed at any rotation naming the selected row. -/
theorem rowSelectorPolynomial_eval_eq_lagrangeBasisValue_of_rotation
    {n : ℕ} {omega x : Fp}
    (hn : 0 < n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hroot : omega ^ n = 1)
    (hnFp : (n : Fp) ≠ 0)
    (selected : Fin n) (rotation : ℤ)
    (hrotation : omega ^ (selected : ℕ) = omega ^ rotation)
    (hx : x ≠ omega ^ rotation) :
    (rowSelectorPolynomial omega selected).eval x =
      lagrangeBasisValue omega n (x ^ n) x rotation := by
  have hxSelected : x ≠ omega ^ (selected : ℕ) := by
    simpa [hrotation] using hx
  rw [rowSelectorPolynomial_eval_eq_lagrangeBasisValue
    hn hrows hroot hnFp selected hxSelected]
  simp only [lagrangeBasisValue]
  rw [show omega ^ (selected : ℤ) = omega ^ (selected : ℕ) by simp,
    hrotation]

/-- The blinding selector is the sum of the row selectors after `lastUsable`. -/
theorem blindSelectorPolynomial_eq_sum {n : ℕ}
    (omega : Fp) (lastUsable : Fin n) :
    blindSelectorPolynomial omega lastUsable =
      ∑ row ∈ (Finset.univ : Finset (Fin n)).filter
          (fun row => lastUsable.val < row.val),
        rowSelectorPolynomial omega row := by
  classical
  rw [blindSelectorPolynomial, rowPolynomial, Lagrange.interpolate_apply]
  simp_rw [rowSelectorPolynomial_eq_basis]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro row _
  by_cases hselected : lastUsable.val < row.val
  · simp [hselected]
  · simp [hselected]

@[simp] theorem rowSelectorPolynomial_eval {n : ℕ}
    {omega : Fp} (selected row : Fin n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ)) :
    (rowSelectorPolynomial omega selected).eval (omega ^ (row : ℕ)) =
      if row = selected then 1 else 0 := by
  rw [rowSelectorPolynomial, rowPolynomial_eval hrows]
  by_cases h : row = selected
  · subst row
    simp
  · simp [h]

@[simp] theorem blindSelectorPolynomial_eval {n : ℕ}
    {omega : Fp} (lastUsable row : Fin n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ)) :
    (blindSelectorPolynomial omega lastUsable).eval (omega ^ (row : ℕ)) =
      if lastUsable.val < row.val then 1 else 0 := by
  rw [blindSelectorPolynomial, rowPolynomial_eval hrows]

/-- `l₀` is nonzero at the first row. -/
theorem firstSelectorPolynomial_nonzero {n : ℕ}
    {omega : Fp} (first : Fin n) (hfirst : (first : ℕ) = 0)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ)) :
    (rowSelectorPolynomial omega first).eval (omega ^ 0) ≠ 0 := by
  have hpow : omega ^ (first : ℕ) = omega ^ 0 := by rw [hfirst]
  rw [← hpow, rowSelectorPolynomial_eval first first hrows]
  norm_num

/-- `l_last` is nonzero at the final usable row. -/
theorem lastSelectorPolynomial_nonzero {n : ℕ}
    {omega : Fp} (lastUsable : Fin n)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ)) :
    (rowSelectorPolynomial omega lastUsable).eval
        (omega ^ (lastUsable : ℕ)) ≠ 0 := by
  rw [rowSelectorPolynomial_eval lastUsable lastUsable hrows]
  norm_num

/--
Before the final usable row, both `l_last` and `l_blind` vanish, so the
permutation/lookup recurrence's active-row multiplier is one.
-/
theorem last_add_blind_active {n : ℕ}
    {omega : Fp} (lastUsable row : Fin n)
    (hrow : (row : ℕ) < lastUsable)
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ)) :
    1 -
      ((rowSelectorPolynomial omega lastUsable).eval (omega ^ (row : ℕ)) +
       (blindSelectorPolynomial omega lastUsable).eval (omega ^ (row : ℕ))) ≠ 0 := by
  rw [rowSelectorPolynomial_eval lastUsable row hrows,
    blindSelectorPolynomial_eval lastUsable row hrows]
  have hne : row ≠ lastUsable := Fin.ne_of_lt hrow
  simp [hne, Nat.not_lt.mpr (Nat.le_of_lt hrow)]

end Zcash.Snark
