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
