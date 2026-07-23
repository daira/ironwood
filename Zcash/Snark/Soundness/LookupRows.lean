import Mathlib
import Zcash.Snark.Soundness.ConstraintSatisfaction
import Zcash.Snark.Soundness.LookupAssembly
import Zcash.Snark.Soundness.PermutationRows

/-!
# The verifier's lookup constraints, read row by row

This is the lookup counterpart of `PermutationRows`.  It reads the five polynomials emitted by
`lookupExpressions` on the evaluation domain:

* the first two pin the running product at its endpoints;
* the third is the product recurrence;
* the fourth pins the first permuted-input value to the first permuted-table value;
* the fifth says each later permuted-input value either matches the table at that row or repeats
  the preceding input value.

The last two facts feed `Lookup.run_structure`; the first three telescope through
`RunningProduct.prod_eq_or_factor_eq_zero`.  The exceptional zero-factor branch is retained.
-/

namespace Zcash.Snark

open Polynomial Finset

/-- Polynomial-valued lookup evaluations.  The next product and previous permuted-input openings
are represented by composing with `ω X` and `ω⁻¹ X`, respectively. -/
noncomputable def lookupEvalPolys (omega : Fp) (z a s : Polynomial Fp) :
    LookupEval (Polynomial Fp) where
  productEval := z
  productNextEval := z.comp (C omega * X)
  permutedInputEval := a
  permutedInputInvEval := a.comp (C omega⁻¹ * X)
  permutedTableEval := s

@[simp] theorem lookupEvalPolys_productEval (omega : Fp) (z a s : Polynomial Fp) :
    (lookupEvalPolys omega z a s).productEval = z := rfl

@[simp] theorem lookupEvalPolys_permutedInputEval (omega : Fp) (z a s : Polynomial Fp) :
    (lookupEvalPolys omega z a s).permutedInputEval = a := rfl

@[simp] theorem lookupEvalPolys_permutedTableEval (omega : Fp) (z a s : Polynomial Fp) :
    (lookupEvalPolys omega z a s).permutedTableEval = s := rfl

/-- The lookup product's next evaluation is the next domain row. -/
theorem eval_lookupEvalPolys_productNextEval (omega : Fp) (z a s : Polynomial Fp) (i : ℕ) :
    ((lookupEvalPolys omega z a s).productNextEval).eval (omega ^ i)
      = z.eval (omega ^ (i + 1)) := by
  rw [lookupEvalPolys, eval_comp_rotate, pow_succ, mul_comm]

/-- On every non-first row, the inverse-rotated lookup input is the preceding row. -/
theorem eval_lookupEvalPolys_permutedInputInvEval_succ
    (omega : Fp) (z a s : Polynomial Fp) (homega : omega ≠ 0) (i : ℕ) :
    ((lookupEvalPolys omega z a s).permutedInputInvEval).eval (omega ^ (i + 1))
      = a.eval (omega ^ i) := by
  rw [lookupEvalPolys, eval_comp_rotate, pow_succ]
  congr 1
  field_simp

/-- Constraint three, evaluated at an active row, is the lookup running-product recurrence. -/
theorem lookup_product_row_recurrence
    (omega beta gamma : Fp) (z a s input table lLastP lBlindP : Polynomial Fp) {n : ℕ}
    (hdvd : (X ^ n - 1 : Polynomial Fp) ∣
      (z.comp (C omega * X) * (a + C beta) * (s + C gamma)
        - z * (input + C beta) * (table + C gamma))
        * (1 - (lLastP + lBlindP)))
    {i : ℕ} (hpow : (omega ^ i) ^ n = 1)
    (hactive : 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0) :
    z.eval (omega ^ (i + 1)) * (a.eval (omega ^ i) + beta)
        * (s.eval (omega ^ i) + gamma)
      = z.eval (omega ^ i) * (input.eval (omega ^ i) + beta)
        * (table.eval (omega ^ i) + gamma) := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hpow
  simp only [eval_mul, eval_sub, eval_add, eval_C, eval_one, eval_comp_rotate,
    mul_comm omega] at hzero
  rcases mul_eq_zero.mp hzero with hrec | hact
  · exact sub_eq_zero.mp hrec
  · exact absurd hact hactive

/-- Constraint four pins the first permuted-input value to the first permuted-table value. -/
theorem lookup_run_start_of_dvd
    (a s l0P : Polynomial Fp) {n : ℕ}
    (hdvd : (X ^ n - 1 : Polynomial Fp) ∣ l0P * (a - s))
    {r : Fp} (hpow : r ^ n = 1) (hl0 : l0P.eval r ≠ 0) :
    a.eval r = s.eval r := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hpow
  rw [eval_mul, eval_sub] at hzero
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hl0)

/-- Constraint five says an active permuted-input row either matches the table row or repeats its
predecessor. -/
theorem lookup_run_step_of_dvd
    (a s aPrev lLastP lBlindP : Polynomial Fp) {n : ℕ}
    (hdvd : (X ^ n - 1 : Polynomial Fp) ∣
      (a - s) * (a - aPrev) * (1 - (lLastP + lBlindP)))
    {r : Fp} (hpow : r ^ n = 1)
    (hactive : 1 - (lLastP.eval r + lBlindP.eval r) ≠ 0) :
    a.eval r = s.eval r ∨ a.eval r = aPrev.eval r := by
  have hzero := eval_eq_zero_of_dvd_vanishing hdvd hpow
  simp only [eval_mul, eval_sub, eval_one, eval_add] at hzero
  have hpairs := (mul_eq_zero.mp hzero).resolve_right hactive
  rcases mul_eq_zero.mp hpairs with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- The deployed run constraints imply the semantic run structure over all active lookup rows. -/
theorem lookup_run_structure_of_dvd
    (omega : Fp) (a s l0P lLastP lBlindP : Polynomial Fp) {n u : ℕ}
    (homega : omega ≠ 0)
    (hstart : (X ^ n - 1 : Polynomial Fp) ∣ l0P * (a - s))
    (hstep : (X ^ n - 1 : Polynomial Fp) ∣
      (a - s) * (a - a.comp (C omega⁻¹ * X)) * (1 - (lLastP + lBlindP)))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < u + 1,
      1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) :
    ∀ i : Fin (u + 1), ∃ j : Fin (u + 1),
      a.eval (omega ^ (i : ℕ)) = s.eval (omega ^ (j : ℕ)) := by
  have h0 : a.eval (omega ^ (0 : ℕ)) = s.eval (omega ^ (0 : ℕ)) :=
    lookup_run_start_of_dvd a s l0P hstart (hrow 0) hl0
  apply run_structure
    (fun i : Fin (u + 1) => a.eval (omega ^ (i : ℕ)))
    (fun i : Fin (u + 1) => s.eval (omega ^ (i : ℕ)))
    0 h0 (Or.inl h0)
  intro i
  have hs := lookup_run_step_of_dvd a s (a.comp (C omega⁻¹ * X)) lLastP lBlindP
    hstep (hrow (i + 1)) (hactive (i + 1) (by omega))
  rcases hs with hs | ha
  · exact Or.inl hs
  · exact Or.inr (by
      simpa using ha.trans
        (eval_lookupEvalPolys_permutedInputInvEval_succ omega 0 a s homega i))

/-- Constraints one through three telescope to the whole-column lookup product identity, or expose
an input/table factor that vanished in the legitimate `z`-ends-at-zero branch. -/
theorem lookup_product_eq_or_factor_eq_zero
    (omega beta gamma : Fp) (z a s input table l0P lLastP lBlindP : Polynomial Fp)
    {n m : ℕ}
    (hproduct : (X ^ n - 1 : Polynomial Fp) ∣
      (z.comp (C omega * X) * (a + C beta) * (s + C gamma)
        - z * (input + C beta) * (table + C gamma))
        * (1 - (lLastP + lBlindP)))
    (hstart : (X ^ n - 1 : Polynomial Fp) ∣ l0P * (1 - z))
    (hend : (X ^ n - 1 : Polynomial Fp) ∣ lLastP * (z ^ 2 - z))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < m,
      1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0)
    (hlast : lLastP.eval (omega ^ m) ≠ 0) :
    ((∏ i ∈ range m, (a.eval (omega ^ i) + beta) * (s.eval (omega ^ i) + gamma))
        = ∏ i ∈ range m,
          (input.eval (omega ^ i) + beta) * (table.eval (omega ^ i) + gamma))
      ∨ ∃ i ∈ range m,
          (input.eval (omega ^ i) + beta) * (table.eval (omega ^ i) + gamma) = 0 := by
  apply prod_eq_or_factor_eq_zero
    (fun i => z.eval (omega ^ i))
    (fun i => (input.eval (omega ^ i) + beta) * (table.eval (omega ^ i) + gamma))
    (fun i => (a.eval (omega ^ i) + beta) * (s.eval (omega ^ i) + gamma))
  · intro i hi
    simpa [mul_assoc] using
      lookup_product_row_recurrence omega beta gamma z a s input table lLastP lBlindP
        hproduct (hrow i) (hactive i hi)
  · exact running_product_start hstart (hrow 0) hl0
  · exact running_product_end (by simpa [mul_comm] using hend) (hrow m) hlast

end Zcash.Snark
