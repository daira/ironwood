import Mathlib
import Zcash.Snark.Soundness.Constraints

/-!
# Splitting the combined constraint check back into its parts

The verifier never checks the constraints one at a time. It folds the whole list by the challenge
`y` — `acc·y + v`, halo2's `vanishing/verifier.rs` — and checks the single result. The soundness
argument needs the opposite direction: from "the fold is divisible by `Xⁿ − 1`" conclude "every
constraint is", because the permutation and lookup arguments reason about individual rows.

That step is not free. The fold is a polynomial in `y` whose coefficients are the constraints, so a
`y` that happens to be one of its roots hides a violation. This module makes the price explicit:

* `foldPoly` — the fold read as a polynomial in `y`, and `eval_foldPoly` relating it to the fold.
* `foldPoly_eq_zero_iff` — it is the zero polynomial exactly when every entry is zero.
* `foldl_modByMonic` — the fold commutes with reduction mod `Xⁿ − 1`, so the combined check says the
  reduced constraints fold to zero.
* `foldSplitWitness` — one polynomial in `y` per `X`-coefficient of those reduced constraints. If
  some constraint does not vanish on the domain, one of these is nonzero and `y` must root it.
* `constraints_dvd_of_good_y` — avoiding those roots forces every constraint to vanish on the whole
  domain. This is the `y`-side analogue of `hgood`, priced the same way: each witness excludes fewer
  than `length` of the `p` challenges (`szBadSet_foldSplitWitness_card_le`).
-/

namespace Zcash.Snark

open Polynomial Finset

/-- The `acc·y + v` fold read as a polynomial in `y`: `[c₀, …, c_{m-1}]` becomes
`c₀·y^{m-1} + ⋯ + c_{m-1}`. -/
noncomputable def foldPoly (l : List Fp) : Polynomial Fp :=
  l.foldl (fun acc v => acc * X + C v) 0

@[simp] theorem foldPoly_nil : foldPoly [] = 0 := rfl

/-- The fold grows from the right: appending `v` multiplies by `y` and adds. -/
theorem foldPoly_concat (l : List Fp) (v : Fp) :
    foldPoly (l ++ [v]) = foldPoly l * X + C v := by
  simp [foldPoly, List.foldl_append]

/-- Evaluating the fold polynomial at `y` is the verifier's fold. -/
theorem eval_foldPoly (l : List Fp) (y : Fp) :
    (foldPoly l).eval y = l.foldl (fun acc v => acc * y + v) 0 := by
  suffices h : ∀ (t : List Fp) (acc : Polynomial Fp),
      (t.foldl (fun acc v => acc * X + C v) acc).eval y
        = t.foldl (fun acc v => acc * y + v) (acc.eval y) by
    simpa [foldPoly] using h l 0
  intro t
  induction t with
  | nil => intro acc; simp
  | cons a s ih =>
      intro acc
      simp only [List.foldl_cons]
      have h := ih (acc * X + C a)
      simp only [eval_add, eval_mul, eval_C, eval_X] at h
      exact h

/-- The fold polynomial has degree below the list length, so it is determined by fewer than
`length` challenges. -/
theorem natDegree_foldPoly_lt {l : List Fp} (hl : l ≠ []) : (foldPoly l).natDegree < l.length := by
  induction l using List.reverseRecOn with
  | nil => exact absurd rfl hl
  | append_singleton t v ih =>
      rw [foldPoly_concat, List.length_append, List.length_singleton]
      rcases eq_or_ne t [] with rfl | ht
      · simp [foldPoly]
      · refine Nat.lt_succ_of_le ((natDegree_add_le _ _).trans (max_le ?_ ?_))
        · exact (natDegree_mul_le).trans (by simpa using Nat.succ_le_of_lt (ih ht))
        · exact (natDegree_C v).le.trans (Nat.zero_le _)

/-- The fold polynomial is zero exactly when every entry is. One `y` cannot distinguish these, which
is why splitting the check costs a bad set. -/
theorem foldPoly_eq_zero_iff (l : List Fp) : foldPoly l = 0 ↔ ∀ v ∈ l, v = 0 := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton t v ih =>
      rw [foldPoly_concat]
      constructor
      · intro h
        have hv : v = 0 := by
          have := congrArg (Polynomial.coeff · 0) h
          simpa [coeff_add, coeff_C, mul_coeff_zero] using this
        have ht : foldPoly t = 0 := by
          rw [hv, map_zero, add_zero] at h
          exact (mul_eq_zero.mp h).resolve_right X_ne_zero
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact (ih.mp ht) u hu
        · simpa [List.mem_singleton.mp hu] using hv
      · intro h
        have hv : v = 0 := h v (by simp)
        have ht : foldPoly t = 0 := ih.mpr fun u hu => h u (by simp [hu])
        simp [hv, ht]


/-! ## Reducing modulo the vanishing polynomial

A constraint holds on the whole evaluation domain exactly when `Xⁿ − 1` divides it, which for a
monic divisor is exactly "its remainder is `0`". The fold commutes with taking that remainder, so
the combined check says the remainders themselves fold to zero — and each `X`-coefficient of that
statement is one polynomial equation in `y`. -/

/-- `Xⁿ − 1` is monic for `n ≠ 0`, so remainders against it are well behaved. -/
theorem monic_X_pow_sub_one {n : ℕ} (hn : n ≠ 0) : (X ^ n - 1 : Polynomial Fp).Monic := by
  simpa using monic_X_pow_sub_C (1 : Fp) hn

/-- A constraint vanishes on the domain exactly when its remainder is zero. -/
theorem dvd_iff_modByMonic_eq_zero {n : ℕ} (hn : n ≠ 0) (c : Polynomial Fp) :
    (X ^ n - 1 : Polynomial Fp) ∣ c ↔ c %ₘ (X ^ n - 1) = 0 :=
  (modByMonic_eq_zero_iff_dvd (monic_X_pow_sub_one hn)).symm

/-- The `y` fold commutes with reduction: folding and then reducing is reducing and then folding. -/
theorem foldl_modByMonic (cs : List (Polynomial Fp)) (y : Fp) {r : Polynomial Fp} (hr : r.Monic) :
    (cs.foldl (fun acc q => acc * C y + q) 0) %ₘ r
      = (cs.map (fun c => c %ₘ r)).foldl (fun acc q => acc * C y + q) 0 := by
  suffices h : ∀ (t : List (Polynomial Fp)) (acc : Polynomial Fp),
      (t.foldl (fun acc q => acc * C y + q) acc) %ₘ r
        = (t.map (fun c => c %ₘ r)).foldl (fun acc q => acc * C y + q) (acc %ₘ r) by
    simpa [zero_modByMonic] using h cs 0
  intro t
  induction t with
  | nil => intro acc; simp
  | cons a u ih =>
      intro acc
      have hstep : (acc * C y + a) %ₘ r = (acc %ₘ r) * C y + a %ₘ r := by
        rw [add_modByMonic, mul_comm acc (C y), ← smul_eq_C_mul, smul_modByMonic,
          smul_eq_C_mul, mul_comm]
      simpa [hstep] using ih (acc * C y + a)

/-- The `j`-th coefficient of the reduced constraints, folded as a polynomial in `y`. The combined
check forces `y` to be one of its roots, so a nonzero witness is what makes splitting cost
something. -/
noncomputable def foldSplitWitness (cs : List (Polynomial Fp)) (n j : ℕ) : Polynomial Fp :=
  foldPoly (cs.map (fun c => (c %ₘ (X ^ n - 1)).coeff j))

/-- The witness has degree below the list length, so it excludes at most `length − 1` challenges. -/
theorem natDegree_foldSplitWitness_lt {cs : List (Polynomial Fp)} (hcs : cs ≠ []) (n j : ℕ) :
    (foldSplitWitness cs n j).natDegree < cs.length := by
  have hne : cs.map (fun c => (c %ₘ (X ^ n - 1)).coeff j) ≠ [] := by
    simpa using hcs
  simpa using natDegree_foldPoly_lt hne

/-- The price of splitting: each coefficient's witness excludes at most `length − 1` challenges. -/
theorem szBadSet_foldSplitWitness_card_le {cs : List (Polynomial Fp)} (hcs : cs ≠ []) (n j : ℕ) :
    (szBadSet (foldSplitWitness cs n j)).card < cs.length :=
  lt_of_le_of_lt (szBadSet_card_le _) (natDegree_foldSplitWitness_lt hcs n j)

/-- A constraint that does not vanish on the domain makes some coefficient's witness nonzero. -/
theorem exists_foldSplitWitness_ne_zero {cs : List (Polynomial Fp)} {n : ℕ} (hn : n ≠ 0)
    {c : Polynomial Fp} (hmem : c ∈ cs) (hdvd : ¬ (X ^ n - 1 : Polynomial Fp) ∣ c) :
    ∃ j, foldSplitWitness cs n j ≠ 0 := by
  have hres : c %ₘ (X ^ n - 1) ≠ 0 := fun h => hdvd ((dvd_iff_modByMonic_eq_zero hn c).mpr h)
  obtain ⟨j, hj⟩ : ∃ j, (c %ₘ (X ^ n - 1)).coeff j ≠ 0 := by
    by_contra hall
    exact hres (Polynomial.ext fun j => by simpa using not_exists.mp hall j)
  refine ⟨j, fun h => hj ?_⟩
  exact (foldPoly_eq_zero_iff _).mp h _ (List.mem_map_of_mem hmem)

/-- The combined check forces `y` to root every coefficient's witness. -/
theorem eval_foldSplitWitness_eq_zero {cs : List (Polynomial Fp)} {hq : Polynomial Fp} {n : ℕ}
    (hn : n ≠ 0) {y : Fp}
    (hfold : cs.foldl (fun acc q => acc * C y + q) 0 = hq * (X ^ n - 1)) (j : ℕ) :
    (foldSplitWitness cs n j).eval y = 0 := by
  have hmonic := monic_X_pow_sub_one hn
  have hzero : (cs.map (fun c => c %ₘ (X ^ n - 1))).foldl (fun acc q => acc * C y + q) 0 = 0 := by
    rw [← foldl_modByMonic cs y hmonic, hfold]
    exact (modByMonic_eq_zero_iff_dvd hmonic).mpr ⟨hq, mul_comm _ _⟩
  have hcoeff : (List.foldl (fun acc q => acc * C y + q) 0
      (cs.map (fun c => c %ₘ (X ^ n - 1)))).coeff j = 0 := by
    rw [hzero, coeff_zero]
  rw [foldSplitWitness, eval_foldPoly]
  have key : ∀ (t : List (Polynomial Fp)) (acc : Polynomial Fp),
      ((t.map (fun c => c %ₘ (X ^ n - 1))).foldl (fun acc q => acc * C y + q) acc).coeff j
        = (t.map (fun c => (c %ₘ (X ^ n - 1)).coeff j)).foldl (fun acc v => acc * y + v)
            (acc.coeff j) := by
    intro t
    induction t with
    | nil => intro acc; simp
    | cons a u ih =>
        intro acc
        simpa [coeff_add, coeff_C_mul, mul_comm] using ih (acc * C y + a %ₘ (X ^ n - 1))
  have hkey := key cs 0
  simp only [coeff_zero] at hkey
  rw [← hkey, hcoeff]

/-- **Splitting the combined check.** A challenge outside every coefficient witness's root set turns
the single folded identity into one identity per constraint: every constraint vanishes on the whole
evaluation domain. This is the `y`-side analogue of `hgood`, priced by
`szBadSet_foldSplitWitness_card_le`, and it is what lets the permutation and lookup arguments talk
about individual rows. -/
theorem constraints_dvd_of_good_y (cs : List (Polynomial Fp)) (hq : Polynomial Fp) {n : ℕ}
    (hn : n ≠ 0) {y : Fp}
    (hfold : cs.foldl (fun acc q => acc * C y + q) 0 = hq * (X ^ n - 1))
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness cs n j)) :
    ∀ c ∈ cs, (X ^ n - 1 : Polynomial Fp) ∣ c := by
  intro c hmem
  by_contra hdvd
  obtain ⟨j, hj⟩ := exists_foldSplitWitness_ne_zero hn hmem hdvd
  exact (not_mem_szBadSet.mp (hgoodY j)) hj (eval_foldSplitWitness_eq_zero hn hfold j)

end Zcash.Snark
