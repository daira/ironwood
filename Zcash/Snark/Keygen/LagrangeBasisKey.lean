import Zcash.Snark.Soundness.InstanceCommitment
import Zcash.Snark.Keygen.Pipeline

/-!
# The closed form of the Lagrange basis over the evaluation domain

Over the `2^k` root-of-unity domain, the `i`-th Lagrange basis polynomial has the
closed coefficient form `ℓ_i = n⁻¹ · Σ_t ω^{-i·t} Xᵗ`: it has degree below `n` and
evaluates to `δ_{ij}` at `ω^j` (the geometric sum of a nontrivial root vanishes), so it
is the interpolation of `Pi.single i (1 : Fp)`. This is the coefficient bridge between the
derived Lagrange basis (`derivedUrsGLagrange`, the scaled inverse group-FFT of the
monomial URS) and `LagrangeCommitmentKey.generator_eq`'s commitment form: with the
closed form, each required generator equation becomes a computable commitment identity.
-/

namespace Zcash.Snark.Keygen

open Polynomial

/-- `ℓ_i` in closed coefficient form: `n⁻¹ · Σ_{t < n} ω^{-i·t} Xᵗ`. -/
noncomputable def lagrangeBasisClosed (k : ℕ) (i : Fin (2 ^ k)) : Polynomial Fp :=
  ((2 ^ k : Fp))⁻¹ • ∑ t : Fin (2 ^ k),
    Polynomial.C ((omegaOf k)⁻¹ ^ ((i : ℕ) * (t : ℕ))) * Polynomial.X ^ (t : ℕ)

theorem lagrangeBasisClosed_coeff (k : ℕ) (i : Fin (2 ^ k)) (t : Fin (2 ^ k)) :
    (lagrangeBasisClosed k i).coeff (t : ℕ) =
      (2 ^ k : Fp)⁻¹ * (omegaOf k)⁻¹ ^ ((i : ℕ) * (t : ℕ)) := by
  classical
  rw [lagrangeBasisClosed, Polynomial.coeff_smul, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hbt
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp only [mul_ite, mul_one, mul_zero, ite_eq_right_iff]
    intro hb
    exact absurd (Fin.ext hb.symm) hbt
  · intro ht
    exact absurd (Finset.mem_univ t) ht

theorem lagrangeBasisClosed_natDegree_lt (k : ℕ) (i : Fin (2 ^ k)) :
    (lagrangeBasisClosed k i).natDegree < 2 ^ k := by
  classical
  have hdeg : (lagrangeBasisClosed k i).degree < (2 ^ k : ℕ) := by
    rw [lagrangeBasisClosed]
    refine lt_of_le_of_lt (Polynomial.degree_smul_le _ _) ?_
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe _)]
    intro t _
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _)
      (by exact_mod_cast WithBot.coe_lt_coe.mpr t.isLt)
  by_cases hzero : lagrangeBasisClosed k i = 0
  · rw [hzero, Polynomial.natDegree_zero]
    exact Nat.two_pow_pos k
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hdeg

/-- The closed form evaluates to the Kronecker delta on the domain: at `ω^j` the sum is
geometric in `ω^j·ω^{-i}`, which is `n` at `j = i` and a vanishing nontrivial-root sum
otherwise. -/
theorem lagrangeBasisClosed_eval (k : ℕ) (hk : k ≤ 32) (i j : Fin (2 ^ k)) :
    (lagrangeBasisClosed k i).eval (omegaOf k ^ (j : ℕ)) =
      if j = i then 1 else 0 := by
  classical
  have homega : omegaOf k ≠ 0 :=
    (omegaOf_isPrimitiveRoot k hk).ne_zero (Nat.two_pow_pos k).ne'
  set zeta : Fp := omegaOf k ^ (j : ℕ) * ((omegaOf k)⁻¹) ^ (i : ℕ) with hzeta
  have heval : (lagrangeBasisClosed k i).eval (omegaOf k ^ (j : ℕ)) =
      (2 ^ k : Fp)⁻¹ * ∑ t : Fin (2 ^ k), zeta ^ (t : ℕ) := by
    rw [lagrangeBasisClosed, Polynomial.eval_smul, Polynomial.eval_finsetSum,
      smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      hzeta, mul_pow]
    ring
  rw [heval]
  by_cases hij : j = i
  · subst hij
    have hone : zeta = 1 := by
      rw [hzeta, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ homega)]
    simp only [hone, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    have hn : (2 ^ k : Fp) ≠ 0 := by
      have hcast := domainSize_cast_ne_zero k hk
      rwa [show ((2 ^ k : ℕ) : Fp) = (2 ^ k : Fp) by push_cast; ring] at hcast
    rw [show ((2 ^ k : ℕ) : Fp) = (2 ^ k : Fp) by push_cast; ring,
      inv_mul_cancel₀ hn]
    simp
  · rw [if_neg hij]
    have hz1 : zeta ≠ 1 := by
      rw [hzeta, inv_pow]
      intro h1
      rw [mul_inv_eq_one₀ (pow_ne_zero _ homega)] at h1
      exact hij (omegaOf_powers_injective k hk h1)
    have hzn : zeta ^ (2 ^ k) = 1 := by
      rw [hzeta, inv_pow, mul_pow, ← inv_pow, ← pow_mul, ← pow_mul,
        Nat.mul_comm (j : ℕ), Nat.mul_comm (i : ℕ), pow_mul, pow_mul]
      simp [(omegaOf_isPrimitiveRoot k hk).pow_eq_one]
    have hsum : ∑ t : Fin (2 ^ k), zeta ^ (t : ℕ) = 0 := by
      rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hz1, hzn]
      simp
    rw [hsum, mul_zero]

/-- The interpolated Kronecker column IS the closed form: both have degree below the
node count and agree on every node. -/
theorem rowPolynomial_single_eq_closed (k : ℕ) (hk : k ≤ 32) (i : Fin (2 ^ k)) :
    rowPolynomial (omegaOf k) (Pi.single i (1 : Fp)) = lagrangeBasisClosed k i := by
  classical
  symm
  rw [rowPolynomial]
  apply Lagrange.eq_interpolate_of_eval_eq _ (omegaOf_powers_injective k hk).injOn
  · rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by exact_mod_cast lagrangeBasisClosed_natDegree_lt k i)
  · intro j _
    rw [lagrangeBasisClosed_eval k hk i j, Pi.single_apply]

/-- The Lagrange commitment key's required coefficient vector, in computable closed
form: `ℓ_i`'s `t`-th coefficient is `n⁻¹ · ω^{-i·t}`. -/
theorem polynomialCoefficients_single_closed (k : ℕ) (hk : k ≤ 32)
    (i t : Fin (2 ^ k)) :
    polynomialCoefficients (2 ^ k) (rowPolynomial (omegaOf k) (Pi.single i (1 : Fp))) t =
      (2 ^ k : Fp)⁻¹ * (omegaOf k)⁻¹ ^ ((i : ℕ) * (t : ℕ)) := by
  rw [polynomialCoefficients, rowPolynomial_single_eq_closed k hk i]
  exact lagrangeBasisClosed_coeff k i t

theorem permPolysOf_length (k : ℕ) (cs : Halo2.ConstraintSystem Fp)
    (ops : Halo2.Operations Fp) :
    (permPolysOf k cs ops).length = (permColsOf cs).length := by
  simp [permPolysOf]

theorem permPolysOf_getD_length (k : ℕ) (cs : Halo2.ConstraintSystem Fp)
    (ops : Halo2.Operations Fp) (c : ℕ) (hc : c < (permColsOf cs).length) :
    ((permPolysOf k cs ops).getD c []).length = 2 ^ k := by
  have hcl : c < (permPolysOf k cs ops).length := by
    rw [permPolysOf_length]; exact hc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl]
  simp [permPolysOf]

/-- **The derived σ commitments are Lagrange-key commitments of the derived σ rows**:
the executable Pippenger pipeline (with halo2's default blind, the `w` generator) equals
the abstract prefix-key commitment. The two hypotheses are the per-URS setup facts —
the derived basis length and the generator identities, native-tier at a concrete URS
through the closed coefficient form (`polynomialCoefficients_single_closed`). -/
theorem permutationCommitmentsOf_getD_eq_commitInstance
    {G : Type} [AddCommGroup G] [Module Fp G] [Inhabited G]
    (urs : URS G) (cs : Halo2.ConstraintSystem Fp) (ops : Halo2.Operations Fp)
    (hlen : (derivedUrsGLagrange urs).length = 2 ^ urs.k)
    (hprefix : ∀ i : Fin (2 ^ urs.k), (i : ℕ) < (derivedUrsGLagrange urs).length →
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial (omegaOf urs.k) (Pi.single i (1 : Fp)))))
    (c : ℕ) (hc : c < (permColsOf cs).length) :
    (permutationCommitmentsOf urs.w (derivedUrsGLagrange urs) urs.k cs ops).getD c 0 =
      (LagrangeCommitmentKey.ofPrefix urs (omegaOf urs.k) (derivedUrsGLagrange urs)
          hprefix).commitInstance
        ((permPolysOf urs.k cs ops).getD c []) 1 := by
  classical
  have hrowlen : ((permPolysOf urs.k cs ops).getD c []).length = 2 ^ urs.k :=
    permPolysOf_getD_length urs.k cs ops c hc
  rw [LagrangeCommitmentKey.ofPrefix_commitInstance_eq urs (omegaOf urs.k) _ hprefix _ 1
    (by rw [hrowlen, hlen]) (by rw [hrowlen])]
  have hcl : c < (permPolysOf urs.k cs ops).length := by
    rw [permPolysOf_length]; exact hc
  have hget : ((permPolysOf urs.k cs ops).map
      (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow urs.w
        (derivedUrsGLagrange urs))).getD c 0 =
      Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow urs.w
        (derivedUrsGLagrange urs) ((permPolysOf urs.k cs ops).getD c []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hcl,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcl]
    rfl
  rw [permutationCommitmentsOf, List.parMap_eq_map, hget,
    Fast.Msm.commitLagrangeFastWith_eq Fast.Msm.defaultWindow
      (by norm_num [Fast.Msm.defaultWindow]) urs.w]
  rw [← LagrangeCommitmentKey.commitPrefixNat_eq_commitPrefix,
    Fast.Msm.commitLagrangeSpec, LagrangeCommitmentKey.commitPrefixNat]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul Fp ((1 : Fp).val) urs.w,
    ZMod.natCast_rightInverse (1 : Fp), one_smul]

/-- The `ofPrefix` setup obligation in fully computable form: the noncomputable
interpolation coefficients are replaced by the closed form, so a concrete URS can
discharge the per-generator identities by native evaluation. -/
theorem ofPrefix_setup_of_closed {G : Type} [AddCommGroup G] [Module Fp G]
    [Inhabited G] (urs : URS G) (hk : urs.k ≤ 32)
    (hgen : ∀ i : Fin (2 ^ urs.k),
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs fun t : Fin (2 ^ urs.k) =>
          (2 ^ urs.k : Fp)⁻¹ * (omegaOf urs.k)⁻¹ ^ ((i : ℕ) * (t : ℕ))) :
    ∀ i : Fin (2 ^ urs.k), (i : ℕ) < (derivedUrsGLagrange urs).length →
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial (omegaOf urs.k) (Pi.single i (1 : Fp)))) := by
  intro i _
  rw [hgen i]
  congr 1
  funext t
  rw [polynomialCoefficients_single_closed urs.k hk i t]

end Zcash.Snark.Keygen
