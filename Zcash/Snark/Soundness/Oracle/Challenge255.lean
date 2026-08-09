import Mathlib.Data.Int.CardIntervalMod
import Zcash.Snark.Soundness.Oracle.Model

/-!
# Exact bias of the deployed challenge conversion

Halo2's `Challenge255::new` turns one 64-byte squeeze into a field challenge: the digest is read
as a 512-bit integer and reduced modulo `p`.  The security layer prices squeezes as exactly
uniform (`uniformChallenge`); this module prices the gap between that ideal and the deployed
conversion, assuming only that the digest itself is uniform.  Idealizing Blake2b as a uniform
512-bit digest stays external (`Oracle/Model.lean`).

Write `2 ^ 512 = challengeQuot * p + challengeRem`.  Reduction sends `challengeQuot + 1` digests
to each of the first `challengeRem` field elements and `challengeQuot` to the rest
(`challenge255_apply`), so an event's probability exceeds its uniform value by at most
`challengeRem * (p - challengeRem) / (p * 2 ^ 512)` — attained by the heavy residues, so the
constant is exact; it is below `2 ^ -260` (`challenge255Bias_le`).  `challenge255_eventBias_le`
states the bound as the `PMFEventBiasLE` premise that `event_measure_le_of_bias` and the
work-factor capstone's bias conjunct consume; `challenge255_badSet_le` runs one squeeze through
that transport.
-/

namespace Zcash.Snark

open scoped ENNReal
open Zcash.Arithmetic (scalarFieldOrder card_Fp)

/-- The digest space of one squeeze: `Challenge255` reads a 64-byte digest as a 512-bit integer. -/
def challengeDigestCard : ℕ := 2 ^ 512

instance : NeZero challengeDigestCard :=
  ⟨by unfold challengeDigestCard; exact pow_ne_zero _ (by decide)⟩

/-- Digests landing on each field element before the remainder is spent: `2 ^ 512 / p`. -/
def challengeQuot : ℕ := challengeDigestCard / scalarFieldOrder

/-- The heavy prefix: field elements below `challengeRem` receive one extra digest. -/
def challengeRem : ℕ := challengeDigestCard % scalarFieldOrder

/-- One deployed squeeze under an ideal digest: a uniform 512-bit integer reduced modulo `p`. -/
noncomputable def challenge255 : PMF Fp :=
  PMF.map (fun n : Fin challengeDigestCard => ((n : ℕ) : Fp))
    (PMF.uniformOfFintype (Fin challengeDigestCard))

/-- The exact one-sided distance from uniform: `challengeRem * (p - challengeRem)` over
`p * 2 ^ 512`, about `2 ^ -260.99`. -/
noncomputable def challenge255Bias : ℝ≥0∞ :=
  ((challengeRem * (scalarFieldOrder - challengeRem) : ℕ) : ℝ≥0∞) /
    ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞)

/-- Each fiber of the reduction has `challengeQuot` digests, plus one on the heavy prefix. -/
private theorem challenge255_fiberCard (x : Fp) :
    (Finset.univ.filter fun n : Fin challengeDigestCard => x = ((n : ℕ) : Fp)).card
      = challengeQuot + if x.val < challengeRem then 1 else 0 := by
  have hp : 0 < scalarFieldOrder := Nat.pos_of_ne_zero (NeZero.ne _)
  have hcard :
      (Finset.univ.filter fun n : Fin challengeDigestCard => x = ((n : ℕ) : Fp)).card
        = ((Finset.range challengeDigestCard).filter
            fun m : ℕ => x = ((m : ℕ) : Fp)).card := by
    refine Finset.card_bij (fun n _ => (n : ℕ)) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr a.isLt, ha⟩
    · intro a _ b _ hab
      exact Fin.val_injective hab
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      exact ⟨⟨m, hm.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm.2⟩, rfl⟩
  have hpred : ∀ m : ℕ, (x = ((m : ℕ) : Fp)) ↔ m ≡ x.val [MOD scalarFieldOrder] := by
    intro m
    have h1 : (x = ((m : ℕ) : Fp)) ↔ x.val ≡ m [MOD scalarFieldOrder] := by
      rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    exact h1.trans ⟨Nat.ModEq.symm, Nat.ModEq.symm⟩
  rw [hcard, Finset.filter_congr fun m _ => hpred m, ← Nat.count_eq_card_filter_range,
    Nat.count_modEq_card (hr := hp), Nat.mod_eq_of_lt (ZMod.val_lt x)]
  rfl

/-- The law of one converted squeeze: `challengeQuot + 1` weight on the heavy prefix,
`challengeQuot` elsewhere, over the digest count. -/
theorem challenge255_apply (x : Fp) :
    challenge255 x
      = ((challengeQuot + if x.val < challengeRem then 1 else 0 : ℕ) : ℝ≥0∞)
          / (challengeDigestCard : ℕ) := by
  classical
  unfold challenge255
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, challenge255_fiberCard x,
    div_eq_mul_inv]

private theorem challenge255_key_le {p q r N s h : ℕ} (hN : N = p * q + r) (hrp : r ≤ p)
    (hhr : h ≤ r) (hhs : h ≤ s) :
    p * (q * s + h) ≤ s * N + r * (p - r) := by
  have hsplit : (p - r) * h + r * h = p * h := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hrp]
  have hcore : p * h ≤ r * s + r * (p - r) :=
    calc p * h = (p - r) * h + r * h := hsplit.symm
      _ ≤ (p - r) * r + r * s :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hhr) (Nat.mul_le_mul_left _ hhs)
      _ = r * s + r * (p - r) := by rw [Nat.mul_comm (p - r) r]; exact Nat.add_comm _ _
  calc p * (q * s + h) = p * q * s + p * h := by ring
    _ ≤ p * q * s + (r * s + r * (p - r)) := Nat.add_le_add_left hcore _
    _ = s * (p * q + r) + r * (p - r) := by ring
    _ = s * N + r * (p - r) := by rw [hN]

/-- **The deployed conversion overshoots uniform by at most the exact reduction bias.**  This is
the `PMFEventBiasLE` premise of `event_measure_le_of_bias` and of the work-factor capstone's bias
conjunct, instantiated at the deployed `Challenge255` law for one squeeze. -/
theorem challenge255_eventBias_le :
    PMFEventBiasLE challenge255 uniformChallenge challenge255Bias := by
  classical
  intro S
  have hS : S = ↑S.toFinset := (Set.coe_toFinset S).symm
  set T : Finset Fp := S.toFinset
  have hp0 : ((scalarFieldOrder : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hN0 : ((challengeDigestCard : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  set h : ℕ := (T.filter fun x : Fp => x.val < challengeRem).card with hh
  have hH_le_r : h ≤ challengeRem := by
    have hle : (T.filter fun x : Fp => x.val < challengeRem).card
        ≤ (Finset.range challengeRem).card := by
      refine Finset.card_le_card_of_injOn ZMod.val ?_ ?_
      · intro x hx
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
      · intro a _ b _ hab
        rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val b, hab]
    simpa [hh] using hle.trans_eq (Finset.card_range _)
  have hH_le_s : h ≤ T.card := Finset.card_filter_le _ _
  have hsum : ∑ x ∈ T, (challengeQuot + if x.val < challengeRem then 1 else 0)
      = challengeQuot * T.card + h := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm, hh,
      Finset.card_filter]
  have lhs_eq : challenge255.toOuterMeasure S
      = ((challengeQuot * T.card + h : ℕ) : ℝ≥0∞) / (challengeDigestCard : ℕ) := by
    rw [hS, PMF.toOuterMeasure_apply_finset,
      Finset.sum_congr rfl fun x _ => challenge255_apply x]
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Nat.cast_sum, hsum]
  have rhs_eq : uniformChallenge.toOuterMeasure S
      = ((T.card : ℕ) : ℝ≥0∞) / (scalarFieldOrder : ℕ) := by
    rw [hS, uniformChallenge_badSet, card_Fp]
  rw [lhs_eq, rhs_eq]
  unfold challenge255Bias
  have e1 : ((challengeQuot * T.card + h : ℕ) : ℝ≥0∞) / (challengeDigestCard : ℕ)
      = ((scalarFieldOrder * (challengeQuot * T.card + h) : ℕ) : ℝ≥0∞)
          / ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    exact (ENNReal.mul_div_mul_left _ _ hp0 (ENNReal.natCast_ne_top _)).symm
  have e2 : ((T.card : ℕ) : ℝ≥0∞) / (scalarFieldOrder : ℕ)
      = ((T.card * challengeDigestCard : ℕ) : ℝ≥0∞)
          / ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    exact (ENNReal.mul_div_mul_right _ _ hN0 (ENNReal.natCast_ne_top _)).symm
  rw [e1, e2, ENNReal.div_add_div_same, ← Nat.cast_add]
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  have hp : 0 < scalarFieldOrder := Nat.pos_of_ne_zero (NeZero.ne scalarFieldOrder)
  unfold challengeQuot challengeRem at hH_le_r ⊢
  exact challenge255_key_le
    (Nat.div_add_mod challengeDigestCard scalarFieldOrder).symm
    (Nat.mod_lt challengeDigestCard hp).le hH_le_r hH_le_s

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 8192 in
/-- The exact bias is below `2 ^ -260`: `challengeRem * (p - challengeRem) * 2 ^ 260` fits under
`p * 2 ^ 512`, checked by kernel arithmetic. -/
theorem challenge255Bias_le : challenge255Bias ≤ 1 / 2 ^ 260 := by
  have hnum : challengeRem * (scalarFieldOrder - challengeRem) * 2 ^ 260
      ≤ scalarFieldOrder * challengeDigestCard := by decide
  have hnum' : ((challengeRem * (scalarFieldOrder - challengeRem) : ℕ) : ℝ≥0∞) * 2 ^ 260
      ≤ ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hnum
  have hden0 : ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))
  have hdentop : ((scalarFieldOrder * challengeDigestCard : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have h2pow0 : ((2 : ℝ≥0∞) ^ 260) ≠ 0 := pow_ne_zero _ (by simp)
  have h2powtop : ((2 : ℝ≥0∞) ^ 260) ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  unfold challenge255Bias
  rw [ENNReal.div_le_iff_le_mul (Or.inl hden0) (Or.inl hdentop), one_div,
    ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl h2pow0) (Or.inl h2powtop)]
  exact hnum'

/-- One squeeze through the transport theorem: a bad set's probability under the deployed
conversion is its uniform probability plus the exact bias. -/
theorem challenge255_badSet_le (bad : Finset Fp) :
    challenge255.toOuterMeasure ↑bad
      ≤ (bad.card : ℝ≥0∞) / Fintype.card Fp + challenge255Bias :=
  event_measure_le_of_bias challenge255_eventBias_le _
    (le_of_eq (uniformChallenge_badSet bad))

end Zcash.Snark
