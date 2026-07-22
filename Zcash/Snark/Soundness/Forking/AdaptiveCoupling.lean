import Zcash.Snark.Soundness.Forking.Adversary.Algebraic

/-!
# The adaptive random-oracle coupling for the multiopen challenges

The multiopen budget (`Soundness.Multiopen.BudgetedExtraction`) prices its events over the joint
uniform draw of the four fresh challenges `(x₁, x₂, x₃, x₄)`. The computed adversary, however,
*reads* those challenges from its oracle table at transcript prefixes of its own output
(`computedDeployedAlgebraicInstance`: `ν i = O (algebraicFullPrefixesPre init (A.run O) i)`), and a
`Q`-query machine can grind — steer its committed prefixes toward favourable answers. So the honest
coupling between the coin draw and the challenge draw is *not* a distribution equality: it is a
query-loss bound, exactly as in the `(Q+k)·3/|F|` and `(Q+1)/|F|` terms of the existing AGM
composition.

This module proves that bound for *joint four-challenge events of small measure*:

* **The peeling ladder** (`peelG1`–`peelG4`, `peelEsc`, `peel_decomposition`): a point of a set
  `σ ⊆ F⁴` of measure at most `s ≤ τ⁴` always exposes one coordinate lying in an escape set of
  measure at most `τ`, determined by the *earlier* coordinates alone. This is the standard
  multi-level forking degradation (the `k`-th-root loss), made pointwise and constructive.
* **The decoded escape composition** (`PeelDecode`, `PeelDecode.landsBelow_measure_le`): mirroring
  `StagedDecode` (`Forking.Adversary.OracleComp`), a transcript decoder turns the peeling escapes
  into blind pointwise escape sets for the query experiment, and `escapesDuringC_measure_le'`
  prices the landing event at `(Q + 4) · τ`.
* **The family instantiation** (`ComputedAlgebraicFSFamily.multiopen_landsBelow_measure_le`): the
  four multiopen squeeze prefixes of the computed algebraic family are the `Fin 11` pre-IPA points
  `5,6,7,8` (`θ β γ y x x₁ x₂ x₃ x₄ ξ z`), so the bound applies to the family's adversary with its
  declared query budget.

The remaining concrete input is the transcript decoder itself (`PeelDecode`'s `stateAt`): decoding
the accept event's base data back out of a squeeze prefix. Its `Fin 11`-chain half is the in-tree
`fullDecodeDeployed` pattern (take-prefixes at the fixed `preIpaLen` positions), and the coherence
it needs is the `x₁`-level analogue of the proven `preIpaTranscript_inj` (`Forking.Adversary.PreIpa`
"Injective absorb encoding"). This module keeps the decoder abstract, as the in-tree
`StagedDecode`/`PrefixDecode` compositions do.
-/

namespace Zcash.Snark

open scoped ENNReal

/-! ## A product lower bound: heavy fibers push mass into the joint set -/

open Classical in
/-- Fibers of measure at least `β` contribute jointly: the heavy-fiber mass times `β` is a lower
bound for the product measure. The counting converse of `uniformOfFintype_prod_fiber_bound`. -/
theorem uniformOfFintype_prod_fiber_lower {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    [Nonempty B] (S : Set (A × B)) (β : ℝ≥0∞) :
    (PMF.uniformOfFintype A).toOuterMeasure
        {a : A | β ≤ (PMF.uniformOfFintype B).toOuterMeasure {b : B | (a, b) ∈ S}} * β
      ≤ (PMF.uniformOfFintype (A × B)).toOuterMeasure S := by
  classical
  set H : Set A :=
    {a : A | β ≤ (PMF.uniformOfFintype B).toOuterMeasure {b : B | (a, b) ∈ S}} with hH
  rw [uniformOfFintype_toOuterMeasure_set, uniformOfFintype_toOuterMeasure_set]
  -- the joint count dominates the heavy fibers' counts
  have hcard : ∀ a : A, a ∈ H →
      β * (Fintype.card B : ℝ≥0∞) ≤ (Nat.card {b : B | (a, b) ∈ S} : ℝ≥0∞) := by
    intro a ha
    have h := ha
    rw [hH, Set.mem_setOf_eq, uniformOfFintype_toOuterMeasure_set] at h
    rw [ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
      (Or.inl (ENNReal.natCast_ne_top _))] at h
    exact h
  have hfib : ∀ a : A, Nat.card {b : B | (a, b) ∈ S} = ∑ b : B, if (a, b) ∈ S then 1 else 0 := by
    intro a
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Finset.card_filter]
  have hsplit : (Nat.card S : ℝ≥0∞) = ∑ a : A, (Nat.card {b : B | (a, b) ∈ S} : ℝ≥0∞) := by
    have htot : Nat.card S = ∑ x : A × B, if x ∈ S then 1 else 0 := by
      rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card',
        show S.toFinset = Finset.univ.filter (· ∈ S) from by
          ext x; simp [Set.mem_toFinset],
        Finset.card_filter]
    have hnat : Nat.card S = ∑ a : A, Nat.card {b : B | (a, b) ∈ S} := by
      rw [htot, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun a _ => (hfib a).symm
    rw [hnat]
    push_cast
    rfl
  have hHsum : (Nat.card H : ℝ≥0∞) * (β * Fintype.card B) ≤ (Nat.card S : ℝ≥0∞) := by
    rw [hsplit, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
    calc (H.toFinset.card : ℝ≥0∞) * (β * Fintype.card B)
        = ∑ _a ∈ H.toFinset, β * (Fintype.card B : ℝ≥0∞) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ H.toFinset, (Nat.card {b : B | (a, b) ∈ S} : ℝ≥0∞) :=
          Finset.sum_le_sum fun a ha => hcard a (Set.mem_toFinset.mp ha)
      _ ≤ ∑ a : A, (Nat.card {b : B | (a, b) ∈ S} : ℝ≥0∞) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  -- divide through by `|A × B|`
  have hA0 : (Fintype.card A : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hAtop : (Fintype.card A : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hB0 : (Fintype.card B : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hBtop : (Fintype.card B : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [Fintype.card_prod]
  push_cast
  rw [ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hA0 hB0))
    (Or.inl (ENNReal.mul_ne_top hAtop hBtop))]
  calc (Nat.card H : ℝ≥0∞) / (Fintype.card A) * β
        * ((Fintype.card A : ℝ≥0∞) * Fintype.card B)
      = ((Nat.card H : ℝ≥0∞) / (Fintype.card A) * (Fintype.card A))
          * (β * Fintype.card B) := by ring
    _ = (Nat.card H : ℝ≥0∞) * (β * Fintype.card B) := by
        rw [ENNReal.div_mul_cancel hA0 hAtop]
    _ ≤ (Nat.card S : ℝ≥0∞) := hHsum

/-! ## The four-level peeling ladder

For `σ ⊆ F⁴` and a per-level threshold `τ`, the nested heavy-fiber measures `peelG4 ⊇ peelG3 ⊇ …`
classify each prefix of coordinates by whether the remaining conditional mass still exceeds `τ`.
A member of a below-threshold `σ` must fall off the heavy chain at some level, and the set it falls
into — determined by the *earlier* coordinates alone — has measure at most `τ`. -/

section Peel

variable {F : Type*} [Fintype F] [Nonempty F]

open Classical in
/-- The innermost fiber measure: the mass of `σ`'s last coordinate over a fixed prefix. -/
noncomputable def peelG4 (σ : Set (F × F × F × F)) (a b c : F) : ℝ≥0∞ :=
  (PMF.uniformOfFintype F).toOuterMeasure {d : F | (a, b, c, d) ∈ σ}

open Classical in
/-- The `x₃`-level heavy measure: the mass of third coordinates whose last-level fiber is heavy. -/
noncomputable def peelG3 (σ : Set (F × F × F × F)) (τ : ℝ≥0∞) (a b : F) : ℝ≥0∞ :=
  (PMF.uniformOfFintype F).toOuterMeasure {c : F | τ ≤ peelG4 σ a b c}

open Classical in
/-- The `x₂`-level heavy measure. -/
noncomputable def peelG2 (σ : Set (F × F × F × F)) (τ : ℝ≥0∞) (a : F) : ℝ≥0∞ :=
  (PMF.uniformOfFintype F).toOuterMeasure {b : F | τ ≤ peelG3 σ τ a b}

open Classical in
/-- The `x₁`-level heavy measure. -/
noncomputable def peelG1 (σ : Set (F × F × F × F)) (τ : ℝ≥0∞) : ℝ≥0∞ :=
  (PMF.uniformOfFintype F).toOuterMeasure {a : F | τ ≤ peelG2 σ τ a}

/-- The peeling escape set at each level: gated by that level's own heavy measure sitting at or
below `τ`, so its uniform measure never exceeds `τ`; the body is the next level's heavy set (the
`σ`-fiber itself at the last level). Levels beyond the fourth are empty. -/
noncomputable def peelEsc (σ : Set (F × F × F × F)) (τ : ℝ≥0∞) : ℕ → F → F → F → Set F
  | 0, _, _, _ => if peelG1 σ τ ≤ τ then {x : F | τ ≤ peelG2 σ τ x} else ∅
  | 1, a, _, _ => if peelG2 σ τ a ≤ τ then {x : F | τ ≤ peelG3 σ τ a x} else ∅
  | 2, a, b, _ => if peelG3 σ τ a b ≤ τ then {x : F | τ ≤ peelG4 σ a b x} else ∅
  | 3, a, b, c => if peelG4 σ a b c ≤ τ then {x : F | (a, b, c, x) ∈ σ} else ∅
  | _ + 4, _, _, _ => ∅

/-- The escape sets ignore coordinates at or beyond their own level. -/
theorem peelEsc_congr (σ : Set (F × F × F × F)) (τ : ℝ≥0∞) (lvl : ℕ) {a b c a' b' c' : F}
    (ha : 1 ≤ lvl → a = a') (hb : 2 ≤ lvl → b = b') (hc : 3 ≤ lvl → c = c') :
    peelEsc σ τ lvl a b c = peelEsc σ τ lvl a' b' c' := by
  match lvl with
  | 0 => rfl
  | 1 => rw [ha (by omega)]; exact rfl
  | 2 => rw [ha (by omega), hb (by omega)]; exact rfl
  | 3 => rw [ha (by omega), hb (by omega), hc (by omega)]
  | n + 4 => rfl

/-- Every peeling escape set has uniform measure at most `τ`. -/
theorem peelEsc_measure_le (σ : Set (F × F × F × F)) (τ : ℝ≥0∞) (lvl : ℕ) (a b c : F) :
    (PMF.uniformOfFintype F).toOuterMeasure (peelEsc σ τ lvl a b c) ≤ τ := by
  match lvl with
  | 0 =>
      show (PMF.uniformOfFintype F).toOuterMeasure
        (if peelG1 σ τ ≤ τ then {x : F | τ ≤ peelG2 σ τ x} else ∅) ≤ τ
      split_ifs with h
      · exact h
      · simp
  | 1 =>
      show (PMF.uniformOfFintype F).toOuterMeasure
        (if peelG2 σ τ a ≤ τ then {x : F | τ ≤ peelG3 σ τ a x} else ∅) ≤ τ
      split_ifs with h
      · exact h
      · simp
  | 2 =>
      show (PMF.uniformOfFintype F).toOuterMeasure
        (if peelG3 σ τ a b ≤ τ then {x : F | τ ≤ peelG4 σ a b x} else ∅) ≤ τ
      split_ifs with h
      · exact h
      · simp
  | 3 =>
      show (PMF.uniformOfFintype F).toOuterMeasure
        (if peelG4 σ a b c ≤ τ then {x : F | (a, b, c, x) ∈ σ} else ∅) ≤ τ
      split_ifs with h
      · exact h
      · simp
  | n + 4 =>
      show (PMF.uniformOfFintype F).toOuterMeasure (∅ : Set F) ≤ τ
      simp

/-- Level-3 chain: a heavy `x₃` measure forces joint mass in the last two coordinates. -/
theorem peelG3_mul_le (σ : Set (F × F × F × F)) (τ : ℝ≥0∞) (a b : F) :
    peelG3 σ τ a b * τ
      ≤ (PMF.uniformOfFintype (F × F)).toOuterMeasure {cd : F × F | (a, b, cd.1, cd.2) ∈ σ} := by
  exact uniformOfFintype_prod_fiber_lower {cd : F × F | (a, b, cd.1, cd.2) ∈ σ} τ

/-- Level-2 chain: a heavy `x₂` measure forces joint mass in the last three coordinates. -/
theorem peelG2_mul_le (σ : Set (F × F × F × F)) (τ : ℝ≥0∞) (a : F) :
    peelG2 σ τ a * (τ * τ)
      ≤ (PMF.uniformOfFintype (F × F × F)).toOuterMeasure
          {bcd : F × F × F | (a, bcd.1, bcd.2.1, bcd.2.2) ∈ σ} := by
  refine le_trans (mul_le_mul_right' ?_ _)
    (uniformOfFintype_prod_fiber_lower
      {bcd : F × F × F | (a, bcd.1, bcd.2.1, bcd.2.2) ∈ σ} (τ * τ))
  refine (PMF.uniformOfFintype F).toOuterMeasure.mono ?_
  intro b hb
  have h3 := peelG3_mul_le σ τ a b
  have hb' : τ ≤ peelG3 σ τ a b := hb
  exact le_trans (mul_le_mul_right' hb' τ) h3

/-- Level-1 chain: a heavy `x₁` measure forces joint mass in the whole set. -/
theorem peelG1_mul_le (σ : Set (F × F × F × F)) (τ : ℝ≥0∞) :
    peelG1 σ τ * (τ * (τ * τ))
      ≤ (PMF.uniformOfFintype (F × F × F × F)).toOuterMeasure σ := by
  have hσ : σ = {abcd : F × F × F × F | (abcd.1, abcd.2.1, abcd.2.2.1, abcd.2.2.2) ∈ σ} := by
    ext ⟨a, b, c, d⟩; rfl
  refine le_trans (mul_le_mul_right' ?_ _)
    (le_trans (uniformOfFintype_prod_fiber_lower
      {abcd : F × (F × F × F) | (abcd.1, abcd.2.1, abcd.2.2.1, abcd.2.2.2) ∈ σ} (τ * (τ * τ)))
      (le_of_eq (by rw [← hσ])))
  refine (PMF.uniformOfFintype F).toOuterMeasure.mono ?_
  intro a ha
  have h2 := peelG2_mul_le σ τ a
  have ha' : τ ≤ peelG2 σ τ a := ha
  exact le_trans (mul_le_mul_right' ha' (τ * τ)) h2

open Classical in
/-- **The peeling decomposition.** A member of a below-threshold joint set always exposes one
coordinate inside its level's escape set: if `(a,b,c,d) ∈ σ` and `μ(σ) ≤ s ≤ τ⁴`, then some
coordinate `j` lies in `peelEsc σ τ j` at the earlier coordinates — a set of measure at most `τ`
determined before that coordinate is read. -/
theorem peel_decomposition {σ : Set (F × F × F × F)} {τ s : ℝ≥0∞} {a b c d : F}
    (hσ : (a, b, c, d) ∈ σ)
    (hs : (PMF.uniformOfFintype (F × F × F × F)).toOuterMeasure σ ≤ s)
    (hsτ : s ≤ τ * (τ * (τ * τ))) :
    ∃ j : Fin 4, ![a, b, c, d] j ∈ peelEsc σ τ (j : ℕ) a b c := by
  classical
  -- τ = 0 forces σ empty, contradicting membership
  rcases eq_or_ne τ 0 with hτ0 | hτ0
  · exfalso
    have hmem : (PMF.uniformOfFintype (F × F × F × F)).toOuterMeasure {(a, b, c, d)} ≤ 0 := by
      refine le_trans ((PMF.uniformOfFintype (F × F × F × F)).toOuterMeasure.mono
        (Set.singleton_subset_iff.mpr hσ)) (le_trans hs (le_trans hsτ (by simp [hτ0])))
    rw [uniformOfFintype_toOuterMeasure_singleton, nonpos_iff_eq_zero,
      ENNReal.div_eq_zero_iff] at hmem
    rcases hmem with h | h
    · exact one_ne_zero h
    · exact ENNReal.natCast_ne_top _ h
  by_cases h2 : τ ≤ peelG2 σ τ a
  · -- level-0 escape; its gate holds because a heavy `x₁` level would blow the budget
    have hgate : peelG1 σ τ ≤ τ := by
      by_contra hg
      push_neg at hg
      -- τ < peelG1 ≤ 1, so τ is finite and the strict product beats the budget
      have hle1 : peelG1 σ τ ≤ 1 := by
        rw [peelG1, ← uniformOfFintype_toOuterMeasure_univ (α := F)]
        exact (PMF.uniformOfFintype F).toOuterMeasure.mono (Set.subset_univ _)
      have hτtop : τ ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hg hle1)
      have hτ3 : τ * (τ * τ) ≠ 0 := by
        simp only [ne_eq, mul_eq_zero, not_or]
        exact ⟨hτ0, hτ0, hτ0⟩
      have hτ3top : τ * (τ * τ) ≠ ⊤ :=
        ENNReal.mul_ne_top hτtop (ENNReal.mul_ne_top hτtop hτtop)
      have hstrict : τ * (τ * (τ * τ)) < peelG1 σ τ * (τ * (τ * τ)) := by
        have h := (ENNReal.mul_lt_mul_right hτ3 hτ3top) hg
        rw [show τ * (τ * (τ * τ)) = τ * (τ * τ) * τ from by ring,
          show peelG1 σ τ * (τ * (τ * τ)) = τ * (τ * τ) * peelG1 σ τ from by ring]
        exact h
      have hbudget := peelG1_mul_le σ τ
      have : τ * (τ * (τ * τ)) < s :=
        lt_of_lt_of_le (lt_of_lt_of_le hstrict hbudget) hs
      exact absurd hsτ (not_le.mpr this)
    refine ⟨0, ?_⟩
    show a ∈ peelEsc σ τ 0 a b c
    show a ∈ if peelG1 σ τ ≤ τ then {x : F | τ ≤ peelG2 σ τ x} else ∅
    rw [if_pos hgate]
    exact h2
  · push_neg at h2
    by_cases h3 : τ ≤ peelG3 σ τ a b
    · refine ⟨1, ?_⟩
      show b ∈ peelEsc σ τ 1 a b c
      show b ∈ if peelG2 σ τ a ≤ τ then {x : F | τ ≤ peelG3 σ τ a x} else ∅
      rw [if_pos (le_of_lt h2)]
      exact h3
    · push_neg at h3
      by_cases h4 : τ ≤ peelG4 σ a b c
      · refine ⟨2, ?_⟩
        show c ∈ peelEsc σ τ 2 a b c
        show c ∈ if peelG3 σ τ a b ≤ τ then {x : F | τ ≤ peelG4 σ a b x} else ∅
        rw [if_pos (le_of_lt h3)]
        exact h4
      · push_neg at h4
        refine ⟨3, ?_⟩
        show d ∈ peelEsc σ τ 3 a b c
        show d ∈ if peelG4 σ a b c ≤ τ then {x : F | (a, b, c, x) ∈ σ} else ∅
        rw [if_pos (le_of_lt h4)]
        exact hσ

end Peel

/-! ## The decoded escape composition

Mirroring `StagedDecode` (`Forking.Adversary.OracleComp`): a transcript decoder recovers, at each
squeeze point, the joint accept event (`stateAt`), the point's level among the four challenges
(`levelOf`), and the earlier squeeze points (`chainAt`) — reading the table only *off* the point
itself, so the peeling escape sets are blind and `escapesDuringC_measure_le'` applies. -/

/-- Decode a four-challenge squeeze point: its joint accept event, its level, and its chain of
earlier squeeze points. `accept` is the per-output joint event over the four challenges;
`prefixes` are the output's own squeeze points. -/
structure PeelDecode (T F : Type*) {P : Type*} (accept : P → Set (F × F × F × F))
    (prefixes : P → Fin 4 → T) : Type _ where
  /-- The joint accept event of the transcript point's continuation. -/
  stateAt : T → Set (F × F × F × F)
  /-- The challenge level the transcript point sits at. -/
  levelOf : T → ℕ
  /-- The earlier squeeze points through the transcript point. -/
  chainAt : T → Fin 4 → T
  /-- On an output's own prefixes, the decoded state is the output's accept event. -/
  stateAt_prefixes : ∀ p (j : Fin 4), stateAt (prefixes p j) = accept p
  /-- On an output's own prefixes, the decoded level is the prefix's level. -/
  levelOf_prefixes : ∀ p (j : Fin 4), levelOf (prefixes p j) = (j : ℕ)
  /-- On an output's own prefixes, the decoded chain returns the earlier prefixes. -/
  chainAt_prefixes : ∀ p (j i : Fin 4), (i : ℕ) < (j : ℕ) →
    chainAt (prefixes p j) i = prefixes p i
  /-- Chain points before a transcript point's level differ from it. -/
  chainAt_ne : ∀ t (i : Fin 4), (i : ℕ) < levelOf t → chainAt t i ≠ t

namespace PeelDecode

variable {T F : Type*} [Fintype F] [Nonempty F] {P : Type*}
  {accept : P → Set (F × F × F × F)} {prefixes : P → Fin 4 → T}

/-- The decode's escape sets: the peeling escape of the decoded state at the decoded level, over
the chain's earlier answers. -/
noncomputable def esc (D : PeelDecode T F accept prefixes) (τ : ℝ≥0∞) : T → (T → F) → Set F :=
  fun t O => peelEsc (D.stateAt t) τ (D.levelOf t)
    (O (D.chainAt t 0)) (O (D.chainAt t 1)) (O (D.chainAt t 2))

/-- The decode's escape sets are blind at their own point: the peeling escape at level `j` reads
only the chain answers before `j`, whose points differ from `t`. -/
theorem esc_blind [DecidableEq T] (D : PeelDecode T F accept prefixes) (τ : ℝ≥0∞)
    (t : T) (O : T → F) (v : F) : D.esc τ t (Function.update O t v) = D.esc τ t O := by
  classical
  refine peelEsc_congr _ _ _ ?_ ?_ ?_ <;> intro hl <;>
    rw [Function.update_apply, if_neg (D.chainAt_ne t _ (by omega))]

/-- Each decoded escape set has uniform measure at most `τ`. -/
theorem esc_measure_le (D : PeelDecode T F accept prefixes) (τ : ℝ≥0∞) (t : T) (O : T → F) :
    (PMF.uniformOfFintype F).toOuterMeasure (D.esc τ t O) ≤ τ :=
  peelEsc_measure_le _ _ _ _ _ _

/-- The four challenge answers read at an output's own squeeze points. -/
def prefixReads (prefixes : P → Fin 4 → T) (A : OracleComp T F P) (O : T → F) :
    F × F × F × F :=
  (O (prefixes (A.run O) 0), O (prefixes (A.run O) 1),
    O (prefixes (A.run O) 2), O (prefixes (A.run O) 3))

/-- A run whose challenge reads land in a below-threshold joint accept event escapes: the peeling
decomposition exposes one read inside its level's escape set, and the completed run queries that
point. -/
theorem lands_forces (D : PeelDecode T F accept prefixes) {A : OracleComp T F P} {O : T → F}
    {τ s : ℝ≥0∞}
    (hland : prefixReads prefixes A O ∈ accept (A.run O))
    (hbelow : (PMF.uniformOfFintype (F × F × F × F)).toOuterMeasure (accept (A.run O)) ≤ s)
    (hsτ : s ≤ τ * (τ * (τ * τ))) :
    (A.completing prefixes).escapesDuringC (D.esc τ) O := by
  classical
  obtain ⟨j, hj⟩ := peel_decomposition hland hbelow hsτ
  refine OracleComp.escapesDuringC_completing (D.esc τ) prefixes (j := j) ?_
  show O (prefixes (A.run O) j) ∈ peelEsc (D.stateAt (prefixes (A.run O) j)) τ
    (D.levelOf (prefixes (A.run O) j))
    (O (D.chainAt (prefixes (A.run O) j) 0)) (O (D.chainAt (prefixes (A.run O) j) 1))
    (O (D.chainAt (prefixes (A.run O) j) 2))
  rw [D.stateAt_prefixes, D.levelOf_prefixes]
  have hcongr : peelEsc (accept (A.run O)) τ (j : ℕ)
      (O (D.chainAt (prefixes (A.run O) j) 0)) (O (D.chainAt (prefixes (A.run O) j) 1))
      (O (D.chainAt (prefixes (A.run O) j) 2))
      = peelEsc (accept (A.run O)) τ (j : ℕ)
        (O (prefixes (A.run O) 0)) (O (prefixes (A.run O) 1)) (O (prefixes (A.run O) 2)) := by
    refine peelEsc_congr _ _ _ ?_ ?_ ?_ <;> intro hl <;>
      rw [D.chainAt_prefixes _ _ _ (by omega)]
  rw [hcongr]
  fin_cases j <;> exact hj

open Classical in
/-- **The adaptive coupling bound.** A `Q`-query adversary's four challenge reads land in a
below-threshold joint accept event with probability at most `(Q + 4) · τ`, for any per-level
threshold `τ` with `s ≤ τ⁴`: the four extra queries read the output's own squeeze points, and each
query risks at most the peeling escape measure `τ`. This is the query-loss form of the
random-oracle coupling between the coin draw and the joint uniform challenge draw — the multiopen
analogue of the `(Q+k)·3/|F|` and `(Q+1)/|F|` terms already in the AGM composition. -/
theorem landsBelow_measure_le [Fintype T] [DecidableEq T]
    (D : PeelDecode T F accept prefixes) {A : OracleComp T F P} {Q : ℕ}
    (hQ : A.QueryBound Q) {τ s : ℝ≥0∞} (hsτ : s ≤ τ * (τ * (τ * τ))) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | prefixReads prefixes A O ∈ accept (A.run O) ∧
        (PMF.uniformOfFintype (F × F × F × F)).toOuterMeasure (accept (A.run O)) ≤ s}
      ≤ (Q + 4 : ℕ) * τ := by
  have hsub : {O : T → F | prefixReads prefixes A O ∈ accept (A.run O) ∧
      (PMF.uniformOfFintype (F × F × F × F)).toOuterMeasure (accept (A.run O)) ≤ s}
      ⊆ {O : T → F | (A.completing prefixes).escapesDuringC (D.esc τ) O} := by
    intro O hO
    exact D.lands_forces hO.1 hO.2 hsτ
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  have h := escapesDuringC_measure_le' (D.esc τ) (D.esc_blind τ) (D.esc_measure_le τ)
    (OracleComp.queryBound_completing prefixes hQ)
  exact_mod_cast h

end PeelDecode

end Zcash.Snark
