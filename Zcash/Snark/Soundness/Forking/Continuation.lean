import Zcash.Snark.Soundness.Forking.AdaptiveCoupling

/-!
# The conditional-continuation ladder

The adaptive coupling (`Forking.AdaptiveCoupling`) prices a below-threshold landing at `(Q+4)·τ`
once a weight family satisfies the averaging and landing obligations. This module builds the
weights: the *resampled continuation measures* of the run — at each multiopen squeeze level,
redraw that level's answer at the run's own squeeze point, rerun the machine, and measure how
heavy the next level is. Overwriting keeps the escape sets blind (`updEsc`), and the run may be
rerun freely, so the accept event is free to depend on the whole table — the case that defeats
the fixed-set `PeelDecode`.

The ladder is generic over the machine, the accept family, and the squeeze points; the structural
inputs — each squeeze point knows its level, earlier prefixes survive a resample at a later one —
are packaged in `ResampleStable`, transcript geometry the concrete multiopen instantiation
discharges by prefix-length bookkeeping (`Composition.Prefixes`). The top gate is not assumed:
the chain `contV0 · τ³ ≤ contJoint` derives it from a threshold on the four-fold resampled joint
— the resampling account that replaces the fixed ladder's `peelG1_mul_le`.
-/

namespace Zcash.Snark

open scoped ENNReal
open Classical

variable {T F P : Type*} [Fintype F] [Nonempty F]

/-! ## The resampled continuation measures -/

/-- The leaf: the run's four squeeze reads land in its own accept event. -/
def contLeaf (A : OracleComp T F P) (accept : P → Set (F × F × F × F))
    (prefixes : P → Fin 4 → T) (O : T → F) : Prop :=
  PeelDecode.prefixReads prefixes A O ∈ accept (A.run O)

/-- One resample step: overwrite the current run's level-`j` squeeze answer. -/
def contUpd [DecidableEq T] (A : OracleComp T F P) (prefixes : P → Fin 4 → T) (j : Fin 4)
    (O : T → F) (v : F) : T → F :=
  Function.update O (prefixes (A.run O) j) v

open Classical in
/-- Level 3: redraw the `x₄` answer at the run's own squeeze point, rerun, and measure
acceptance. -/
noncomputable def contV3 [DecidableEq T] (A : OracleComp T F P)
    (accept : P → Set (F × F × F × F)) (prefixes : P → Fin 4 → T) (O : T → F) : ℝ≥0∞ :=
  (PMF.uniformOfFintype F).toOuterMeasure
    {d : F | contLeaf A accept prefixes (contUpd A prefixes 3 O d)}

open Classical in
/-- Level 2: redraw the `x₃` answer and measure how often the level-3 continuation is heavy. -/
noncomputable def contV2 [DecidableEq T] (A : OracleComp T F P)
    (accept : P → Set (F × F × F × F)) (prefixes : P → Fin 4 → T) (τ : ℝ≥0∞) (O : T → F) :
    ℝ≥0∞ :=
  (PMF.uniformOfFintype F).toOuterMeasure
    {c : F | τ ≤ contV3 A accept prefixes (contUpd A prefixes 2 O c)}

open Classical in
/-- Level 1. -/
noncomputable def contV1 [DecidableEq T] (A : OracleComp T F P)
    (accept : P → Set (F × F × F × F)) (prefixes : P → Fin 4 → T) (τ : ℝ≥0∞) (O : T → F) :
    ℝ≥0∞ :=
  (PMF.uniformOfFintype F).toOuterMeasure
    {b : F | τ ≤ contV2 A accept prefixes τ (contUpd A prefixes 1 O b)}

open Classical in
/-- Level 0 — the top of the ladder. -/
noncomputable def contV0 [DecidableEq T] (A : OracleComp T F P)
    (accept : P → Set (F × F × F × F)) (prefixes : P → Fin 4 → T) (τ : ℝ≥0∞) (O : T → F) :
    ℝ≥0∞ :=
  (PMF.uniformOfFintype F).toOuterMeasure
    {a : F | τ ≤ contV1 A accept prefixes τ (contUpd A prefixes 0 O a)}

open Classical in
/-- The four-fold resampled joint: redraw `x₁,…,x₄` in order at the (successively rerun)
machine's own squeeze points and measure acceptance. -/
noncomputable def contJoint [DecidableEq T] (A : OracleComp T F P)
    (accept : P → Set (F × F × F × F)) (prefixes : P → Fin 4 → T) (O : T → F) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (F × F × F × F)).toOuterMeasure
    {w : F × F × F × F | contLeaf A accept prefixes
      (contUpd A prefixes 3
        (contUpd A prefixes 2
          (contUpd A prefixes 1
            (contUpd A prefixes 0 O w.1) w.2.1) w.2.2.1) w.2.2.2)}

/-! ## The structural inputs -/

/-- **Transcript geometry for the resampled ladder.** Each squeeze point knows its level
(`level`, read off the point alone — concretely, its transcript length), and resampling a level's
answer at the run's own squeeze point preserves the run's prefixes through that level. -/
structure ResampleStable [DecidableEq T] (A : OracleComp T F P) (prefixes : P → Fin 4 → T)
    (level : T → ℕ) : Prop where
  /-- A run's `j`-th squeeze point carries level `j`. -/
  level_prefixes : ∀ (O : T → F) (j : Fin 4), level (prefixes (A.run O) j) = (j : ℕ)
  /-- Overwriting the answer at the run's own `j`-th squeeze point preserves the prefixes through
  level `j`. -/
  prefix_update : ∀ (O : T → F) (j : Fin 4) (v : F) (i : Fin 4), (i : ℕ) ≤ (j : ℕ) →
    prefixes (A.run (Function.update O (prefixes (A.run O) j) v)) i
      = prefixes (A.run O) i

namespace ResampleStable

variable {A : OracleComp T F P} {accept : P → Set (F × F × F × F)}
  {prefixes : P → Fin 4 → T} {level : T → ℕ}

/-- Resampling at the level-3 point leaves the level-3 continuation unchanged: the redraw
overwrites the resampled answer. -/
theorem contV3_update [DecidableEq T] (hS : ResampleStable A prefixes level) (O : T → F)
    (v : F) :
    contV3 A accept prefixes (contUpd A prefixes 3 O v) = contV3 A accept prefixes O := by
  have hpre : prefixes (A.run (Function.update O (prefixes (A.run O) 3) v)) 3
      = prefixes (A.run O) 3 :=
    hS.prefix_update O 3 v 3 le_rfl
  simp only [contV3, contUpd, hpre]
  congr 1
  ext d
  simp only [Set.mem_setOf_eq, Function.update_idem]

/-- Resampling at the level-2 point leaves the level-2 continuation unchanged. -/
theorem contV2_update [DecidableEq T] (hS : ResampleStable A prefixes level) {τ : ℝ≥0∞}
    (O : T → F) (v : F) :
    contV2 A accept prefixes τ (contUpd A prefixes 2 O v) = contV2 A accept prefixes τ O := by
  have hpre : prefixes (A.run (Function.update O (prefixes (A.run O) 2) v)) 2
      = prefixes (A.run O) 2 :=
    hS.prefix_update O 2 v 2 le_rfl
  simp only [contV2, contUpd, hpre]
  congr 1
  ext c
  simp only [Set.mem_setOf_eq, Function.update_idem]

/-- Resampling at the level-1 point leaves the level-1 continuation unchanged. -/
theorem contV1_update [DecidableEq T] (hS : ResampleStable A prefixes level) {τ : ℝ≥0∞}
    (O : T → F) (v : F) :
    contV1 A accept prefixes τ (contUpd A prefixes 1 O v) = contV1 A accept prefixes τ O := by
  have hpre : prefixes (A.run (Function.update O (prefixes (A.run O) 1) v)) 1
      = prefixes (A.run O) 1 :=
    hS.prefix_update O 1 v 1 le_rfl
  simp only [contV1, contUpd, hpre]
  congr 1
  ext b
  simp only [Set.mem_setOf_eq, Function.update_idem]

/-- Resampling at the level-0 point leaves the top continuation unchanged. -/
theorem contV0_update [DecidableEq T] (hS : ResampleStable A prefixes level) {τ : ℝ≥0∞}
    (O : T → F) (v : F) :
    contV0 A accept prefixes τ (contUpd A prefixes 0 O v) = contV0 A accept prefixes τ O := by
  have hpre : prefixes (A.run (Function.update O (prefixes (A.run O) 0) v)) 0
      = prefixes (A.run O) 0 :=
    hS.prefix_update O 0 v 0 le_rfl
  simp only [contV0, contUpd, hpre]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, Function.update_idem]

/-! ### The chain

`contV0 · τ³ ≤ contJoint`: a heavy top continuation forces resampled joint mass. The
varying-fiber form of `peelG1_mul_le` — any answer-dependence of the rerun's accept event is
absorbed into the joint set, whose fibers the product lower bound reads. -/

/-- The level-2 chain step. -/
theorem contV2_mul_le [DecidableEq T] (hS : ResampleStable A prefixes level) (τ : ℝ≥0∞)
    (O : T → F) :
    contV2 A accept prefixes τ O * τ
      ≤ (PMF.uniformOfFintype (F × F)).toOuterMeasure
          {cd : F × F | contLeaf A accept prefixes
            (contUpd A prefixes 3 (contUpd A prefixes 2 O cd.1) cd.2)} := by
  refine le_trans (mul_le_mul_right' ?_ τ)
    (uniformOfFintype_prod_fiber_lower
      {cd : F × F | contLeaf A accept prefixes
        (contUpd A prefixes 3 (contUpd A prefixes 2 O cd.1) cd.2)} τ)
  refine (PMF.uniformOfFintype F).toOuterMeasure.mono ?_
  intro c hc
  simp only [contV2, Set.mem_setOf_eq] at hc
  simp only [Set.mem_setOf_eq]
  simpa only [contV3, Set.mem_setOf_eq] using hc

/-- The level-1 chain step. -/
theorem contV1_mul_le [DecidableEq T] (hS : ResampleStable A prefixes level) (τ : ℝ≥0∞)
    (O : T → F) :
    contV1 A accept prefixes τ O * (τ * τ)
      ≤ (PMF.uniformOfFintype (F × F × F)).toOuterMeasure
          {bcd : F × F × F | contLeaf A accept prefixes
            (contUpd A prefixes 3 (contUpd A prefixes 2
              (contUpd A prefixes 1 O bcd.1) bcd.2.1) bcd.2.2)} := by
  refine le_trans (mul_le_mul_right' ?_ (τ * τ))
    (uniformOfFintype_prod_fiber_lower
      {bcd : F × F × F | contLeaf A accept prefixes
        (contUpd A prefixes 3 (contUpd A prefixes 2
          (contUpd A prefixes 1 O bcd.1) bcd.2.1) bcd.2.2)} (τ * τ))
  refine (PMF.uniformOfFintype F).toOuterMeasure.mono ?_
  intro b hb
  simp only [contV1, Set.mem_setOf_eq] at hb
  simp only [Set.mem_setOf_eq]
  exact le_trans (mul_le_mul_right' hb τ) (hS.contV2_mul_le τ _)

/-- **The chain.** `contV0 · τ³ ≤ contJoint`. -/
theorem contV0_mul_le [DecidableEq T] (hS : ResampleStable A prefixes level) (τ : ℝ≥0∞)
    (O : T → F) :
    contV0 A accept prefixes τ O * (τ * (τ * τ)) ≤ contJoint A accept prefixes O := by
  refine le_trans (mul_le_mul_right' ?_ (τ * (τ * τ)))
    (uniformOfFintype_prod_fiber_lower
      {w : F × (F × F × F) | contLeaf A accept prefixes
        (contUpd A prefixes 3 (contUpd A prefixes 2 (contUpd A prefixes 1
          (contUpd A prefixes 0 O w.1) w.2.1) w.2.2.1) w.2.2.2)} (τ * (τ * τ)))
  refine (PMF.uniformOfFintype F).toOuterMeasure.mono ?_
  intro a ha
  simp only [contV0, Set.mem_setOf_eq] at ha
  simp only [Set.mem_setOf_eq]
  exact le_trans (mul_le_mul_right' ha (τ * τ)) (hS.contV1_mul_le τ _)

/-- The top gate from the joint threshold: `contJoint ≤ s ≤ τ⁴` and a nontrivial finite `τ`
force `contV0 ≤ τ` — the resampling account. -/
theorem contV0_le_of_joint [DecidableEq T] (hS : ResampleStable A prefixes level)
    {τ s : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτtop : τ ≠ ⊤) (hsτ : s ≤ τ * (τ * (τ * τ)))
    {O : T → F} (hJ : contJoint A accept prefixes O ≤ s) :
    contV0 A accept prefixes τ O ≤ τ := by
  by_contra hg
  push_neg at hg
  have hτ3 : τ * (τ * τ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨hτ0, hτ0, hτ0⟩
  have hτ3top : τ * (τ * τ) ≠ ⊤ :=
    ENNReal.mul_ne_top hτtop (ENNReal.mul_ne_top hτtop hτtop)
  have hstrict : τ * (τ * (τ * τ)) < contV0 A accept prefixes τ O * (τ * (τ * τ)) := by
    have h := (ENNReal.mul_lt_mul_right hτ3 hτ3top) hg
    rw [show τ * (τ * (τ * τ)) = τ * (τ * τ) * τ from by ring,
      show contV0 A accept prefixes τ O * (τ * (τ * τ))
        = τ * (τ * τ) * contV0 A accept prefixes τ O from by ring]
    exact h
  exact absurd hsτ (not_le.mpr
    (lt_of_lt_of_le (lt_of_lt_of_le hstrict (hS.contV0_mul_le τ O)) hJ))

end ResampleStable

/-! ## The gated weight family and its two obligations

At a level-`j` squeeze point the weight is `τ` exactly when the point is the run's own `j`-th
prefix, the level's own continuation gate holds — self-stable under the candidate overwrite, so
the gate is the escape measure — and the drawn answer made the next level heavy. -/

open Classical in
/-- The conditional-continuation weight family. -/
noncomputable def contWt [DecidableEq T] (A : OracleComp T F P)
    (accept : P → Set (F × F × F × F)) (prefixes : P → Fin 4 → T) (level : T → ℕ)
    (τ : ℝ≥0∞) : T → (T → F) → ℝ≥0∞ :=
  fun t O =>
    if level t = 3 then
      (if t = prefixes (A.run O) 3 ∧ contV3 A accept prefixes O ≤ τ ∧
          contLeaf A accept prefixes O then τ else 0)
    else if level t = 2 then
      (if t = prefixes (A.run O) 2 ∧ contV2 A accept prefixes τ O ≤ τ ∧
          τ ≤ contV3 A accept prefixes O then τ else 0)
    else if level t = 1 then
      (if t = prefixes (A.run O) 1 ∧ contV1 A accept prefixes τ O ≤ τ ∧
          τ ≤ contV2 A accept prefixes τ O then τ else 0)
    else
      (if t = prefixes (A.run O) 0 ∧ contV0 A accept prefixes τ O ≤ τ ∧
          τ ≤ contV1 A accept prefixes τ O then τ else 0)

open Classical in
/-- Counting: an indicator sum at value `τ` over a set of measure at most `τ` is at most
`τ·τ·|F|`. The measure hypothesis is only needed when the set is inhabited. -/
private theorem sum_if_mem_le {τ : ℝ≥0∞} (SB : Set F)
    (h : ∀ w, w ∈ SB → (PMF.uniformOfFintype F).toOuterMeasure SB ≤ τ) :
    (∑ v : F, if v ∈ SB then τ else 0) ≤ τ * τ * Fintype.card F := by
  rcases Set.eq_empty_or_nonempty SB with rfl | ⟨w, hw⟩
  · simp
  have hμ := h w hw
  rw [uniformOfFintype_toOuterMeasure_set] at hμ
  have hcard : (Nat.card SB : ℝ≥0∞) ≤ τ * Fintype.card F := by
    have hne : ((Fintype.card F : ℕ) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have htop : ((Fintype.card F : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    calc (Nat.card SB : ℝ≥0∞)
        = (Nat.card SB : ℝ≥0∞) / Fintype.card F * Fintype.card F :=
          (ENNReal.div_mul_cancel hne htop).symm
      _ ≤ τ * Fintype.card F := mul_le_mul_right' hμ _
  have hsum : (∑ v : F, if v ∈ SB then τ else 0) = τ * Nat.card SB := by
    classical
    have hcards : (Finset.univ.filter (fun v : F => v ∈ SB)).card = Nat.card SB := by
      rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
      congr 1
      ext v
      simp
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
      mul_comm, hcards]
  rw [hsum]
  calc τ * (Nat.card SB : ℝ≥0∞) ≤ τ * (τ * Fintype.card F) := mul_le_mul_left' hcard τ
    _ = τ * τ * Fintype.card F := by ring

open Classical in
/-- Counting: a `τ`-bounded function supported on a set of measure at most `τ` sums to at most
`τ·τ·|F|`. The measure hypothesis is only needed when the support is inhabited. -/
private theorem sum_le_of_support {τ : ℝ≥0∞} (f : F → ℝ≥0∞) (SB : Set F)
    (hf : ∀ v, f v ≤ τ) (hsupp : ∀ v, f v ≠ 0 → v ∈ SB)
    (h : ∀ w, w ∈ SB → (PMF.uniformOfFintype F).toOuterMeasure SB ≤ τ) :
    (∑ v : F, f v) ≤ τ * τ * Fintype.card F := by
  refine le_trans (Finset.sum_le_sum (fun v _ => ?_)) (sum_if_mem_le SB h)
  by_cases hv : v ∈ SB
  · rw [if_pos hv]; exact hf v
  · rw [if_neg hv]
    exact le_of_eq (not_not.mp fun hne => hv (hsupp v hne))

namespace ResampleStable

variable {A : OracleComp T F P} {accept : P → Set (F × F × F × F)}
  {prefixes : P → Fin 4 → T} {level : T → ℕ}

/-- **The averaging obligation.** The weight family averages at most `τ·τ` over a fresh answer at
any point: within a level's branch, the candidates that fire all share the pre-run — the
overwritten tables are one `contUpd` orbit — so the firing set sits inside the gate's own heavy
set, of measure at most `τ` by the gate. -/
theorem contWt_avg [DecidableEq T] (hS : ResampleStable A prefixes level) (τ : ℝ≥0∞)
    (t : T) (O : T → F) :
    (∑ v : F, contWt A accept prefixes level τ t (Function.update O t v))
      ≤ τ * τ * Fintype.card F := by
  classical
  by_cases h3 : level t = 3
  · refine sum_le_of_support _ {v : F | t = prefixes (A.run (Function.update O t v)) 3 ∧
        contV3 A accept prefixes (Function.update O t v) ≤ τ ∧
        contLeaf A accept prefixes (Function.update O t v)} (fun v => ?_) (fun v hne => ?_) ?_
    · rw [contWt, if_pos h3]
      split_ifs
      · exact le_rfl
      · exact zero_le'
    · rw [contWt, if_pos h3] at hne
      by_cases hb : t = prefixes (A.run (Function.update O t v)) 3 ∧
          contV3 A accept prefixes (Function.update O t v) ≤ τ ∧
          contLeaf A accept prefixes (Function.update O t v)
      · exact hb
      · rw [if_neg hb] at hne
        exact absurd rfl hne
    · intro w hw
      obtain ⟨hwt, hwgate, -⟩ := hw
      refine le_trans ((PMF.uniformOfFintype F).toOuterMeasure.mono ?_) hwgate
      intro v hv
      obtain ⟨-, -, hvleaf⟩ := hv
      show v ∈ {d : F | contLeaf A accept prefixes
        (contUpd A prefixes 3 (Function.update O t w) d)}
      have hupd : contUpd A prefixes 3 (Function.update O t w) v = Function.update O t v := by
        rw [contUpd, ← hwt, Function.update_idem]
      rw [Set.mem_setOf_eq, hupd]
      exact hvleaf
  by_cases h2 : level t = 2
  · refine sum_le_of_support _ {v : F | t = prefixes (A.run (Function.update O t v)) 2 ∧
        contV2 A accept prefixes τ (Function.update O t v) ≤ τ ∧
        τ ≤ contV3 A accept prefixes (Function.update O t v)} (fun v => ?_) (fun v hne => ?_) ?_
    · rw [contWt, if_neg h3, if_pos h2]
      split_ifs
      · exact le_rfl
      · exact zero_le'
    · rw [contWt, if_neg h3, if_pos h2] at hne
      by_cases hb : t = prefixes (A.run (Function.update O t v)) 2 ∧
          contV2 A accept prefixes τ (Function.update O t v) ≤ τ ∧
          τ ≤ contV3 A accept prefixes (Function.update O t v)
      · exact hb
      · rw [if_neg hb] at hne
        exact absurd rfl hne
    · intro w hw
      obtain ⟨hwt, hwgate, -⟩ := hw
      refine le_trans ((PMF.uniformOfFintype F).toOuterMeasure.mono ?_) hwgate
      intro v hv
      obtain ⟨-, -, hvheavy⟩ := hv
      show v ∈ {c : F | τ ≤ contV3 A accept prefixes
        (contUpd A prefixes 2 (Function.update O t w) c)}
      have hupd : contUpd A prefixes 2 (Function.update O t w) v = Function.update O t v := by
        rw [contUpd, ← hwt, Function.update_idem]
      rw [Set.mem_setOf_eq, hupd]
      exact hvheavy
  by_cases h1 : level t = 1
  · refine sum_le_of_support _ {v : F | t = prefixes (A.run (Function.update O t v)) 1 ∧
        contV1 A accept prefixes τ (Function.update O t v) ≤ τ ∧
        τ ≤ contV2 A accept prefixes τ (Function.update O t v)} (fun v => ?_) (fun v hne => ?_) ?_
    · rw [contWt, if_neg h3, if_neg h2, if_pos h1]
      split_ifs
      · exact le_rfl
      · exact zero_le'
    · rw [contWt, if_neg h3, if_neg h2, if_pos h1] at hne
      by_cases hb : t = prefixes (A.run (Function.update O t v)) 1 ∧
          contV1 A accept prefixes τ (Function.update O t v) ≤ τ ∧
          τ ≤ contV2 A accept prefixes τ (Function.update O t v)
      · exact hb
      · rw [if_neg hb] at hne
        exact absurd rfl hne
    · intro w hw
      obtain ⟨hwt, hwgate, -⟩ := hw
      refine le_trans ((PMF.uniformOfFintype F).toOuterMeasure.mono ?_) hwgate
      intro v hv
      obtain ⟨-, -, hvheavy⟩ := hv
      show v ∈ {b : F | τ ≤ contV2 A accept prefixes τ
        (contUpd A prefixes 1 (Function.update O t w) b)}
      have hupd : contUpd A prefixes 1 (Function.update O t w) v = Function.update O t v := by
        rw [contUpd, ← hwt, Function.update_idem]
      rw [Set.mem_setOf_eq, hupd]
      exact hvheavy
  · refine sum_le_of_support _ {v : F | t = prefixes (A.run (Function.update O t v)) 0 ∧
        contV0 A accept prefixes τ (Function.update O t v) ≤ τ ∧
        τ ≤ contV1 A accept prefixes τ (Function.update O t v)} (fun v => ?_) (fun v hne => ?_) ?_
    · rw [contWt, if_neg h3, if_neg h2, if_neg h1]
      split_ifs
      · exact le_rfl
      · exact zero_le'
    · rw [contWt, if_neg h3, if_neg h2, if_neg h1] at hne
      by_cases hb : t = prefixes (A.run (Function.update O t v)) 0 ∧
          contV0 A accept prefixes τ (Function.update O t v) ≤ τ ∧
          τ ≤ contV1 A accept prefixes τ (Function.update O t v)
      · exact hb
      · rw [if_neg hb] at hne
        exact absurd rfl hne
    · intro w hw
      obtain ⟨hwt, hwgate, -⟩ := hw
      refine le_trans ((PMF.uniformOfFintype F).toOuterMeasure.mono ?_) hwgate
      intro v hv
      obtain ⟨-, -, hvheavy⟩ := hv
      show v ∈ {a : F | τ ≤ contV1 A accept prefixes τ
        (contUpd A prefixes 0 (Function.update O t w) a)}
      have hupd : contUpd A prefixes 0 (Function.update O t w) v = Function.update O t v := by
        rw [contUpd, ← hwt, Function.update_idem]
      rw [Set.mem_setOf_eq, hupd]
      exact hvheavy

/-- **The landing obligation.** On an accepting run whose resampled joint sits within the
`τ⁴`-budget, the completed run escapes: the joint threshold derives the top gate, and the walk
down the levels exposes the first heavy answer at the run's own squeeze point. -/
theorem contWt_lands [DecidableEq T] (hS : ResampleStable A prefixes level)
    {τ s : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτtop : τ ≠ ⊤) (hsτ : s ≤ τ * (τ * (τ * τ)))
    {O : T → F} (hleaf : contLeaf A accept prefixes O)
    (hJ : contJoint A accept prefixes O ≤ s) :
    (A.completing prefixes).escapesDuringC
      (updEsc (contWt A accept prefixes level τ) τ) O := by
  classical
  have hgate0 : contV0 A accept prefixes τ O ≤ τ :=
    hS.contV0_le_of_joint hτ0 hτtop hsτ hJ
  have hl0 : level (prefixes (A.run O) 0) = 0 := by simpa using hS.level_prefixes O 0
  have hl1 : level (prefixes (A.run O) 1) = 1 := by simpa using hS.level_prefixes O 1
  have hl2 : level (prefixes (A.run O) 2) = 2 := by simpa using hS.level_prefixes O 2
  have hl3 : level (prefixes (A.run O) 3) = 3 := by simpa using hS.level_prefixes O 3
  by_cases h1 : τ ≤ contV1 A accept prefixes τ O
  · refine OracleComp.escapesDuringC_completing _ prefixes (j := 0) ?_
    rw [mem_updEsc_self]
    rw [contWt, if_neg (by rw [hl0]; omega), if_neg (by rw [hl0]; omega),
      if_neg (by rw [hl0]; omega), if_pos ⟨rfl, hgate0, h1⟩]
  push_neg at h1
  by_cases h2 : τ ≤ contV2 A accept prefixes τ O
  · refine OracleComp.escapesDuringC_completing _ prefixes (j := 1) ?_
    rw [mem_updEsc_self]
    rw [contWt, if_neg (by rw [hl1]; omega), if_neg (by rw [hl1]; omega),
      if_pos hl1, if_pos ⟨rfl, le_of_lt h1, h2⟩]
  push_neg at h2
  by_cases h3 : τ ≤ contV3 A accept prefixes O
  · refine OracleComp.escapesDuringC_completing _ prefixes (j := 2) ?_
    rw [mem_updEsc_self]
    rw [contWt, if_neg (by rw [hl2]; omega), if_pos hl2,
      if_pos ⟨rfl, le_of_lt h2, h3⟩]
  push_neg at h3
  · refine OracleComp.escapesDuringC_completing _ prefixes (j := 3) ?_
    rw [mem_updEsc_self]
    rw [contWt, if_pos hl3, if_pos ⟨rfl, le_of_lt h3, hleaf⟩]

open Classical in
/-- **The adaptive query-loss endpoint.** A `Q`-query machine's run accepts with its resampled
joint inside the `τ⁴`-budget with probability at most `(Q + 4)·τ`: the weight family's escape
sets are blind by overwriting, each has measure at most `τ` by the averaging obligation, and the
landing walk charges the four completing queries. The conditional-continuation replacement for
`PeelDecode.landsBelow_measure_le`, with no `stateAt` — the accept event may read the whole
table. -/
theorem contLand_measure_le [Fintype T] [DecidableEq T]
    (hS : ResampleStable A prefixes level) {Q : ℕ} (hQ : A.QueryBound Q)
    {τ s : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτtop : τ ≠ ⊤) (hsτ : s ≤ τ * (τ * (τ * τ))) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | contLeaf A accept prefixes O ∧ contJoint A accept prefixes O ≤ s}
      ≤ (Q + 4 : ℕ) * τ := by
  have hsub : {O : T → F | contLeaf A accept prefixes O ∧
      contJoint A accept prefixes O ≤ s}
      ⊆ {O : T → F | (A.completing prefixes).escapesDuringC
          (updEsc (contWt A accept prefixes level τ) τ) O} := by
    intro O hO
    exact hS.contWt_lands hτ0 hτtop hsτ hO.1 hO.2
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  have h := updEsc_escapesDuringC_measure_le (contWt A accept prefixes level τ) τ
    (fun t O => updEsc_measure_le _ hτ0 t O (hS.contWt_avg τ t O))
    (OracleComp.queryBound_completing prefixes hQ)
  exact_mod_cast h

end ResampleStable

/-! ## The one-level squeeze: a pinned bad set at a single fresh challenge

The `x`-squeeze analogue of the ladder, one level deep: the run reads one challenge at its own
squeeze point, and a bad set pinned before the squeeze prices the read at `(Q+1)·ε`. The pinning
hypotheses — the squeeze point and the bad set survive resampling the answer — are the
pre-squeeze-pinning content: the bad set is built from data committed before the challenge. -/

open Classical in
/-- The one-level escape: the candidate answer is bad for the (rerun) output. Blind by
overwriting. -/
noncomputable def xEsc [DecidableEq T] (A : OracleComp T F P) (xpt : P → T)
    (bad : P → Set F) : T → (T → F) → Set F :=
  fun t O => {v : F | t = xpt (A.run (Function.update O t v)) ∧
    v ∈ bad (A.run (Function.update O t v))}

open Classical in
/-- **The one-level squeeze price.** If the squeeze point and the bad set are pinned under
resampling the squeeze answer, and every output's bad set has measure at most `ε`, then a
`Q`-query machine's own squeeze answer is bad with probability at most `(Q+1)·ε`. -/
theorem xEsc_measure_le [Fintype T] [DecidableEq T] (A : OracleComp T F P) (xpt : P → T)
    (bad : P → Set F)
    (hstab : ∀ (O : T → F) (v : F),
      xpt (A.run (Function.update O (xpt (A.run O)) v)) = xpt (A.run O))
    (hpin : ∀ (O : T → F) (v : F),
      bad (A.run (Function.update O (xpt (A.run O)) v)) = bad (A.run O))
    {ε : ℝ≥0∞} (hbad : ∀ p, (PMF.uniformOfFintype F).toOuterMeasure (bad p) ≤ ε)
    {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | O (xpt (A.run O)) ∈ bad (A.run O)} ≤ (Q + 1 : ℕ) * ε := by
  classical
  -- the bad read escapes the completed run at the output's own squeeze point
  have hsub : {O : T → F | O (xpt (A.run O)) ∈ bad (A.run O)}
      ⊆ {O : T → F | (A.completing (fun p (_ : Fin 1) => xpt p)).escapesDuringC
          (xEsc A xpt bad) O} := by
    intro O hO
    refine OracleComp.escapesDuringC_completing _ (fun p (_ : Fin 1) => xpt p) (j := 0) ?_
    show O (xpt (A.run O)) ∈ xEsc A xpt bad (xpt (A.run O)) O
    constructor
    · rw [Function.update_eq_self]
    · rw [Function.update_eq_self]
      exact hO
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  -- blindness by overwriting; per-point measure by the pinning orbit
  have hblind : ∀ (t : T) (O : T → F) (v : F),
      xEsc A xpt bad t (Function.update O t v) = xEsc A xpt bad t O := by
    intro t O v
    ext u
    simp only [xEsc, Set.mem_setOf_eq, Function.update_idem]
  have hesc : ∀ (t : T) (O : T → F),
      (PMF.uniformOfFintype F).toOuterMeasure (xEsc A xpt bad t O) ≤ ε := by
    intro t O
    rcases Set.eq_empty_or_nonempty (xEsc A xpt bad t O) with hemp | ⟨w, hw⟩
    · rw [hemp]
      simp
    obtain ⟨hwt, -⟩ := hw
    refine le_trans ((PMF.uniformOfFintype F).toOuterMeasure.mono ?_)
      (hbad (A.run (Function.update O t w)))
    intro v hv
    obtain ⟨-, hvbad⟩ := hv
    have hupd : Function.update (Function.update O t w) t v = Function.update O t v := by
      rw [Function.update_idem]
    have hpinw := hpin (Function.update O t w) v
    rw [← hwt] at hpinw
    rw [hupd] at hpinw
    rw [← hpinw]
    exact hvbad
  have h := escapesDuringC_measure_le' (xEsc A xpt bad) hblind hesc
    (OracleComp.queryBound_completing (fun p (_ : Fin 1) => xpt p) hQ)
  exact_mod_cast h

/-! ## The table-reading squeeze

The concrete constraint bad set reads more than the output: the earlier squeeze answers (the
challenges before `x`) are table reads. The squeeze below carries `bad` as a function of the
output *and* the table, with one pinning hypothesis: resampling the run's own squeeze answer
preserves the set — so `bad` may read any point other than the run's own squeeze point. -/

open Classical in
/-- The one-level escape with a table-reading bad set: the candidate answer is bad for the
(rerun) output at the (updated) table. Blind by overwriting. -/
noncomputable def xEscTable [DecidableEq T] (A : OracleComp T F P) (xpt : P → T)
    (bad : P → (T → F) → Set F) : T → (T → F) → Set F :=
  fun t O => {v : F | t = xpt (A.run (Function.update O t v)) ∧
    v ∈ bad (A.run (Function.update O t v)) (Function.update O t v)}

open Classical in
/-- **The one-level squeeze price, table-reading form.** As `xEsc_measure_le`, with the bad set
a function of the output and the table; the pinning hypothesis `hpin` states both stabilities at
once — the rerun at a resampled squeeze answer carries the same bad set. -/
theorem xEscTable_measure_le [Fintype T] [DecidableEq T] (A : OracleComp T F P) (xpt : P → T)
    (bad : P → (T → F) → Set F)
    (hpin : ∀ (O : T → F) (v : F),
      bad (A.run (Function.update O (xpt (A.run O)) v))
          (Function.update O (xpt (A.run O)) v)
        = bad (A.run O) O)
    {ε : ℝ≥0∞} (hbad : ∀ p O, (PMF.uniformOfFintype F).toOuterMeasure (bad p O) ≤ ε)
    {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | O (xpt (A.run O)) ∈ bad (A.run O) O} ≤ (Q + 1 : ℕ) * ε := by
  classical
  have hsub : {O : T → F | O (xpt (A.run O)) ∈ bad (A.run O) O}
      ⊆ {O : T → F | (A.completing (fun p (_ : Fin 1) => xpt p)).escapesDuringC
          (xEscTable A xpt bad) O} := by
    intro O hO
    refine OracleComp.escapesDuringC_completing _ (fun p (_ : Fin 1) => xpt p) (j := 0) ?_
    show O (xpt (A.run O)) ∈ xEscTable A xpt bad (xpt (A.run O)) O
    constructor
    · rw [Function.update_eq_self]
    · rw [Function.update_eq_self]
      exact hO
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  have hblind : ∀ (t : T) (O : T → F) (v : F),
      xEscTable A xpt bad t (Function.update O t v) = xEscTable A xpt bad t O := by
    intro t O v
    ext u
    simp only [xEscTable, Set.mem_setOf_eq, Function.update_idem]
  have hesc : ∀ (t : T) (O : T → F),
      (PMF.uniformOfFintype F).toOuterMeasure (xEscTable A xpt bad t O) ≤ ε := by
    intro t O
    rcases Set.eq_empty_or_nonempty (xEscTable A xpt bad t O) with hemp | ⟨w, hw⟩
    · rw [hemp]
      simp
    obtain ⟨hwt, -⟩ := hw
    refine le_trans ((PMF.uniformOfFintype F).toOuterMeasure.mono ?_)
      (hbad (A.run (Function.update O t w)) (Function.update O t w))
    intro v hv
    obtain ⟨-, hvbad⟩ := hv
    have hupd : Function.update (Function.update O t w) t v = Function.update O t v := by
      rw [Function.update_idem]
    have hpinw := hpin (Function.update O t w) v
    rw [← hwt] at hpinw
    rw [hupd] at hpinw
    rw [← hpinw]
    exact hvbad
  have h := escapesDuringC_measure_le' (xEscTable A xpt bad) hblind hesc
    (OracleComp.queryBound_completing (fun p (_ : Fin 1) => xpt p) hQ)
  exact_mod_cast h

end Zcash.Snark
