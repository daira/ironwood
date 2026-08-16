import Zcash.Security.GroupHash.Sampler

/-!
# The costed rejection-sampling simulator

`fibreSampler` says what the ideal world's per-query answer looks like.
This module gives the algorithm behind it: the rejection sampler, with its
per-round acceptance mass.

On a fresh query the simulator makes exactly one `R`-query. In `idealLaw`
that query appears as the single uniform draw of `Q`. The simulator then
samples the pair by rejection. Each round draws `u₀ : F` and a slot
`j < d` uniformly, computes the single-term fibre of `Q - f u₀`, and
accepts slot `j` of that fibre when it exists. Under the fibre-size
hypothesis `(singleFibre f P).card ≤ d`, each round accepts every pair of
`fibre f Q` with the same probability `1 / (#F·d)`. So conditional on
acceptance the output is uniform on the fibre, exactly as in
`fibreSampler f Q`. Summing over the fibre, a round accepts with
probability `pairCount f Q / (#F·d)`.

The simulator is capped at `K` rounds, since an uncapped rejection loop is
not a finite computation. When all `K` rounds reject, it falls back to a
uniform pair. The fallback also covers the group elements whose fibre is
empty, which no round can accept.
-/

namespace Zcash.Security.GroupHash

open scoped ENNReal
open CompElliptic.Hashing (pairCount)

variable {F : Type} [Fintype F] [DecidableEq F]
variable {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The single-term fibre: the inputs that `f` sends to `P`. -/
def singleFibre (f : F → G) (P : G) : Finset F :=
  Finset.univ.filter fun u => f u = P

omit [DecidableEq F] [AddCommGroup G] [Fintype G] in
/-- Unfolds membership in the single-term fibre to the defining equation
`f u = P`. -/
@[simp] theorem mem_singleFibre {f : F → G} {P : G} {u : F} :
    u ∈ singleFibre f P ↔ f u = P := by
  simp [singleFibre]

omit [Fintype G] in
/-- Summing the sizes of the single-term fibres of `Q - f u₀` over `u₀`
gives `pairCount f Q`. -/
theorem sum_singleFibre_card (f : F → G) (Q : G) :
    ∑ u₀, (singleFibre f (Q - f u₀)).card = pairCount f Q := by
  rw [← fibre_card, Finset.card_eq_sum_card_fiberwise
    (f := Prod.fst) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun u₀ _ => ?_
  refine Finset.card_bij (fun u₁ _ => (u₀, u₁)) ?_ ?_ ?_
  · intro u₁ hu₁
    simp only [mem_singleFibre] at hu₁
    simp [fibre, eq_sub_iff_add_eq'] at hu₁ ⊢
    exact hu₁
  · intro u₁ _ u₁' _ h
    exact (Prod.mk.injEq _ _ _ _).mp h |>.2
  · intro p hp
    simp only [Finset.mem_filter, fibre, Finset.mem_univ, true_and] at hp
    obtain ⟨hQ, hfst⟩ := hp
    refine ⟨p.2, ?_, ?_⟩
    · rw [mem_singleFibre, eq_sub_iff_add_eq', ← hfst]
      exact hQ
    · show (u₀, p.2) = p
      simp [← hfst]

/-- In a duplicate-free list of length at most `d`, an element of the list
is at exactly one of the `d` slots. Anything else is at none. -/
theorem card_slots_eq {α : Type*} [DecidableEq α] {l : List α} (hnd : l.Nodup)
    {d : ℕ} (hlen : l.length ≤ d) (b : α) :
    (Finset.univ.filter fun j : Fin d => l[(j : ℕ)]? = some b).card
      = if b ∈ l then 1 else 0 := by
  by_cases hb : b ∈ l
  · have hidx : l.idxOf b < l.length := List.idxOf_lt_length_iff.mpr hb
    rw [if_pos hb]
    have hset : (Finset.univ.filter fun j : Fin d => l[(j : ℕ)]? = some b)
        = {⟨l.idxOf b, lt_of_lt_of_le hidx hlen⟩} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hj
        rcases List.getElem?_eq_some_iff.mp hj with ⟨hlt, hget⟩
        have hgg : l[(j : ℕ)] = l[l.idxOf b] := by
          rw [hget, List.getElem_idxOf hidx]
        exact Fin.ext (hnd.getElem_inj_iff.mp hgg)
      · rintro rfl
        rw [List.getElem?_eq_getElem hidx]
        exact congrArg some (List.getElem_idxOf hidx)
    rw [hset, Finset.card_singleton]
  · rw [if_neg hb, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j _ hj
    rcases List.getElem?_eq_some_iff.mp hj with ⟨hlt, hget⟩
    exact hb (hget ▸ List.getElem_mem hlt)

/-- One rejection round: draw `u₀` and a slot `j < d` uniformly, and accept
slot `j` of the single-term fibre of `Q - f u₀` when it exists. -/
noncomputable def rejectionRound [Nonempty F] (f : F → G) (d : ℕ) [NeZero d]
    (Q : G) : PMF (Option (F × F)) :=
  (PMF.uniformOfFintype F).bind fun u₀ =>
    (PMF.uniformOfFintype (Fin d)).map fun (j : Fin d) =>
      ((singleFibre f (Q - f u₀)).toList[(j : ℕ)]?).map fun u₁ => (u₀, u₁)

omit [DecidableEq F] [Fintype G] in
/-- A pair `(u₀, u₁)` is in the fibre of `Q` exactly when `u₁` is in the
single-term fibre of `Q - f u₀`. -/
theorem mem_fibre_iff_snd {f : F → G} {Q : G} {p : F × F} :
    p ∈ fibre f Q ↔ p.2 ∈ singleFibre f (Q - f p.1) := by
  simp [fibre, eq_sub_iff_add_eq']

omit [Fintype G] in
/-- Acceptance mass of one round: each pair of the fibre of `Q` is accepted
with the same probability `1 / (#F·d)`, and nothing outside the fibre is ever
accepted. -/
theorem rejectionRound_apply_some [Nonempty F] (f : F → G) {d : ℕ} [NeZero d]
    (hd : ∀ P : G, (singleFibre f P).card ≤ d) (Q : G) (p : F × F) :
    rejectionRound f d Q (some p)
      = if p ∈ fibre f Q then ((Fintype.card F : ℝ≥0∞) * d)⁻¹ else 0 := by
  rw [rejectionRound, PMF.bind_apply, tsum_fintype]
  have hinner : ∀ u₀ : F,
      ((PMF.uniformOfFintype (Fin d)).map fun (j : Fin d) =>
        (((singleFibre f (Q - f u₀)).toList[(j : ℕ)]?).map fun u₁ => (u₀, u₁)))
        (some p)
      = if p.1 = u₀ ∧ p.2 ∈ singleFibre f (Q - f u₀) then (d : ℝ≥0∞)⁻¹
        else 0 := by
    intro u₀
    rw [PMF.map_apply, tsum_fintype]
    have hcond : ∀ j : Fin d,
        (some p = ((singleFibre f (Q - f u₀)).toList[(j : ℕ)]?).map
          fun u₁ => (u₀, u₁))
        ↔ (p.1 = u₀ ∧ (singleFibre f (Q - f u₀)).toList[(j : ℕ)]? = some p.2) := by
      intro j
      cases hget : (singleFibre f (Q - f u₀)).toList[(j : ℕ)]? with
      | none => simp
      | some u₁ =>
          simp only [Option.map_some, Option.some.injEq, Prod.ext_iff]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, h2.symm⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, h2.symm⟩
    simp only [hcond]
    by_cases hfst : p.1 = u₀
    · simp only [hfst, true_and]
      calc ∑ j : Fin d, (if (singleFibre f (Q - f u₀)).toList[(j : ℕ)]? = some p.2
              then (PMF.uniformOfFintype (Fin d)) j else 0)
          = ∑ j ∈ Finset.univ.filter fun j : Fin d =>
              (singleFibre f (Q - f u₀)).toList[(j : ℕ)]? = some p.2,
              (d : ℝ≥0∞)⁻¹ := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [PMF.uniformOfFintype_apply, Fintype.card_fin]
        _ = if p.2 ∈ singleFibre f (Q - f u₀) then (d : ℝ≥0∞)⁻¹ else 0 := by
            rw [Finset.sum_const, card_slots_eq (Finset.nodup_toList _)
              ((Finset.length_toList _).le.trans (hd _)) p.2]
            by_cases hmem : p.2 ∈ singleFibre f (Q - f u₀)
            · simp [hmem, Finset.mem_toList]
            · simp [hmem, Finset.mem_toList]
    · simp [hfst]
  simp only [hinner, PMF.uniformOfFintype_apply, mul_ite, mul_zero]
  have hFne : (Fintype.card F : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hFnt : (Fintype.card F : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [Fintype.sum_eq_single p.1
    (fun x hx => if_neg fun hc => hx hc.1.symm)]
  by_cases hp : p ∈ fibre f Q
  · rw [if_pos ⟨rfl, mem_fibre_iff_snd.mp hp⟩, if_pos hp,
      ENNReal.mul_inv (Or.inl hFne) (Or.inl hFnt)]
  · rw [if_neg fun hc => hp (mem_fibre_iff_snd.mpr hc.2), if_neg hp]

/-- The per-round acceptance probability: `pairCount f Q / (#F·d)`. -/
noncomputable def acceptProb (f : F → G) (d : ℕ) (Q : G) : ℝ≥0∞ :=
  (pairCount f Q : ℝ≥0∞) / ((Fintype.card F : ℝ≥0∞) * d)

omit [Fintype G] in
/-- Under the fibre-size hypothesis, the pair count is at most `#F·d`. -/
theorem pairCount_le (f : F → G) {d : ℕ}
    (hd : ∀ P : G, (singleFibre f P).card ≤ d) (Q : G) :
    pairCount f Q ≤ Fintype.card F * d := by
  rw [← sum_singleFibre_card]
  calc ∑ u₀, (singleFibre f (Q - f u₀)).card
      ≤ ∑ _u₀ : F, d := Finset.sum_le_sum fun u₀ _ => hd _
    _ = Fintype.card F * d := by
        rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]

omit [Fintype G] in
/-- One round rejects with probability exactly `1 - acceptProb f d Q`. -/
theorem rejectionRound_apply_none [Nonempty F] (f : F → G) {d : ℕ} [NeZero d]
    (hd : ∀ P : G, (singleFibre f P).card ≤ d) (Q : G) :
    rejectionRound f d Q none = 1 - acceptProb f d Q := by
  have htotal := (rejectionRound f d Q).tsum_coe
  rw [tsum_fintype, Fintype.sum_option] at htotal
  have hsum : ∑ p : F × F, rejectionRound f d Q (some p) = acceptProb f d Q := by
    calc ∑ p : F × F, rejectionRound f d Q (some p)
        = ∑ p : F × F, if p ∈ fibre f Q
            then ((Fintype.card F : ℝ≥0∞) * d)⁻¹ else 0 := by
          exact Finset.sum_congr rfl fun p _ => rejectionRound_apply_some f hd Q p
      _ = ∑ p ∈ fibre f Q, ((Fintype.card F : ℝ≥0∞) * d)⁻¹ := by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      _ = acceptProb f d Q := by
          rw [Finset.sum_const, fibre_card, acceptProb, div_eq_mul_inv, nsmul_eq_mul]
  rw [hsum] at htotal
  have hne : acceptProb f d Q ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by
      simp [Nat.cast_eq_zero, Fintype.card_ne_zero, NeZero.ne d])
  exact ENNReal.eq_sub_of_add_eq hne htotal

omit [DecidableEq F] [Fintype G] in
/-- Toward a target `Q` with an empty fibre, a round is surely a rejection:
every single-term fibre of `Q - f u₀` is empty, so no slot can accept. -/
theorem rejectionRound_empty [Nonempty F] (f : F → G) (d : ℕ) [NeZero d]
    {Q : G} (hempty : ¬ (fibre f Q).Nonempty) :
    rejectionRound f d Q = PMF.pure none := by
  have hsf : ∀ u₀ : F, singleFibre f (Q - f u₀) = ∅ := by
    intro u₀
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨u₁, hu₁⟩
    exact hempty ⟨(u₀, u₁), mem_fibre_iff_snd.mpr hu₁⟩
  rw [rejectionRound]
  simp [hsf]
  exact PMF.map_const _ _

/-- The capped simulator: up to `K` rejection rounds toward the target `Q`,
then the uniform-pair fallback. Returns the sample together with the number
of rounds consumed (the fallback consumes all `K`). -/
noncomputable def simCapped [Nonempty F] (f : F → G) (d : ℕ) [NeZero d]
    (Q : G) : ℕ → PMF ((F × F) × ℕ)
  | 0 => (PMF.uniformOfFintype (F × F)).map fun p => (p, 0)
  | K + 1 => (rejectionRound f d Q).bind fun r =>
      r.elim ((simCapped f d Q K).map fun x => (x.1, x.2 + 1))
        fun p => PMF.pure (p, 1)

omit [DecidableEq F] [Fintype G] in
/-- One step of the capped simulator, decomposed under an event `S`: the
rejection branch continues into `simCapped f d Q K` against the shifted
event, and each acceptance contributes its mass when `(p, 1)` lands in `S`. -/
theorem simCapped_succ_toOuterMeasure [Nonempty F] (f : F → G) {d : ℕ}
    [NeZero d] (Q : G) (K : ℕ) (S : Set ((F × F) × ℕ)) :
    (simCapped f d Q (K+1)).toOuterMeasure S
      = rejectionRound f d Q none
          * (simCapped f d Q K).toOuterMeasure ((fun x => (x.1, x.2 + 1)) ⁻¹' S)
        + ∑ p : F × F, rejectionRound f d Q (some p)
            * S.indicator (fun _ => (1 : ℝ≥0∞)) (p, 1) := by
  classical
  rw [simCapped, PMF.toOuterMeasure_bind_apply, tsum_fintype, Fintype.sum_option]
  simp only [Option.elim_none, Option.elim_some, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_pure_apply, Set.indicator_apply]

omit [DecidableEq F] [Fintype G] in
/-- A capped run with at least one round available consumes at least one
round: acceptance uses one, and the rejection branch shifts the count up. -/
theorem simCapped_succ_snd_pos [Nonempty F] (f : F → G) {d : ℕ} [NeZero d]
    (Q : G) (K : ℕ) : ∀ x ∈ (simCapped f d Q (K+1)).support, 0 < x.2 := by
  intro x hx
  rw [simCapped, PMF.support_bind] at hx
  obtain ⟨r, -, hx⟩ := Set.mem_iUnion₂.mp hx
  cases r with
  | none =>
      rw [Option.elim_none, PMF.support_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact Nat.succ_pos _
  | some p =>
      rw [Option.elim_some, PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact Nat.zero_lt_one

omit [Fintype G] in
/-- The tail of the round count: for `k < K`, the capped simulator consumes
more than `k` rounds exactly when its first `k` rounds all reject, with
probability `(1 - acceptProb f d Q)^k`. -/
theorem simCapped_tail [Nonempty F] (f : F → G) {d : ℕ} [NeZero d]
    (hd : ∀ P : G, (singleFibre f P).card ≤ d) (Q : G) :
    ∀ K k : ℕ, k < K →
      (simCapped f d Q K).toOuterMeasure {x | k < x.2}
        = (1 - acceptProb f d Q)^k
  | K + 1, 0, _ => by
      rw [pow_zero]
      exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
        (simCapped_succ_snd_pos f Q K)
  | K + 1, k + 1, h => by
      rw [pow_succ', simCapped_succ_toOuterMeasure]
      have hpre : (fun x : (F × F) × ℕ => (x.1, x.2 + 1)) ⁻¹'
          {x : (F × F) × ℕ | k+1 < x.2} = {x | k < x.2} := by
        ext x
        simp
      have hsum : (∑ p : F × F, rejectionRound f d Q (some p)
            * Set.indicator {x : (F × F) × ℕ | k+1 < x.2}
                (fun _ => (1 : ℝ≥0∞)) (p, 1))
          = 0 :=
        Finset.sum_eq_zero fun p _ => by
          rw [Set.indicator_of_notMem (by simp), mul_zero]
      rw [hpre, hsum, add_zero,
        simCapped_tail f hd Q K k (Nat.lt_of_succ_lt_succ h),
        rejectionRound_apply_none f hd Q]

omit [DecidableEq F] [Fintype G] in
/-- A capped run consumes at most `K` rounds; the fallback consumes all of
them. -/
theorem simCapped_snd_le [Nonempty F] (f : F → G) {d : ℕ} [NeZero d] (Q : G) :
    ∀ K : ℕ, ∀ x ∈ (simCapped f d Q K).support, x.2 ≤ K
  | 0 => by
      intro x hx
      rw [simCapped, PMF.support_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact le_refl 0
  | K + 1 => by
      intro x hx
      rw [simCapped, PMF.support_bind] at hx
      obtain ⟨r, -, hx⟩ := Set.mem_iUnion₂.mp hx
      cases r with
      | none =>
          rw [Option.elim_none, PMF.support_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact Nat.succ_le_succ (simCapped_snd_le f Q K y hy)
      | some p =>
          rw [Option.elim_some, PMF.support_pure, Set.mem_singleton_iff] at hx
          subst hx
          exact Nat.succ_le_succ (Nat.zero_le K)

omit [Fintype G] in
/-- Under the fibre-size hypothesis the acceptance probability is a genuine
probability. -/
theorem acceptProb_le_one (f : F → G) {d : ℕ}
    (hd : ∀ P : G, (singleFibre f P).card ≤ d) (Q : G) :
    acceptProb f d Q ≤ 1 := by
  rw [acceptProb]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul, ← Nat.cast_mul]
  exact_mod_cast pairCount_le f hd Q

omit [Fintype G] in
/-- The mass one round accepts inside an event `S`: the acceptance
probability times the fibre sampler's measure of `S`. -/
theorem accepted_mass [Nonempty F] (f : F → G) {d : ℕ} [NeZero d]
    (hd : ∀ P : G, (singleFibre f P).card ≤ d) (Q : G) (S : Set (F × F)) :
    (∑ p : F × F, rejectionRound f d Q (some p)
        * S.indicator (fun _ => (1 : ℝ≥0∞)) p)
      = acceptProb f d Q * (fibreSampler f Q).toOuterMeasure S := by
  have hstep : ∀ p : F × F, rejectionRound f d Q (some p)
      * S.indicator (fun _ => (1 : ℝ≥0∞)) p
      = (if p ∈ fibre f Q then S.indicator (fun _ => (1 : ℝ≥0∞)) p else 0)
        * ((Fintype.card F : ℝ≥0∞) * d)⁻¹ := by
    intro p
    rw [rejectionRound_apply_some f hd Q p]
    by_cases hf : p ∈ fibre f Q
    · rw [if_pos hf, if_pos hf, mul_comm]
    · rw [if_neg hf, if_neg hf, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun p _ => hstep p, ← Finset.sum_mul,
    ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  by_cases hne : (fibre f Q).Nonempty
  · have hpc : (pairCount f Q : ℝ≥0∞) ≠ 0 := by
      rw [← fibre_card]
      exact_mod_cast Finset.card_ne_zero_of_mem hne.choose_spec
    rw [fibreSampler_toOuterMeasure f hne S, acceptProb, div_eq_mul_inv,
      show (pairCount f Q : ℝ≥0∞) * ((Fintype.card F : ℝ≥0∞) * d)⁻¹
          * ((∑ p ∈ fibre f Q, S.indicator (fun _ => (1 : ℝ≥0∞)) p)
            * (pairCount f Q : ℝ≥0∞)⁻¹)
        = ((pairCount f Q : ℝ≥0∞) * (pairCount f Q : ℝ≥0∞)⁻¹)
          * ((∑ p ∈ fibre f Q, S.indicator (fun _ => (1 : ℝ≥0∞)) p)
            * ((Fintype.card F : ℝ≥0∞) * d)⁻¹) from by ring,
      ENNReal.mul_inv_cancel hpc (ENNReal.natCast_ne_top _), one_mul]
  · have hfe : fibre f Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hpc : pairCount f Q = 0 := by rw [← fibre_card, hfe, Finset.card_empty]
    rw [hfe, acceptProb, hpc]
    simp

/-- The distribution of the pair that `simCapped` returns for the target
`Q` at round cap `K`, ignoring how many rounds it took. -/
noncomputable def simOut [Nonempty F] (f : F → G) (d : ℕ) [NeZero d]
    (Q : G) (K : ℕ) : PMF (F × F) :=
  (simCapped f d Q K).map Prod.fst

omit [Fintype G] in
/-- One step of the output law is an affine combination: with the rejection
mass `1 - acceptProb f d Q` the sampler behaves as at cap `K`, and with the
acceptance mass `acceptProb f d Q` it samples `fibreSampler f Q`. -/
theorem simOut_succ_toOuterMeasure [Nonempty F] (f : F → G) {d : ℕ}
    [NeZero d] (hd : ∀ P : G, (singleFibre f P).card ≤ d) (Q : G) (K : ℕ)
    (S : Set (F × F)) :
    (simOut f d Q (K+1)).toOuterMeasure S
      = (1 - acceptProb f d Q) * (simOut f d Q K).toOuterMeasure S
        + acceptProb f d Q * (fibreSampler f Q).toOuterMeasure S := by
  simp only [simOut, PMF.toOuterMeasure_map_apply]
  rw [simCapped_succ_toOuterMeasure, rejectionRound_apply_none f hd Q]
  have hpre : (fun x : (F × F) × ℕ => (x.1, x.2 + 1)) ⁻¹' (Prod.fst ⁻¹' S)
      = Prod.fst ⁻¹' S := rfl
  have hsum : (∑ p : F × F, rejectionRound f d Q (some p)
        * Set.indicator (Prod.fst ⁻¹' S) (fun _ => (1 : ℝ≥0∞)) (p, 1))
      = acceptProb f d Q * (fibreSampler f Q).toOuterMeasure S := by
    rw [← accepted_mass f hd Q S]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem (show (p, 1) ∈ Prod.fst ⁻¹' S from hp),
        Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem (show (p, 1) ∉ Prod.fst ⁻¹' S from hp),
        Set.indicator_of_notMem hp]
  rw [hpre, hsum]

omit [DecidableEq F] [Fintype G] in
/-- Toward a target with an empty fibre, the capped output law is exactly
the fibre sampler at every cap `K`: every round rejects, so the run always
ends in the fallback draw, which is `fibreSampler f Q`'s fallback too. -/
theorem simOut_empty [Nonempty F] (f : F → G) (d : ℕ) [NeZero d] {Q : G}
    (hempty : ¬ (fibre f Q).Nonempty) :
    ∀ K : ℕ, simOut f d Q K = fibreSampler f Q
  | 0 => by
      rw [simOut, simCapped, PMF.map_comp, fibreSampler, dif_neg hempty]
      exact PMF.map_id _
  | K + 1 => by
      simp only [simOut, simCapped, rejectionRound_empty f d hempty,
        PMF.pure_bind, Option.elim_none, PMF.map_comp]
      exact simOut_empty f d hempty K

end Zcash.Security.GroupHash
