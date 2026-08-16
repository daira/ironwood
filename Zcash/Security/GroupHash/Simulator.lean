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

/-- The capped simulator: up to `K` rejection rounds toward the target `Q`,
then the uniform-pair fallback. Returns the sample together with the number
of rounds consumed (the fallback consumes all `K`). -/
noncomputable def simCapped [Nonempty F] (f : F → G) (d : ℕ) [NeZero d]
    (Q : G) : ℕ → PMF ((F × F) × ℕ)
  | 0 => (PMF.uniformOfFintype (F × F)).map fun p => (p, 0)
  | K + 1 => (rejectionRound f d Q).bind fun r =>
      match r with
      | some p => PMF.pure (p, 1)
      | none => (simCapped f d Q K).map fun x => (x.1, x.2 + 1)

/-- The distribution of the pair that `simCapped` returns for the target
`Q` at round cap `K`, ignoring how many rounds it took. -/
noncomputable def simOut [Nonempty F] (f : F → G) (d : ℕ) [NeZero d]
    (Q : G) (K : ℕ) : PMF (F × F) :=
  (simCapped f d Q K).map Prod.fst

end Zcash.Security.GroupHash
