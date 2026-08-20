import Mathlib.Probability.Distributions.Uniform
import CompElliptic.Hashing.TwoTermUniformity
import Zcash.Common.Oracle.Model

/-!
# The fibre sampler and the single-query bias

This is the cryptographic core of the group-hash indifferentiability argument
(zcash/ironwood#198). It builds the ideal world's per-query answer distribution
and bounds how far it is from the real world's, for a single query.

## The two per-query laws

The deployed group hash is `H(m) = f(u₀) + f(u₁)`, where `(u₀, u₁)` is the
output of `hash_to_field(m, 2)`, modelled as a random oracle into `F × F`, and
`f = mapToCurve`. A distinguisher can recompute `(u₀, u₁)` itself and check that
`H(m)` really is `f(u₀) + f(u₁)`, so what it can observe on a fresh query is the
*pair* `(u₀, u₁)`, from which the group element is a fixed function.

So each world hands the distinguisher a fresh draw from a distribution on
`F × F`:

- **real world**: the pair is uniform on `F × F` — this is `hash_to_field`
  answering honestly;
- **ideal world**: a random oracle `R` returns a uniform group element `Q`, and
  a *simulator* must return a pair `(u₀, u₁)` with `f(u₀) + f(u₁) = Q`, sampled
  uniformly from the fibre of `Q` under the two-term sum — the set of all pairs
  `(u₀, u₁)` that `(u₀, u₁) ↦ f(u₀) + f(u₁)` sends to `Q`.

`idealLaw f` is the ideal world's law: draw `Q` uniformly, then draw a pair
uniformly from the fibre of `Q`.

## The fibre sampler and its fallback

`fibreSampler f Q` samples a pair uniformly from the fibre
`{(u₀, u₁) | f(u₀) + f(u₁) = Q}`. When that fibre is empty — some group elements
may be missed by the two-term sum — there is no pair to return, so the sampler
falls back to a uniform pair on `F × F`. The fallback keeps `fibreSampler f Q` a
genuine distribution; its only effect is on the bias, and it is accounted for
there.

## The single-query bias

`weightedBias_real_le` and `weightedBias_ideal_le` bound the one-squeeze bias
between the two laws, in each direction. Two pieces of vocabulary. First,
`PMFWeightedBiasLE μ ν δ` — the statement being proved — says `μ` *overshoots*
`ν` by at most `δ`: for every test `w` valued in `[0, 1]`,
`∑ₓ μ(x)·w(x) ≤ ∑ₓ ν(x)·w(x) + δ`. This one-sided form is what the adaptive
hybrid `runFreshPMF_eventBiasLE` consumes, so a single-query bound composes to a
`Q`-query one. Second, the *regularity distance* is the sum

  `∑_Q |pairCount f Q / (#F)² − 1 / #G|`,

the L¹ distance between the two-term output distribution and the uniform
distribution on `G`. CompElliptic's `sum_abs_prob_dev_le` bounds it by `β`
(relying on the Weil bound). Both bias directions come out at this same `β`.

To see why, regroup the per-pair difference by the group element
`Q = f u₀ + f u₁`. Take a nonempty fibre of `Q`, with `k = pairCount f Q ≥ 1`
pairs. Every pair in it looks identical to both laws: the ideal law puts
`1 / (#G·k)` on each — it spreads the `1/#G` that `R` gives to `Q` uniformly
over the `k` pairs — and the real law puts `1 / (#F)²` on each. So the absolute
difference is one constant across all `k` pairs, and summed over the fibre it is

  `k · |1 / (#G·k) − 1 / (#F)²| = |1/#G − k / (#F)²|`,

a single regularity term. The fibre size `k` enters only as `pairCount f Q`
inside that term, and the derivation is the same whatever `k` is — which is why
nonempty fibres need no case split on size. Summing over the nonempty fibres
gives the `pairCount f Q > 0` part of the regularity distance.

The empty fibres need extra care in one direction only. When the ideal law
overshoots the real one, its fallback contributes a *fallback mass* `e / #G`
(spread over all pairs), where `e` is the number of group elements the two-term
sum misses — the mass the ideal random oracle `R` sends to those missed
elements. That fallback mass is exactly the empty-fibre part of the same
regularity distance: an empty fibre has `pairCount f Q = 0`, so its term is
`|0 − 1/#G| = 1/#G`, and there are `e` of them, totalling `e / #G`. So the
nonempty part and the fallback mass together are the *whole* regularity distance
`∑_Q |pairCount f Q / (#F)² − 1/#G| ≤ β` — the fallback fills in the terms the
nonempty part left out, and the bound stays at `β`. In the other direction the
fallback only raises the ideal law, which shrinks `real − ideal`, so that
direction is bounded by the nonempty part alone.
-/

namespace Zcash.Security.GroupHash

open scoped ENNReal
open CompElliptic.Hashing (pairCount)

variable {F : Type*} [Fintype F] [DecidableEq F]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The fibre of `Q` under the two-term sum: the pairs `(u₀, u₁)` with
`f u₀ + f u₁ = Q`. Its cardinality is `pairCount f Q`. -/
def fibre (f : F → G) (Q : G) : Finset (F × F) :=
  Finset.univ.filter fun p => f p.1 + f p.2 = Q

omit [DecidableEq F] [Fintype G] in
/-- The fibre's cardinality is exactly the pair count. -/
theorem fibre_card (f : F → G) (Q : G) : (fibre f Q).card = pairCount f Q := rfl

omit [DecidableEq F] [Fintype G] in
/-- A pair lies in the fibre of its own image. -/
theorem mem_fibre_self (f : F → G) (p : F × F) : p ∈ fibre f (f p.1 + f p.2) := by
  simp [fibre]

omit [DecidableEq F] [Fintype G] in
/-- The fibre of a pair's image is nonempty (it contains the pair). -/
theorem fibre_image_nonempty (f : F → G) (p : F × F) : (fibre f (f p.1 + f p.2)).Nonempty :=
  ⟨p, mem_fibre_self f p⟩

/-- **The fibre sampler.** Draw a pair uniformly from the fibre of `Q`; when the
fibre is empty, fall back to a uniform pair on `F × F` so this stays a genuine
distribution. -/
noncomputable def fibreSampler [Nonempty F] (f : F → G) (Q : G) : PMF (F × F) :=
  if h : (fibre f Q).Nonempty then PMF.uniformOfFinset _ h
  else PMF.uniformOfFintype (F × F)

/-- **The ideal per-query law.** Draw a group element uniformly, then a pair
uniformly from its fibre. This is the distribution that the ideal-world
simulator's answer follows on a fresh query. -/
noncomputable def idealLaw [Nonempty F] [Nonempty G] (f : F → G) : PMF (F × F) :=
  (PMF.uniformOfFintype G).bind (fibreSampler f)

/-- The number of group elements that the two-term sum misses — the elements
whose fibre is empty. Their fallback mass is what the ideal law adds on top of the
fibre-uniform part. -/
def emptyCount (f : F → G) : ℕ := (Finset.univ.filter fun Q => pairCount f Q = 0).card

omit [DecidableEq F] [Fintype G] in
/-- On a pair in the fibre of `Q`, the sampler puts the uniform weight
`1 / pairCount f Q`. -/
theorem fibreSampler_apply_mem [Nonempty F] (f : F → G) {Q : G} {p : F × F}
    (hp : p ∈ fibre f Q) : fibreSampler f Q p = (pairCount f Q : ℝ≥0∞)⁻¹ := by
  rw [fibreSampler, dif_pos ⟨p, hp⟩, PMF.uniformOfFinset_apply_of_mem _ hp, fibre_card]

omit [DecidableEq F] [Fintype G] in
/-- On a pair outside a nonempty fibre of `Q`, the sampler puts no weight. -/
theorem fibreSampler_apply_not_mem [Nonempty F] (f : F → G) {Q : G} {p : F × F}
    (hne : (fibre f Q).Nonempty) (hp : p ∉ fibre f Q) : fibreSampler f Q p = 0 := by
  rw [fibreSampler, dif_pos hne, PMF.uniformOfFinset_apply_of_notMem _ hp]

omit [DecidableEq F] [Fintype G] in
/-- On the empty fibre of `Q`, the sampler falls back to the uniform pair weight. -/
theorem fibreSampler_apply_empty [Nonempty F] (f : F → G) {Q : G} (p : F × F)
    (hempty : ¬ (fibre f Q).Nonempty) :
    fibreSampler f Q p = (Fintype.card (F × F) : ℝ≥0∞)⁻¹ := by
  rw [fibreSampler, dif_neg hempty, PMF.uniformOfFintype_apply]

omit [DecidableEq F] [Fintype G] in
/-- The fibre sampler's measure of an event, when the fibre is nonempty: the
event's share of the fibre. -/
theorem fibreSampler_toOuterMeasure [Nonempty F] (f : F → G) {Q : G}
    (hne : (fibre f Q).Nonempty) (S : Set (F × F)) :
    (fibreSampler f Q).toOuterMeasure S
      = (∑ p ∈ fibre f Q, S.indicator (fun _ => (1 : ℝ≥0∞)) p)
        * (pairCount f Q : ℝ≥0∞)⁻¹ := by
  classical
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  calc ∑ x : F × F, S.indicator (fibreSampler f Q) x
      = ∑ x ∈ fibre f Q, S.indicator (fibreSampler f Q) x := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
        by_cases hs : x ∈ S
        · rw [Set.indicator_of_mem hs, fibreSampler_apply_not_mem f hne hx]
        · rw [Set.indicator_of_notMem hs]
    _ = ∑ x ∈ fibre f Q, S.indicator (fun _ => (1 : ℝ≥0∞)) x
          * (pairCount f Q : ℝ≥0∞)⁻¹ := by
        refine Finset.sum_congr rfl fun x hx => ?_
        by_cases hs : x ∈ S
        · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs,
            fibreSampler_apply_mem f hx, one_mul]
        · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, zero_mul]
    _ = (∑ p ∈ fibre f Q, S.indicator (fun _ => (1 : ℝ≥0∞)) p)
          * (pairCount f Q : ℝ≥0∞)⁻¹ := by
        rw [Finset.sum_mul]

omit [DecidableEq F] [Fintype G] in
/-- The sampler's weight on `p`, split into its fibre-uniform part (nonzero only
on the fibre containing `p`) and its empty-fibre fallback part. -/
theorem fibreSampler_apply_eq [Nonempty F] (f : F → G) (Q : G) (p : F × F) :
    fibreSampler f Q p
      = (if Q = f p.1 + f p.2 then (pairCount f (f p.1 + f p.2) : ℝ≥0∞)⁻¹ else 0)
        + (if pairCount f Q = 0 then (Fintype.card (F × F) : ℝ≥0∞)⁻¹ else 0) := by
  have hself : pairCount f (f p.1 + f p.2) ≠ 0 := by
    rw [← fibre_card]
    exact Finset.card_ne_zero_of_mem (mem_fibre_self f p)
  by_cases hpc : pairCount f Q = 0
  · have hempty : ¬ (fibre f Q).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, not_not, ← Finset.card_eq_zero, fibre_card]; exact hpc
    have hne : Q ≠ f p.1 + f p.2 := fun h => hself (h ▸ hpc)
    rw [fibreSampler_apply_empty f p hempty, if_neg hne, if_pos hpc, zero_add]
  · have hne : (fibre f Q).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, ne_eq, ← Finset.card_eq_zero, fibre_card]; exact hpc
    rw [if_neg hpc, add_zero]
    by_cases hp : p ∈ fibre f Q
    · have hQ : Q = f p.1 + f p.2 := by
        have := (Finset.mem_filter.mp hp).2; exact this.symm
      rw [fibreSampler_apply_mem f hp, if_pos hQ, hQ]
    · rw [fibreSampler_apply_not_mem f hne hp,
        if_neg (fun h => hp (by rw [h]; exact mem_fibre_self f p))]

omit [DecidableEq F] in
/-- The pointwise value of the ideal law: the weight of `p`'s own fibre spread
over the group, plus the empty-fibre fallback mass spread over all pairs. -/
theorem idealLaw_apply [Nonempty F] [Nonempty G] (f : F → G) (p : F × F) :
    idealLaw f p
      = (Fintype.card G : ℝ≥0∞)⁻¹ * (pairCount f (f p.1 + f p.2) : ℝ≥0∞)⁻¹
        + (emptyCount f : ℝ≥0∞)
          * ((Fintype.card G : ℝ≥0∞)⁻¹ * (Fintype.card (F × F) : ℝ≥0∞)⁻¹) := by
  rw [idealLaw, PMF.bind_apply, tsum_fintype]
  have hstep : ∀ Q : G, (PMF.uniformOfFintype G) Q * fibreSampler f Q p
      = (Fintype.card G : ℝ≥0∞)⁻¹ *
          ((if Q = f p.1 + f p.2 then (pairCount f (f p.1 + f p.2) : ℝ≥0∞)⁻¹ else 0)
            + (if pairCount f Q = 0 then (Fintype.card (F × F) : ℝ≥0∞)⁻¹ else 0)) := by
    intro Q
    rw [PMF.uniformOfFintype_apply, fibreSampler_apply_eq f Q p]
  rw [Finset.sum_congr rfl fun Q _ => hstep Q, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ (f p.1 + f p.2)
      (fun _ => (pairCount f (f p.1 + f p.2) : ℝ≥0∞)⁻¹),
    if_pos (Finset.mem_univ _)]
  have hcount : (∑ Q : G, if pairCount f Q = 0 then (Fintype.card (F × F) : ℝ≥0∞)⁻¹ else 0)
      = (emptyCount f : ℝ≥0∞) * (Fintype.card (F × F) : ℝ≥0∞)⁻¹ := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
      emptyCount]
  rw [hcount, mul_add]
  ring

/-- A weighted bias bound follows from the one-sided L¹ bound: against any
`[0, 1]`-valued test, `μ` can exceed `ν` by at most the total of the pointwise
overshoots `μ x - ν x` (truncated subtraction). -/
theorem pmfWeightedBiasLE_of_sum_tsub_le {Ω : Type*} [Fintype Ω] {μ ν : PMF Ω} {δ : ℝ≥0∞}
    (h : ∑ x, (μ x - ν x) ≤ δ) : Zcash.Common.PMFWeightedBiasLE μ ν δ := by
  intro w hw
  calc ∑ x, μ x * w x
      ≤ ∑ x, (ν x * w x + (μ x - ν x) * w x) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [← add_mul]
        gcongr
        exact le_add_tsub
    _ = ∑ x, ν x * w x + ∑ x, (μ x - ν x) * w x := Finset.sum_add_distrib
    _ ≤ ∑ x, ν x * w x + ∑ x, (μ x - ν x) := by
        refine add_le_add le_rfl (Finset.sum_le_sum fun x _ => ?_)
        calc (μ x - ν x) * w x ≤ (μ x - ν x) * 1 := by gcongr; exact hw x
          _ = μ x - ν x := mul_one _
    _ ≤ ∑ x, ν x * w x + δ := add_le_add le_rfl h

omit [DecidableEq F] in
/-- Sums over pairs regroup by the pair's group image, weighted by the fibre
sizes. -/
theorem sum_pairs_eq [Nonempty F] (f : F → G) (g : G → ℝ≥0∞) :
    ∑ p : F × F, g (f p.1 + f p.2) = ∑ Q, (pairCount f Q : ℝ≥0∞) * g Q := by
  rw [← Finset.sum_fiberwise Finset.univ (fun p : F × F => f p.1 + f p.2)
    (fun p => g (f p.1 + f p.2))]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [show (pairCount f Q : ℝ≥0∞) * g Q
      = ∑ _p ∈ Finset.univ.filter (fun p : F × F => f p.1 + f p.2 = Q), g Q by
    rw [Finset.sum_const, nsmul_eq_mul]; rfl]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [(Finset.mem_filter.mp hp).2]

omit [DecidableEq F] in
/-- The total pointwise overshoot of the real law over the ideal law is at most
the regularity distance: dropping the ideal law's fallback part only enlarges
the overshoot, and the fibre-uniform part regroups to the regularity terms of
the nonempty fibres. -/
theorem sum_tsub_uniform_idealLaw_le [Nonempty F] [Nonempty G] (f : F → G) {β : ℝ}
    (hdev : ∑ Q, |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
        - 1 / (Fintype.card G : ℝ)| ≤ β) :
    ∑ p : F × F, (PMF.uniformOfFintype (F × F) p - idealLaw f p)
      ≤ ENNReal.ofReal β := by
  have hcard : (Fintype.card (F × F) : ℝ≥0∞)⁻¹
      = ENNReal.ofReal (1 / (Fintype.card F : ℝ)^2) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast, one_div,
      Fintype.card_prod, Nat.cast_mul, sq]
  have hpoint : ∀ p : F × F,
      PMF.uniformOfFintype (F × F) p - idealLaw f p
        ≤ (Fintype.card (F × F) : ℝ≥0∞)⁻¹
            - (Fintype.card G : ℝ≥0∞)⁻¹ * (pairCount f (f p.1 + f p.2) : ℝ≥0∞)⁻¹ := by
    intro p
    rw [PMF.uniformOfFintype_apply, idealLaw_apply]
    exact tsub_le_tsub_left (self_le_add_right _ _) _
  refine le_trans (Finset.sum_le_sum fun p _ => hpoint p) ?_
  rw [sum_pairs_eq f (fun Q => (Fintype.card (F × F) : ℝ≥0∞)⁻¹
    - (Fintype.card G : ℝ≥0∞)⁻¹ * (pairCount f Q : ℝ≥0∞)⁻¹)]
  have hterm : ∀ Q : G, (pairCount f Q : ℝ≥0∞) * ((Fintype.card (F × F) : ℝ≥0∞)⁻¹
      - (Fintype.card G : ℝ≥0∞)⁻¹ * (pairCount f Q : ℝ≥0∞)⁻¹)
      ≤ ENNReal.ofReal |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
          - 1 / (Fintype.card G : ℝ)| := by
    intro Q
    by_cases hk : pairCount f Q = 0
    · simp [hk]
    · have hkpos : (0 : ℝ) < pairCount f Q := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      have hGpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
      have hFpos : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
      have hgk : (Fintype.card G : ℝ≥0∞)⁻¹ * (pairCount f Q : ℝ≥0∞)⁻¹
          = ENNReal.ofReal (1 / ((Fintype.card G : ℝ) * (pairCount f Q : ℝ))) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
          ENNReal.ofReal_mul (le_of_lt hGpos), ENNReal.ofReal_natCast,
          ENNReal.ofReal_natCast, one_div, ENNReal.mul_inv
            (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
            (Or.inl (ENNReal.natCast_ne_top _))]
      rw [hcard, hgk, ← ENNReal.ofReal_sub _ (by positivity),
        ← ENNReal.ofReal_natCast (pairCount f Q), ← ENNReal.ofReal_mul (by positivity)]
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_le_ofReal
        (le_abs_self _))
      refine le_of_eq ?_
      field_simp
  refine le_trans (Finset.sum_le_sum fun Q _ => hterm Q) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun Q _ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hdev

omit [DecidableEq F] in
/-- **The single-query bias, real overshooting ideal.** The real per-query law
(uniform on `F × F`) overshoots the ideal law by at most the regularity distance
against every `[0, 1]`-valued test. -/
theorem weightedBias_real_le [Nonempty F] [Nonempty G] (f : F → G) {β : ℝ}
    (hdev : ∑ Q, |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
        - 1 / (Fintype.card G : ℝ)| ≤ β) :
    Zcash.Common.PMFWeightedBiasLE (PMF.uniformOfFintype (F × F)) (idealLaw f)
      (ENNReal.ofReal β) :=
  pmfWeightedBiasLE_of_sum_tsub_le (sum_tsub_uniform_idealLaw_le f hdev)

omit [DecidableEq F] in
/-- The total pointwise overshoot of the ideal law over the real law is at most
the regularity distance: the fibre-uniform part accounts for the nonempty
fibres' regularity terms, and the fallback mass is exactly the empty fibres'
terms, so together they exhaust the sum. -/
theorem sum_tsub_idealLaw_uniform_le [Nonempty F] [Nonempty G] (f : F → G) {β : ℝ}
    (hdev : ∑ Q, |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
        - 1 / (Fintype.card G : ℝ)| ≤ β) :
    ∑ p : F × F, (idealLaw f p - PMF.uniformOfFintype (F × F) p)
      ≤ ENNReal.ofReal β := by
  have hcard : (Fintype.card (F × F) : ℝ≥0∞)⁻¹
      = ENNReal.ofReal (1 / (Fintype.card F : ℝ)^2) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast, one_div,
      Fintype.card_prod, Nat.cast_mul, sq]
  -- The pointwise overshoot splits into the fibre part's overshoot plus the
  -- fallback summand.
  have hpoint : ∀ p : F × F,
      idealLaw f p - PMF.uniformOfFintype (F × F) p
        ≤ ((Fintype.card G : ℝ≥0∞)⁻¹ * (pairCount f (f p.1 + f p.2) : ℝ≥0∞)⁻¹
              - (Fintype.card (F × F) : ℝ≥0∞)⁻¹)
            + (emptyCount f : ℝ≥0∞)
              * ((Fintype.card G : ℝ≥0∞)⁻¹ * (Fintype.card (F × F) : ℝ≥0∞)⁻¹) := by
    intro p
    rw [idealLaw_apply, PMF.uniformOfFintype_apply]
    generalize (Fintype.card G : ℝ≥0∞)⁻¹ * (pairCount f (f p.1 + f p.2) : ℝ≥0∞)⁻¹ = A
    generalize (emptyCount f : ℝ≥0∞)
      * ((Fintype.card G : ℝ≥0∞)⁻¹ * (Fintype.card (F × F) : ℝ≥0∞)⁻¹) = B
    calc A + B - (Fintype.card (F × F) : ℝ≥0∞)⁻¹
        = B + A - (Fintype.card (F × F) : ℝ≥0∞)⁻¹ := by rw [add_comm]
      _ ≤ B + (A - (Fintype.card (F × F) : ℝ≥0∞)⁻¹) := add_tsub_le_assoc
      _ = A - (Fintype.card (F × F) : ℝ≥0∞)⁻¹ + B := add_comm _ _
  refine le_trans (Finset.sum_le_sum fun p _ => hpoint p) ?_
  rw [Finset.sum_add_distrib]
  -- The fallback summands total the fallback mass `emptyCount / #G`.
  have hfall : (∑ _p : F × F, (emptyCount f : ℝ≥0∞)
      * ((Fintype.card G : ℝ≥0∞)⁻¹ * (Fintype.card (F × F) : ℝ≥0∞)⁻¹))
      = (emptyCount f : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hswap : (Fintype.card (F × F) : ℝ≥0∞) * ((emptyCount f : ℝ≥0∞)
        * ((Fintype.card G : ℝ≥0∞)⁻¹ * (Fintype.card (F × F) : ℝ≥0∞)⁻¹))
        = ((emptyCount f : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹)
          * ((Fintype.card (F × F) : ℝ≥0∞) * (Fintype.card (F × F) : ℝ≥0∞)⁻¹) := by
      ring
    rw [hswap, ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _), mul_one]
  rw [hfall, sum_pairs_eq f (fun Q => (Fintype.card G : ℝ≥0∞)⁻¹ * (pairCount f Q : ℝ≥0∞)⁻¹
    - (Fintype.card (F × F) : ℝ≥0∞)⁻¹)]
  -- Per output: nonempty fibres pay their regularity term through the fibre
  -- part, empty fibres pay theirs through the fallback mass.
  have hterm : ∀ Q : G, (pairCount f Q : ℝ≥0∞)
      * ((Fintype.card G : ℝ≥0∞)⁻¹ * (pairCount f Q : ℝ≥0∞)⁻¹
          - (Fintype.card (F × F) : ℝ≥0∞)⁻¹)
      ≤ if pairCount f Q = 0 then 0
        else ENNReal.ofReal |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
          - 1 / (Fintype.card G : ℝ)| := by
    intro Q
    by_cases hk : pairCount f Q = 0
    · simp [hk]
    · rw [if_neg hk]
      have hkpos : (0 : ℝ) < pairCount f Q := by
        exact_mod_cast Nat.pos_of_ne_zero hk
      have hGpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
      have hFpos : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
      have hgk : (Fintype.card G : ℝ≥0∞)⁻¹ * (pairCount f Q : ℝ≥0∞)⁻¹
          = ENNReal.ofReal (1 / ((Fintype.card G : ℝ) * (pairCount f Q : ℝ))) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
          ENNReal.ofReal_mul (le_of_lt hGpos), ENNReal.ofReal_natCast,
          ENNReal.ofReal_natCast, one_div, ENNReal.mul_inv
            (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
            (Or.inl (ENNReal.natCast_ne_top _))]
      rw [hcard, hgk, ← ENNReal.ofReal_sub _ (by positivity),
        ← ENNReal.ofReal_natCast (pairCount f Q), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_sub_comm]
      refine le_trans (le_of_eq ?_) (le_abs_self _)
      field_simp
  refine le_trans (add_le_add (Finset.sum_le_sum fun Q _ => hterm Q) le_rfl) ?_
  -- The fallback mass is the empty fibres' share of the regularity distance.
  have hempty : (emptyCount f : ℝ≥0∞) * (Fintype.card G : ℝ≥0∞)⁻¹
      = ∑ Q, if pairCount f Q = 0
          then ENNReal.ofReal |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
            - 1 / (Fintype.card G : ℝ)| else 0 := by
    have hGpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    have hcongr : ∀ Q : G, (if pairCount f Q = 0
        then ENNReal.ofReal |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
          - 1 / (Fintype.card G : ℝ)| else 0)
        = if pairCount f Q = 0 then (Fintype.card G : ℝ≥0∞)⁻¹ else 0 := by
      intro Q
      by_cases hk : pairCount f Q = 0
      · rw [if_pos hk, if_pos hk, hk, Nat.cast_zero, zero_div, zero_sub, abs_neg,
          abs_of_nonneg (by positivity), ENNReal.ofReal_div_of_pos hGpos,
          ENNReal.ofReal_one, ENNReal.ofReal_natCast, one_div]
      · rw [if_neg hk, if_neg hk]
    rw [Finset.sum_congr rfl fun Q _ => hcongr Q, Finset.sum_ite, Finset.sum_const,
      Finset.sum_const_zero, add_zero, nsmul_eq_mul, emptyCount]
  rw [hempty, ← Finset.sum_add_distrib]
  have hjoin : ∀ Q : G, ((if pairCount f Q = 0 then 0
      else ENNReal.ofReal |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
        - 1 / (Fintype.card G : ℝ)|)
      + (if pairCount f Q = 0
        then ENNReal.ofReal |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
          - 1 / (Fintype.card G : ℝ)| else 0))
      = ENNReal.ofReal |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
          - 1 / (Fintype.card G : ℝ)| := by
    intro Q
    by_cases hk : pairCount f Q = 0
    · rw [if_pos hk, if_pos hk, zero_add]
    · rw [if_neg hk, if_neg hk, add_zero]
  rw [Finset.sum_congr rfl fun Q _ => hjoin Q,
    ← ENNReal.ofReal_sum_of_nonneg (fun Q _ => abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hdev

omit [DecidableEq F] in
/-- **The single-query bias, ideal overshooting real.** The same regularity
distance bounds the other direction: the ideal law overshoots the real one by at
most `β`, the fallback mass of the empty fibres being part of the same sum. -/
theorem weightedBias_ideal_le [Nonempty F] [Nonempty G] (f : F → G) {β : ℝ}
    (hdev : ∑ Q, |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
        - 1 / (Fintype.card G : ℝ)| ≤ β) :
    Zcash.Common.PMFWeightedBiasLE (idealLaw f) (PMF.uniformOfFintype (F × F))
      (ENNReal.ofReal β) :=
  pmfWeightedBiasLE_of_sum_tsub_le (sum_tsub_idealLaw_uniform_le f hdev)

end Zcash.Security.GroupHash
