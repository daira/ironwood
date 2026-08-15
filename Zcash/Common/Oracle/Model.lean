import Mathlib.Probability.Distributions.Uniform

/-!
# One-sided bias interfaces for oracle experiments

`PMFEventBiasLE` and `PMFWeightedBiasLE` are the one-sided statistical-distance interfaces the
adaptive hybrid (`Oracle/Hybrid.lean`) and the security capstones consume: `actual` overshoots
`ideal` by at most `ε`, on every event (`PMFEventBiasLE`) or against every `[0,1]`-valued test
(`PMFWeightedBiasLE`, the stronger continuation-weighted form).

Generic in the sample space, with no dependency on any transcript type or field. The `Fp`-specific
uniform-challenge idealization (`uniformChallenge`) and the deployed `Challenge255 → Fp` conversion
bias live on the Snark side (`Zcash/Snark/Soundness/Oracle/ChallengeUniform.lean` and
`Challenge255.lean`), since they name concrete deployed objects.
-/
namespace Zcash.Common

open scoped ENNReal

/-- `actual` overshoots `ideal` by at most `ε` on every event.  This one-sided statistical-distance
interface is the exact premise needed to transport a soundness upper bound; it may represent one
squeeze or an entire adaptive transcript experiment. -/
def PMFEventBiasLE {Ω : Type*} (actual ideal : PMF Ω) (ε : ℝ≥0∞) : Prop :=
  ∀ S : Set Ω, actual.toOuterMeasure S ≤ ideal.toOuterMeasure S + ε

/-- `actual` overshoots `ideal` by at most `ε` against every test taking values in `[0,1]`.

This finite weighted form is stronger than `PMFEventBiasLE`: indicator tests recover events, while
continuation probabilities are the weights needed to compose a one-squeeze bound through an
adaptive query tree. -/
def PMFWeightedBiasLE {Ω : Type*} [Fintype Ω]
    (actual ideal : PMF Ω) (ε : ℝ≥0∞) : Prop :=
  ∀ weight : Ω → ℝ≥0∞, (∀ x, weight x ≤ 1) →
    ∑ x, actual x * weight x ≤ ∑ x, ideal x * weight x + ε

/-- A weighted bias bound specializes to the event-bias interface used by the capstones. -/
theorem PMFWeightedBiasLE.eventBiasLE {Ω : Type*} [Fintype Ω]
    {actual ideal : PMF Ω} {ε : ℝ≥0∞}
    (hbias : PMFWeightedBiasLE actual ideal ε) :
    PMFEventBiasLE actual ideal ε := by
  classical
  intro S
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, tsum_fintype, tsum_fintype]
  simpa only [Set.indicator_apply, mul_ite, mul_one, mul_zero] using
    hbias (fun x ↦ if x ∈ S then 1 else 0) (fun x ↦ by
      by_cases hx : x ∈ S <;> simp [hx])

/-- Mixing pointwise-biased experiments with the same outer distribution preserves their bias.
This transports a per-parameter event bound to the corresponding joint experiment. -/
theorem PMFEventBiasLE.bind_same {α β : Type*} [Fintype β] {μ : PMF β}
    {actual ideal : β → PMF α} {ε : ℝ≥0∞}
    (hbias : ∀ b, PMFEventBiasLE (actual b) (ideal b) ε) :
    PMFEventBiasLE (μ.bind actual) (μ.bind ideal) ε := by
  intro S
  simp only [PMF.toOuterMeasure_bind_apply, tsum_fintype]
  calc
    ∑ b, μ b * (actual b).toOuterMeasure S ≤
        ∑ b, μ b * ((ideal b).toOuterMeasure S + ε) :=
      Finset.sum_le_sum fun b _ ↦ mul_le_mul_right (hbias b S) _
    _ = ∑ b, μ b * (ideal b).toOuterMeasure S + ε := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      have hmass : (∑ b, μ b) = 1 := by
        have h := μ.tsum_coe
        rwa [tsum_fintype] at h
      rw [hmass, one_mul]

/-- Transport an ideal-experiment event bound to an explicitly related actual distribution. -/
theorem event_measure_le_of_bias {Ω : Type*} {actual ideal : PMF Ω} {ε bound : ℝ≥0∞}
    (hbias : PMFEventBiasLE actual ideal ε) (event : Set Ω)
    (hideal : ideal.toOuterMeasure event ≤ bound) :
    actual.toOuterMeasure event ≤ bound + ε := by
  exact (hbias event).trans (add_le_add hideal le_rfl)

end Zcash.Common
