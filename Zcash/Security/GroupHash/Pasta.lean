import CompElliptic.CurveForms.ShortWeierstrass
import CompElliptic.Fields.Pasta
import CompElliptic.Hashing.PastaSSWU
import CompElliptic.Hashing.SignedLift
import CompElliptic.Hashing.TwoTermUniformity
import CompElliptic.Hashing.WellDistributed
import Zcash.Security.GroupHash.Sampler
import Zcash.Security.GroupHash.Simulator

/-!
# The single-query bias at the deployed Pasta group hashes

This instantiates the generic single-query bias of `GroupHash/Sampler.lean` at
the mappings the deployed group hashes actually use: `Pallas.mapToCurve` and
`Vesta.mapToCurve`, CompElliptic's formalizations of RFC 9380's `map_to_curve`
for the Pasta curves.

The generic bias theorems consume one hypothesis: the regularity distance of
the mapping is at most some `β`. CompElliptic's regularity analysis supplies
that for a mapping satisfying the Weil bound. We state the Weil-bound
hypothesis for the *zero-repaired* variant of the deployed mapping rather than
for the deployed mapping itself, because the zero-repaired variant is
literally odd, and odd mappings are what the established character-sum
analysis addresses. The hypothesis is the substantive analytic input either
way; the two variants' character sums differ by at most `2`
(`norm_charSum_mapToCurve_sub_zeroRepaired`), so nothing essential hangs on
the choice. `sum_abs_prob_dev_transport_le` then carries the regularity
conclusion to the deployed mapping: the two mappings agree away from the
single input `0`, so the deployed mapping's regularity distance is at most the
repaired one's budget `β` plus the transport term `(4·#F − 2)/(#F)²`.

So each curve gets its regularity-distance bound
(`pallas_regularityDistance_le`, `vesta_regularityDistance_le`) and the two
bias directions at the deployed mapping (`pallas_weightedBias_real_le`,
`pallas_weightedBias_ideal_le`, and the Vesta twins), all under the named
`WeilBounded` hypothesis: established mathematics, but an unformalized input
(see CompElliptic's `WellDistributed.lean`).

`GroupHash/Simulator.lean`'s rejection sampler is also instantiated here.
Its one counting input is an unconditional single-fibre bound: CompElliptic
counts the nonzero preimages of a point
(`Pallas.card_mapToCurve_fibre_le` and the Vesta twin), and the input `0`
adds at most one more. `deployedFibreBound` names the resulting bound, and
the deployed mappings satisfy the simulator's fibre-size hypothesis at that
constant. The round-count tails and law, the two-sided output-law bias, and
the `K → ∞` convergence then instantiate directly.
-/

namespace Zcash.Security.GroupHash

open CompElliptic.Hashing (pairCount WeilBounded zeroRepaired
  sum_abs_prob_dev_transport_le)
open CompElliptic.CurveForms.ShortWeierstrass (SWPoint)
open CompElliptic.Curves.Pasta
open CompElliptic.Fields.Pasta (PallasBaseField VestaBaseField)

/-! ## Pallas -/

/-- The deployed Pallas mapping agrees with its zero-repaired variant away from
`0`, because the repair fires only at `0`. -/
theorem pallas_eq_zeroRepaired_off_zero :
    ∀ u : PallasBaseField, u ≠ 0 → Pallas.mapToCurve u
      = zeroRepaired Pallas.mapToCurve u :=
  fun _ hu => (if_neg hu).symm

/-- **The deployed-map regularity premiss for Pallas**: from a Weil-type bound
with constant `C` on the zero-repaired mapping, the deployed mapping's
regularity distance is at most `β + (4·#F − 2)/(#F)²`, by the transport
across the single input `0`. -/
theorem pallas_regularityDistance_le {C β : ℝ}
    (h : WeilBounded (zeroRepaired Pallas.mapToCurve) C) (hβ : 0 ≤ β)
    (hbound : ((Fintype.card (SWPoint Pallas.curve) : ℝ) - 1) * C^4
      / (Fintype.card PallasBaseField : ℝ)^2 ≤ β^2) :
    ∑ Q, |(pairCount Pallas.mapToCurve Q : ℝ)
        / (Fintype.card PallasBaseField : ℝ)^2
        - 1 / (Fintype.card (SWPoint Pallas.curve) : ℝ)|
      ≤ β + (4 * Fintype.card PallasBaseField - 2)
          / (Fintype.card PallasBaseField : ℝ)^2 :=
  sum_abs_prob_dev_transport_le Pallas.mapToCurve _ 0
    pallas_eq_zeroRepaired_off_zero h hβ hbound

/-- **The single-query bias at the deployed Pallas mapping, real overshooting
ideal**, under the named Weil-bound hypothesis (constant `C`). -/
theorem pallas_weightedBias_real_le {C β : ℝ}
    (h : WeilBounded (zeroRepaired Pallas.mapToCurve) C) (hβ : 0 ≤ β)
    (hbound : ((Fintype.card (SWPoint Pallas.curve) : ℝ) - 1) * C^4
      / (Fintype.card PallasBaseField : ℝ)^2 ≤ β^2) :
    Zcash.Common.PMFWeightedBiasLE
      (PMF.uniformOfFintype (PallasBaseField × PallasBaseField))
      (idealLaw Pallas.mapToCurve)
      (ENNReal.ofReal (β + (4 * Fintype.card PallasBaseField - 2)
        / (Fintype.card PallasBaseField : ℝ)^2)) :=
  weightedBias_real_le _ (pallas_regularityDistance_le h hβ hbound)

/-- **The single-query bias at the deployed Pallas mapping, ideal overshooting
real**, under the named Weil-bound hypothesis (constant `C`). -/
theorem pallas_weightedBias_ideal_le {C β : ℝ}
    (h : WeilBounded (zeroRepaired Pallas.mapToCurve) C) (hβ : 0 ≤ β)
    (hbound : ((Fintype.card (SWPoint Pallas.curve) : ℝ) - 1) * C^4
      / (Fintype.card PallasBaseField : ℝ)^2 ≤ β^2) :
    Zcash.Common.PMFWeightedBiasLE (idealLaw Pallas.mapToCurve)
      (PMF.uniformOfFintype (PallasBaseField × PallasBaseField))
      (ENNReal.ofReal (β + (4 * Fintype.card PallasBaseField - 2)
        / (Fintype.card PallasBaseField : ℝ)^2)) :=
  weightedBias_ideal_le _ (pallas_regularityDistance_le h hβ hbound)

/-! ## Vesta -/

/-- The deployed Vesta mapping agrees with its zero-repaired variant away from
`0`, because the repair fires only at `0`. -/
theorem vesta_eq_zeroRepaired_off_zero :
    ∀ u : VestaBaseField, u ≠ 0 → Vesta.mapToCurve u
      = zeroRepaired Vesta.mapToCurve u :=
  fun _ hu => (if_neg hu).symm

/-- **The deployed-map regularity premiss for Vesta**: from a Weil-type bound
with constant `C` on the zero-repaired mapping, the deployed mapping's
regularity distance is at most `β + (4·#F − 2)/(#F)²`, by the transport
across the single input `0`. -/
theorem vesta_regularityDistance_le {C β : ℝ}
    (h : WeilBounded (zeroRepaired Vesta.mapToCurve) C) (hβ : 0 ≤ β)
    (hbound : ((Fintype.card (SWPoint Vesta.curve) : ℝ) - 1) * C^4
      / (Fintype.card VestaBaseField : ℝ)^2 ≤ β^2) :
    ∑ Q, |(pairCount Vesta.mapToCurve Q : ℝ)
        / (Fintype.card VestaBaseField : ℝ)^2
        - 1 / (Fintype.card (SWPoint Vesta.curve) : ℝ)|
      ≤ β + (4 * Fintype.card VestaBaseField - 2)
          / (Fintype.card VestaBaseField : ℝ)^2 :=
  sum_abs_prob_dev_transport_le Vesta.mapToCurve _ 0
    vesta_eq_zeroRepaired_off_zero h hβ hbound

/-- **The single-query bias at the deployed Vesta mapping, real overshooting
ideal**, under the named Weil-bound hypothesis (constant `C`). -/
theorem vesta_weightedBias_real_le {C β : ℝ}
    (h : WeilBounded (zeroRepaired Vesta.mapToCurve) C) (hβ : 0 ≤ β)
    (hbound : ((Fintype.card (SWPoint Vesta.curve) : ℝ) - 1) * C^4
      / (Fintype.card VestaBaseField : ℝ)^2 ≤ β^2) :
    Zcash.Common.PMFWeightedBiasLE
      (PMF.uniformOfFintype (VestaBaseField × VestaBaseField))
      (idealLaw Vesta.mapToCurve)
      (ENNReal.ofReal (β + (4 * Fintype.card VestaBaseField - 2)
        / (Fintype.card VestaBaseField : ℝ)^2)) :=
  weightedBias_real_le _ (vesta_regularityDistance_le h hβ hbound)

/-- **The single-query bias at the deployed Vesta mapping, ideal overshooting
real**, under the named Weil-bound hypothesis (constant `C`). -/
theorem vesta_weightedBias_ideal_le {C β : ℝ}
    (h : WeilBounded (zeroRepaired Vesta.mapToCurve) C) (hβ : 0 ≤ β)
    (hbound : ((Fintype.card (SWPoint Vesta.curve) : ℝ) - 1) * C^4
      / (Fintype.card VestaBaseField : ℝ)^2 ≤ β^2) :
    Zcash.Common.PMFWeightedBiasLE (idealLaw Vesta.mapToCurve)
      (PMF.uniformOfFintype (VestaBaseField × VestaBaseField))
      (ENNReal.ofReal (β + (4 * Fintype.card VestaBaseField - 2)
        / (Fintype.card VestaBaseField : ℝ)^2)) :=
  weightedBias_ideal_le _ (vesta_regularityDistance_le h hβ hbound)

/-! ## The simulator at the deployed mappings -/

/-- The single-fibre bound at the deployed mappings: CompElliptic counts at
most `10` nonzero preimages per point, and the input `0` can add one more.
The definition localizes the constant, so a tightened CompElliptic count
(the optimum is `4`) changes it in one place. -/
def deployedFibreBound : ℕ := 11

instance : NeZero deployedFibreBound := ⟨by decide⟩

/-- The deployed Pallas mapping has at most `deployedFibreBound` preimages
per point: the nonzero ones counted by `Pallas.card_mapToCurve_fibre_le`,
and possibly `0`. This discharges the simulator's fibre-size hypothesis. -/
theorem pallas_singleFibre_card_le (P : SWPoint Pallas.curve) :
    (singleFibre Pallas.mapToCurve P).card ≤ deployedFibreBound :=
  card_singleFibre_le_succ (fun Q => Pallas.card_mapToCurve_fibre_le Q) P

/-- The deployed Pallas round-count tail: below the cap `K`, more than `k`
rounds are consumed with probability exactly
`(1 - acceptProb Pallas.mapToCurve deployedFibreBound Q)^k`. -/
theorem pallas_simCapped_tail (Q : SWPoint Pallas.curve) {K k : ℕ}
    (h : k < K) :
    (simCapped Pallas.mapToCurve deployedFibreBound Q K).toOuterMeasure {x | k < x.2}
      = (1 - acceptProb Pallas.mapToCurve deployedFibreBound Q)^k :=
  simCapped_tail Pallas.mapToCurve pallas_singleFibre_card_le Q K k h

/-- The deployed Pallas round-count law: below the cap the round count is
geometric. -/
theorem pallas_simCapped_round_law (Q : SWPoint Pallas.curve) {K i : ℕ}
    (h : i+1 < K) :
    (simCapped Pallas.mapToCurve deployedFibreBound Q K).toOuterMeasure {x | x.2 = i+1}
      = acceptProb Pallas.mapToCurve deployedFibreBound Q
        * (1 - acceptProb Pallas.mapToCurve deployedFibreBound Q)^i :=
  simCapped_round_law Pallas.mapToCurve pallas_singleFibre_card_le Q h

/-- The deployed Pallas output law at cap `K` and the fibre sampler are
within `(1 - acceptProb Pallas.mapToCurve deployedFibreBound Q)^K` of each other on every
event, in both directions. -/
theorem pallas_simOut_eventBiasLE (Q : SWPoint Pallas.curve) (K : ℕ) :
    Zcash.Common.PMFEventBiasLE (simOut Pallas.mapToCurve deployedFibreBound Q K)
      (fibreSampler Pallas.mapToCurve Q)
      ((1 - acceptProb Pallas.mapToCurve deployedFibreBound Q)^K)
    ∧ Zcash.Common.PMFEventBiasLE (fibreSampler Pallas.mapToCurve Q)
      (simOut Pallas.mapToCurve deployedFibreBound Q K)
      ((1 - acceptProb Pallas.mapToCurve deployedFibreBound Q)^K) :=
  ⟨simOut_eventBiasLE_fibreSampler Pallas.mapToCurve
      pallas_singleFibre_card_le Q K,
   fibreSampler_eventBiasLE_simOut Pallas.mapToCurve
      pallas_singleFibre_card_le Q K⟩

/-- As its cap grows, the deployed Pallas simulator's output law converges
to the fibre sampler on every event, for every target. -/
theorem pallas_simOut_tendsto (Q : SWPoint Pallas.curve)
    (S : Set (PallasBaseField × PallasBaseField)) :
    Filter.Tendsto
      (fun K => (simOut Pallas.mapToCurve deployedFibreBound Q K).toOuterMeasure S)
      Filter.atTop
      (nhds ((fibreSampler Pallas.mapToCurve Q).toOuterMeasure S)) :=
  simOut_tendsto_fibreSampler Pallas.mapToCurve pallas_singleFibre_card_le Q S

/-- The deployed Vesta mapping has at most `deployedFibreBound` preimages
per point: the nonzero ones counted by `Vesta.card_mapToCurve_fibre_le`,
and possibly `0`. This discharges the simulator's fibre-size hypothesis. -/
theorem vesta_singleFibre_card_le (P : SWPoint Vesta.curve) :
    (singleFibre Vesta.mapToCurve P).card ≤ deployedFibreBound :=
  card_singleFibre_le_succ (fun Q => Vesta.card_mapToCurve_fibre_le Q) P

/-- The deployed Vesta round-count tail: below the cap `K`, more than `k`
rounds are consumed with probability exactly
`(1 - acceptProb Vesta.mapToCurve deployedFibreBound Q)^k`. -/
theorem vesta_simCapped_tail (Q : SWPoint Vesta.curve) {K k : ℕ}
    (h : k < K) :
    (simCapped Vesta.mapToCurve deployedFibreBound Q K).toOuterMeasure {x | k < x.2}
      = (1 - acceptProb Vesta.mapToCurve deployedFibreBound Q)^k :=
  simCapped_tail Vesta.mapToCurve vesta_singleFibre_card_le Q K k h

/-- The deployed Vesta round-count law: below the cap the round count is
geometric. -/
theorem vesta_simCapped_round_law (Q : SWPoint Vesta.curve) {K i : ℕ}
    (h : i+1 < K) :
    (simCapped Vesta.mapToCurve deployedFibreBound Q K).toOuterMeasure {x | x.2 = i+1}
      = acceptProb Vesta.mapToCurve deployedFibreBound Q
        * (1 - acceptProb Vesta.mapToCurve deployedFibreBound Q)^i :=
  simCapped_round_law Vesta.mapToCurve vesta_singleFibre_card_le Q h

/-- The deployed Vesta output law at cap `K` and the fibre sampler are
within `(1 - acceptProb Vesta.mapToCurve deployedFibreBound Q)^K` of each other on every
event, in both directions. -/
theorem vesta_simOut_eventBiasLE (Q : SWPoint Vesta.curve) (K : ℕ) :
    Zcash.Common.PMFEventBiasLE (simOut Vesta.mapToCurve deployedFibreBound Q K)
      (fibreSampler Vesta.mapToCurve Q)
      ((1 - acceptProb Vesta.mapToCurve deployedFibreBound Q)^K)
    ∧ Zcash.Common.PMFEventBiasLE (fibreSampler Vesta.mapToCurve Q)
      (simOut Vesta.mapToCurve deployedFibreBound Q K)
      ((1 - acceptProb Vesta.mapToCurve deployedFibreBound Q)^K) :=
  ⟨simOut_eventBiasLE_fibreSampler Vesta.mapToCurve
      vesta_singleFibre_card_le Q K,
   fibreSampler_eventBiasLE_simOut Vesta.mapToCurve
      vesta_singleFibre_card_le Q K⟩

/-- As its cap grows, the deployed Vesta simulator's output law converges
to the fibre sampler on every event, for every target. -/
theorem vesta_simOut_tendsto (Q : SWPoint Vesta.curve)
    (S : Set (VestaBaseField × VestaBaseField)) :
    Filter.Tendsto
      (fun K => (simOut Vesta.mapToCurve deployedFibreBound Q K).toOuterMeasure S)
      Filter.atTop
      (nhds ((fibreSampler Vesta.mapToCurve Q).toOuterMeasure S)) :=
  simOut_tendsto_fibreSampler Vesta.mapToCurve vesta_singleFibre_card_le Q S

end Zcash.Security.GroupHash
