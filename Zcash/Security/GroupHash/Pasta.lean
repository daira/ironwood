import CompElliptic.CurveForms.ShortWeierstrass
import CompElliptic.Fields.Pasta
import CompElliptic.Hashing.PastaSSWU
import CompElliptic.Hashing.SignedLift
import CompElliptic.Hashing.TwoTermUniformity
import CompElliptic.Hashing.WellDistributed
import Zcash.Security.GroupHash.Sampler

/-!
# The single-query bias at the deployed Pasta group hashes

This instantiates the generic single-query bias of `GroupHash/Sampler.lean` at
the mappings the deployed group hashes actually use: `Pallas.mapToCurve` and
`Vesta.mapToCurve`, CompElliptic's formalizations of RFC 9380's `map_to_curve`
for the Pasta curves.

The generic bias theorems consume one hypothesis: the regularity distance of
the mapping is at most some `ε`. CompElliptic's regularity analysis supplies
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
repaired one's budget `ε` plus the transport term `(4·#F − 2)/(#F)²`.

So each curve gets its regularity-distance bound
(`pallas_regularityDistance_le`, `vesta_regularityDistance_le`) and the two
bias directions at the deployed mapping (`pallas_weightedBias_real_le`,
`pallas_weightedBias_ideal_le`, and the Vesta twins), all under the named
`WeilBounded` hypothesis: established mathematics, but an unformalized input
(see CompElliptic's `WellDistributed.lean`).
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

/-- **The deployed-map regularity premiss for Pallas**: from the Weil bound on
the zero-repaired mapping, the deployed mapping's regularity distance is at
most `ε + (4·#F − 2)/(#F)²`, by the transport across the single input `0`. -/
theorem pallas_regularityDistance_le {C ε : ℝ}
    (h : WeilBounded (zeroRepaired Pallas.mapToCurve) C) (hε : 0 ≤ ε)
    (hbound : ((Fintype.card (SWPoint Pallas.curve) : ℝ) - 1) * C^4
      / (Fintype.card PallasBaseField : ℝ)^2 ≤ ε^2) :
    ∑ Q, |(pairCount Pallas.mapToCurve Q : ℝ)
        / (Fintype.card PallasBaseField : ℝ)^2
        - 1 / (Fintype.card (SWPoint Pallas.curve) : ℝ)|
      ≤ ε + (4 * Fintype.card PallasBaseField - 2)
          / (Fintype.card PallasBaseField : ℝ)^2 :=
  sum_abs_prob_dev_transport_le Pallas.mapToCurve _ 0
    pallas_eq_zeroRepaired_off_zero h hε hbound

/-- **The single-query bias at the deployed Pallas mapping, real overshooting
ideal**, under the named Weil-bound hypothesis. -/
theorem pallas_weightedBias_real_le {C ε : ℝ}
    (h : WeilBounded (zeroRepaired Pallas.mapToCurve) C) (hε : 0 ≤ ε)
    (hbound : ((Fintype.card (SWPoint Pallas.curve) : ℝ) - 1) * C^4
      / (Fintype.card PallasBaseField : ℝ)^2 ≤ ε^2) :
    Zcash.Common.PMFWeightedBiasLE
      (PMF.uniformOfFintype (PallasBaseField × PallasBaseField))
      (idealLaw Pallas.mapToCurve)
      (ENNReal.ofReal (ε + (4 * Fintype.card PallasBaseField - 2)
        / (Fintype.card PallasBaseField : ℝ)^2)) :=
  weightedBias_real_le _ (pallas_regularityDistance_le h hε hbound)

/-- **The single-query bias at the deployed Pallas mapping, ideal overshooting
real**, under the named Weil-bound hypothesis. -/
theorem pallas_weightedBias_ideal_le {C ε : ℝ}
    (h : WeilBounded (zeroRepaired Pallas.mapToCurve) C) (hε : 0 ≤ ε)
    (hbound : ((Fintype.card (SWPoint Pallas.curve) : ℝ) - 1) * C^4
      / (Fintype.card PallasBaseField : ℝ)^2 ≤ ε^2) :
    Zcash.Common.PMFWeightedBiasLE (idealLaw Pallas.mapToCurve)
      (PMF.uniformOfFintype (PallasBaseField × PallasBaseField))
      (ENNReal.ofReal (ε + (4 * Fintype.card PallasBaseField - 2)
        / (Fintype.card PallasBaseField : ℝ)^2)) :=
  weightedBias_ideal_le _ (pallas_regularityDistance_le h hε hbound)

/-! ## Vesta -/

/-- The deployed Vesta mapping agrees with its zero-repaired variant away from
`0`, because the repair fires only at `0`. -/
theorem vesta_eq_zeroRepaired_off_zero :
    ∀ u : VestaBaseField, u ≠ 0 → Vesta.mapToCurve u
      = zeroRepaired Vesta.mapToCurve u :=
  fun _ hu => (if_neg hu).symm

/-- **The deployed-map regularity premiss for Vesta**: from the Weil bound on
the zero-repaired mapping, the deployed mapping's regularity distance is at
most `ε + (4·#F − 2)/(#F)²`, by the transport across the single input `0`. -/
theorem vesta_regularityDistance_le {C ε : ℝ}
    (h : WeilBounded (zeroRepaired Vesta.mapToCurve) C) (hε : 0 ≤ ε)
    (hbound : ((Fintype.card (SWPoint Vesta.curve) : ℝ) - 1) * C^4
      / (Fintype.card VestaBaseField : ℝ)^2 ≤ ε^2) :
    ∑ Q, |(pairCount Vesta.mapToCurve Q : ℝ)
        / (Fintype.card VestaBaseField : ℝ)^2
        - 1 / (Fintype.card (SWPoint Vesta.curve) : ℝ)|
      ≤ ε + (4 * Fintype.card VestaBaseField - 2)
          / (Fintype.card VestaBaseField : ℝ)^2 :=
  sum_abs_prob_dev_transport_le Vesta.mapToCurve _ 0
    vesta_eq_zeroRepaired_off_zero h hε hbound

/-- **The single-query bias at the deployed Vesta mapping, real overshooting
ideal**, under the named Weil-bound hypothesis. -/
theorem vesta_weightedBias_real_le {C ε : ℝ}
    (h : WeilBounded (zeroRepaired Vesta.mapToCurve) C) (hε : 0 ≤ ε)
    (hbound : ((Fintype.card (SWPoint Vesta.curve) : ℝ) - 1) * C^4
      / (Fintype.card VestaBaseField : ℝ)^2 ≤ ε^2) :
    Zcash.Common.PMFWeightedBiasLE
      (PMF.uniformOfFintype (VestaBaseField × VestaBaseField))
      (idealLaw Vesta.mapToCurve)
      (ENNReal.ofReal (ε + (4 * Fintype.card VestaBaseField - 2)
        / (Fintype.card VestaBaseField : ℝ)^2)) :=
  weightedBias_real_le _ (vesta_regularityDistance_le h hε hbound)

/-- **The single-query bias at the deployed Vesta mapping, ideal overshooting
real**, under the named Weil-bound hypothesis. -/
theorem vesta_weightedBias_ideal_le {C ε : ℝ}
    (h : WeilBounded (zeroRepaired Vesta.mapToCurve) C) (hε : 0 ≤ ε)
    (hbound : ((Fintype.card (SWPoint Vesta.curve) : ℝ) - 1) * C^4
      / (Fintype.card VestaBaseField : ℝ)^2 ≤ ε^2) :
    Zcash.Common.PMFWeightedBiasLE (idealLaw Vesta.mapToCurve)
      (PMF.uniformOfFintype (VestaBaseField × VestaBaseField))
      (ENNReal.ofReal (ε + (4 * Fintype.card VestaBaseField - 2)
        / (Fintype.card VestaBaseField : ℝ)^2)) :=
  weightedBias_ideal_le _ (vesta_regularityDistance_le h hε hbound)

end Zcash.Security.GroupHash
