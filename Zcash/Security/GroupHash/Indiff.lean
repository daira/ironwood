import CompElliptic.Hashing.PastaSSWU
import CompElliptic.Hashing.SignedLift
import CompElliptic.Hashing.WellDistributed
import Zcash.Security.GroupHash.Pasta
import Zcash.Security.GroupHash.Sampler
import Zcash.Common.Oracle.Hybrid

/-!
# Indifferentiability of the group hash from a random oracle, one-oracle form

This composes the single-query bias of `GroupHash/Sampler.lean` through the
adaptive hybrid `runFreshPMF_eventBiasLE`: a distinguisher making at most `q`
fresh queries tells the real world from the ideal world with advantage at most
`q·ε`, where `ε` is the regularity distance.

## The one-oracle game

The distinguisher here is an adaptive query tree `A : OracleComp M (F × F) Bool`:
it submits messages and receives *pairs*. This is the collapsed form of the
indifferentiability game. In the full game the distinguisher has two oracles —
`hash_to_field` returning pairs, and the group hash `H` returning group
elements — but in both worlds every `H`-answer is a deterministic function of
the pair at the same message: in the real world `H(m) = f(u₀) + f(u₁)` by
construction, and in the ideal world the simulator's pair satisfies the same
equation with `H = R` exactly. So an `H`-query gives the distinguisher
nothing that a pair-query does not, and the two-oracle game collapses
computably to this one-oracle game. (The formal reduction is
`twoOracleIndiffFromRO` in `TwoOracle.lean`.)

`IndiffFromRO f q δ` says: every `q`-query distinguisher's acceptance
probability changes by at most `δ` when the real per-query law (uniform pairs)
is replaced by the ideal one (`idealLaw f`), in both directions. Fresh
sampling per query node is the right semantics for distinct messages, because
a random oracle answers distinct messages independently; a distinguisher that
would repeat a message must first be deduplicated (`OracleComp.dedup`), which
preserves its result and its query bound.

`indiffFromRO_of_regularity` discharges it from the regularity distance.
The parametric Pasta corollaries (`pallas_indiffFromRO_of_weilBounded`,
`vesta_indiffFromRO_of_weilBounded`) instantiate that at the deployed
mappings under a `WeilBounded` hypothesis and an explicit budget; the
concrete endpoints (`pallas_indiffFromRO`, `vesta_indiffFromRO`) then
take only Weil's theorem at the two branch covers —the `CharSumBounded`
inputs of CompElliptic's `Hashing/WeilInstance.lean`— and conclude with
the single term `q/2^120`.
-/

namespace Zcash.Security.GroupHash

open Zcash.Common (PMFEventBiasLE PMFWeightedBiasLE OracleComp)
open Zcash.Common.OracleComp (runFreshPMF runFreshPMF_eventBiasLE)
open CompElliptic.Hashing (pairCount WeilBounded zeroRepaired CharSumBounded)
open CompElliptic.CurveForms.ShortWeierstrass (SWPoint)
open CompElliptic.Curves.Pasta
open CompElliptic.Fields.Pasta (PallasBaseField VestaBaseField)
open scoped ENNReal

variable {F : Type*} [Fintype F] [DecidableEq F]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **One-oracle indifferentiability from a random oracle.** Every `q`-query
distinguisher — an adaptive query tree submitting messages and receiving
pairs — has its acceptance probability moved by at most `δ` when the real
per-query law (uniform pairs, the honest `hash_to_field`) is replaced by the
ideal one (`idealLaw f`, the simulator's law), in both directions and against
every acceptance event. -/
def IndiffFromRO [Nonempty F] [Nonempty G] (f : F → G) (q : ℕ) (δ : ℝ≥0∞) : Prop :=
  ∀ {M : Type} (A : OracleComp M (F × F) Bool), A.QueryBound q →
    PMFEventBiasLE (runFreshPMF (PMF.uniformOfFintype (F × F)) A)
        (runFreshPMF (idealLaw f) A) δ
      ∧ PMFEventBiasLE (runFreshPMF (idealLaw f) A)
        (runFreshPMF (PMF.uniformOfFintype (F × F)) A) δ

omit [DecidableEq F] in
/-- **The multi-query composition**: a regularity distance of `ε` gives
indifferentiability at `q·ε`, by charging the single-query bias once per
query node of the adaptive tree (`runFreshPMF_eventBiasLE`). -/
theorem indiffFromRO_of_regularity [Nonempty F] [Nonempty G] (f : F → G)
    {ε : ℝ} (q : ℕ)
    (hdev : ∑ Q, |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
        - 1 / (Fintype.card G : ℝ)| ≤ ε) :
    IndiffFromRO f q (q * ENNReal.ofReal ε) := by
  intro M A hQ
  exact ⟨runFreshPMF_eventBiasLE (weightedBias_real_le f hdev) hQ,
    runFreshPMF_eventBiasLE (weightedBias_ideal_le f hdev) hQ⟩

/-- The transport term rounds up to `4/#F`: dropping the subtracted `2`
simplifies the endpoint bounds. -/
theorem transport_term_le (α : Type*) [Fintype α] [Nonempty α] :
    (4 * Fintype.card α - 2) / (Fintype.card α : ℝ)^2
      ≤ 4 / Fintype.card α := by
  have hx : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  calc (4 * Fintype.card α - 2) / (Fintype.card α : ℝ)^2
      ≤ 4 * Fintype.card α / (Fintype.card α : ℝ)^2 := by
        gcongr
        linarith
    _ = 4 / (Fintype.card α : ℝ) := by
        rw [sq, ← div_div, mul_div_assoc, div_self hx.ne', mul_one]

/-- **Indifferentiability at the deployed Pallas mapping, from a Weil
bound and a budget.** The `WeilBounded` hypothesis supplies a constant `C`:
each nontrivial character sum of the zero-repaired mapping is at most
`C·√#F`. The budget hypothesis `hbound` lets `ε` absorb the regularity
distance that `C` induces. Then `q` queries distinguish with advantage at
most `q · (ε + 4/#F)`. The concrete endpoint `pallas_indiffFromRO`
instantiates both. -/
theorem pallas_indiffFromRO_of_weilBounded {C ε : ℝ} (q : ℕ)
    (h : WeilBounded (zeroRepaired Pallas.mapToCurve) C) (hε : 0 ≤ ε)
    (hbound : ((Fintype.card (SWPoint Pallas.curve) : ℝ) - 1) * C^4
      / (Fintype.card PallasBaseField : ℝ)^2 ≤ ε^2) :
    IndiffFromRO Pallas.mapToCurve q
      (q * ENNReal.ofReal (ε + 4 / Fintype.card PallasBaseField)) :=
  indiffFromRO_of_regularity Pallas.mapToCurve q
    ((pallas_regularityDistance_le h hε hbound).trans
      (by gcongr ε + ?_; exact transport_term_le PallasBaseField))

/-- **Indifferentiability at the deployed Vesta mapping, from a Weil
bound and a budget.** The `WeilBounded` hypothesis supplies a constant `C`:
each nontrivial character sum of the zero-repaired mapping is at most
`C·√#F`. The budget hypothesis `hbound` lets `ε` absorb the regularity
distance that `C` induces. Then `q` queries distinguish with advantage at
most `q · (ε + 4/#F)`. The concrete endpoint `vesta_indiffFromRO`
instantiates both. -/
theorem vesta_indiffFromRO_of_weilBounded {C ε : ℝ} (q : ℕ)
    (h : WeilBounded (zeroRepaired Vesta.mapToCurve) C) (hε : 0 ≤ ε)
    (hbound : ((Fintype.card (SWPoint Vesta.curve) : ℝ) - 1) * C^4
      / (Fintype.card VestaBaseField : ℝ)^2 ≤ ε^2) :
    IndiffFromRO Vesta.mapToCurve q
      (q * ENNReal.ofReal (ε + 4 / Fintype.card VestaBaseField)) :=
  indiffFromRO_of_regularity Vesta.mapToCurve q
    ((vesta_regularityDistance_le h hε hbound).trans
      (by gcongr ε + ?_; exact transport_term_le VestaBaseField))

/-! ## The concrete endpoints

Instantiating the Weil side removes every analytic hypothesis: from Weil's
theorem at the two branch covers alone —the `CharSumBounded` inputs of
CompElliptic's `Hashing/WeilInstance.lean`— the advantage bound is the
single term `q/2^120`. The parametric endpoints conclude with advantage
`q·(ε + 4/#F)`; instantiating `ε := 1/2^120 - 4/#F` makes the sum
telescope to exactly `1/2^120` — the subtraction pre-pays the zero-repair
transport inside the budget. Two side conditions remain, both exact
rational arithmetic on the card numerals: `ε ≥ 0` (the transport
`4/#F ≈ 2^{-252}` is far below `2^{-120}`), and the budget check
`(#G - 1)·(21/2)⁴/#F² ≤ ε²` (the regularity distance is about
`2^{-120.2}`, a headroom factor of about `2^{0.2} ≈ 1.16`). -/

/-- **Concrete indifferentiability at the deployed Pallas mapping.** From
Weil's theorem at the two branch covers of iso-Pallas, `q` queries
distinguish the group hash from a random oracle with advantage at most
`q/2^120`. -/
theorem pallas_indiffFromRO (q : ℕ)
    (h1 : CharSumBounded Pallas.sswu.modelPoints1
      (Pallas.sswu.cover1Map Pallas.isSquare_neg_one)
      (100 * (Fintype.card PallasBaseField : ℝ)))
    (h2 : CharSumBounded Pallas.sswu.modelPoints2
      (Pallas.sswu.cover2Map Pallas.isSquare_neg_one)
      (100 * (Fintype.card PallasBaseField : ℝ))) :
    IndiffFromRO Pallas.mapToCurve q ((q : ℝ≥0∞) / 2^120) := by
  have hcard : Fintype.card PallasBaseField
      = CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := ZMod.card _
  have hG : Fintype.card (SWPoint Pallas.curve)
      = CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
    simpa using Pallas.card_eq
  have hε : (0:ℝ) ≤ 1/2^120 - 4 / (Fintype.card PallasBaseField : ℝ) := by
    rw [hcard]
    norm_num
  have hbound : ((Fintype.card (SWPoint Pallas.curve) : ℝ) - 1) * (21/2:ℝ)^4
      / (Fintype.card PallasBaseField : ℝ)^2
      ≤ (1/2^120 - 4 / (Fintype.card PallasBaseField : ℝ))^2 := by
    rw [hG, hcard]
    norm_num
  -- Present the budget as `(ε + 4/#F)` with `ε := 1/2^120 - 4/#F`, so the
  -- parametric conclusion telescopes to `q/2^120` exactly.
  rw [show ((q : ℝ≥0∞) / 2^120) = q * ENNReal.ofReal ((1:ℝ)/2^120) from by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, mul_one_div],
    show ((1:ℝ)/2^120) = (1/2^120 - 4 / (Fintype.card PallasBaseField : ℝ))
      + 4 / (Fintype.card PallasBaseField : ℝ) from by ring]
  intro M A hQ
  exact pallas_indiffFromRO_of_weilBounded q
    (Pallas.weilBounded_zeroRepaired_mapToCurve h1 h2) hε hbound A hQ

/-- **Concrete indifferentiability at the deployed Vesta mapping.** From
Weil's theorem at the two branch covers of iso-Vesta, `q` queries
distinguish the group hash from a random oracle with advantage at most
`q/2^120`. -/
theorem vesta_indiffFromRO (q : ℕ)
    (h1 : CharSumBounded Vesta.sswu.modelPoints1
      (Vesta.sswu.cover1Map Vesta.isSquare_neg_one)
      (100 * (Fintype.card VestaBaseField : ℝ)))
    (h2 : CharSumBounded Vesta.sswu.modelPoints2
      (Vesta.sswu.cover2Map Vesta.isSquare_neg_one)
      (100 * (Fintype.card VestaBaseField : ℝ))) :
    IndiffFromRO Vesta.mapToCurve q ((q : ℝ≥0∞) / 2^120) := by
  have hcard : Fintype.card VestaBaseField
      = CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := ZMod.card _
  have hG : Fintype.card (SWPoint Vesta.curve)
      = CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    simpa using Vesta.card_eq
  have hε : (0:ℝ) ≤ 1/2^120 - 4 / (Fintype.card VestaBaseField : ℝ) := by
    rw [hcard]
    norm_num
  have hbound : ((Fintype.card (SWPoint Vesta.curve) : ℝ) - 1) * (21/2:ℝ)^4
      / (Fintype.card VestaBaseField : ℝ)^2
      ≤ (1/2^120 - 4 / (Fintype.card VestaBaseField : ℝ))^2 := by
    rw [hG, hcard]
    norm_num
  -- Present the budget as `(ε + 4/#F)` with `ε := 1/2^120 - 4/#F`, so the
  -- parametric conclusion telescopes to `q/2^120` exactly.
  rw [show ((q : ℝ≥0∞) / 2^120) = q * ENNReal.ofReal ((1:ℝ)/2^120) from by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, mul_one_div],
    show ((1:ℝ)/2^120) = (1/2^120 - 4 / (Fintype.card VestaBaseField : ℝ))
      + 4 / (Fintype.card VestaBaseField : ℝ) from by ring]
  intro M A hQ
  exact vesta_indiffFromRO_of_weilBounded q
    (Vesta.weilBounded_zeroRepaired_mapToCurve h1 h2) hε hbound A hQ

/-! ## The composition with the capped simulator

Indifferentiability relates the deployed construction to a random oracle
through an exhibited ideal-world simulator. `IndiffFromRO` exhibits the
idealized one, answering with `idealLaw f` itself; the capped simulator
answers with `simLaw f d K` instead, and the two laws differ on events by
at most `simLawBias f d K`, the uniform average of the per-target
all-rounds-reject mass. Charging that difference once per query, on top
of the regularity budget, gives the same indifferentiability statement
with the algorithmic simulator as the exhibited witness. -/

/-- **One-oracle indifferentiability from a random oracle, witnessed by
the capped simulator.** As `IndiffFromRO`, but the ideal world's
simulator is the capped algorithm: it answers from `simLaw f d K` rather
than the mathematical `idealLaw f`. -/
def IndiffFromROCapped [Nonempty F] [Nonempty G] (f : F → G) (d : ℕ)
    [NeZero d] (K q : ℕ) (δ : ℝ≥0∞) : Prop :=
  ∀ {M : Type} (A : OracleComp M (F × F) Bool), A.QueryBound q →
    PMFEventBiasLE (runFreshPMF (PMF.uniformOfFintype (F × F)) A)
        (runFreshPMF (simLaw f d K) A) δ
      ∧ PMFEventBiasLE (runFreshPMF (simLaw f d K) A)
        (runFreshPMF (PMF.uniformOfFintype (F × F)) A) δ

/-- **The capped multi-query composition**: a regularity distance of `ε`
gives indifferentiability against the capped simulator at
`q · (ε + simLawBias f d K)`. Each query is charged the single-query bias
plus the capped simulator's average bias. -/
theorem indiffFromROCapped_of_regularity [Nonempty F] [Nonempty G]
    (f : F → G) {d : ℕ} [NeZero d]
    (hd : ∀ P : G, (singleFibre f P).card ≤ d) {ε : ℝ} (q K : ℕ)
    (hdev : ∑ Q, |(pairCount f Q : ℝ) / (Fintype.card F : ℝ)^2
        - 1 / (Fintype.card G : ℝ)| ≤ ε) :
    IndiffFromROCapped f d K q
      (q * (ENNReal.ofReal ε + simLawBias f d K)) := by
  intro M A hQ
  have hswap := (simLaw_eventBiasLE_idealLaw f hd K).weightedBiasLE
  have hswap' := (idealLaw_eventBiasLE_simLaw f hd K).weightedBiasLE
  constructor
  · have h₁ := runFreshPMF_eventBiasLE (weightedBias_real_le f hdev) hQ
    have h₂ := runFreshPMF_eventBiasLE hswap' hQ
    have := h₁.trans h₂
    rwa [← mul_add,
      add_comm (simLawBias f d K) (ENNReal.ofReal ε)] at this
  · have h₁ := runFreshPMF_eventBiasLE hswap hQ
    have h₂ := runFreshPMF_eventBiasLE (weightedBias_ideal_le f hdev) hQ
    have := h₁.trans h₂
    rwa [← mul_add] at this

/-- **Indifferentiability at the deployed Pallas mapping, witnessed by the
capped simulator**: the `IndiffFromRO` budget plus the capped simulator's
average bias, per query. -/
theorem pallas_indiffFromROCapped {C ε : ℝ} (q K : ℕ)
    (h : WeilBounded (zeroRepaired Pallas.mapToCurve) C) (hε : 0 ≤ ε)
    (hbound : ((Fintype.card (SWPoint Pallas.curve) : ℝ) - 1) * C^4
      / (Fintype.card PallasBaseField : ℝ)^2 ≤ ε^2) :
    IndiffFromROCapped Pallas.mapToCurve deployedFibreBound K q
      (q * (ENNReal.ofReal (ε + 4 / Fintype.card PallasBaseField)
        + simLawBias Pallas.mapToCurve deployedFibreBound K)) :=
  indiffFromROCapped_of_regularity Pallas.mapToCurve
    pallas_singleFibre_card_le q K
    ((pallas_regularityDistance_le h hε hbound).trans
      (by gcongr ε + ?_; exact transport_term_le PallasBaseField))

/-- **Indifferentiability at the deployed Vesta mapping, witnessed by the
capped simulator**: the `IndiffFromRO` budget plus the capped simulator's
average bias, per query. -/
theorem vesta_indiffFromROCapped {C ε : ℝ} (q K : ℕ)
    (h : WeilBounded (zeroRepaired Vesta.mapToCurve) C) (hε : 0 ≤ ε)
    (hbound : ((Fintype.card (SWPoint Vesta.curve) : ℝ) - 1) * C^4
      / (Fintype.card VestaBaseField : ℝ)^2 ≤ ε^2) :
    IndiffFromROCapped Vesta.mapToCurve deployedFibreBound K q
      (q * (ENNReal.ofReal (ε + 4 / Fintype.card VestaBaseField)
        + simLawBias Vesta.mapToCurve deployedFibreBound K)) :=
  indiffFromROCapped_of_regularity Vesta.mapToCurve
    vesta_singleFibre_card_le q K
    ((vesta_regularityDistance_le h hε hbound).trans
      (by gcongr ε + ?_; exact transport_term_le VestaBaseField))

end Zcash.Security.GroupHash
