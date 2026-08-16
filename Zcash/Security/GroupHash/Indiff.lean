import CompElliptic.Hashing.PastaSSWU
import CompElliptic.Hashing.SignedLift
import CompElliptic.Hashing.WellDistributed
import Zcash.Security.GroupHash.Pasta
import Zcash.Security.GroupHash.Sampler
import Zcash.Common.Oracle.Hybrid

/-!
# Indifferentiability of the group hash from a random oracle, one-oracle form

This composes the single-query bias of `GroupHash/Sampler.lean` through the
adaptive hybrid `runFreshPMF_eventBiasLE`: a distinguisher making at most `Q`
fresh queries tells the real world from the ideal world with advantage at most
`Q · ε`, where `ε` is the regularity distance.

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

`IndiffFromRO f Q δ` says: every `Q`-query distinguisher's acceptance
probability changes by at most `δ` when the real per-query law (uniform pairs)
is replaced by the ideal one (`idealLaw f`), in both directions. Fresh
sampling per query node is the right semantics for distinct messages, because
a random oracle answers distinct messages independently; a distinguisher that
would repeat a message must first be deduplicated (`OracleComp.dedup`), which
preserves its result and its query bound.

`indiffFromRO_of_regularity` discharges it from the regularity distance, and
the Pasta corollaries instantiate that at the deployed mappings under the
named `WeilBounded` hypothesis.
-/

namespace Zcash.Security.GroupHash

open Zcash.Common (PMFEventBiasLE PMFWeightedBiasLE OracleComp)
open Zcash.Common.OracleComp (runFreshPMF runFreshPMF_eventBiasLE)
open CompElliptic.Hashing (pairCount WeilBounded zeroRepaired)
open CompElliptic.CurveForms.ShortWeierstrass (SWPoint)
open CompElliptic.Curves.Pasta
open CompElliptic.Fields.Pasta (PallasBaseField VestaBaseField)
open scoped ENNReal

variable {F : Type*} [Fintype F] [DecidableEq F]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **One-oracle indifferentiability from a random oracle.** Every `Q`-query
distinguisher — an adaptive query tree submitting messages and receiving
pairs — has its acceptance probability moved by at most `δ` when the real
per-query law (uniform pairs, the honest `hash_to_field`) is replaced by the
ideal one (`idealLaw f`, the simulator's law), in both directions and against
every acceptance event. -/
def IndiffFromRO [Nonempty F] [Nonempty G] (f : F → G) (Q : ℕ) (δ : ℝ≥0∞) : Prop :=
  ∀ {M : Type} (A : OracleComp M (F × F) Bool), A.QueryBound Q →
    PMFEventBiasLE (runFreshPMF (PMF.uniformOfFintype (F × F)) A)
        (runFreshPMF (idealLaw f) A) δ
      ∧ PMFEventBiasLE (runFreshPMF (idealLaw f) A)
        (runFreshPMF (PMF.uniformOfFintype (F × F)) A) δ

omit [DecidableEq F] in
/-- **The multi-query composition**: a regularity distance of `ε` gives
indifferentiability at `Q · ε`, by charging the single-query bias once per
query node of the adaptive tree (`runFreshPMF_eventBiasLE`). -/
theorem indiffFromRO_of_regularity [Nonempty F] [Nonempty G] (f : F → G)
    {ε : ℝ} (Q : ℕ)
    (hdev : ∑ Q', |(pairCount f Q' : ℝ) / (Fintype.card F : ℝ)^2
        - 1 / (Fintype.card G : ℝ)| ≤ ε) :
    IndiffFromRO f Q (Q * ENNReal.ofReal ε) := by
  intro M A hQ
  exact ⟨runFreshPMF_eventBiasLE (weightedBias_real_le f hdev) hQ,
    runFreshPMF_eventBiasLE (weightedBias_ideal_le f hdev) hQ⟩

/-- **Indifferentiability at the deployed Pallas mapping**, under the named
Weil-bound hypothesis on the zero-repaired mapping: `Q` queries distinguish
with advantage at most `Q · (ε + (4·#F − 2)/(#F)²)`. -/
theorem pallas_indiffFromRO {C ε : ℝ} (Q : ℕ)
    (h : WeilBounded (zeroRepaired Pallas.mapToCurve) C) (hε : 0 ≤ ε)
    (hbound : ((Fintype.card (SWPoint Pallas.curve) : ℝ) - 1) * C^4
      / (Fintype.card PallasBaseField : ℝ)^2 ≤ ε^2) :
    IndiffFromRO Pallas.mapToCurve Q
      (Q * ENNReal.ofReal (ε + (4 * Fintype.card PallasBaseField - 2)
        / (Fintype.card PallasBaseField : ℝ)^2)) :=
  indiffFromRO_of_regularity Pallas.mapToCurve Q
    (pallas_regularityDistance_le h hε hbound)

/-- **Indifferentiability at the deployed Vesta mapping**, under the named
Weil-bound hypothesis on the zero-repaired mapping: `Q` queries distinguish
with advantage at most `Q · (ε + (4·#F − 2)/(#F)²)`. -/
theorem vesta_indiffFromRO {C ε : ℝ} (Q : ℕ)
    (h : WeilBounded (zeroRepaired Vesta.mapToCurve) C) (hε : 0 ≤ ε)
    (hbound : ((Fintype.card (SWPoint Vesta.curve) : ℝ) - 1) * C^4
      / (Fintype.card VestaBaseField : ℝ)^2 ≤ ε^2) :
    IndiffFromRO Vesta.mapToCurve Q
      (Q * ENNReal.ofReal (ε + (4 * Fintype.card VestaBaseField - 2)
        / (Fintype.card VestaBaseField : ℝ)^2)) :=
  indiffFromRO_of_regularity Vesta.mapToCurve Q
    (vesta_regularityDistance_le h hε hbound)

end Zcash.Security.GroupHash
