import Mathlib.Probability.Distributions.Uniform
import Zcash.Arithmetic

/-!
# The uniform-challenge idealization

`uniformChallenge` models a fresh random-oracle squeeze as exactly uniform over `Fp`. This is the
ideal law used by the unsuffixed and `generatorRO` soundness theorems. Halo2's deployed
`Challenge255 → Fp` conversion is not definitionally this PMF; a consumer making a deployed-law
claim crosses the gap explicitly through the one-sided bias interface (`Oracle/Challenge255.lean`,
`challenge255_eventBias_le`).

This is `Fp`-specific, hence on the Snark side rather than in `Zcash.Common.Oracle`.
-/
namespace Zcash.Snark

open scoped ENNReal
open Zcash.Arithmetic (Fp)

/-- A fresh random-oracle squeeze, modeled as exactly uniform over `Fp`. -/
noncomputable def uniformChallenge : PMF Fp := PMF.uniformOfFintype Fp

/-- A uniform challenge lands in `bad` with probability `|bad| / |Fp|`. -/
theorem uniformChallenge_badSet (bad : Finset Fp) :
    uniformChallenge.toOuterMeasure bad = (bad.card : ℝ≥0∞) / Fintype.card Fp := by
  rw [uniformChallenge, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

end Zcash.Snark
