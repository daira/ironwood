import Zcash.Snark.Fixtures.SingleAction.Fixture
import Zcash.Snark.Keygen.LagrangeBasisKey

/-!
# The derived Lagrange commitment key at the captured URS

The two per-URS setup facts of the derived Lagrange basis, discharged natively at the
captured Orchard URS through the closed coefficient form: the basis has full domain
length, and every basis point is the commitment of its Lagrange polynomial's
coefficients (`2 ^ 11` MSMs — deliberately in the expensive keygen lane). Together they
build the full `LagrangeCommitmentKey`, completing the derived σ/fixed commitment
identification (`permutationCommitmentsOf_getD_eq_commitInstance`) at the deployed
parameters.
-/

namespace Zcash.Snark.Keygen

open Zcash.Snark.Fixture

/-- The derived Lagrange basis covers the whole `2 ^ 11` domain. -/
theorem derivedUrsGLagrange_length_captured :
    (derivedUrsGLagrange capturedURS).length = 2 ^ capturedURS.k := by
  native_decide

/-- Every derived Lagrange basis point is the closed-form generator commitment. -/
theorem derivedUrsGLagrange_closedNat_captured :
    ∀ i : Fin (2 ^ capturedURS.k),
      (derivedUrsGLagrange capturedURS).getD (i : ℕ) 0 =
        commitClosedNat capturedURS i := by
  native_decide

/-- The full Lagrange commitment key over the captured URS, from the derived basis. -/
noncomputable def capturedLagrangeKey :
    LagrangeCommitmentKey capturedURS (omegaOf capturedURS.k) :=
  .ofPrefix capturedURS (omegaOf capturedURS.k) (derivedUrsGLagrange capturedURS)
    (ofPrefix_setup_of_closed capturedURS (by norm_num) fun i =>
      (derivedUrsGLagrange_closedNat_captured i).trans
        (commitClosedNat_eq capturedURS i))
