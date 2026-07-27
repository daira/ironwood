import Zcash.Snark.Fixtures.MultiAction.Fixture
import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment

/-!
# The captured verifying key's static checks

`DeployedConstraintStaticChecks` collects the verifying-key facts the rewind-free constraint
capstone needs independently of the adversary run: the three query layouts cover the shape's
query counts, `ω` has exact order `n`, and `n` does not vanish in `𝔽`. This module evaluates
all five at the captured Post-NU6.3 key and packages them for any deployed root family whose
verifying key is the captured one.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark

/-- The captured advice query layout covers the shape's advice query count (`25`). -/
theorem vk_advice_layout_length : shape.numAdviceQueries ≤ vk.adviceQueryLayout.length := by
  native_decide

/-- The captured instance query layout covers the shape's instance query count (`1`). -/
theorem vk_instance_layout_length : shape.numInstanceQueries ≤ vk.instanceQueryLayout.length := by
  native_decide

/-- The captured fixed query layout covers the shape's fixed query count (`29`). -/
theorem vk_fixed_layout_length : shape.numFixedQueries ≤ vk.fixedQueryLayout.length := by
  native_decide

/-- The captured `ω` has order dividing `n`: `ω ^ 2048 = 1`. -/
theorem vk_omega_order : vk.omega ^ vk.n = 1 := by
  native_decide

/-- The captured domain size does not vanish in the scalar field: `(2048 : 𝔽) ≠ 0`. -/
theorem vk_n_cast_ne_zero : ((vk.n : ℕ) : Fp) ≠ 0 := by
  native_decide

/-- **The static checks at the captured key.** Any deployed root family carrying the captured
verifying key satisfies `DeployedConstraintStaticChecks`: all five fields are the `native_decide`
evaluations above, transported along `hvk`. -/
theorem deployedConstraintStaticChecks_of_captured
    (family : ComputedDeployedRootFSFamily shape)
    (hvk : ∀ basis, family.vk basis = vk) :
    DeployedConstraintStaticChecks family :=
  { adviceLength := fun basis => by rw [hvk basis]; exact vk_advice_layout_length
    instanceLength := fun basis => by rw [hvk basis]; exact vk_instance_layout_length
    fixedLength := fun basis => by rw [hvk basis]; exact vk_fixed_layout_length
    omegaOrder := fun basis => by rw [hvk basis]; exact vk_omega_order
    characteristic := fun basis => by rw [hvk basis]; exact vk_n_cast_ne_zero }

end Zcash.Snark.Fixture2
