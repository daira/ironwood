import Zcash.Snark.Fixtures.MultiAction.Degree
import Zcash.Snark.Soundness.Composition.ScheduleBudget

/-!
# The `x`-squeeze schedule at the captured key

`deployedConstraintXSqueezeSchedule_of_pinned` prices the constraint-difference root set from
the verifying key's degree caps. This module discharges those caps at the captured Post-NU6.3
key (`Fixtures.MultiAction.Degree`): with `B = 2047`, `W = 7`, `Dc = 8188` and
`D = Dq = 20470`, every cap holds, so for any deployed root family carrying the captured key the
schedule's `epsilonX` is the concrete `20470 / |𝔽|`. The causal half (`pinned`) passes through
as the named premise.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark
open scoped ENNReal

/-- **The `x`-squeeze schedule at the captured key.** The degree caps are discharged from the
captured verifying key, so `epsilonX` is the concrete `20470 / |𝔽|`; the squeeze-pinning
premise passes through unchanged. -/
noncomputable def deployedConstraintXSqueezeSchedule_captured
    (family : ComputedDeployedRootFSFamily shape)
    (hvk : ∀ basis, family.vk basis = vk)
    (hpinned : ∀ basis
      (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
      (v : Fp),
      deployedConstraintXBadSet family basis
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 4) v) =
        deployedConstraintXBadSet family basis O) :
    DeployedConstraintXSqueezeSchedule family ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞)) := by
  have hk : 2 ^ shape.k - 1 = 2047 := by norm_num [shape]
  have h := deployedConstraintXSqueezeSchedule_of_pinned family
    (B := 2047) (W := 7) (Dc := 8188) (D := 20470) (Dq := 20470)
    (by norm_num) (by omega)
    (fun basis => by rw [hvk basis]; exact vk_n_pred_le)
    (fun basis => by rw [hvk basis]; exact vk_gates_degree_le)
    (fun basis => by rw [hvk basis]; exact vk_chunk_width_le)
    (fun basis => by rw [hvk basis]; exact vk_lookup_input_degree_le)
    (fun basis => by rw [hvk basis]; exact vk_lookup_table_degree_le)
    (fun basis => by rw [hvk basis]; rw [← hk]; exact vk_quotient_tail_le)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hpinned
  simpa using h

end Zcash.Snark.Fixture2
