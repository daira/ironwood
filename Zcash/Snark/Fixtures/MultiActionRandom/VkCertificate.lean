import Zcash.Snark.Keygen.Certificate
import Zcash.Snark.Fixtures.MultiActionRandom.Fixture
import Zcash.Snark.Fixtures.PostNu63Random
import Mathlib.Util.AssertNoSorry

/-!
# The random two-action verifying key, certified derived

The captured verifying key of the random two-action capture equals the key derived end-to-end
from the ported `configure`/keygen at the captured URS — transported from the single-action
keygen certificate (`Keygen/Certificate.lean`) along the cross-capture point equalities of
`Fixtures/PostNu63Random.lean`, never re-evaluating keygen. The transport is the
`Fixtures/MultiAction/VkCertificate.lean` proof verbatim: both keys mention the proof count only
in `Fin`-domain types, so every field equality of the single-action certificate restates
verbatim at this capture's shape.
-/

namespace Zcash.Snark.FixtureRandom2

open Zcash.Snark
open Zcash.Snark.Keygen (derivedActionVk fixedCommitmentsOf permutationCommitmentsOf)
open Zcash.Snark.PostNu63Fixture

set_option maxRecDepth 1000000 in
/-- **The captured random two-action verifying key is fully derived.** The cross-capture URS
equality rewrites the goal to the honest single-action URS; opening both records with the same
definitional `simp only` set as the single-action proof makes the field spellings coincide, and
each field is discharged by the corresponding component of the single-action certificate, with
the two commitment families rewritten along the cross-capture point equalities. -/
theorem vk_eq_derived : vk = derivedActionVk shape capturedURS := by
  rw [randomMulti_uses_same_urs]
  have h := Zcash.Snark.Keygen.vk_eq_derived
  unfold Zcash.Snark.Fixture.vk at h
  unfold vk
  simp only [derivedActionVk, Halo2.TopLevelCircuit.verifierKeyAt,
    VerifyingKey.ofOperations, fixedCommitmentsOf, permutationCommitmentsOf] at h ⊢
  rw [VerifyingKey.mk.injEq] at h ⊢
  obtain ⟨ho, hn, hb, hd, hc, hg, hiq, haq, hfq, hfcf, hpcf, hpch, hli, hlt⟩ := h
  refine ⟨ho, hn, hb, hd, hc, hg, hiq, haq, hfq, ?_, ?_, hpch, hli, hlt⟩
  · rw [randomMulti_uses_same_fixedCommitments]; exact hfcf
  · rw [randomMulti_uses_same_permutationCommonCommitments]; exact hpcf

assert_no_sorry vk_eq_derived

end Zcash.Snark.FixtureRandom2
