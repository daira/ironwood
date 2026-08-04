import Zcash.Snark.Fixtures.PostNu63
import Zcash.Snark.Fixtures.SingleAction.Random.Fixture
import Zcash.Snark.Fixtures.MultiAction.Random.Fixture
import Mathlib.Util.AssertNoSorry

/-!
# Post-NU6.3 provenance for the random match-only captures

The random captures (`Fixtures/{SingleAction,MultiAction}/Random`) run the deployed verifier on random proof strings, so no accepting
evaluation binds their URS the way `capturedMsm_eval_eq_zero` binds the honest captures'. Their
URS story is cross-capture identity: each random dump lists the same URS and verifying-key
commitment points as the honest single-action capture (the equalities below), and that capture's
URS is in turn bound by its accepting evaluation and by the Lean-derived commitments of the
boundary statements. The random families' verifying-key certificates
(`Fixtures/*/Random/VkCertificate.lean`) transport the single-action keygen certificate along these
equalities, exactly as `Fixtures/MultiAction/Honest/VkCertificate.lean` does.

This file is separate from `Fixtures/PostNu63.lean` so the honest multi-action certificate,
which imports that file, does not pick up a build dependency on the random fixture data
modules. The honest single-action capture is the shared right-hand side throughout, matching the
direction convention there.
-/

namespace Zcash.Snark.PostNu63Fixture

/-! ## The random single-action capture -/

theorem randomSingle_uses_postNu63 : CapturedSingleRandom.capturedCircuitId = "PostNu6_3" := by
  native_decide

theorem randomSingle_uses_canonicalVk :
    CapturedSingleRandom.capturedVkTranscriptRepr = canonicalVkTranscriptRepr := by
  native_decide

/-- The random single-action capture lists the same `2 ^ 11` URS generators as the honest
single-action capture. -/
theorem randomSingle_uses_same_ursG : CapturedSingleRandom.capturedUrsG = CapturedSingle.capturedUrsG := by
  native_decide

/-- The same `w` and `u` URS points (point-table entries `2048` and `2049`). -/
theorem randomSingle_uses_same_wu :
    CapturedSingleRandom.capturedPoint 2048 = CapturedSingle.capturedPoint 2048 ∧
      CapturedSingleRandom.capturedPoint 2049 = CapturedSingle.capturedPoint 2049 := by
  native_decide

/-- The same ten Lagrange-basis points. -/
theorem randomSingle_uses_same_ursGLagrange :
    CapturedSingleRandom.capturedUrsGLagrange = CapturedSingle.capturedUrsGLagrange := by
  native_decide

/-- The same 29 fixed-column commitments. -/
theorem randomSingle_uses_same_fixedCommitments :
    CapturedSingleRandom.capturedFixedCommitments = CapturedSingle.capturedFixedCommitments := by
  native_decide

/-- The same 15 permutation commitments, compared by point value: the point-table indices shift
with the instance-commitment count, so a shared table prefix is not available. -/
theorem randomSingle_uses_same_permutationCommonCommitments :
    CapturedSingleRandom.capturedPermutationCommonCommitments
      = CapturedSingle.capturedPermutationCommonCommitments := by
  native_decide

/-- The random single-action capture carries the honest single-action URS record;
`Fixtures/SingleAction/Random/VkCertificate.lean` rewrites along this equality. -/
theorem randomSingle_uses_same_urs : CapturedSingleRandom.capturedURS = CapturedSingle.capturedURS := by
  simp only [CapturedSingleRandom.capturedURS, CapturedSingle.capturedURS, randomSingle_uses_same_ursG,
    randomSingle_uses_same_wu.1, randomSingle_uses_same_wu.2]

theorem randomSingle_uses_same_vk : CapturedSingleRandom.vk = CapturedSingle.vk := by
  apply verifyingKey_eq_of_fields
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext i
    simp only [CapturedSingleRandom.vk, CapturedSingle.vk]
    rw [randomSingle_uses_same_fixedCommitments]
  · funext i
    simp only [CapturedSingleRandom.vk, CapturedSingle.vk]
    rw [randomSingle_uses_same_permutationCommonCommitments]
  · rfl
  · rfl
  · rfl

/-! ## The random two-action capture -/

theorem randomMulti_uses_postNu63 : CapturedMultiRandom.capturedCircuitId = "PostNu6_3" := by
  native_decide

theorem randomMulti_uses_canonicalVk :
    CapturedMultiRandom.capturedVkTranscriptRepr = canonicalVkTranscriptRepr := by
  native_decide

theorem randomMulti_uses_same_ursG : CapturedMultiRandom.capturedUrsG = CapturedSingle.capturedUrsG := by
  native_decide

theorem randomMulti_uses_same_wu :
    CapturedMultiRandom.capturedPoint 2048 = CapturedSingle.capturedPoint 2048 ∧
      CapturedMultiRandom.capturedPoint 2049 = CapturedSingle.capturedPoint 2049 := by
  native_decide

theorem randomMulti_uses_same_ursGLagrange :
    CapturedMultiRandom.capturedUrsGLagrange = CapturedSingle.capturedUrsGLagrange := by
  native_decide

theorem randomMulti_uses_same_fixedCommitments :
    CapturedMultiRandom.capturedFixedCommitments = CapturedSingle.capturedFixedCommitments := by
  native_decide

theorem randomMulti_uses_same_permutationCommonCommitments :
    CapturedMultiRandom.capturedPermutationCommonCommitments
      = CapturedSingle.capturedPermutationCommonCommitments := by
  native_decide

theorem randomMulti_uses_same_urs : CapturedMultiRandom.capturedURS = CapturedSingle.capturedURS := by
  simp only [CapturedMultiRandom.capturedURS, CapturedSingle.capturedURS, randomMulti_uses_same_ursG,
    randomMulti_uses_same_wu.1, randomMulti_uses_same_wu.2]

theorem randomMulti_uses_same_vk : CapturedMultiRandom.vk = CapturedSingle.vk := by
  apply verifyingKey_eq_of_fields
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext i
    simp only [CapturedMultiRandom.vk, CapturedSingle.vk]
    rw [randomMulti_uses_same_fixedCommitments]
  · funext i
    simp only [CapturedMultiRandom.vk, CapturedSingle.vk]
    rw [randomMulti_uses_same_permutationCommonCommitments]
  · rfl
  · rfl
  · rfl

end Zcash.Snark.PostNu63Fixture
