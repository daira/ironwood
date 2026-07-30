import Zcash.Snark.Fixtures.SingleActionRandom.FiatShamir
import Zcash.Snark.Fixtures.SingleActionRandom.VkCertificate
import Mathlib.Util.AssertNoSorry

/-!
# The trust boundary at the Lean-derived key (random single-action)

The statement of record for the random single-action capture: the deployed verifier's
fingerprint — `assemble` at the challenges Lean's Fiat–Shamir schedule model derives from the
captured oracle — matches the captured MSM, with the verifying key spelled as its end-to-end
derivation from the ported `configure`/keygen at the captured URS (`VkCertificate.lean`). The
dumped verifying-key record no longer enters the comparison, and the captured challenges are
derived rather than taken as given.

Because the proof string is random, this is the statement the whole random family exists for:
the slots whose honest values are recomputable — `fixedEvals`, `permutationCommonEvals`,
`instanceEvals` — carry random values here, so a sourcing swap or recompute-shortcut in
`assemble` mismatches instead of hiding behind honest structure.

The instance side stays `derivedInstanceCommitment` — already a derivation, the Lagrange
commitment of the captured public inputs, pinned to the captured points by
`instance_commitments_derived` — since only the honest single-action capture has a
`Keygen/InstanceCapture.lean` analogue.
-/

namespace Zcash.Snark.FixtureRandom

open Zcash.Snark

/-- **The fingerprint match at the derived verifying key.** The transported certificate
(`vk_eq_derived`) rewrites the dumped key out of `nonInteractiveFingerprint_matches`. -/
theorem nonInteractiveFingerprint_matches_derived :
    MsmMatch
      (nonInteractiveFingerprint capturedFs capturedInit
        (Keygen.derivedActionVk shape capturedURS) derivedInstanceCommitment ps)
      capturedMsm := by
  have h : vk = Keygen.derivedActionVk shape capturedURS := vk_eq_derived
  rw [← h]
  exact nonInteractiveFingerprint_matches

assert_no_sorry nonInteractiveFingerprint_matches_derived

end Zcash.Snark.FixtureRandom
