import Zcash.Snark.Fixtures.TripleActionRandom.FiatShamir
import Zcash.Snark.Fixtures.TripleActionRandom.VkCertificate
import Mathlib.Util.AssertNoSorry

/-!
# The trust boundary at the Lean-derived key (random three-action)

The statement of record for the random three-action capture: the deployed verifier's
fingerprint — `assemble` at the challenges Lean's Fiat–Shamir schedule model derives from the
captured oracle — matches the captured MSM, with the verifying key spelled as its end-to-end
derivation from the ported `configure`/keygen at the captured URS (`VkCertificate.lean`). The
dumped verifying-key record no longer enters the comparison, the captured challenges are
derived rather than taken as given, and the Fiat-Shamir prefix they are derived from is
`initialTranscript` applied to the derived artifacts, not the dumped `capturedInit`
(`capturedInit_eq_initialTranscript` discharges the two against each other).

Because the proof string is random, this is the statement the whole random family exists for:
the slots whose honest values are recomputable — `fixedEvals`, `permutationCommonEvals`,
`instanceEvals` — carry random values here, so a sourcing swap or recompute-shortcut in
`assemble` mismatches instead of hiding behind honest structure.

The instance side stays `derivedInstanceCommitment` — already a derivation, the Lagrange
commitment of the captured public inputs, pinned to the captured points by
`instance_commitments_derived` — since only the honest single-action capture has a
`Keygen/InstanceCapture.lean` analogue.
-/

namespace Zcash.Snark.FixtureRandom3

open Zcash.Snark

/-- **The fingerprint match at the derived verifying key.** The transported certificate
(`vk_eq_derived`) rewrites the dumped key out of `nonInteractiveFingerprint_matches`. The
Fiat-Shamir prefix is the statement-bound one, built by `initialTranscript` from the same
derived key representation and instance commitments rather than read from the dump. -/
theorem nonInteractiveFingerprint_matches_derived :
    MsmMatch
      (nonInteractiveFingerprintForStatement capturedFs capturedVkTranscriptRepr
        derivedVk derivedInstanceCommitment ps)
      capturedMsm := by
  have h : vk = derivedVk := vk_eq_derived
  rw [← h]
  exact nonInteractiveFingerprint_matches

assert_no_sorry nonInteractiveFingerprint_matches_derived

end Zcash.Snark.FixtureRandom3
