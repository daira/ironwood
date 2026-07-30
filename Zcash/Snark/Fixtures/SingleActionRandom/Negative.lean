import Zcash.Snark.Fixtures.SingleActionRandom.FiatShamir

/-!
# Aliveness guards for the random single-action capture

A match-only capture witnesses coefficient agreement without the accepting evaluation the honest
families carry, so it needs its own guards against being silently dead:

- `valid_capture_assembles` — the model does not spuriously reject the random point. The trust
  boundary's transfer direction needs the model's accept set to contain the deployed one, and
  this witnesses the straight-line premise of `Core.ProofString` at a generic input.
- `capturedMsm_evalNat_ne_zero` — the capture is genuinely non-accepting, so a mislabeled honest
  capture or dead export plumbing cannot pass for it.
- one blind-slot tamper canary — the match has bite at this point: bumping a `fixedEvals` slot
  still assembles but no longer matches. The full per-slot sensitivity sweep lives in the honest
  families (`Fixtures/{SingleAction,MultiAction}/Negative/Sweep.lean`), whose slot-naming
  regression coverage a random capture does not replace.

The rejection-path negatives of the honest families are deliberately absent: they exercise the
model's rejection set, which is challenge/VK-dependent and already covered there.
-/

namespace Zcash.Snark.FixtureRandom

open Zcash.Snark

theorem valid_capture_assembles : (assemble? vk derivedInstanceCommitment ps ch).isSome = true := by
  native_decide

/-- The captured MSM does not evaluate to the identity: the random capture is genuinely
non-accepting. -/
theorem capturedMsm_evalNat_ne_zero : capturedMsm.evalNat capturedURS ≠ 0 := by
  native_decide

/-- Blind-slot canary: `fixedEvals` is transcript-claimed, so the tamper survives `assemble?`
and must be caught by the match itself. Stated at the captured `ch`, so a failure is MSM
sensitivity, not a schedule derailment. -/
def psTamperedFixedEval : ProofString shape Fp G :=
  { ps with
    fixedEvals := fun q =>
      if q.val = 0 then
        ps.fixedEvals q + 1
      else
        ps.fixedEvals q }

theorem tampered_fixed_eval_assembles :
    (assemble? vk derivedInstanceCommitment psTamperedFixedEval ch).isSome = true := by
  native_decide

theorem tampered_fixed_eval_fingerprint_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psTamperedFixedEval ch) capturedMsm := by
  native_decide

end Zcash.Snark.FixtureRandom
