import Zcash.Snark.Keygen.Certificate
import Zcash.Snark.Fixtures.MultiAction.Fixture
import Zcash.Snark.Fixtures.PostNu63
import Mathlib.Util.AssertNoSorry

/-!
# The multi-action verifying key, certified derived

The captured multi-action verifying key equals the key derived end-to-end from the ported
`configure`/keygen at the captured URS — transported from the single-action certificate
(`Keygen/Certificate.lean`), never re-evaluating keygen. Two facts make the transport
definitional: the two dumps carry one and the same URS and verifying-key commitment points
(`Fixtures/PostNu63.lean`), and both the captured key and the derived key mention the proof
count only in `Fin`-domain types, so every field equality of the single-action certificate
restates verbatim at the multi-action shape.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark
open Zcash.Snark.Keygen (derivedActionVk derivedActionVk_cast toVerifierKey_action
  actionProofParamsFor actionProofParamsFor_mergeDerived_eq fixedCommitmentsOf
  permutationCommitmentsOf)
open Zcash.Snark.PostNu63Fixture
open Zcash.Circuits.Action (actionCircuit)

set_option maxRecDepth 1000000 in
/-- **The captured multi-action verifying key is fully derived.** The cross-capture URS
equality rewrites the goal to the single-action URS; opening both records with the same
definitional `simp only` set as the single-action proof makes the field spellings coincide,
and each field is discharged by the corresponding component of the single-action
certificate, with the two commitment families rewritten along the cross-capture point
equalities. -/
theorem vk_eq_derived : vk = derivedActionVk shape capturedURS := by
  rw [captures_use_same_urs]
  have h := Zcash.Snark.Keygen.vk_eq_derived
  unfold Zcash.Snark.Fixture.vk at h
  unfold vk
  simp only [derivedActionVk, Halo2.TopLevelCircuit.verifierKeyAt,
    VerifyingKey.ofOperations, fixedCommitmentsOf, permutationCommitmentsOf] at h ⊢
  rw [VerifyingKey.mk.injEq] at h ⊢
  obtain ⟨ho, hn, hb, hd, hc, hg, hiq, haq, hfq, hfcf, hpcf, hpch, hli, hlt⟩ := h
  refine ⟨ho, hn, hb, hd, hc, hg, hiq, haq, hfq, ?_, ?_, hpch, hli, hlt⟩
  · rw [captures_use_same_fixedCommitments]; exact hfcf
  · rw [captures_use_same_permutationCommonCommitments]; exact hpcf

/-- The derived shape at two proofs is the captured multi-action shape. -/
theorem actionProofParamsFor_two_mergeDerived :
    (actionProofParamsFor 2).mergeDerived actionCircuit = shape := by
  rw [actionProofParamsFor_mergeDerived_eq]
  rfl

set_option maxRecDepth 1000000 in
/-- **`vk = actionCircuit.toVerifierKey (actionProofParamsFor 2) capturedURS`** — the
captured multi-action verifying key IS the closed circuit's derived verifying key at the
two-proof parameters (transported along `actionProofParamsFor_two_mergeDerived`). -/
theorem vk_eq_toVerifierKey :
    vk = actionProofParamsFor_two_mergeDerived
      ▸ actionCircuit.toVerifierKey (actionProofParamsFor 2) capturedURS := by
  rw [toVerifierKey_action, vk_eq_derived]
  exact (derivedActionVk_cast actionProofParamsFor_two_mergeDerived capturedURS).symm

assert_no_sorry vk_eq_derived
assert_no_sorry vk_eq_toVerifierKey

end Zcash.Snark.Fixture2
