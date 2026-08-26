import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Soundness.Deployed.Verification

/-!
# Conditional soundness and deployed acceptance

Soundness starts from `DeployedAccepts`: `assemble?` succeeds and the resulting MSM evaluates to
zero. The adaptive and straight-line AGM routes consume this predicate directly.

## The deployed route

`deployedAccepts_verifierEq` exposes the equivalent flattened IPA equation used by the current
straight-line AGM analysis. Extraction and Action semantics live in `Soundness.AGM` and
`Circuits.Integration`; this module intentionally exports no forked-transcript compatibility lane.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- **Deployed acceptance.** `assemble?` succeeds on the typed proof string and the assembled
MSM evaluates to zero over the URS — the hypothesis every soundness endpoint consumes.

Semantic reach of the chain built on this predicate:
- `TopLevelCircuitCorrectness`'s component conditions are discharged by the Action integration
  layer (`Circuits/Integration/ActionCorrectness.lean`, applying
  `actionTopLevelCircuitCorrectness`) for the deployed Action circuit. So the adaptive-statement
  stack ends at `ActionTerminal.ActionBundleWitness` —the circuit's private witnesses with their
  `ActionSpec` satisfaction proofs at the adversary's public inputs— rather than at
  gate/lookup/copy constraint satisfaction.
- The output side is composed: `Security/Ledger/ActionBundleBridge.lean` takes `ActionSpec`
  —including its `HashGuarded` Sinsemilla escape branches— to the abstract Orchard ledger
  relation, and the extraction experiment consumes it in
  `Security/Ledger/OrchardExtractionExperiment.lean`.
- On the input side, the deployed Action key is derived and certified against the capture by
  `Keygen/Certificate.lean`.

The predicate begins at typed, post-decode values by design. The following remain below the
accepted formal floor:
- that the capture faithfully records the deployed Rust artifact's key;
- byte-level serialization and parsing of protocol elements by transaction creators and
  consumers, and canonicity of their encodings;
- transcript serialization by the prover and verifier;
- the use of BLAKE2b as the transcript hash.

The last two are spot-checked by the fingerprint captures rather than proved for all
inputs; a byte-level verifier model remains open work (`Fingerprint/Match.lean`,
*What remains external*). The predicate covers one proof bundle, and the knowledge-error
bounds are correspondingly per bundle: halo2's optional probabilistic batch verification
layer (`BatchVerifier`) is currently outside the scope of the formalized verifier. -/
def DeployedAccepts [DecidableEq G] [Inhabited G] (shape : Shape) (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Prop :=
  match assemble? vk instanceCommitment ps ch with
  | some m => (hk ▸ m : Msm urs.k Fp G).eval urs = 0
  | none => False

/-- Transport MSM evaluation across the equality `shape.k = urs.k`. -/
theorem eval_cast {shape : Shape} {urs : URS G} (hk : shape.k = urs.k) (m : Msm shape.k Fp G) :
    (hk ▸ m : Msm urs.k Fp G).eval urs = m.eval ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
  -- With `urs` free, destructuring + `subst hk` collapses the cast to `rfl`. Isolating the
  -- transport here keeps `deployedAccepts_verifierEq` from destructuring the URS in place,
  -- which would tangle the accept hypothesis's own `hk`-cast.
  obtain ⟨k, g, w, u⟩ := urs
  change shape.k = k at hk
  subst hk
  rfl

/-- Deployed acceptance implies halo2's explicit IPA verifier equation. -/
theorem deployedAccepts_verifierEq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (h : DeployedAccepts shape urs hk vk instanceCommitment ps ch) :
    DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch := by
  unfold DeployedAccepts at h
  cases hm : assemble? vk instanceCommitment ps ch with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some m =>
      rw [hm] at h
      simp only [] at h
      rw [eval_cast hk m] at h
      have hmeq := assemble?_eq_some vk instanceCommitment ps ch hm
      unfold DeployedIpaVerifierEq
      rw [← deployed_verification_eq (hk ▸ urs.g) urs.w urs.u ps ch
            (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)), ← hmeq]
      exact h

/-- The proof's deployed multiopen commitment over the supplied URS. -/
abbrev deployedCommitment [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : G :=
  multiopenCommitment (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch

end Zcash.Snark
