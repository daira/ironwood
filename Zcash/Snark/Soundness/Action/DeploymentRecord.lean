import Zcash.Snark.Soundness.Action.AdaptiveStatementModel
import Zcash.Snark.Soundness.Oracle.Challenge255
import Zcash.Snark.Soundness.AGM.ProbabilityVesta

/-!
# The deployment-instantiation record

The Action capstones are exact inside their stated model; interpreting them as claims about the
deployed verifier requires identifying each modeled ingredient with its deployed counterpart.
`ActionDeploymentInstantiation` is that bridge as one machine-readable surface: a field per
floor, each stating the identification against the development's own definitions, with the
deployed objects carried as record data.  A term of this record is what a deployment
interpretation supplies, with one derivation left on top: the per-squeeze challenge bias
composes into the capstones' joint-experiment premise by a hybrid over the table's reads.  No
term is constructed here, and fields whose floors are intentionally permanent say so in their
docstrings.

The adversary-class restriction — deployed provers are modeled as represented online-AGM
programs — is carried by `ComputedAdaptiveActionStatementFSFamily` itself, the type the record
is parameterized over, so it appears as the record's parameter rather than as a field.
Consuming this record from the capstone statements belongs to the auditable-contract
restructuring; this module contributes the record shape.
-/

namespace Zcash.Snark

open scoped ENNReal

/-- One deployment interpretation of the adaptive Action capstones: the deployed challenge law,
basis law, key digest, and acceptance predicate, each identified with its modeled counterpart.

Fields split by status.  `challengeWithinBias` is partly discharged — the modulo-reduction stage
is `challenge255_eventBias_le` with `challengeBias := challenge255Bias`, below `2 ^ -260` — and
what remains behind it is the permanent Blake2b-to-uniform-digest floor.  `basisIsGeneratorRO`
is the GroupHash-as-random-oracle idealization, permanent up to the encoding-distribution
groundwork.  `vkDigestAgreesOnCanonical` binds the family's opaque digest to the deployed one at
the canonical key only — the capstones claim no cross-key binding.  `acceptsFaithful` is the
typed post-decode boundary: the byte-level verifier model stays open work
(`Fingerprint/Match.lean`, *What remains external*).  `dlogAdvantage` is data, not a proof
obligation: the caller-supplied advantage family whose identification with a standard
resource-bounded discrete-log game is the permanent external estimate. -/
structure ActionDeploymentInstantiation {T : Type*} [DecidableEq T] (pp : ProofParams)
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (query : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → T) where
  /-- The deployed one-squeeze challenge law. -/
  deployedChallengeLaw : PMF Fp
  /-- The claimed one-sided distance of the deployed law from the uniform squeeze. -/
  challengeBias : ℝ≥0∞
  /-- The deployed squeeze overshoots the uniform idealization by at most `challengeBias`.  The
  reduction stage is proven (`challenge255_eventBias_le`); the digest stage is the Blake2b
  floor. -/
  challengeWithinBias : PMFEventBiasLE deployedChallengeLaw uniformChallenge challengeBias
  /-- The deployed distribution of the augmented URS basis. -/
  deployedBasisLaw : PMF (AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
  /-- The deployed fixed hash-to-curve derivation realizes the generator-random-oracle
  experiment.  Permanent under the GroupHash idealization. -/
  basisIsGeneratorRO :
    deployedBasisLaw = (orchardGeneratorROSetup query).map (orchardGeneratorROBasis query)
  /-- The deployed verifying-key digest. -/
  deployedVkDigest : VerifyingKey (AdaptiveActionStatementShape pp) Fp VestaG → Fp
  /-- The family's opaque transcript digest agrees with the deployed digest at the canonical
  key of every basis.  Single-key agreement only: no cross-key binding is claimed or needed. -/
  vkDigestAgreesOnCanonical : ∀ basis,
    family.vkHash basis (adaptiveActionStatementVk pp basis) =
      deployedVkDigest (adaptiveActionStatementVk pp basis)
  /-- The deployed verifier's acceptance on typed inputs. -/
  deployedTypedAccepts :
    (AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
      family.Coins → Prop
  /-- Deployed acceptance agrees with the model's checked acceptance — capture faithfulness at
  the typed, post-decode boundary. -/
  acceptsFaithful : ∀ basis O, deployedTypedAccepts basis O ↔ family.accepts basis O
  /-- The assumed discrete-log advantage at each query/group-work budget — the value the
  profiles consume.  Data, not an obligation: its identification with a standard
  resource-bounded game is the permanent external estimate. -/
  dlogAdvantage : ℕ → ℕ → ℝ≥0∞

end Zcash.Snark
