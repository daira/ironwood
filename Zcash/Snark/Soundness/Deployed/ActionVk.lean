import Zcash.Circuits.Integration.ActionTerminal
import Zcash.Snark.Keygen.Certificate

/-!
# The Action soundness terminal at the deployed verifying key

`actionBundleStatement_or_relation_of_acceptedNodeBinding` is stated at the
circuit-derived verifying key `orchardActionTopLevelCircuit.toVerifierKey pp urs`
for generic proof parameters and URS, with every object indexed by the derived
`Shape` `pp.mergeDerived orchardActionTopLevelCircuit`. The keygen certificate
(`Zcash.Snark.Keygen.Certificate`) proves that at the capture these are the
DEPLOYED artifacts: `shape_eq_mergeDerived` identifies the derived `Shape` with
the fixture's `shape`, and `vk_eq_derived` identifies the captured `Fixture.vk`
with the shape-explicit derived key `derivedActionVk Fixture.shape capturedURS`.

This module joins the two: the terminal instantiated at the deployed verifier —
`actionProofParams`, `capturedURS`, the fixture `shape` in every index position,
and the captured `Fixture.vk` in every key position.

## Transport route

No cast, `▸`, or `HEq` occurs anywhere, in the statements or in the proofs. The
transport lemma `actionDeployed_transport` states everything at a VARIABLE shape
`s` and a VARIABLE key `K`, with two plain equations:

* `hs : actionProofParams.mergeDerived orchardActionTopLevelCircuit = s`, and
* `hK : K = derivedActionVk s capturedURS` — both sides live in
  `VerifyingKey s Fp G`, so this is an ordinary `Eq`, not an `HEq`.

`subst hs` turns every index into the derived `Shape`; `hK` is then rewritten
backwards along `toVerifierKey_action` (`toVerifierKey pp urs =
derivedActionVk (pp.mergeDerived top) urs`) and `subst hK` turns every key into
`orchardActionTopLevelCircuit.toVerifierKey actionProofParams capturedURS`. At
that point the goal is literally the generic terminal. The public theorem
instantiates the lemma with the two certificate equalities verbatim
(`shape_eq_mergeDerived`, `vk_eq_derived`).

The instance-commitment family is the one object of the terminal whose
circuit-native spelling (`ActionInstanceCommitment.commitment pp urs`) is TYPED
at the derived shape and therefore cannot be written at the fixture `shape`. It
is respelled here shape-generically as `deployedInstanceCommitment`, whose type
mentions only the ambient `Shape`; at the derived shape it is `commitment
actionProofParams capturedURS` by `deployedInstanceCommitment_eq` (`rfl`).

The `k`-match and blinding-factor premises of the generic terminal are
discharged internally from the fixture data (`shape_k_eq_capturedURS_k`,
`vk_blindingFactors_lt`) rather than assumed.

The bundle-wide challenge exclusions are taken as the unfolded fields of
`ResolverPermutationChallengeExclusions` (`γ`, `β`) and
`TopLevelLookupChallengeExclusions` (`γ`, `β`, `θ`): the latter structure types
its challenges at `(pp.mergeDerived top).k`, which cannot be spelled at the
fixture `shape` without evaluating the derived domain exponent. Its `γ`/`β`
fields are shape-generic and appear here at `Fixture.vk`; the `θ` field, like the
lookup-selector realization premise, is inherited verbatim from the
Clean/Ironwood seam and still names the circuit
(`orchardActionTopLevelCircuit`) — those two premises are the seam's cap and have
no Snark-native spelling today.
-/

namespace Zcash.Snark

open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Snark.Fixture
open ActionInstanceCommitment

/-- The captured `Shape`'s IPA depth matches the captured URS: both record the
literal deployed `k = 11`. -/
theorem shape_k_eq_capturedURS_k : Fixture.shape.k = capturedURS.k := rfl

set_option maxRecDepth 100000 in
/-- The deployed verifying key's blinding factors are below its domain size
(`5 < 2048` on the captured record). -/
theorem vk_blindingFactors_lt : Fixture.vk.blindingFactors < Fixture.vk.n := by
  decide

/--
The deployed public-instance commitment family, spelled at an arbitrary `Shape`
index.

`ActionInstanceCommitment.commitment` has the derived `Shape` baked into its
type, so it cannot be applied to public inputs indexed by the fixture `shape`.
This is the same family — the Action circuit's single primary column carries the
Lagrange commitment of that proof's public rows, every other column index
commits to zero — with the index left as an ordinary parameter.
-/
noncomputable def deployedInstanceCommitment (s : Shape)
    (inputs : Fin s.numProofs → PublicInputs) :
    Fin s.numProofs → ℕ → G :=
  fun proofIndex column =>
    if column =
        (Action.Circuit.configure
          Specs.Sinsemilla.orchardGenerators {}).1.primary.index then
      (instanceKey actionProofParams capturedURS).commitInstance
        (inputs proofIndex).rows 1
    else 0

/-- At the derived `Shape` the respelled family is the circuit-native one. -/
theorem deployedInstanceCommitment_eq
    (inputs :
      Fin (actionProofParams.mergeDerived
        orchardActionTopLevelCircuit).numProofs → PublicInputs) :
    deployedInstanceCommitment
        (actionProofParams.mergeDerived orchardActionTopLevelCircuit) inputs
      = commitment actionProofParams capturedURS inputs := rfl

set_option maxRecDepth 1000000 in
/--
Transport of the terminal along a `Shape` equality and a key equality: every
premise is stated at a variable shape `s` and a variable key `K`, so that
substituting the certificate equalities `shape_eq_mergeDerived` and
`vk_eq_derived` reduces the goal to the generic terminal at
`(actionProofParams, capturedURS)`. Both equalities are ordinary `Eq`s and are
consumed by `subst`; no cast appears in the statement or in the proof.
-/
private theorem actionDeployed_transport
    (s : Shape)
    (hs : actionProofParams.mergeDerived orchardActionTopLevelCircuit = s)
    (K : VerifyingKey s Fp G)
    (hK : K = derivedActionVk s capturedURS)
    (hk : s.k = capturedURS.k)
    (hbl : K.blindingFactors < K.n)
    (inputs : Fin s.numProofs → PublicInputs)
    (ps : ProofString s Fp G)
    (ch : Challenges s.k Fp)
    (pU pW : Fp) (a : Fin (2 ^ capturedURS.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings capturedURS (evalVector capturedURS.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := deployedInstanceCommitment s inputs)
          capturedURS hk K ps ch)
        (x4BatchEvals
          (instanceCommitment := deployedInstanceCommitment s inputs)
          K ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := deployedInstanceCommitment s inputs)
          K ps ch),
      OpenedMemberDecode
        (instanceCommitment := deployedInstanceCommitment s inputs)
        capturedURS hk K ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts capturedURS hk K
        (deployedInstanceCommitment s inputs) ps ch)
    (hpoly : Polynomial Fp)
    (hquot :
      hpoly =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts .vanishingH)
    (hbind : ∀
      (slot : DeployedMemberSlot
        (instanceCommitment := deployedInstanceCommitment s inputs) K ps ch)
      (point : Fp),
      point ∈ deployedSetPts
          (instanceCommitment := deployedInstanceCommitment s inputs)
          K ps ch slot.setIndex →
      (decodedMemberPolynomial
        (instanceCommitment := deployedInstanceCommitment s inputs)
        capturedURS hk K ps ch memberDecode slot).eval point =
          deployedMemberClaim
            (instanceCommitment := deployedInstanceCommitment s inputs)
            K ps ch slot point
        ∨ HasNontrivialRelation (F := Fp)
            capturedURS.g capturedURS.u capturedURS.w)
    (hxgood :
      ch.x ∉ szBadSet
        (combineConstraints
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).fixedCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).adviceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).instanceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).gates
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).sets
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).chunks
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).lookups
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).beta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).gamma
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).delta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).theta
          ch.y
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).chunkLen
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).l0
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).lLast
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).lBlind -
          hpoly * (X ^ K.n - 1)))
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode) (hblinding := hbl)
            haccepts).constraints
          K.n j))
    (permGamma :
      ch.gamma ∉ allResolverPermutationGammaBadSet K ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        actionActiveRows)
    (permBeta :
      ch.beta ∉ allResolverPermutationBetaBadSet K
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        actionActiveRows)
    (lookupSelectorValues : ∀ proofIndex lookup
      (_henabled :
        lookup ∈ operationEnabledLookups
          (orchardActionTopLevelCircuit.operations 0) 0),
      lookup.InputSelectorValuesRealized
        orchardActionTopLevelCircuit
        (resolverEnvironment K
          (CanonicalMemberConstraintRelation.acceptedPolynomial
            (memberDecode := memberDecode) haccepts)
          proofIndex
          (orchardActionTopLevelCircuit.usableRowsAt
            orchardActionTopLevelCircuit.domainExponent)))
    (lookupGamma :
      ch.gamma ∉ allResolverLookupGammaBadSet K ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        (K.n - K.blindingFactors - 2))
    (lookupBeta :
      ch.beta ∉ allResolverLookupBetaBadSet K ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        (K.n - K.blindingFactors - 2))
    (lookupTheta :
      ch.theta ∉ TopLevelLookupCoherence.allTopLevelLookupThetaBadSet
        orchardActionTopLevelCircuit actionProofParams capturedURS
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)) :
    BundleStatement Specs.Sinsemilla.orchardGenerators orchardBases inputs ∨
      HasNontrivialRelation (F := Fp)
        capturedURS.g capturedURS.u capturedURS.w := by
  subst hs
  rw [← Keygen.toVerifierKey_action actionProofParams capturedURS] at hK
  subst hK
  have terminal :=
    actionBundleStatement_or_relation_of_acceptedNodeBinding
      actionProofParams capturedURS hk inputs ps ch pU pW a
  rw [← deployedInstanceCommitment_eq inputs] at terminal
  exact terminal batchOpenings memberDecode haccepts hpoly hquot hbind
    hxgood hgoodY ⟨permGamma, permBeta⟩ lookupSelectorValues
    ⟨lookupGamma, lookupBeta, lookupTheta⟩

set_option maxRecDepth 1000000 in
/--
**The Action soundness terminal at the deployed verifier.** The generic terminal
`actionBundleStatement_or_relation_of_acceptedNodeBinding` with every verifier
object at the deployed artifacts: the captured verifying key `Fixture.vk`, the
fixture `shape` in every index position, the captured URS, and the deployed
proof-shape parameters. The `Shape`/key transport comes from the keygen
certificate (`shape_eq_mergeDerived`, `vk_eq_derived`), applied by `subst` inside
`actionDeployed_transport`; the `k`-match and blinding-factor side conditions are
the fixture facts `shape_k_eq_capturedURS_k` and `vk_blindingFactors_lt`,
discharged here rather than assumed.
-/
theorem actionBundleStatement_or_relation_of_acceptedNodeBinding_deployed
    (inputs : Fin Fixture.shape.numProofs → PublicInputs)
    (ps : ProofString Fixture.shape Fp G)
    (ch : Challenges Fixture.shape.k Fp)
    (pU pW : Fp) (a : Fin (2 ^ capturedURS.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings capturedURS (evalVector capturedURS.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
          capturedURS shape_k_eq_capturedURS_k Fixture.vk ps ch)
        (x4BatchEvals
          (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
          Fixture.vk ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
          Fixture.vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
        capturedURS shape_k_eq_capturedURS_k Fixture.vk ps ch
        batchOpenings i hi)
    (haccepts :
      DeployedAccepts capturedURS shape_k_eq_capturedURS_k Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch)
    (hpoly : Polynomial Fp)
    (hquot :
      hpoly =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts .vanishingH)
    (hbind : ∀
      (slot : DeployedMemberSlot
        (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
        Fixture.vk ps ch)
      (point : Fp),
      point ∈ deployedSetPts
          (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
          Fixture.vk ps ch slot.setIndex →
      (decodedMemberPolynomial
        (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
        capturedURS shape_k_eq_capturedURS_k Fixture.vk ps ch
        memberDecode slot).eval point =
          deployedMemberClaim
            (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
            Fixture.vk ps ch slot point
        ∨ HasNontrivialRelation (F := Fp)
            capturedURS.g capturedURS.u capturedURS.w)
    (hxgood :
      ch.x ∉ szBadSet
        (combineConstraints
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).fixedCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).adviceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).instanceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).gates
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).sets
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).chunks
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).lookups
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).beta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).gamma
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).delta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).theta
          ch.y
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).chunkLen
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).l0
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).lLast
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).lBlind -
          hpoly * (X ^ Fixture.vk.n - 1)))
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := vk_blindingFactors_lt) haccepts).constraints
          Fixture.vk.n j))
    (permGamma :
      ch.gamma ∉ allResolverPermutationGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        actionActiveRows)
    (permBeta :
      ch.beta ∉ allResolverPermutationBetaBadSet Fixture.vk
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        actionActiveRows)
    (lookupSelectorValues : ∀ proofIndex lookup
      (_henabled :
        lookup ∈ operationEnabledLookups
          (orchardActionTopLevelCircuit.operations 0) 0),
      lookup.InputSelectorValuesRealized
        orchardActionTopLevelCircuit
        (resolverEnvironment Fixture.vk
          (CanonicalMemberConstraintRelation.acceptedPolynomial
            (memberDecode := memberDecode) haccepts)
          proofIndex
          (orchardActionTopLevelCircuit.usableRowsAt
            orchardActionTopLevelCircuit.domainExponent)))
    (lookupGamma :
      ch.gamma ∉ allResolverLookupGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupBeta :
      ch.beta ∉ allResolverLookupBetaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupTheta :
      ch.theta ∉ TopLevelLookupCoherence.allTopLevelLookupThetaBadSet
        orchardActionTopLevelCircuit actionProofParams capturedURS
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)) :
    BundleStatement Specs.Sinsemilla.orchardGenerators orchardBases inputs ∨
      HasNontrivialRelation (F := Fp)
        capturedURS.g capturedURS.u capturedURS.w :=
  actionDeployed_transport
    Fixture.shape Keygen.shape_eq_mergeDerived
    Fixture.vk Keygen.vk_eq_derived
    shape_k_eq_capturedURS_k vk_blindingFactors_lt
    inputs ps ch pU pW a batchOpenings memberDecode haccepts hpoly hquot hbind
    hxgood hgoodY permGamma permBeta lookupSelectorValues
    lookupGamma lookupBeta lookupTheta

assert_no_sorry actionBundleStatement_or_relation_of_acceptedNodeBinding_deployed

end Zcash.Snark
