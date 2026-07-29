import Zcash.Snark.Soundness.Action.Terminal
import Zcash.Snark.Soundness.StraightLine.TopLevelTerminal

/-!
# The rewind-free decode at the Action terminal

`ActionTerminal` concludes the concrete Action bundle statement from the decoded opened-batch
interface: an `OpenedBatchOpenings`, a per-set `OpenedMemberDecode`, deployed acceptance, the
canonical quotient, and the member-binding premise.

`AGM.DecodeToOpened` presents a rewind-free `DeployedAlgebraicDecode` in exactly that shape, so the
straight-line route reaches the same terminal from one accepting execution.  This module ties the
two together: a decoding run supplies its own decode and acceptance, both at the run's complete
challenge record, and what remains are the challenge exclusions — `hxgood`, `hgoodY`, and the
permutation and lookup exclusions — which `StraightLineActionEvent` prices, not this module.

The terminal is used unchanged.  Nothing in this module weakens its statement: the verifying key
is still `actionCircuit.toVerifierKey`, and no free semantic proposition, `hencodes`, or decoded
column feed is reintroduced.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)

variable {G : Type} [AddCommGroup G] [Module Fp G] [DecidableEq G] [Inhabited G]

local instance vestaInhabitedStraightLineActionTerminal : Inhabited VestaG := ⟨0⟩

/-- **The Action bundle statement from a rewind-free decode.**  The decode supplies the batch
openings, the member decodes, the `x₄` designation and the member-binding premise; the caller
supplies acceptance and the challenge exclusions.

The member-binding premise never takes its relation branch here: a decode already carries the
value equations, so `memberBinding` lands on the left for every slot and point. -/
def action_bundleStatement_or_relation_of_decode
    (pp : ProofParams) (urs : URS G)
    (hk : (pp.mergeDerived actionCircuit).k = urs.k)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp G)
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (decode : DeployedAlgebraicDecode urs hk
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch < scalarFieldOrder)
    (haccepts :
      DeployedAccepts urs hk
        (actionCircuit.toVerifierKey pp urs)
        (actionCircuit.instanceCommitment pp urs inputs) ps ch) :=
  action_bundleStatement_or_relation_of_decodedMemberPolynomial_eq
    pp urs hk inputs ps ch pU pW a
    (decode.toOpenedBatch hchar)
    (fun i hi => decode.toMemberDecode hchar i hi)
    haccepts _ rfl
    (fun slot point hpoint => PSum.inl (decode.memberBinding hchar slot point hpoint))

/-- The Action endpoint when a pre-`x` constraint identity has already supplied canonical circuit
satisfaction.  This avoids re-testing the `x`-dependent reassembled quotient polynomial. -/
def action_bundleStatement_or_relation_of_decode_circuitSat
    (pp : ProofParams) (urs : URS G)
    (hk : (pp.mergeDerived actionCircuit).k = urs.k)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp G)
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (decode : DeployedAlgebraicDecode urs hk
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch < scalarFieldOrder)
    (haccepts : DeployedAccepts urs hk
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch)
    (hpoly : Polynomial Fp)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
        (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n pp urs)
        haccepts).CircuitSat ch.y hpoly
          (actionCircuit.toVerifierKey pp urs).n a)
    (hgoodY : ∀ j, ch.y ∉ szBadSet
      (foldSplitWitness
        (CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n pp urs)
          haccepts).constraints
        (actionCircuit.toVerifierKey pp urs).n j))
    (permutationExclusions : ResolverPermutationChallengeExclusions
      (actionCircuit.toVerifierKey pp urs) ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
      actionActiveRows)
    (lookupExclusions : TopLevelLookup.ChallengeExclusions
      actionCircuit pp urs ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)) :
    BundleStatement inputs ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  exact topLevelStatements_or_relation_of_circuitSat
    actionCircuit pp urs hk inputs ps ch pU pW a
    (decode.toOpenedBatch hchar)
    (fun i hi => decode.toMemberDecode hchar i hi) haccepts
    hpoly hsatisfied hgoodY
    (ActionCorrectness.ofAcceptedCircuitSat pp urs hk inputs ps ch pU pW a
      (decode.toOpenedBatch hchar)
      (fun i hi => decode.toMemberDecode hchar i hi) haccepts hpoly hsatisfied hgoodY
      permutationExclusions lookupExclusions)

/-- **The Action terminal reached from the straight-line constraint event.**  A family at the
Action shape supplies the decode and the acceptance from its own accepting run, so the terminal
is reached without a rewind.

`hvk` and `hI` identify the family's verifying key and instance commitment with the Action
circuit's, and the run data is transported along them.  Everything is stated at the run's
complete challenge record — acceptance reads the IPA rounds, so the root layer's zero-round
record cannot carry it.  The challenge exclusions are still open, exactly as in
`action_bundleStatement_or_relation_of_decode`. -/
def action_bundleStatement_or_relation_of_straightLineDecoded
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder) :=
  action_bundleStatement_or_relation_of_decode pp
    (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) rfl inputs
    (straightLineRunOutput family basis O).1.proof.1
    (straightLineRunRecord family basis O)
    ((straightLineRunOutput family basis O).1.multiU
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    ((straightLineRunOutput family basis O).1.multiBlind
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    ((straightLineRunOutput family basis O).1.aMulti
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    (straightLineRunDecodeAt family static basis O
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      hvk hI hdecoded)
    hchar
    (straightLineRunAcceptsAt family static basis O
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      hvk hI hdecoded)

/-- **Executable Action-terminal relation finder.**  The constraint adapter first reconstructs
the decoded run from the family's retained batch coordinates.  This finder then checks the four
terminal exclusion packages as finite propositions and executes the same Action terminal used by
the semantic proof.  Only its explicit relation branch is returned; the statement branch returns
`none`.

The proof parameters `static`, `hvk`, `hI`, and `hchar` certify the fixed deployed artifacts.  No
fixture, `Nonempty`, or selected existential witness contributes returned data. -/
def actionTerminalRelationFinder
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) →
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    let pnu := (wrappedAdversary family.toFamily basis).run O
    let urs := ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis
    let ch := chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)
    match family.straightLineConstraintOutcome? static basis O with
    | none => none
    | some (PSum.inr relation) =>
        some (augmentedBasis_ursOfAugmentedBasis
          (pp.mergeDerived actionCircuit).k basis ▸
            AugmentedRelationWitness.toAlgebraicRelationWitness relation)
    | some (PSum.inl success) =>
        let decode : DeployedAlgebraicDecode urs rfl
            (actionCircuit.toVerifierKey pp urs)
            (actionCircuit.instanceCommitment pp urs inputs) pnu.1.proof.1 ch
            (pnu.1.aMulti (wrappedPreIpaReads pnu))
            (pnu.1.multiU (wrappedPreIpaReads pnu))
            (pnu.1.multiBlind (wrappedPreIpaReads pnu)) := hI basis ▸ hvk basis ▸
          success.witness.decode.reRound (runRounds family.toFamily basis O)
        let haccepts : DeployedAccepts urs rfl
            (actionCircuit.toVerifierKey pp urs)
            (actionCircuit.instanceCommitment pp urs inputs) pnu.1.proof.1 ch :=
          hI basis ▸ hvk basis ▸ success.accepts
        let model := CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n pp urs) haccepts
        let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi) haccepts
        match hxgood : szBadSetAvoidance?
            (ComputablePolynomial.sub
              (combineConstraintsData model.fixedCols model.adviceCols model.instanceCols model.gates
                model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
                ch.y model.chunkLen model.l0 model.lLast model.lBlind)
              (ComputablePolynomial.mul (polynomial CommitmentId.vanishingH)
                (ComputablePolynomial.sub
                  (ComputablePolynomial.pow ComputablePolynomial.X
                    (actionCircuit.toVerifierKey pp urs).n)
                  (ComputablePolynomial.const 1)))) ch.x with
        | some hxgoodProof =>
          let hn : (actionCircuit.toVerifierKey pp urs).n ≠ 0 := by
            change 2 ^ actionCircuit.domainExponent ≠ 0
            positivity
          match hgoodY : foldSplitAvoidance? model.constraints
              (actionCircuit.toVerifierKey pp urs).n hn ch.y with
          | some hgoodYProof =>
            match hpermutation : resolverPermutationChallengeExclusions?
                (actionCircuit.toVerifierKey pp urs) ch polynomial actionActiveRows with
            | some hpermutationProof =>
              match hlookup : TopLevelLookup.topLevelLookupChallengeExclusions?
                  actionCircuit pp urs ch polynomial with
              | some hlookupProof =>
                match action_bundleStatement_or_relation_of_decode pp urs rfl inputs
                    pnu.1.proof.1 ch
                    (pnu.1.multiU (wrappedPreIpaReads pnu))
                    (pnu.1.multiBlind (wrappedPreIpaReads pnu))
                    (pnu.1.aMulti (wrappedPreIpaReads pnu)) decode
                    (hchar basis O) haccepts (by
                      simpa only [ComputablePolynomial.sub_eq, ComputablePolynomial.mul_eq,
                        ComputablePolynomial.pow_eq, ComputablePolynomial.X_eq,
                        ComputablePolynomial.const_eq, Polynomial.C_1,
                        combineConstraintsData_eq] using hxgoodProof.down)
                    hgoodYProof.down
                    hpermutationProof.down hlookupProof.down with
                | PSum.inl _ => none
                | PSum.inr relation =>
                    some (augmentedBasis_ursOfAugmentedBasis
                      (pp.mergeDerived actionCircuit).k basis ▸
                        AugmentedRelationWitness.toAlgebraicRelationWitness relation)
              | none => none
            | none => none
          | none => none
        | none => none

/-- The single relation finder priced by the final Action capstone: the existing IPA/unbatching/
quotient finder first, followed by the executable Action-terminal finder. -/
def actionRelationFinder
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) →
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    match family.straightLineConstraintRelationFinder basis O with
    | some relation => some relation
    | none => actionTerminalRelationFinder pp family static inputs hvk hI hchar basis O

end ActionTerminal

end Zcash.Snark
