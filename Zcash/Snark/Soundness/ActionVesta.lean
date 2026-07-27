import Zcash.Snark.Soundness.TopLevelVesta
import Zcash.Circuits.Integration.ActionInstanceCommitment

/-!
# Action soundness over a circuit-derived Vesta verifying key

This module combines the verifier-native Vesta terminal with the Action
formal-circuit endpoint. The verifying key and public-instance commitments are
derived from the supplied proof parameters, URS, and public inputs.

In particular, the statement is not tied to a captured fixture and does not
assume that `numProofs = 1`.
-/

namespace Zcash.Snark

open Polynomial
open Classical
open scoped ENNReal

open Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open ActionInstanceCommitment

set_option maxHeartbeats 20000

local instance actionVestaInhabited : Inhabited VestaG := ⟨0⟩

attribute [local irreducible] deployedSetQueries deployedSetCommIds
  deployedX4PairCount x4BatchCommitments x4BatchEvals

set_option maxRecDepth 1000000 in
/--
The Action/Vesta soundness capstone for arbitrary proof multiplicity.

Acceptance determines the member decoder and all advice/instance selections.
The circuit determines its shape and verifying key, while the public inputs
determine their verifier commitments. If all challenge exclusions hold, the
accepted proof bundle satisfies the Action specification, unless the supplied
URS admits a nontrivial discrete-log relation.
-/
theorem actionBundleStatement_or_relation_of_vestaTerminal
    (pp : ProofParams) (urs : URS VestaG)
    (hk :
      (pp.mergeDerived orchardActionTopLevelCircuit).k = urs.k)
    (inputs :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
        PublicInputs)
    (ps :
      ProofString (pp.mergeDerived orchardActionTopLevelCircuit) Fp VestaG)
    (ch :
      Challenges (pp.mergeDerived orchardActionTopLevelCircuit).k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := commitment pp urs inputs)
          urs hk (orchardActionTopLevelCircuit.toVerifierKey pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := commitment pp urs inputs)
          (orchardActionTopLevelCircuit.toVerifierKey pp urs) ps ch)
        a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i <
        deployedX4PairCount
          (orchardActionTopLevelCircuit.toVerifierKey pp urs)
          (commitment pp urs inputs) ps ch →
      0 < (deployedSetQueries
        (orchardActionTopLevelCircuit.toVerifierKey pp urs)
        (commitment pp urs inputs) ps ch i).length)
    (hprob1 : ∀ i, i <
        deployedX4PairCount
          (orchardActionTopLevelCircuit.toVerifierKey pp urs)
          (commitment pp urs inputs) ps ch →
      (((deployedSetQueries
          (orchardActionTopLevelCircuit.toVerifierKey pp urs)
          (commitment pp urs inputs) ps ch i).length - 1 : ℕ) : ℝ≥0∞) /
          Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter
            (OpenedX1Accept urs hk
              (orchardActionTopLevelCircuit.toVerifierKey pp urs)
              (commitment pp urs inputs) ps ch)))
    (haccepts :
      DeployedAccepts urs hk
        (orchardActionTopLevelCircuit.toVerifierKey pp urs)
        (commitment pp urs inputs) ps ch)
    (i m : ℕ)
    (hm : m < (deployedSetQueries
      (orchardActionTopLevelCircuit.toVerifierKey pp urs)
      (commitment pp urs inputs) ps ch i).length)
    (colPoly : Fin (deployedSetQueries
      (orchardActionTopLevelCircuit.toVerifierKey pp urs)
      (commitment pp urs inputs) ps ch i).length → Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries
            (orchardActionTopLevelCircuit.toVerifierKey pp urs)
            (commitment pp urs inputs) ps ch)).points.getD i []).length)
        (m₀ : Fin (deployedSetQueries
          (orchardActionTopLevelCircuit.toVerifierKey pp urs)
          (commitment pp urs inputs) ps ch i).length),
      (colPoly m₀).eval
          (((constructIntermediateSets
            (assembleQueries
              (orchardActionTopLevelCircuit.toVerifierKey pp urs)
              (commitment pp urs inputs) ps ch)).points.getD i [])[idx]) =
        ((deployedSetQueries
          (orchardActionTopLevelCircuit.toVerifierKey pp urs)
          (commitment pp urs inputs) ps ch i).getD
            (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets
      (assembleQueries
        (orchardActionTopLevelCircuit.toVerifierKey pp urs)
        (commitment pp urs inputs) ps ch)).points.getD i [] = [ch.x])
    (hevals : ∀ d₀,
      ((deployedSetQueries
        (orchardActionTopLevelCircuit.toVerifierKey pp urs)
        (commitment pp urs inputs) ps ch i).getD m d₀).2 =
        [expectedHEval
          (allExpressions
            (orchardActionTopLevelCircuit.toVerifierKey pp urs) ps ch
            (lagrangeBasis
              (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega
              (orchardActionTopLevelCircuit.toVerifierKey pp urs).n
              (orchardActionTopLevelCircuit.toVerifierKey pp urs).blindingFactors
              (ch.x ^
                (orchardActionTopLevelCircuit.toVerifierKey pp urs).n)
              ch.x).1
            (lagrangeBasis
              (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega
              (orchardActionTopLevelCircuit.toVerifierKey pp urs).n
              (orchardActionTopLevelCircuit.toVerifierKey pp urs).blindingFactors
              (ch.x ^
                (orchardActionTopLevelCircuit.toVerifierKey pp urs).n)
              ch.x).2.1
            (lagrangeBasis
              (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega
              (orchardActionTopLevelCircuit.toVerifierKey pp urs).n
              (orchardActionTopLevelCircuit.toVerifierKey pp urs).blindingFactors
              (ch.x ^
                (orchardActionTopLevelCircuit.toVerifierKey pp urs).n)
              ch.x).2.2)
          ch.y
          (ch.x ^ (orchardActionTopLevelCircuit.toVerifierKey pp urs).n)])
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode :=
          vestaExtractedMemberDecode urs hk
            (orchardActionTopLevelCircuit.toVerifierKey pp urs)
            (commitment pp urs inputs) ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := ActionPermutationDomain.blindingFactors_lt pp urs)
        haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (let model :=
          CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode urs hk
                (orchardActionTopLevelCircuit.toVerifierKey pp urs)
                (commitment pp urs inputs) ps ch
                pbatch hlen hprob1 haccepts)
            (hblinding := ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts
        combineConstraints model.fixedCols model.adviceCols model.instanceCols
          model.gates model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y model.chunkLen
          model.l0 model.lLast model.lBlind -
            hpoly *
              (X ^ (orchardActionTopLevelCircuit.toVerifierKey pp urs).n - 1)))
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode urs hk
                (orchardActionTopLevelCircuit.toVerifierKey pp urs)
                (commitment pp urs inputs) ps ch
                pbatch hlen hprob1 haccepts)
            (hblinding := ActionPermutationDomain.blindingFactors_lt pp urs)
            haccepts).constraints
          (orchardActionTopLevelCircuit.toVerifierKey pp urs).n j))
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        (orchardActionTopLevelCircuit.toVerifierKey pp urs)
        ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode urs hk
              (orchardActionTopLevelCircuit.toVerifierKey pp urs)
              (commitment pp urs inputs) ps ch
              pbatch hlen hprob1 haccepts)
          haccepts)
        actionActiveRows)
    (lookupExclusions :
      TopLevelLookupCoherence.TopLevelLookupChallengeExclusions
        orchardActionTopLevelCircuit pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode urs hk
              (orchardActionTopLevelCircuit.toVerifierKey pp urs)
              (commitment pp urs inputs) ps ch
              pbatch hlen hprob1 haccepts)
          haccepts)) :
    BundleStatement Specs.Sinsemilla.orchardGenerators orchardBases inputs ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let vk := orchardActionTopLevelCircuit.toVerifierKey pp urs
  let instanceCommitment := commitment pp urs inputs
  let memberDecode :=
    vestaExtractedMemberDecode urs hk vk instanceCommitment ps ch
      pbatch hlen hprob1 haccepts
  have hgeneric :=
    topLevelBundleStatement_or_relation_of_vestaTerminal
      orchardActionTopLevelCircuit pp urs hk instanceCommitment
      ps ch pU pW hpoly pbatch hξcur hlen hprob1 haccepts
      (ActionPermutationDomain.blindingFactors_lt pp urs)
      (ActionGateCoherence.topLevelGateCoherence pp urs)
      i m hm colPoly hbindAll hquot hroute hevals claimed hxgood hgoodY
      (cell := FlatCell actionNumPermCols actionDomainSize)
      (fun hsatisfied =>
        topLevelCorrectnessOfAcceptedCircuitSat
          pp urs hk inputs ps ch pU pW a₀ pbatch memberDecode
          haccepts hpoly hsatisfied hgoodY
          permutationExclusions lookupExclusions)
  rcases hgeneric with htop | hrelation
  · exact
      actionBundleStatement_or_relation_of_acceptedTopLevelBundle
        pp urs hk inputs ps ch pU pW a₀ pbatch memberDecode
        haccepts htop
  · exact Or.inr hrelation

assert_no_sorry actionBundleStatement_or_relation_of_vestaTerminal

end Zcash.Snark
