import Zcash.Snark.Soundness.Deployed.ActionVk
import Zcash.Snark.Soundness.Canonical.Vesta
import Zcash.Snark.Soundness.Multiopen.CanonicalSelection

/-!
# Deployed Action soundness capstone

This module is the Action-specific deployed capstone of the Vesta
constraint-soundness bridge. It selects the deployed Action proof's advice and
instance members from the accepted canonical route, invokes the verifier-native
canonical Vesta adapter, and hands the resulting circuit satisfaction fact to the
Action formal-circuit terminal at the Clean/Ironwood boundary.

The public capstone has no free proposition, encoding callback, or member
decoder. Its circuit model and decoder are both determined by deployed
acceptance.
-/

namespace Zcash.Snark

open Polynomial
open Classical
open scoped ENNReal
open Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Snark.Fixture
open ActionInstanceCommitment

set_option maxHeartbeats 20000

namespace Deployed

set_option maxRecDepth 1000000 in
private theorem actionCapturedQueryCounts_transport
    (s : Shape)
    (hs : actionProofParams.mergeDerived actionCircuit = s)
    (K : VerifyingKey s Fp Fixture.G)
    (hK : K = derivedActionVk s capturedURS) :
    K.adviceQueryLayout.length = s.numAdviceQueries ∧
      K.instanceQueryLayout.length = s.numInstanceQueries := by
  subst hs
  rw [← Keygen.toVerifierKey_action actionProofParams capturedURS] at hK
  subst hK
  exact
    ⟨actionCircuit.toVerifierKey_adviceQueryCount
      actionProofParams capturedURS,
    actionCircuit.toVerifierKey_instanceQueryCount
      actionProofParams capturedURS⟩

private theorem actionCapturedAdviceQueryCount :
    Fixture.vk.adviceQueryLayout.length = Fixture.shape.numAdviceQueries :=
  (actionCapturedQueryCounts_transport
    Fixture.shape Keygen.shape_eq_mergeDerived
    Fixture.vk Keygen.vk_eq_derived).1

private theorem actionCapturedInstanceQueryCount :
    Fixture.vk.instanceQueryLayout.length = Fixture.shape.numInstanceQueries :=
  (actionCapturedQueryCounts_transport
    Fixture.shape Keygen.shape_eq_mergeDerived
    Fixture.vk Keygen.vk_eq_derived).2

attribute [local irreducible] deployedSetQueries deployedSetCommIds
  deployedX4PairCount x4BatchCommitments x4BatchEvals
  Fixture.vk Fixture.shape capturedURS commitment

set_option maxRecDepth 1000000 in
/--
The deployed Action instance of the canonical Vesta terminal.

The advice and instance member choices are constructed from the accepted route;
the resulting exact feed equalities replace the terminal's independently
selected feeds. The result is canonical Action-model circuit satisfaction or
the standard discrete-log-relation alternative.
-/
theorem acceptedModel_circuitSat_or_relation_of_deployedAccepts
    (inputs : Fin Fixture.shape.numProofs → PublicInputs Fp)
    (ps : ProofString Fixture.shape Fp Fixture.G)
    (ch : Challenges Fixture.shape.k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ capturedURS.k) → Fp}
    (pbatch :
      OpenedBatchOpenings capturedURS (evalVector capturedURS.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := commitment actionProofParams capturedURS inputs)
          capturedURS shape_k_eq_capturedURS_k Fixture.vk ps ch)
        (x4BatchEvals
          (instanceCommitment := commitment actionProofParams capturedURS inputs)
          Fixture.vk ps ch)
        a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch →
      0 < (deployedSetQueries Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch →
      (((deployedSetQueries Fixture.vk
          (commitment actionProofParams capturedURS inputs) ps ch i).length - 1 :
          ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter
            (OpenedX1Accept capturedURS shape_k_eq_capturedURS_k Fixture.vk
              (commitment actionProofParams capturedURS inputs) ps ch)))
    (haccepts :
      DeployedAccepts capturedURS shape_k_eq_capturedURS_k Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch)
    (i m : ℕ)
    (hm : m < (deployedSetQueries Fixture.vk
      (commitment actionProofParams capturedURS inputs) ps ch i).length)
    (colPoly : Fin (deployedSetQueries Fixture.vk
      (commitment actionProofParams capturedURS inputs) ps ch i).length →
        Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries Fixture.vk
            (commitment actionProofParams capturedURS inputs) ps ch)).points.getD
              i []).length)
        (m₀ : Fin (deployedSetQueries Fixture.vk
          (commitment actionProofParams capturedURS inputs) ps ch i).length),
      (colPoly m₀).eval
          (((constructIntermediateSets
            (assembleQueries Fixture.vk
              (commitment actionProofParams capturedURS inputs) ps ch)).points.getD
                i [])[idx]) =
        ((deployedSetQueries Fixture.vk
          (commitment actionProofParams capturedURS inputs) ps ch i).getD
            (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp)
          capturedURS.g capturedURS.u capturedURS.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets
      (assembleQueries Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch)).points.getD
          i [] = [ch.x])
    (hevals : ∀ d₀,
      ((deployedSetQueries Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch i).getD
          m d₀).2 =
        [expectedHEval
          (allExpressions Fixture.vk ps ch
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors (ch.x ^ Fixture.vk.n) ch.x).1
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors
              (ch.x ^ Fixture.vk.n) ch.x).2.1
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors
              (ch.x ^ Fixture.vk.n) ch.x).2.2)
          ch.y (ch.x ^ Fixture.vk.n)])
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode :=
          vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
            Fixture.vk (commitment actionProofParams capturedURS inputs) ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := vk_blindingFactors_lt) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (let model :=
          CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
                Fixture.vk (commitment actionProofParams capturedURS inputs) ps ch
                pbatch hlen hprob1 haccepts)
            (hblinding := vk_blindingFactors_lt) haccepts
        combineConstraints model.fixedCols model.adviceCols model.instanceCols
          model.gates model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y model.chunkLen
          model.l0 model.lLast model.lBlind -
            hpoly * (X ^ Fixture.vk.n - 1))) :
    (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode :=
          vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
            Fixture.vk (commitment actionProofParams capturedURS inputs) ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := vk_blindingFactors_lt) haccepts).CircuitSat
          ch.y hpoly Fixture.vk.n a₀ ∨
      HasNontrivialRelation (F := Fp)
        capturedURS.g capturedURS.u capturedURS.w := by
  exact
    acceptedModel_circuitSat_or_relation_of_acceptedSelections
      capturedURS shape_k_eq_capturedURS_k Fixture.vk
      (commitment actionProofParams capturedURS inputs) ps ch pU pW hpoly
      pbatch hξcur hlen hprob1 haccepts vk_blindingFactors_lt
      actionCapturedAdviceQueryCount actionCapturedInstanceQueryCount
      i m hm colPoly hbindAll hquot hroute hevals claimed hxgood

assert_no_sorry acceptedModel_circuitSat_or_relation_of_deployedAccepts

set_option maxRecDepth 1000000 in
private theorem action_bundleStatement_or_relation_of_acceptedModel_circuitSat_or_relation
    (inputs : Fin Fixture.shape.numProofs → PublicInputs Fp)
    (ps : ProofString Fixture.shape Fp Fixture.G)
    (ch : Challenges Fixture.shape.k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ capturedURS.k) → Fp}
    (pbatch :
      OpenedBatchOpenings capturedURS (evalVector capturedURS.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := commitment actionProofParams capturedURS inputs)
          capturedURS shape_k_eq_capturedURS_k Fixture.vk ps ch)
        (x4BatchEvals
          (instanceCommitment := commitment actionProofParams capturedURS inputs)
          Fixture.vk ps ch)
        a₀ pU pW)
    (hlen : ∀ i, i < deployedX4PairCount Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch →
      0 < (deployedSetQueries Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch →
      (((deployedSetQueries Fixture.vk
          (commitment actionProofParams capturedURS inputs) ps ch i).length - 1 :
          ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter
            (OpenedX1Accept capturedURS shape_k_eq_capturedURS_k Fixture.vk
              (commitment actionProofParams capturedURS inputs) ps ch)))
    (haccepts :
      DeployedAccepts capturedURS shape_k_eq_capturedURS_k Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch)
    (hterminal :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode :=
          vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
            Fixture.vk (commitment actionProofParams capturedURS inputs) ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := vk_blindingFactors_lt) haccepts).CircuitSat
          ch.y hpoly Fixture.vk.n a₀ ∨
        HasNontrivialRelation (F := Fp)
          capturedURS.g capturedURS.u capturedURS.w)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
                Fixture.vk (commitment actionProofParams capturedURS inputs)
                ps ch pbatch hlen hprob1 haccepts)
            (hblinding := vk_blindingFactors_lt) haccepts).constraints
          Fixture.vk.n j))
    (permGamma :
      ch.gamma ∉ allResolverPermutationGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (commitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (permBeta :
      ch.beta ∉ allResolverPermutationBetaBadSet Fixture.vk
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (commitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (lookupGamma :
      ch.gamma ∉ allResolverLookupGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (commitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupBeta :
      ch.beta ∉ allResolverLookupBetaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (commitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupTheta :
      ch.theta ∉ TopLevelLookupCoherence.allTopLevelLookupThetaBadSet
        actionCircuit actionProofParams capturedURS
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (commitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)) :
    BundleStatement inputs ∨
      HasNontrivialRelation (F := Fp)
        capturedURS.g capturedURS.u capturedURS.w := by
  rcases hterminal with hsatisfied | hrelation
  · exact
      action_bundleStatement_or_relation_of_acceptedModel_circuitSat_deployed
        inputs ps ch pU pW a₀ pbatch
        (vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
          Fixture.vk (commitment actionProofParams capturedURS inputs) ps ch
          pbatch hlen hprob1 haccepts)
        haccepts hpoly hsatisfied hgoodY permGamma permBeta
        lookupGamma lookupBeta lookupTheta
  · exact Or.inr hrelation

set_option maxRecDepth 1000000 in
/--
The deployed Action soundness statement obtained directly from the
constraint-carrying Vesta terminal.

Unlike the underlying Vesta terminal, this capstone exposes no arbitrary
proposition `S`, no encoding callback, and no freely chosen member decoder.
Deployed acceptance determines the decoder and canonical constraint model;
the accepted route determines the advice and instance member selections.
-/
theorem action_bundleStatement_or_relation_of_deployedAccepts
    (inputs : Fin Fixture.shape.numProofs → PublicInputs Fp)
    (ps : ProofString Fixture.shape Fp Fixture.G)
    (ch : Challenges Fixture.shape.k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ capturedURS.k) → Fp}
    (pbatch :
      OpenedBatchOpenings capturedURS (evalVector capturedURS.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := commitment actionProofParams capturedURS inputs)
          capturedURS shape_k_eq_capturedURS_k Fixture.vk ps ch)
        (x4BatchEvals
          (instanceCommitment := commitment actionProofParams capturedURS inputs)
          Fixture.vk ps ch)
        a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch →
      0 < (deployedSetQueries Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch →
      (((deployedSetQueries Fixture.vk
          (commitment actionProofParams capturedURS inputs) ps ch i).length - 1 :
          ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter
            (OpenedX1Accept capturedURS shape_k_eq_capturedURS_k Fixture.vk
              (commitment actionProofParams capturedURS inputs) ps ch)))
    (haccepts :
      DeployedAccepts capturedURS shape_k_eq_capturedURS_k Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch)
    (i m : ℕ)
    (hm : m < (deployedSetQueries Fixture.vk
      (commitment actionProofParams capturedURS inputs) ps ch i).length)
    (colPoly : Fin (deployedSetQueries Fixture.vk
      (commitment actionProofParams capturedURS inputs) ps ch i).length →
        Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries Fixture.vk
            (commitment actionProofParams capturedURS inputs) ps ch)).points.getD
              i []).length)
        (m₀ : Fin (deployedSetQueries Fixture.vk
          (commitment actionProofParams capturedURS inputs) ps ch i).length),
      (colPoly m₀).eval
          (((constructIntermediateSets
            (assembleQueries Fixture.vk
              (commitment actionProofParams capturedURS inputs) ps ch)).points.getD
                i [])[idx]) =
        ((deployedSetQueries Fixture.vk
          (commitment actionProofParams capturedURS inputs) ps ch i).getD
            (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp)
          capturedURS.g capturedURS.u capturedURS.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets
      (assembleQueries Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch)).points.getD
          i [] = [ch.x])
    (hevals : ∀ d₀,
      ((deployedSetQueries Fixture.vk
        (commitment actionProofParams capturedURS inputs) ps ch i).getD
          m d₀).2 =
        [expectedHEval
          (allExpressions Fixture.vk ps ch
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors (ch.x ^ Fixture.vk.n) ch.x).1
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors
              (ch.x ^ Fixture.vk.n) ch.x).2.1
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors
              (ch.x ^ Fixture.vk.n) ch.x).2.2)
          ch.y (ch.x ^ Fixture.vk.n)])
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode :=
          vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
            Fixture.vk (commitment actionProofParams capturedURS inputs) ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := vk_blindingFactors_lt) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (let model :=
          CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
                Fixture.vk (commitment actionProofParams capturedURS inputs) ps ch
                pbatch hlen hprob1 haccepts)
            (hblinding := vk_blindingFactors_lt) haccepts
        combineConstraints model.fixedCols model.adviceCols model.instanceCols
          model.gates model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y model.chunkLen
          model.l0 model.lLast model.lBlind -
            hpoly * (X ^ Fixture.vk.n - 1)))
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
                Fixture.vk (commitment actionProofParams capturedURS inputs)
                ps ch pbatch hlen hprob1 haccepts)
            (hblinding := vk_blindingFactors_lt) haccepts).constraints
          Fixture.vk.n j))
    (permGamma :
      ch.gamma ∉ allResolverPermutationGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (commitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (permBeta :
      ch.beta ∉ allResolverPermutationBetaBadSet Fixture.vk
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (commitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (lookupGamma :
      ch.gamma ∉ allResolverLookupGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (commitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupBeta :
      ch.beta ∉ allResolverLookupBetaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (commitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupTheta :
      ch.theta ∉ TopLevelLookupCoherence.allTopLevelLookupThetaBadSet
        actionCircuit actionProofParams capturedURS
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (commitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)) :
    BundleStatement inputs ∨
      HasNontrivialRelation (F := Fp)
        capturedURS.g capturedURS.u capturedURS.w := by
  have hterminal :=
    acceptedModel_circuitSat_or_relation_of_deployedAccepts
      inputs ps ch pU pW hpoly pbatch hξcur hlen hprob1 haccepts
      i m hm colPoly hbindAll hquot hroute hevals claimed hxgood
  exact
    action_bundleStatement_or_relation_of_acceptedModel_circuitSat_or_relation
      inputs ps ch pU pW hpoly pbatch hlen hprob1 haccepts hterminal
      hgoodY permGamma permBeta lookupGamma lookupBeta lookupTheta

assert_no_sorry action_bundleStatement_or_relation_of_deployedAccepts

end Deployed

end Zcash.Snark
