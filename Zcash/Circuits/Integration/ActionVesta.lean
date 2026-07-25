import Zcash.Snark.Soundness.Deployed.ActionVk
import Zcash.Snark.Soundness.CanonicalVesta
import Zcash.Snark.Soundness.Multiopen.CanonicalSelection

/-!
# Deployed Action specialization of the canonical Vesta terminal

This module is the Action-specific edge of the Vesta constraint-soundness
bridge. It selects the deployed Action proof's advice and instance members from
the accepted canonical route, invokes the verifier-native canonical Vesta
adapter, and hands the resulting circuit satisfaction fact to the Action
formal-circuit terminal.

The public capstone has no free proposition, encoding callback, or member
decoder. Its circuit model and decoder are both determined by deployed
acceptance.
-/

namespace Zcash.Snark

open Polynomial
open Classical
open scoped ENNReal

open Halo2 Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Snark.Fixture
open ActionInstanceCommitment

set_option maxHeartbeats 20000

set_option maxRecDepth 1000000 in
private theorem actionCapturedQueryCounts_transport
    (s : Shape)
    (hs : actionProofParams.mergeDerived orchardActionTopLevelCircuit = s)
    (K : VerifyingKey s Fp Fixture.G)
    (hK : K = derivedActionVk s capturedURS) :
    K.adviceQueryLayout.length = s.numAdviceQueries ∧
      K.instanceQueryLayout.length = s.numInstanceQueries := by
  subst hs
  rw [← Keygen.toVerifierKey_action actionProofParams capturedURS] at hK
  subst hK
  exact
    ⟨orchardActionTopLevelCircuit.toVerifierKey_adviceQueryCount
      actionProofParams capturedURS,
    orchardActionTopLevelCircuit.toVerifierKey_instanceQueryCount
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

private theorem actionNumProofs :
    Fixture.shape.numProofs = 1 := by
  rw [← Keygen.shape_eq_mergeDerived]
  rfl

private def actionProofIndex : Fin Fixture.shape.numProofs :=
  ⟨0, by
    rw [actionNumProofs]
    exact Nat.zero_lt_one⟩

private theorem actionProofIndex_unique
    (proofIndex : Fin Fixture.shape.numProofs) :
    proofIndex = actionProofIndex := by
  apply Fin.ext
  have hlt : (proofIndex : ℕ) < 1 := by
    rw [← actionNumProofs]
    exact proofIndex.isLt
  have hz : (proofIndex : ℕ) = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
  simpa only [actionProofIndex] using hz

attribute [local irreducible] deployedSetQueries deployedSetCommIds
  deployedX4PairCount x4BatchCommitments x4BatchEvals
  Fixture.vk Fixture.shape capturedURS deployedInstanceCommitment

set_option maxRecDepth 1000000 in
/--
The deployed Action instance of the canonical Vesta terminal.

The advice and instance member choices are constructed from the accepted route;
the resulting exact feed equalities replace the terminal's independently
selected feeds. The result is canonical Action-model circuit satisfaction or
the standard discrete-log-relation alternative.
-/
theorem actionAcceptedCircuitSat_or_relation_of_vestaTerminalDerived
    (inputs : Fin Fixture.shape.numProofs → PublicInputs)
    (ps : ProofString Fixture.shape Fp Fixture.G)
    (ch : Challenges Fixture.shape.k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ capturedURS.k) → Fp}
    (pbatch :
      OpenedBatchOpenings capturedURS (evalVector capturedURS.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
          capturedURS shape_k_eq_capturedURS_k Fixture.vk ps ch)
        (x4BatchEvals
          (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
          Fixture.vk ps ch)
        a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch →
      0 < (deployedSetQueries Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch →
      (((deployedSetQueries Fixture.vk
          (deployedInstanceCommitment Fixture.shape inputs) ps ch i).length - 1 :
          ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter
            (OpenedX1Accept capturedURS shape_k_eq_capturedURS_k Fixture.vk
              (deployedInstanceCommitment Fixture.shape inputs) ps ch)))
    (haccepts :
      DeployedAccepts capturedURS shape_k_eq_capturedURS_k Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch)
    (i m : ℕ)
    (hm : m < (deployedSetQueries Fixture.vk
      (deployedInstanceCommitment Fixture.shape inputs) ps ch i).length)
    (colPoly : Fin (deployedSetQueries Fixture.vk
      (deployedInstanceCommitment Fixture.shape inputs) ps ch i).length →
        Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries Fixture.vk
            (deployedInstanceCommitment Fixture.shape inputs) ps ch)).points.getD
              i []).length)
        (m₀ : Fin (deployedSetQueries Fixture.vk
          (deployedInstanceCommitment Fixture.shape inputs) ps ch i).length),
      (colPoly m₀).eval
          (((constructIntermediateSets
            (assembleQueries Fixture.vk
              (deployedInstanceCommitment Fixture.shape inputs) ps ch)).points.getD
                i [])[idx]) =
        ((deployedSetQueries Fixture.vk
          (deployedInstanceCommitment Fixture.shape inputs) ps ch i).getD
            (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp)
          capturedURS.g capturedURS.u capturedURS.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets
      (assembleQueries Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch)).points.getD
          i [] = [ch.x])
    (hevals : ∀ d₀,
      ((deployedSetQueries Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch i).getD
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
            Fixture.vk (deployedInstanceCommitment Fixture.shape inputs) ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := vk_blindingFactors_lt) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (let model :=
          CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
                Fixture.vk (deployedInstanceCommitment Fixture.shape inputs) ps ch
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
            Fixture.vk (deployedInstanceCommitment Fixture.shape inputs) ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := vk_blindingFactors_lt) haccepts).CircuitSat
          ch.y hpoly Fixture.vk.n a₀ ∨
      HasNontrivialRelation (F := Fp)
        capturedURS.g capturedURS.u capturedURS.w := by
  let memberDecode :=
    vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
      Fixture.vk (deployedInstanceCommitment Fixture.shape inputs) ps ch
      pbatch hlen hprob1 haccepts
  let model :=
    CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := vk_blindingFactors_lt) haccepts
  let adviceSlot :=
    acceptedAdviceSlot
      (vk := Fixture.vk)
      (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
      (ps := ps) (ch := ch) (proofIndex := actionProofIndex)
      capturedURS shape_k_eq_capturedURS_k haccepts
      actionCapturedAdviceQueryCount
  let instanceSlot :=
    acceptedInstanceSlot
      (vk := Fixture.vk)
      (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
      (ps := ps) (ch := ch) (proofIndex := actionProofIndex)
      capturedURS shape_k_eq_capturedURS_k haccepts
      actionCapturedInstanceQueryCount
  let adviceSet : Fin Fixture.shape.numAdviceQueries → ℕ :=
    fun query => (adviceSlot query).setIndex
  have hadviceSet : ∀ query, adviceSet query <
      deployedX4PairCount Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch :=
    fun query => (adviceSlot query).setIndex_lt
  let adviceMem : ∀ query : Fin Fixture.shape.numAdviceQueries,
      Fin (deployedSetQueries Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch
        (adviceSet query)).length :=
    fun query => (adviceSlot query).memberIndex
  let instanceSet : Fin Fixture.shape.numInstanceQueries → ℕ :=
    fun query => (instanceSlot query).setIndex
  have hinstanceSet : ∀ query, instanceSet query <
      deployedX4PairCount Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch :=
    fun query => (instanceSlot query).setIndex_lt
  let instanceMem : ∀ query : Fin Fixture.shape.numInstanceQueries,
      Fin (deployedSetQueries Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch
        (instanceSet query)).length :=
    fun query => (instanceSlot query).memberIndex
  have hAdvice :
      (fun _ : Fin Fixture.shape.numProofs =>
        rotatedFeed Fixture.vk.omega Fixture.vk.adviceQueryLayout
          (fun query : Fin Fixture.shape.numAdviceQueries =>
            coeffsToPoly
              ((memberDecode (adviceSet query) (hadviceSet query)).cols
                (adviceMem query)))) =
        model.adviceCols := by
    simpa only [adviceSlot, adviceSet, adviceMem, model] using
      acceptedAdviceSelection_feed_eq
        capturedURS shape_k_eq_capturedURS_k Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch pbatch
        memberDecode haccepts actionProofIndex
        actionCapturedAdviceQueryCount vk_blindingFactors_lt
        actionProofIndex_unique
  have hInstance :
      (fun _ : Fin Fixture.shape.numProofs =>
        rotatedFeed Fixture.vk.omega Fixture.vk.instanceQueryLayout
          (fun query : Fin Fixture.shape.numInstanceQueries =>
            coeffsToPoly
              ((memberDecode (instanceSet query) (hinstanceSet query)).cols
                (instanceMem query)))) =
        model.instanceCols := by
    simpa only [instanceSlot, instanceSet, instanceMem, model] using
      acceptedInstanceSelection_feed_eq
        capturedURS shape_k_eq_capturedURS_k Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch pbatch
        memberDecode haccepts actionProofIndex
        actionCapturedInstanceQueryCount vk_blindingFactors_lt
        actionProofIndex_unique
  have hAdviceTerminal :
      (fun _ : Fin Fixture.shape.numProofs =>
        rotatedFeed Fixture.vk.omega Fixture.vk.adviceQueryLayout
          (fun query : Fin Fixture.shape.numAdviceQueries =>
            coeffsToPoly
              ((openedMemberDecode_of_x1Prob
                capturedURS shape_k_eq_capturedURS_k Fixture.vk
                (deployedInstanceCommitment Fixture.shape inputs) ps ch
                pbatch (adviceSet query) (hadviceSet query)
                (hlen _ (hadviceSet query)) (hprob1 _ (hadviceSet query))
                haccepts).cols (adviceMem query)))) =
        model.adviceCols := by
    simpa only [memberDecode, vestaExtractedMemberDecode] using hAdvice
  have hInstanceTerminal :
      (fun _ : Fin Fixture.shape.numProofs =>
        rotatedFeed Fixture.vk.omega Fixture.vk.instanceQueryLayout
          (fun query : Fin Fixture.shape.numInstanceQueries =>
            coeffsToPoly
              ((openedMemberDecode_of_x1Prob
                capturedURS shape_k_eq_capturedURS_k Fixture.vk
                (deployedInstanceCommitment Fixture.shape inputs) ps ch
                pbatch (instanceSet query) (hinstanceSet query)
                (hlen _ (hinstanceSet query)) (hprob1 _ (hinstanceSet query))
                haccepts).cols (instanceMem query)))) =
        model.instanceCols := by
    simpa only [memberDecode, vestaExtractedMemberDecode] using hInstance
  have result :=
    vestaTerminal_circuitSat_or_relation_of_feed_eq
      capturedURS shape_k_eq_capturedURS_k Fixture.vk
      (deployedInstanceCommitment Fixture.shape inputs) ps ch pU pW hpoly
      pbatch hξcur hlen hprob1 haccepts memberDecode vk_blindingFactors_lt
      adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem
      i m hm colPoly hbindAll hquot hroute hevals claimed
      hAdviceTerminal hInstanceTerminal hxgood
  simpa only [memberDecode] using result

assert_no_sorry actionAcceptedCircuitSat_or_relation_of_vestaTerminalDerived

set_option maxRecDepth 1000000 in
private theorem actionBundleStatement_or_relation_of_vestaCircuitSat_or_relation
    (inputs : Fin Fixture.shape.numProofs → PublicInputs)
    (ps : ProofString Fixture.shape Fp Fixture.G)
    (ch : Challenges Fixture.shape.k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ capturedURS.k) → Fp}
    (pbatch :
      OpenedBatchOpenings capturedURS (evalVector capturedURS.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
          capturedURS shape_k_eq_capturedURS_k Fixture.vk ps ch)
        (x4BatchEvals
          (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
          Fixture.vk ps ch)
        a₀ pU pW)
    (hlen : ∀ i, i < deployedX4PairCount Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch →
      0 < (deployedSetQueries Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch →
      (((deployedSetQueries Fixture.vk
          (deployedInstanceCommitment Fixture.shape inputs) ps ch i).length - 1 :
          ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter
            (OpenedX1Accept capturedURS shape_k_eq_capturedURS_k Fixture.vk
              (deployedInstanceCommitment Fixture.shape inputs) ps ch)))
    (haccepts :
      DeployedAccepts capturedURS shape_k_eq_capturedURS_k Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch)
    (hterminal :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode :=
          vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
            Fixture.vk (deployedInstanceCommitment Fixture.shape inputs) ps ch
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
                Fixture.vk (deployedInstanceCommitment Fixture.shape inputs)
                ps ch pbatch hlen hprob1 haccepts)
            (hblinding := vk_blindingFactors_lt) haccepts).constraints
          Fixture.vk.n j))
    (permGamma :
      ch.gamma ∉ allResolverPermutationGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (deployedInstanceCommitment Fixture.shape inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (permBeta :
      ch.beta ∉ allResolverPermutationBetaBadSet Fixture.vk
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (deployedInstanceCommitment Fixture.shape inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (lookupGamma :
      ch.gamma ∉ allResolverLookupGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (deployedInstanceCommitment Fixture.shape inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupBeta :
      ch.beta ∉ allResolverLookupBetaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (deployedInstanceCommitment Fixture.shape inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupTheta :
      ch.theta ∉ TopLevelLookupCoherence.allTopLevelLookupThetaBadSet
        orchardActionTopLevelCircuit actionProofParams capturedURS
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (deployedInstanceCommitment Fixture.shape inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)) :
    BundleStatement Specs.Sinsemilla.orchardGenerators orchardBases inputs ∨
      HasNontrivialRelation (F := Fp)
        capturedURS.g capturedURS.u capturedURS.w := by
  rcases hterminal with hsatisfied | hrelation
  · exact
      actionBundleStatement_or_relation_of_acceptedCircuitSat_deployed
        inputs ps ch pU pW a₀ pbatch
        (vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
          Fixture.vk (deployedInstanceCommitment Fixture.shape inputs) ps ch
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
theorem actionBundleStatement_or_relation_of_vestaTerminalDerived
    (inputs : Fin Fixture.shape.numProofs → PublicInputs)
    (ps : ProofString Fixture.shape Fp Fixture.G)
    (ch : Challenges Fixture.shape.k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ capturedURS.k) → Fp}
    (pbatch :
      OpenedBatchOpenings capturedURS (evalVector capturedURS.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
          capturedURS shape_k_eq_capturedURS_k Fixture.vk ps ch)
        (x4BatchEvals
          (instanceCommitment := deployedInstanceCommitment Fixture.shape inputs)
          Fixture.vk ps ch)
        a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch →
      0 < (deployedSetQueries Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch →
      (((deployedSetQueries Fixture.vk
          (deployedInstanceCommitment Fixture.shape inputs) ps ch i).length - 1 :
          ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter
            (OpenedX1Accept capturedURS shape_k_eq_capturedURS_k Fixture.vk
              (deployedInstanceCommitment Fixture.shape inputs) ps ch)))
    (haccepts :
      DeployedAccepts capturedURS shape_k_eq_capturedURS_k Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch)
    (i m : ℕ)
    (hm : m < (deployedSetQueries Fixture.vk
      (deployedInstanceCommitment Fixture.shape inputs) ps ch i).length)
    (colPoly : Fin (deployedSetQueries Fixture.vk
      (deployedInstanceCommitment Fixture.shape inputs) ps ch i).length →
        Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries Fixture.vk
            (deployedInstanceCommitment Fixture.shape inputs) ps ch)).points.getD
              i []).length)
        (m₀ : Fin (deployedSetQueries Fixture.vk
          (deployedInstanceCommitment Fixture.shape inputs) ps ch i).length),
      (colPoly m₀).eval
          (((constructIntermediateSets
            (assembleQueries Fixture.vk
              (deployedInstanceCommitment Fixture.shape inputs) ps ch)).points.getD
                i [])[idx]) =
        ((deployedSetQueries Fixture.vk
          (deployedInstanceCommitment Fixture.shape inputs) ps ch i).getD
            (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp)
          capturedURS.g capturedURS.u capturedURS.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets
      (assembleQueries Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch)).points.getD
          i [] = [ch.x])
    (hevals : ∀ d₀,
      ((deployedSetQueries Fixture.vk
        (deployedInstanceCommitment Fixture.shape inputs) ps ch i).getD
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
            Fixture.vk (deployedInstanceCommitment Fixture.shape inputs) ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := vk_blindingFactors_lt) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (let model :=
          CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
                Fixture.vk (deployedInstanceCommitment Fixture.shape inputs) ps ch
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
                Fixture.vk (deployedInstanceCommitment Fixture.shape inputs)
                ps ch pbatch hlen hprob1 haccepts)
            (hblinding := vk_blindingFactors_lt) haccepts).constraints
          Fixture.vk.n j))
    (permGamma :
      ch.gamma ∉ allResolverPermutationGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (deployedInstanceCommitment Fixture.shape inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (permBeta :
      ch.beta ∉ allResolverPermutationBetaBadSet Fixture.vk
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (deployedInstanceCommitment Fixture.shape inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (lookupGamma :
      ch.gamma ∉ allResolverLookupGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (deployedInstanceCommitment Fixture.shape inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupBeta :
      ch.beta ∉ allResolverLookupBetaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (deployedInstanceCommitment Fixture.shape inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupTheta :
      ch.theta ∉ TopLevelLookupCoherence.allTopLevelLookupThetaBadSet
        orchardActionTopLevelCircuit actionProofParams capturedURS
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (deployedInstanceCommitment Fixture.shape inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)) :
    BundleStatement Specs.Sinsemilla.orchardGenerators orchardBases inputs ∨
      HasNontrivialRelation (F := Fp)
        capturedURS.g capturedURS.u capturedURS.w := by
  have hterminal :=
    actionAcceptedCircuitSat_or_relation_of_vestaTerminalDerived
      inputs ps ch pU pW hpoly pbatch hξcur hlen hprob1 haccepts
      i m hm colPoly hbindAll hquot hroute hevals claimed hxgood
  exact
    actionBundleStatement_or_relation_of_vestaCircuitSat_or_relation
      inputs ps ch pU pW hpoly pbatch hlen hprob1 haccepts hterminal
      hgoodY permGamma permBeta lookupGamma lookupBeta lookupTheta

assert_no_sorry actionBundleStatement_or_relation_of_vestaTerminalDerived

end Zcash.Snark
