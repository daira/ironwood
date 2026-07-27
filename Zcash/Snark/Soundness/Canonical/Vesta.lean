import Zcash.Snark.Soundness.Canonical.Terminal
import Zcash.Snark.Soundness.Multiopen.CanonicalSelection

/-!
# Canonical accepted-model adapter for the Vesta terminal

The budgeted Vesta terminal still exposes independently selected advice and
instance member feeds and a free proposition callback. This module gives that
boundary verifier-native names:

* `vestaExtractedMemberDecode` is the decoder forced by the accepted `x₁`
  extraction route.
* `acceptedModelCircuitSat_or_relation_of_feed_eq` replaces the free callback
  with canonical accepted-model circuit satisfaction whenever the selected
  feeds are proved equal to the canonical advice and instance feeds.

No formal-circuit or Action concept appears here.
-/

namespace Zcash.Snark

open Polynomial
open Classical
open scoped ENNReal

set_option maxHeartbeats 20000

variable {G : Type*} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

local instance vestaInhabitedCanonicalVesta : Inhabited VestaG := ⟨0⟩

attribute [local irreducible] deployedSetQueries deployedSetCommIds
  deployedX4PairCount x4BatchCommitments x4BatchEvals

/--
The member decoder determined by the accepted Vesta `x₁` extraction path.
-/
noncomputable def vestaExtractedMemberDecode
    {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 :
        ℕ) : ℝ≥0∞) / Fintype.card Fp
          < (PMF.uniformOfFintype Fp).toOuterMeasure
            (Finset.univ.filter
              (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (haccepts :
      DeployedAccepts urs hk vk instanceCommitment ps ch) :
    ∀ i (hi : i < deployedX4PairCount vk instanceCommitment ps ch),
      OpenedMemberDecode urs hk vk instanceCommitment ps ch pbatch i hi :=
  fun i hi =>
    openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch
      pbatch i hi (hlen i hi) (hprob1 i hi) haccepts

set_option maxRecDepth 1000000 in
/--
The Vesta constraint terminal with its free callback specialized to canonical
accepted-model circuit satisfaction.

The caller supplies exact polynomial-feed equalities for the advice and instance
member selections. The terminal's remaining relation is then precisely
`CircuitSat` for the canonical accepted model, apart from the standard
discrete-log-relation alternative.
-/
theorem acceptedModelCircuitSat_or_relation_of_feed_eq
    {shape : Shape}
    (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments urs hk vk instanceCommitment ps ch)
        (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 :
        ℕ) : ℝ≥0∞) / Fintype.card Fp
          < (PMF.uniformOfFintype Fp).toOuterMeasure
            (Finset.univ.filter
              (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (haccepts : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount vk instanceCommitment ps ch),
      OpenedMemberDecode urs hk vk instanceCommitment ps ch pbatch i hi)
    (hblinding : vk.blindingFactors < vk.n)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin shape.numProofs → Fin numAdvice → ℕ)
    (hadviceSet : ∀ proofIndex j,
      adviceSet proofIndex j <
        deployedX4PairCount vk instanceCommitment ps ch)
    (adviceMem : ∀ (proofIndex : Fin shape.numProofs) (j : Fin numAdvice),
      Fin (deployedSetQueries vk instanceCommitment ps ch
        (adviceSet proofIndex j)).length)
    (instanceSet : Fin shape.numProofs → Fin numInstance → ℕ)
    (hinstanceSet : ∀ proofIndex j,
      instanceSet proofIndex j <
        deployedX4PairCount vk instanceCommitment ps ch)
    (instanceMem : ∀ (proofIndex : Fin shape.numProofs)
        (j : Fin numInstance),
      Fin (deployedSetQueries vk instanceCommitment ps ch
        (instanceSet proofIndex j)).length)
    (i m : ℕ)
    (hm : m < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (colPoly : Fin (deployedSetQueries vk instanceCommitment ps ch i).length →
      Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length)
        (m₀ : Fin (deployedSetQueries vk instanceCommitment ps ch i).length),
      (colPoly m₀).eval
          (((constructIntermediateSets
            (assembleQueries vk instanceCommitment ps ch)).points.getD i [])[idx]) =
        ((deployedSetQueries vk instanceCommitment ps ch i).getD
          (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets
      (assembleQueries vk instanceCommitment ps ch)).points.getD i [] = [ch.x])
    (hevals : ∀ d₀,
      ((deployedSetQueries vk instanceCommitment ps ch i).getD m d₀).2 =
        [expectedHEval
          (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).2.2)
          ch.y (ch.x ^ vk.n)])
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts)
    (hAdvice :
      (fun proofIndex : Fin shape.numProofs =>
        rotatedFeed vk.omega vk.adviceQueryLayout
          (fun query : Fin numAdvice =>
            coeffsToPoly
              ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment
                ps ch pbatch (adviceSet proofIndex query)
                (hadviceSet proofIndex query)
                (hlen _ (hadviceSet proofIndex query))
                (hprob1 _ (hadviceSet proofIndex query))
                haccepts).cols (adviceMem proofIndex query)))) =
        (CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := memberDecode)
          (hblinding := hblinding) haccepts).adviceCols)
    (hInstance :
      (fun proofIndex : Fin shape.numProofs =>
        rotatedFeed vk.omega vk.instanceQueryLayout
          (fun query : Fin numInstance =>
            coeffsToPoly
              ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment
                ps ch pbatch (instanceSet proofIndex query)
                (hinstanceSet proofIndex query)
                (hlen _ (hinstanceSet proofIndex query))
                (hprob1 _ (hinstanceSet proofIndex query))
                haccepts).cols (instanceMem proofIndex query)))) =
        (CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := memberDecode)
          (hblinding := hblinding) haccepts).instanceCols)
    (hxgood :
      ch.x ∉ szBadSet
        (let model :=
          CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts
        combineConstraints model.fixedCols model.adviceCols model.instanceCols
          model.gates model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y model.chunkLen
          model.l0 model.lLast model.lBlind -
            hpoly * (X ^ vk.n - 1))) :
    (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts).CircuitSat
          ch.y hpoly vk.n a₀ ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let model :=
    CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode) (hblinding := hblinding) haccepts
  have result :=
    orchard_verifier_vesta_member_constraints_terminal_derived
      urs hk vk instanceCommitment ps ch pU pW
      adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem
      model.fixedCols model.sets model.chunks model.lookups
      model.l0 model.lLast model.lBlind hpoly pbatch hξcur hlen hprob1
      haccepts i m hm colPoly hbindAll hquot hroute hevals
      claimed.fixed
      (fun proofIndex query => by
        have h := claimed.advice proofIndex query
        rw [← congrFun hAdvice proofIndex] at h
        exact h)
      (fun proofIndex query => by
        have h := claimed.«instance» proofIndex query
        rw [← congrFun hInstance proofIndex] at h
        exact h)
      claimed.sets claimed.chunks claimed.lookups
      claimed.l0 claimed.lLast claimed.lBlind
      (by
        rw [hAdvice, hInstance]
        exact hxgood)
      (S := model.CircuitSat ch.y hpoly vk.n a₀)
      (fun _ relation => by
        have h := relation.2
        rw [hAdvice, hInstance] at h
        exact h)
  exact result

assert_no_sorry acceptedModelCircuitSat_or_relation_of_feed_eq

set_option maxRecDepth 1000000 in
/--
The canonical Vesta terminal with its advice and instance selections derived
directly from the accepted query route.

Unlike `acceptedModelCircuitSat_or_relation_of_feed_eq`, callers do not choose
member slots or prove feed equalities. The construction selects the appropriate
member separately for every proof and query index, so this theorem applies to
arbitrary `shape.numProofs`.
-/
theorem acceptedModelCircuitSat_or_relation_of_acceptedSelections
    {shape : Shape}
    (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments urs hk vk instanceCommitment ps ch)
        (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 :
        ℕ) : ℝ≥0∞) / Fintype.card Fp
          < (PMF.uniformOfFintype Fp).toOuterMeasure
            (Finset.univ.filter
              (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (haccepts : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hblinding : vk.blindingFactors < vk.n)
    (hadviceLayout :
      vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (hinstanceLayout :
      vk.instanceQueryLayout.length = shape.numInstanceQueries)
    (i m : ℕ)
    (hm : m < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (colPoly : Fin (deployedSetQueries vk instanceCommitment ps ch i).length →
      Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length)
        (m₀ : Fin (deployedSetQueries vk instanceCommitment ps ch i).length),
      (colPoly m₀).eval
          (((constructIntermediateSets
            (assembleQueries vk instanceCommitment ps ch)).points.getD i [])[idx]) =
        ((deployedSetQueries vk instanceCommitment ps ch i).getD
          (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets
      (assembleQueries vk instanceCommitment ps ch)).points.getD i [] = [ch.x])
    (hevals : ∀ d₀,
      ((deployedSetQueries vk instanceCommitment ps ch i).getD m d₀).2 =
        [expectedHEval
          (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).2.2)
          ch.y (ch.x ^ vk.n)])
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode :=
          vestaExtractedMemberDecode urs hk vk instanceCommitment ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := hblinding) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (let model :=
          CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode urs hk vk instanceCommitment ps ch
                pbatch hlen hprob1 haccepts)
            (hblinding := hblinding) haccepts
        combineConstraints model.fixedCols model.adviceCols model.instanceCols
          model.gates model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y model.chunkLen
          model.l0 model.lLast model.lBlind -
            hpoly * (X ^ vk.n - 1))) :
    (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode :=
          vestaExtractedMemberDecode urs hk vk instanceCommitment ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := hblinding) haccepts).CircuitSat
          ch.y hpoly vk.n a₀ ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let memberDecode :=
    vestaExtractedMemberDecode urs hk vk instanceCommitment ps ch
      pbatch hlen hprob1 haccepts
  let model :=
    CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts
  let adviceSlot := fun proofIndex =>
    acceptedAdviceSlot
      (vk := vk) (instanceCommitment := instanceCommitment)
      (ps := ps) (ch := ch) (proofIndex := proofIndex)
      urs hk haccepts hadviceLayout
  let instanceSlot := fun proofIndex =>
    acceptedInstanceSlot
      (vk := vk) (instanceCommitment := instanceCommitment)
      (ps := ps) (ch := ch) (proofIndex := proofIndex)
      urs hk haccepts hinstanceLayout
  let adviceSet :
      Fin shape.numProofs → Fin shape.numAdviceQueries → ℕ :=
    fun proofIndex query => (adviceSlot proofIndex query).setIndex
  have hadviceSet : ∀ proofIndex query, adviceSet proofIndex query <
      deployedX4PairCount vk instanceCommitment ps ch :=
    fun proofIndex query => (adviceSlot proofIndex query).setIndex_lt
  let adviceMem : ∀ (proofIndex : Fin shape.numProofs)
      (query : Fin shape.numAdviceQueries),
      Fin (deployedSetQueries vk instanceCommitment ps ch
        (adviceSet proofIndex query)).length :=
    fun proofIndex query => (adviceSlot proofIndex query).memberIndex
  let instanceSet :
      Fin shape.numProofs → Fin shape.numInstanceQueries → ℕ :=
    fun proofIndex query => (instanceSlot proofIndex query).setIndex
  have hinstanceSet : ∀ proofIndex query, instanceSet proofIndex query <
      deployedX4PairCount vk instanceCommitment ps ch :=
    fun proofIndex query => (instanceSlot proofIndex query).setIndex_lt
  let instanceMem : ∀ (proofIndex : Fin shape.numProofs)
      (query : Fin shape.numInstanceQueries),
      Fin (deployedSetQueries vk instanceCommitment ps ch
        (instanceSet proofIndex query)).length :=
    fun proofIndex query => (instanceSlot proofIndex query).memberIndex
  have hAdvice :
      (fun proofIndex : Fin shape.numProofs =>
        rotatedFeed vk.omega vk.adviceQueryLayout
          (fun query : Fin shape.numAdviceQueries =>
            coeffsToPoly
              ((memberDecode (adviceSet proofIndex query)
                (hadviceSet proofIndex query)).cols
                (adviceMem proofIndex query)))) =
        model.adviceCols := by
    simpa only [adviceSlot, adviceSet, adviceMem, model] using
      acceptedAdviceSelection_feed_eq
        urs hk vk instanceCommitment ps ch pbatch memberDecode haccepts
        hadviceLayout hblinding
  have hInstance :
      (fun proofIndex : Fin shape.numProofs =>
        rotatedFeed vk.omega vk.instanceQueryLayout
          (fun query : Fin shape.numInstanceQueries =>
            coeffsToPoly
              ((memberDecode (instanceSet proofIndex query)
                (hinstanceSet proofIndex query)).cols
                (instanceMem proofIndex query)))) =
        model.instanceCols := by
    simpa only [instanceSlot, instanceSet, instanceMem, model] using
      acceptedInstanceSelection_feed_eq
        urs hk vk instanceCommitment ps ch pbatch memberDecode haccepts
        hinstanceLayout hblinding
  have hAdviceTerminal :
      (fun proofIndex : Fin shape.numProofs =>
        rotatedFeed vk.omega vk.adviceQueryLayout
          (fun query : Fin shape.numAdviceQueries =>
            coeffsToPoly
              ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment
                ps ch pbatch (adviceSet proofIndex query)
                (hadviceSet proofIndex query)
                (hlen _ (hadviceSet proofIndex query))
                (hprob1 _ (hadviceSet proofIndex query))
                haccepts).cols (adviceMem proofIndex query)))) =
        model.adviceCols := by
    simpa only [memberDecode, vestaExtractedMemberDecode] using hAdvice
  have hInstanceTerminal :
      (fun proofIndex : Fin shape.numProofs =>
        rotatedFeed vk.omega vk.instanceQueryLayout
          (fun query : Fin shape.numInstanceQueries =>
            coeffsToPoly
              ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment
                ps ch pbatch (instanceSet proofIndex query)
                (hinstanceSet proofIndex query)
                (hlen _ (hinstanceSet proofIndex query))
                (hprob1 _ (hinstanceSet proofIndex query))
                haccepts).cols (instanceMem proofIndex query)))) =
        model.instanceCols := by
    simpa only [memberDecode, vestaExtractedMemberDecode] using hInstance
  have result :=
    acceptedModelCircuitSat_or_relation_of_feed_eq
      urs hk vk instanceCommitment ps ch pU pW hpoly
      pbatch hξcur hlen hprob1 haccepts memberDecode hblinding
      adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem
      i m hm colPoly hbindAll hquot hroute hevals claimed
      hAdviceTerminal hInstanceTerminal hxgood
  simpa only [memberDecode] using result

assert_no_sorry acceptedModelCircuitSat_or_relation_of_acceptedSelections

end Zcash.Snark
