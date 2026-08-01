import Zcash.Snark.Soundness.Action.AdaptiveStatementSemantic

/-!
# Adaptive-statement Action event composition

The relation finder combines the load-bearing pre-`theta` instance-coordinate comparison with the
complete one-run Action terminal.  Probability composition keeps the still-to-be-priced
statistical residual explicit; this prevents either silently assuming that residual away or
wrapping an already adaptive theorem in a second query factor.
-/

namespace Zcash.Snark

open Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open scoped ENNReal

local instance adaptiveStatementEventVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- One combined relation finder: bind the selected instance coordinates, compare every proof
coordinate with the annotation at the squeeze where it is used, then run the decoded Action
terminal.  All algebraic mismatch branches therefore share one textbook-DLOG reduction. -/
noncomputable def relationFinder {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) →
    family.Coins → Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
      [family.instanceRepresentationRelationFinder basis O,
       family.preIpaRepresentationRelationFinder basis O,
       family.ipaRepresentationRelationFinder basis O,
       family.semanticRepresentationRelationFinder basis O,
       family.semanticSourceMismatchRelationFinder basis O,
       family.statementQuotientRelationFinder basis O,
       family.terminalRelationFinder hchar basis O]

/-- No result from the combined finder means every coordinate-provenance subfinder was empty. -/
theorem relationFinder_none_provenance {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.relationFinder hchar basis O = none) :
    family.instanceRepresentationRelationFinder basis O = none ∧
      family.preIpaRepresentationRelationFinder basis O = none ∧
      family.ipaRepresentationRelationFinder basis O = none ∧
      family.semanticRepresentationRelationFinder basis O = none ∧
      family.semanticSourceMismatchRelationFinder basis O = none ∧
      family.statementQuotientRelationFinder basis O = none := by
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1
    (by simpa only [relationFinder] using hnone)
  simp only [List.mem_cons, forall_eq_or_imp] at hall
  exact ⟨hall.1, hall.2.1, hall.2.2.1, hall.2.2.2.1, hall.2.2.2.2.1,
    hall.2.2.2.2.2.1⟩

/-- No result from the combined finder also means the pointwise terminal returned no relation. -/
theorem relationFinder_none_terminal {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (hnone : family.relationFinder hchar basis O = none) :
    family.terminalRelationFinder hchar basis O = none := by
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1
    (by simpa only [relationFinder] using hnone)
  apply hall
  simp

/-- The exact DLOG-reduction event of the combined adaptive-statement finder. -/
def relationEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  {q | (family.relationFinder hchar q.1 q.2).isSome}

/-- False-statement acceptance not already converted into explicit relation data. -/
def statisticalResidualEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  family.acceptFalseStatementEvent \ family.relationEvent hchar

/-! ## Concrete statistical surface events -/

/-- The selected statement's `z = 0` slice. -/
def zeroEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  {q | family.runPreIpaReads q.1 q.2 10 = 0}

/-- The union of the selected statement's round-local IPA discrepancy roots. -/
def ipaEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  {q | ∃ j : Fin (AdaptiveActionStatementShape pp).k,
    let output := family.runOutput q.1 q.2
    let t := family.ipaPoint q.1 j output
    q.2 t ∈ outputIpaFallbackBad family q.1 j output t q.2 ∧
      family.ipaRepresentationRelationFinder q.1 q.2 = none}

/-- The union of the six selected-statement deployed-root surfaces. -/
def rootEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  {q | ∃ i : Fin 6,
    let n := deployedRootChallengeIndex i
    let output := family.runOutput q.1 q.2
    let t := family.preIpaPoint q.1 n output
    q.2 t ∈ outputRootBad family q.1 n output t q.2 ∧
      family.preIpaRepresentationRelationFinder q.1 q.2 = none}

/-- The union of the five selected-statement Action semantic surfaces. -/
def semanticEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  {q | ∃ n : Fin 5,
    let n11 : Fin 11 := Fin.castLE (by omega) n
    let output := family.runOutput q.1 q.2
    let t := family.preIpaPoint q.1 n11 output
    q.2 t ∈ outputSemanticBad family q.1 n output t q.2 ∧
      family.semanticRepresentationRelationFinder q.1 q.2 = none}

/-- Every directly priced statistical failure for one adaptive selected statement. -/
def statisticalSurfaceEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp) :
    Set ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) × family.Coins) :=
  family.zeroEvent ∪ (family.ipaEvent ∪ (family.rootEvent ∪ family.semanticEvent))

/-! ## Deterministic surface exhaustion -/

set_option maxHeartbeats 800000 in
theorem BatchWitness.goodRoots_of_not_rootEvent {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins)
    (witness : family.BatchWitness basis O)
    (hroot : (basis, O) ∉ family.rootEvent)
    (hpre : family.preIpaRepresentationRelationFinder basis O = none) :
    family.BatchGoodRoots basis O witness := by
  let output := family.runOutput basis O
  let data := output.proofData
  let fixed := adaptiveStatementInstanceRepresentationList output.instanceRepresentations ++
    family.fixedRepresentations basis
  let nu := family.runPreIpaReads basis O
  have hsets := witness.rootSets_eq
  constructor
  · intro hx1
    apply hroot
    refine ⟨(5 : Fin 6), ?_⟩
    change O (family.preIpaPoint basis 5 output) ∈
        outputRootBad family basis 5 output (family.preIpaPoint basis 5 output) O ∧ _
    refine ⟨?_, hpre⟩
    rw [show output = family.runOutput basis O by rfl, outputRootBad_actual,
      outputRootSurface_five]
    change nu 5 ∈ adaptiveX1AllRootSet (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      data.adaptivePreX1MembersCovered (adaptiveStrictPrefixRecord 5 nu)
    rw [adaptiveX1AllRootSet_strictPrefix]
    rw [show adaptiveX1AllRootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        data.adaptivePreX1MembersCovered nu =
      deployedX1AllRootSet
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
        (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (chRecord nu (fun _ => 0)) witness.batches from hsets.1]
    simpa [output, data, nu, runPreIpaRecord] using hx1
  · intro hx2
    apply hroot
    refine ⟨(4 : Fin 6), ?_⟩
    change O (family.preIpaPoint basis 6 output) ∈
        outputRootBad family basis 6 output (family.preIpaPoint basis 6 output) O ∧ _
    refine ⟨?_, hpre⟩
    rw [show output = family.runOutput basis O by rfl, outputRootBad_actual,
      outputRootSurface_six]
    change nu 6 ∈ adaptiveX2RootSet (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      data.adaptivePreX1MembersCovered (adaptiveStrictPrefixRecord 6 nu)
    rw [adaptiveX2RootSet_strictPrefix]
    rw [show adaptiveX2RootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        data.adaptivePreX1MembersCovered nu =
      deployedX2RootSet
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
        (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (chRecord nu (fun _ => 0)) witness.batches from hsets.2.1]
    simpa [output, data, nu, runPreIpaRecord] using hx2
  · intro hx3
    apply hroot
    refine ⟨(3 : Fin 6), ?_⟩
    change O (family.preIpaPoint basis 7 output) ∈
        outputRootBad family basis 7 output (family.preIpaPoint basis 7 output) O ∧ _
    refine ⟨?_, hpre⟩
    rw [show output = family.runOutput basis O by rfl, outputRootBad_actual,
      outputRootSurface_seven]
    change nu 7 ∈ adaptiveX3RootSet (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ (adaptiveStrictPrefixRecord 7 nu)
    rw [adaptiveX3RootSet_strictPrefix]
    rw [show adaptiveX3RootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
      deployedX3RootSet
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
        (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (chRecord nu (fun _ => 0)) witness.batches from hsets.2.2.1]
    simpa [output, data, nu, runPreIpaRecord] using hx3
  · intro hx4
    apply hroot
    refine ⟨(2 : Fin 6), ?_⟩
    change O (family.preIpaPoint basis 8 output) ∈
        outputRootBad family basis 8 output (family.preIpaPoint basis 8 output) O ∧ _
    refine ⟨?_, hpre⟩
    rw [show output = family.runOutput basis O by rfl, outputRootBad_actual,
      outputRootSurface_eight]
    change nu 8 ∈ adaptiveX4RootSet (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ (adaptiveStrictPrefixRecord 8 nu)
    rw [adaptiveX4RootSet_strictPrefix]
    rw [show adaptiveX4RootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
      deployedX4RootSet
        (ursOfAugmentedBasis (AdaptiveActionStatementShape pp).k basis) rfl
        (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (chRecord nu (fun _ => 0)) witness.batches from hsets.2.2.2.1]
    simpa [output, data, nu, runPreIpaRecord] using hx4
  · intro hxi
    apply hroot
    refine ⟨(0 : Fin 6), ?_⟩
    change O (family.preIpaPoint basis 9 output) ∈
        outputRootBad family basis 9 output (family.preIpaPoint basis 9 output) O ∧ _
    refine ⟨?_, hpre⟩
    rw [show output = family.runOutput basis O by rfl, outputRootBad_actual,
      outputRootSurface_nine]
    change nu 9 ∈ adaptiveXiRootSet (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
      data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
      ⟨data.algebraicProof.ipaS, by simp, rfl⟩ (adaptiveStrictPrefixRecord 9 nu)
    rw [adaptiveXiRootSet_strictPrefix]
    rw [show adaptiveXiRootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨data.algebraicProof.ipaS, by simp, rfl⟩ nu =
      szBadSet (ipaShiftXiPolynomial
        (commitGen (evalVector (AdaptiveActionStatementShape pp).k (nu 7))
            (data.toAlgebraicWfProof.aMulti nu) -
          multiopenValue (adaptiveActionStatementVk pp basis)
            (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
            data.algebraicProof.erase (chRecord nu (fun _ => 0)))
        (commitGen (evalVector (AdaptiveActionStatementShape pp).k (nu 7))
          data.toAlgebraicWfProof.s)) from hsets.2.2.2.2.1]
    simpa [output, data, nu, runPreIpaRecord, runProof] using hxi
  · intro hz
    apply hroot
    refine ⟨(1 : Fin 6), ?_⟩
    change O (family.preIpaPoint basis 10 output) ∈
        outputRootBad family basis 10 output (family.preIpaPoint basis 10 output) O ∧ _
    refine ⟨?_, hpre⟩
    rw [show output = family.runOutput basis O by rfl, outputRootBad_actual,
      outputRootSurface_ten]
    change nu 10 ∈ adaptiveZRootSet (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
      data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
      ⟨data.algebraicProof.ipaS, by simp, rfl⟩ (adaptiveStrictPrefixRecord 10 nu)
    rw [adaptiveZRootSet_strictPrefix]
    rw [show adaptiveZRootSet (adaptiveActionStatementVk pp basis)
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨data.algebraicProof.ipaS, by simp, rfl⟩ nu =
      szBadSet (ipaShiftZPolynomial
        (commitGen (evalVector (AdaptiveActionStatementShape pp).k (nu 7))
            (data.toAlgebraicWfProof.aMulti nu) -
          multiopenValue (adaptiveActionStatementVk pp basis)
            (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
            data.algebraicProof.erase (chRecord nu (fun _ => 0)))
        (data.toAlgebraicWfProof.multiU nu) data.toAlgebraicWfProof.sU
        (commitGen (evalVector (AdaptiveActionStatementShape pp).k (nu 7))
          data.toAlgebraicWfProof.s) (nu 9)) from hsets.2.2.2.2.2]
    simpa [output, data, nu, runPreIpaRecord, runProof] using hz


/-- The adaptive false-statement event is exhausted by the relation event and its literal
statistical residual. -/
theorem acceptFalseStatementEvent_subset {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder) :
    family.acceptFalseStatementEvent ⊆
      family.relationEvent hchar ∪ family.statisticalResidualEvent hchar := by
  intro q hq
  by_cases hrelation : q ∈ family.relationEvent hchar
  · exact Or.inl hrelation
  · exact Or.inr ⟨hq, hrelation⟩

/-! ## Surface pricing -/

/-- The selected-statement zero slice keeps the ordinary one-field query price. -/
theorem zeroEvent_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | family.runPreIpaReads basis O 10 = 0} ≤
        (family.Q + 1 : Nat) * (1 / Fintype.card Fp) := by
  have hzero := fsAdvantageFull_zero_slice_le (family.adversary basis).erase
    (fun _ _ _ => True)
    (fun (output : AdaptiveActionStatementOutput pp basis
        (family.fixedRepresentations basis)) i =>
      output.prefixesPre (family.vkTranscriptRepr basis) i)
    (fun (output : AdaptiveActionStatementOutput pp basis
        (family.fixedRepresentations basis)) j =>
      output.prefixes (family.vkTranscriptRepr basis) j)
    10 (family.queryBound basis)
  simpa only [fsWinsFull, true_and, runPreIpaReads, runOutput] using hzero

/-- Union the round-local IPA prices without another adaptive-query loss. -/
theorem ipaEvent_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | ∃ j : Fin (AdaptiveActionStatementShape pp).k,
        let output := family.runOutput basis O
        let t := family.ipaPoint basis j output
        O t ∈ outputIpaFallbackBad family basis j output t O ∧
          family.ipaRepresentationRelationFinder basis O = none} ≤
      (AdaptiveActionStatementShape pp).k *
        ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) := by
  have hsub : {O | ∃ j : Fin (AdaptiveActionStatementShape pp).k,
      let output := family.runOutput basis O
      let t := family.ipaPoint basis j output
      O t ∈ outputIpaFallbackBad family basis j output t O ∧
        family.ipaRepresentationRelationFinder basis O = none} ⊆
      ⋃ j : Fin (AdaptiveActionStatementShape pp).k,
        {O | let output := family.runOutput basis O
          let t := family.ipaPoint basis j output
          O t ∈ outputIpaFallbackBad family basis j output t O ∧
            family.ipaRepresentationRelationFinder basis O = none} := by
    rintro O ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    ∑ j : Fin (AdaptiveActionStatementShape pp).k,
        (PMF.uniformOfFintype family.Coins).toOuterMeasure
          {O | let output := family.runOutput basis O
            let t := family.ipaPoint basis j output
            O t ∈ outputIpaFallbackBad family basis j output t O ∧
              family.ipaRepresentationRelationFinder basis O = none} ≤
      ∑ _j : Fin (AdaptiveActionStatementShape pp).k,
        ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) := by
          gcongr with j
          exact family.ipaBadWithoutRelation_table_le basis j
    _ = _ := by simp

/-- Union the six deployed-root prices into the existing shape-level root budget. -/
theorem rootEvent_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | ∃ i : Fin 6,
        let n := deployedRootChallengeIndex i
        let output := family.runOutput basis O
        let t := family.preIpaPoint basis n output
        O t ∈ outputRootBad family basis n output t O ∧
          family.preIpaRepresentationRelationFinder basis O = none} ≤
      (family.Q + 1 : Nat) * algebraicRootBudget
        (AdaptiveActionStatementShape pp) (AdaptiveActionStatementShape pp).k := by
  have hsub : {O | ∃ i : Fin 6,
      let n := deployedRootChallengeIndex i
      let output := family.runOutput basis O
      let t := family.preIpaPoint basis n output
      O t ∈ outputRootBad family basis n output t O ∧
        family.preIpaRepresentationRelationFinder basis O = none} ⊆
      ⋃ i : Fin 6, {O |
        let n := deployedRootChallengeIndex i
        let output := family.runOutput basis O
        let t := family.preIpaPoint basis n output
        O t ∈ outputRootBad family basis n output t O ∧
          family.preIpaRepresentationRelationFinder basis O = none} := by
    rintro O ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    ∑ i : Fin 6, (PMF.uniformOfFintype family.Coins).toOuterMeasure
        {O | let n := deployedRootChallengeIndex i
          let output := family.runOutput basis O
          let t := family.preIpaPoint basis n output
          O t ∈ outputRootBad family basis n output t O ∧
            family.preIpaRepresentationRelationFinder basis O = none} ≤
      ∑ i : Fin 6, (family.Q + 1 : Nat) *
        deployedRootEventBudget (AdaptiveActionStatementShape pp) i := by
          gcongr with i
          let n := deployedRootChallengeIndex i
          have h5n : 5 ≤ (n : Nat) := by
            fin_cases i <;> norm_num [n, deployedRootChallengeIndex]
          simpa only [n, adaptiveRootEventIndex_deployedRootChallengeIndex] using
            (family.rootBadWithoutRelation_table_le basis n h5n)
    _ = (family.Q + 1 : Nat) * ∑ i : Fin 6,
        deployedRootEventBudget (AdaptiveActionStatementShape pp) i := by
          rw [Finset.mul_sum]
    _ ≤ _ := by
      gcongr
      exact deployedRootEventBudget_sum_le (AdaptiveActionStatementShape pp)

/-- Union the five semantic surfaces under their existing pointwise bounds. -/
theorem semanticEvent_table_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (epsilon : Fin 5 → ENNReal)
    (hsurface : ∀ (n : Fin 5)
      (instanceCommitment :
        Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
      (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ epsilon n) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure
      {O | ∃ n : Fin 5,
        let n11 : Fin 11 := Fin.castLE (by omega) n
        let output := family.runOutput basis O
        let t := family.preIpaPoint basis n11 output
        O t ∈ outputSemanticBad family basis n output t O ∧
          family.semanticRepresentationRelationFinder basis O = none} ≤
      (family.Q + 1 : Nat) * ∑ n : Fin 5, epsilon n := by
  have hsub : {O | ∃ n : Fin 5,
      let n11 : Fin 11 := Fin.castLE (by omega) n
      let output := family.runOutput basis O
      let t := family.preIpaPoint basis n11 output
      O t ∈ outputSemanticBad family basis n output t O ∧
        family.semanticRepresentationRelationFinder basis O = none} ⊆
      ⋃ n : Fin 5, {O |
        let n11 : Fin 11 := Fin.castLE (by omega) n
        let output := family.runOutput basis O
        let t := family.preIpaPoint basis n11 output
        O t ∈ outputSemanticBad family basis n output t O ∧
          family.semanticRepresentationRelationFinder basis O = none} := by
    rintro O ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    ∑ n : Fin 5, (PMF.uniformOfFintype family.Coins).toOuterMeasure
        {O | let n11 : Fin 11 := Fin.castLE (by omega) n
          let output := family.runOutput basis O
          let t := family.preIpaPoint basis n11 output
          O t ∈ outputSemanticBad family basis n output t O ∧
            family.semanticRepresentationRelationFinder basis O = none} ≤
      ∑ n : Fin 5, (family.Q + 1 : Nat) * epsilon n := by
        gcongr with n
        exact family.semanticBadWithoutRelation_table_le basis n (hsurface n)
    _ = _ := by rw [Finset.mul_sum]

/-- The complete statistical surface union has one shared `(Q + 1)` loss. -/
theorem statisticalSurfaceEvent_prob_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (B : VestaG) (epsilon : Fin 5 → ENNReal)
    (hsurface : ∀
      (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
      (n : Fin 5)
      (instanceCommitment :
        Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
      (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ epsilon n) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
        family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.statisticalSurfaceEvent) ≤
      (family.Q + 1 : Nat) *
        (1 / Fintype.card Fp +
          (AdaptiveActionStatementShape pp).k *
            (2 / (Fintype.card Fp : ENNReal)) +
          algebraicRootBudget (AdaptiveActionStatementShape pp)
            (AdaptiveActionStatementShape pp).k +
          ∑ n : Fin 5, epsilon n) := by
  have hzero :
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
          family.Coins)).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.zeroEvent) ≤
        (family.Q + 1 : Nat) * (1 / Fintype.card Fp) := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (scalarBasis B logs, O) ∈ family.zeroEvent})
    intro logs
    exact family.zeroEvent_table_le (scalarBasis B logs)
  have hipa :
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
          family.Coins)).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.ipaEvent) ≤
        (AdaptiveActionStatementShape pp).k *
          ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (scalarBasis B logs, O) ∈ family.ipaEvent})
    intro logs
    exact family.ipaEvent_table_le (scalarBasis B logs)
  have hroot :
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
          family.Coins)).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.rootEvent) ≤
        (family.Q + 1 : Nat) * algebraicRootBudget
          (AdaptiveActionStatementShape pp) (AdaptiveActionStatementShape pp).k := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (scalarBasis B logs, O) ∈ family.rootEvent})
    intro logs
    exact family.rootEvent_table_le (scalarBasis B logs)
  have hsemantic :
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
          family.Coins)).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.semanticEvent) ≤
        (family.Q + 1 : Nat) * ∑ n : Fin 5, epsilon n := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs => {O | (scalarBasis B logs, O) ∈ family.semanticEvent})
    intro logs
    exact family.semanticEvent_table_le (scalarBasis B logs) epsilon
      (hsurface (scalarBasis B logs))
  unfold statisticalSurfaceEvent
  simp only [Set.preimage_union]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine le_trans (add_le_add hzero (MeasureTheory.measure_union_le _ _)) ?_
  refine le_trans (add_le_add_right (add_le_add hipa
    (MeasureTheory.measure_union_le _ _)) _) ?_
  refine le_trans (add_le_add_right (add_le_add_right (add_le_add hroot hsemantic) _) _) ?_
  ring_nf
  exact le_rfl

/-- Once the deterministic terminal bridge places the literal residual in the concrete surface
union, its probability is fully discharged by the table bounds above. -/
theorem statisticalResidualEvent_prob_le_of_surface_cover {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) (epsilon : Fin 5 → ENNReal)
    (hsurface : ∀
      (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
      (n : Fin 5)
      (instanceCommitment :
        Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
      (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ epsilon n)
    (hcover : family.statisticalResidualEvent hchar ⊆ family.statisticalSurfaceEvent) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
        family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        family.statisticalResidualEvent hchar) ≤
      (family.Q + 1 : Nat) *
        (1 / Fintype.card Fp +
          (AdaptiveActionStatementShape pp).k *
            (2 / (Fintype.card Fp : ENNReal)) +
          algebraicRootBudget (AdaptiveActionStatementShape pp)
            (AdaptiveActionStatementShape pp).k +
          ∑ n : Fin 5, epsilon n) := by
  refine le_trans (MeasureTheory.measure_mono (Set.preimage_mono hcover)) ?_
  exact family.statisticalSurfaceEvent_prob_le B epsilon hsurface

/-- The combined adaptive-statement finder has the standard textbook-DLOG reduction. -/
theorem relation_prob_le_of_textbookDL {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B (family.relationFinder hchar) bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
        family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' family.relationEvent hchar) ≤
      bound + 1 / Fintype.card Fp := by
  simpa [relationEvent, relSetWithCoins] using
    (relationWithCoins_prob_le_of_textbookDL B (family.relationFinder hchar) hDL)

/-- Adaptive-statement soundness composition with the statistical residual exposed as a premise. -/
theorem acceptFalseStatement_prob_le {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) {dlBound residualBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B (family.relationFinder hchar) dlBound)
    (hresidual :
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
          family.Coins)).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
          family.statisticalResidualEvent hchar) ≤ residualBound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
        family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        family.acceptFalseStatementEvent) ≤
      (dlBound + 1 / Fintype.card Fp) + residualBound := by
  refine le_trans (MeasureTheory.measure_mono (Set.preimage_mono
    (family.acceptFalseStatementEvent_subset hchar))) ?_
  rw [Set.preimage_union]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add (family.relation_prob_le_of_textbookDL hchar B hDL) hresidual

/-- When the residual surfaces share the existing adaptive query accounting, statement selection
adds no second multiplicative loss: the capstone contains one `(Q + 1)` factor. -/
theorem acceptFalseStatement_prob_le_of_query_accounting {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) {dlBound epsilon : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B (family.relationFinder hchar) dlBound)
    (hresidual :
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
          family.Coins)).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
          family.statisticalResidualEvent hchar) ≤ (family.Q + 1 : Nat) * epsilon) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
        family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        family.acceptFalseStatementEvent) ≤
      (dlBound + 1 / Fintype.card Fp) + (family.Q + 1 : Nat) * epsilon :=
  family.acceptFalseStatement_prob_le hchar B hDL hresidual

/-- Adaptive-statement false-statement soundness with every statistical surface instantiated.
The deterministic surface-cover premise is separated so its terminal proof remains auditable. -/
theorem acceptFalseStatement_prob_le_of_surface_cover {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) <
        Zcash.Arithmetic.scalarFieldOrder)
    (B : VestaG) {dlBound : ENNReal} (epsilon : Fin 5 → ENNReal)
    (hDL : TextbookDLWithCoinsAdvantageLE B (family.relationFinder hchar) dlBound)
    (hsurface : ∀
      (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
      (n : Fin 5)
      (instanceCommitment :
        Fin (AdaptiveActionStatementShape pp).numProofs → Nat → VestaG)
      (ps : ProofString (AdaptiveActionStatementShape pp) Fp VestaG)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAtOf basis instanceCommitment n ps source earlier) ≤ epsilon n)
    (hcover : family.statisticalResidualEvent hchar ⊆ family.statisticalSurfaceEvent) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → Fp) ×
        family.Coins)).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        family.acceptFalseStatementEvent) ≤
      (dlBound + 1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (1 / Fintype.card Fp +
            (AdaptiveActionStatementShape pp).k *
              (2 / (Fintype.card Fp : ENNReal)) +
            algebraicRootBudget (AdaptiveActionStatementShape pp)
              (AdaptiveActionStatementShape pp).k +
            ∑ n : Fin 5, epsilon n) := by
  apply family.acceptFalseStatement_prob_le hchar B hDL
  exact family.statisticalResidualEvent_prob_le_of_surface_cover hchar B epsilon
    hsurface hcover

end ComputedAdaptiveActionStatementFSFamily

end Zcash.Snark
