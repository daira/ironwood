import Zcash.Circuits.Integration.AdaptiveActionTerminal
import Zcash.Snark.Soundness.AGM.AdaptiveComposition

/-!
# Literal Action soundness for arbitrary adaptive online-AGM adversaries

This file exposes the executable adaptive Action terminal as one combined relation finder.  Its
public event is the literal deployed-verifier event `accept ∧ ¬ BundleStatement`; no
propositionally closed relation is treated as semantic success, and no sequential trace, cut, or
phase presentation is an input.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)
open scoped ENNReal

local instance vestaInhabitedAdaptiveActionEvent : Inhabited VestaG := ⟨0⟩

variable (pp : ProofParams)
  (family : ComputedAdaptiveOnlineAGMFSFamily (pp.mergeDerived actionCircuit))
  (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
  (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey pp
    (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
  (hI : ∀ basis, family.instanceCommitment basis =
    actionCircuit.instanceCommitment pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
  (hchar : ∀ basis O, deployedX4PairCount
    (actionCircuit.toVerifierKey pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (actionCircuit.instanceCommitment pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (adaptiveActionRunOutput family basis O).1.proof.1
    (adaptiveActionRunRecord family basis O) < scalarFieldOrder)

/-- The exact Action soundness event for the bare adaptive online-AGM family. -/
def adaptiveActionAcceptFalseStatementEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  {q | adaptiveActionAccepts family q.1 q.2 ∧ ¬BundleStatement inputs}

/-- The complete adaptive relation finder: provenance, IPA, deployed unbatching, and the
executable Action terminal are charged by one DLOG reduction. -/
def adaptiveActionRelationFinder :
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) →
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    match family.adaptiveStraightLineDeployedRelationFinder basis O with
    | some relation => some relation
    | none => adaptiveActionTerminalRelationFinder pp family inputs hvk hI hchar basis O

/-- Explicit relation-producing runs of the combined adaptive Action finder. -/
def adaptiveActionRelationEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  {q | (adaptiveActionRelationFinder pp family inputs hvk hI hchar q.1 q.2).isSome}

/-- The separately priced adaptive `z = 0` slice. -/
def adaptiveActionZeroEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  {q | q.2 (algebraicFullPrefixesPre family.init
    ((family.toFamily.adversary q.1).run q.2) 10) = 0}

/-- The union of the annotation-aware adaptive IPA surfaces. -/
def adaptiveActionIpaEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  {q | ∃ j : Fin (pp.mergeDerived actionCircuit).k,
    q.2 ∈ family.adaptiveIpaBadWithoutRelation q.1 j}

/-- The union of the six annotation-aware deployed-root surfaces. -/
def adaptiveActionRootEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  {q | ∃ i : Fin 6, q.2 ∈ family.adaptiveRootBadWithoutRelation q.1 i}

/-- The remaining semantic-squeeze obligation after the executable algebraic branches have been
removed.  Subsequent Action surface lemmas refine this residual into the `x/y/β/γ/θ` finite
bad sets; importantly, it is stated directly on the bare adaptive family. -/
def adaptiveActionSemanticResidualEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  adaptiveActionAcceptFalseStatementEvent pp family inputs \
    (adaptiveActionZeroEvent pp family ∪
      (adaptiveActionIpaEvent pp family ∪
        (adaptiveActionRootEvent pp family ∪
          adaptiveActionRelationEvent pp family inputs hvk hI hchar)))

/-- Literal false-statement acceptance is exhausted by the zero slice, adaptive IPA/root
surfaces, the single computed relation event, and the remaining five semantic squeezes. -/
theorem adaptiveActionAcceptFalseStatementEvent_subset :
    adaptiveActionAcceptFalseStatementEvent pp family inputs ⊆
      adaptiveActionZeroEvent pp family ∪
        (adaptiveActionIpaEvent pp family ∪
          (adaptiveActionRootEvent pp family ∪
            (adaptiveActionRelationEvent pp family inputs hvk hI hchar ∪
              adaptiveActionSemanticResidualEvent pp family inputs hvk hI hchar))) := by
  intro q hq
  by_cases hz : q ∈ adaptiveActionZeroEvent pp family
  · exact Or.inl hz
  by_cases hipa : q ∈ adaptiveActionIpaEvent pp family
  · exact Or.inr (Or.inl hipa)
  by_cases hroot : q ∈ adaptiveActionRootEvent pp family
  · exact Or.inr (Or.inr (Or.inl hroot))
  by_cases hrelation : q ∈ adaptiveActionRelationEvent pp family inputs hvk hI hchar
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrelation)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hq, ?_⟩)))
    simp only [Set.mem_union, not_or]
    exact ⟨hz, hipa, hroot, hrelation⟩

/-- Transfer any adaptive Action event across a uniform-URS basis identification. -/
theorem adaptiveActionEvent_prob_eq_of_uniformURS
    {Omega : Type*} (setup : PMF Omega) (B : VestaG)
    (basisOf : Omega →
      AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (hURS : OrchardUniformURSIdentification setup
      (pp.mergeDerived actionCircuit).k B basisOf)
    (event : Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp))) :
    (independentProductPMF setup
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
      ((fun p => (basisOf p.1, p.2)) ⁻¹' event) =
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
      ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' event) := by
  let oraclePMF := PMF.uniformOfFintype
    (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp)
  have hprod :
      (independentProductPMF setup oraclePMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype
            (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → Fp))
          oraclePMF).map (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) oraclePMF :=
        independentProductPMF_map_left setup oraclePMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype
            (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → Fp)).map
              (scalarBasis B)) oraclePMF :=
        congrArg (fun p => independentProductPMF p oraclePMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype
          (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → Fp))
        oraclePMF (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) =>
      p.toOuterMeasure event) hprod
  change ((independentProductPMF setup oraclePMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure event =
    ((independentProductPMF
      (PMF.uniformOfFintype
        (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → Fp))
      oraclePMF).map (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure event at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  calc
    _ = (independentProductPMF
        (PMF.uniformOfFintype
          (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → Fp))
        oraclePMF).toOuterMeasure
      ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' event) := hmeasure
    _ = _ := by rw [independentProductPMF_uniform]

/-- The combined executable adaptive Action finder has the standard textbook-DLOG reduction. -/
theorem adaptiveActionRelation_prob_le_of_textbookDL
    (B : VestaG) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (adaptiveActionRelationFinder pp family inputs hvk hI hchar) bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        adaptiveActionRelationEvent pp family inputs hvk hI hchar) ≤
      bound + 1 / Fintype.card Fp := by
  simpa [adaptiveActionRelationEvent, relSetWithCoins] using
    (relationWithCoins_prob_le_of_textbookDL B
      (adaptiveActionRelationFinder pp family inputs hvk hI hchar) hDL)

/-- The adaptive Action zero slice has the ordinary one-field query-loss price. -/
theorem adaptiveActionZero_prob_le (B : VestaG) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' adaptiveActionZeroEvent pp family) ≤
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) := by
  apply uniformOfFintype_prod_fiber_bound_right
    (fun logs => {O | (scalarBasis B logs, O) ∈ adaptiveActionZeroEvent pp family})
  intro logs
  let basis := scalarBasis B logs
  have hzero := fsAdvantageFull_zero_slice_le (family.toFamily.adversary basis)
    (fun _ _ _ => True) (algebraicFullPrefixesPre family.init)
    (algebraicFullPrefixes family.init) 10 (family.toFamily.queryBound basis)
  simpa only [adaptiveActionZeroEvent, Set.mem_setOf_eq, basis, fsWinsFull, true_and] using hzero

/-- All adaptive IPA surfaces, averaged over the sampled basis, retain their direct squeeze
price. -/
theorem adaptiveActionIpa_prob_le (B : VestaG) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' adaptiveActionIpaEvent pp family) ≤
      (pp.mergeDerived actionCircuit).k *
        ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) := by
  apply uniformOfFintype_prod_fiber_bound_right
    (fun logs => {O | ∃ j : Fin (pp.mergeDerived actionCircuit).k,
      O ∈ family.adaptiveIpaBadWithoutRelation (scalarBasis B logs) j})
  intro logs
  exact family.adaptiveIpaBadWithoutRelation_all_measure_le (scalarBasis B logs)

/-- All six deployed-root surfaces, averaged over the sampled basis, retain their direct adaptive
squeeze price. -/
theorem adaptiveActionRoot_prob_le (B : VestaG) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' adaptiveActionRootEvent pp family) ≤
      (family.Q + 1 : Nat) *
        algebraicRootBudget (pp.mergeDerived actionCircuit)
          (pp.mergeDerived actionCircuit).k := by
  apply uniformOfFintype_prod_fiber_bound_right
    (fun logs => {O | ∃ i : Fin 6,
      O ∈ family.adaptiveRootBadWithoutRelation (scalarBasis B logs) i})
  intro logs
  exact family.adaptiveRootBadWithoutRelation_all_measure_le (scalarBasis B logs)

/-- Probability composition for the bare adaptive family.  The algebraic part is completely
closed by the executable combined finder; `semanticBound` is precisely the remaining five
Action squeeze surfaces. -/
theorem adaptiveActionAcceptFalseStatement_prob_le
    (B : VestaG) {dlogBound semanticBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (adaptiveActionRelationFinder pp family inputs hvk hI hchar) dlogBound)
    (hsemantic :
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → Fp) ×
          (BTranscript Fp VestaG
            (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
              + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
          adaptiveActionSemanticResidualEvent pp family inputs hvk hI hchar) ≤
        semanticBound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        adaptiveActionAcceptFalseStatementEvent pp family inputs) ≤
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        ((pp.mergeDerived actionCircuit).k *
          ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) +
        ((family.Q + 1 : Nat) *
          algebraicRootBudget (pp.mergeDerived actionCircuit)
            (pp.mergeDerived actionCircuit).k +
        ((dlogBound + 1 / Fintype.card Fp) + semanticBound))) := by
  refine le_trans (MeasureTheory.measure_mono
    (Set.preimage_mono
      (adaptiveActionAcceptFalseStatementEvent_subset pp family inputs hvk hI hchar))) ?_
  simp only [Set.preimage_union]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (adaptiveActionZero_prob_le pp family B) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (adaptiveActionIpa_prob_le pp family B) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (adaptiveActionRoot_prob_le pp family B) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (adaptiveActionRelation_prob_le_of_textbookDL pp family inputs hvk hI hchar B hDL)
    hsemantic

end ActionTerminal

end Zcash.Snark
