import Zcash.Circuits.Action.SynthesisLaws

open Halo2

set_option maxHeartbeats 20000

namespace Zcash.Circuits.NoteCommit.Main

open Ecc.MulFixed (FixedBase)
open Specs.Sinsemilla (Generators)

@[circuit_norm]
private theorem witnessMessagePiece_nextRegionIndex
    (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1)
    (i : RegionIndex) :
    (Sinsemilla.HashToPoint.witnessMessagePiece cfg w).nextRegionIndex i = i + 1 := by
  simp [Sinsemilla.HashToPoint.witnessMessagePiece, circuit_norm]

@[circuit_norm]
private theorem witnessShortCheck_nextRegionIndex
    (K bits : ℕ) (cfg : LookupRangeCheck.Config K)
    (w : WitgenIR Fp 1) (i : RegionIndex) :
    (LookupRangeCheck.witnessShortCheck K bits cfg w).nextRegionIndex i = i + 1 := by
  simp [LookupRangeCheck.witnessShortCheck, circuit_norm]

private theorem witnessMessagePiece_inputSelectorsExact
    (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((Sinsemilla.HashToPoint.witnessMessagePiece cfg w).operations i) := by
  simp [Sinsemilla.HashToPoint.witnessMessagePiece,
    Operations.LookupRelevantSelectorActivationsExact,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    Operation.LookupRelevantSelectorActivationsExact, circuit_norm]

private theorem lookupExact_assignAdvice_cons
    (column : Column .advice) (row : ℕ) (witness : WitgenIR Fp 1)
    (body : RegionOperations Fp) :
    RegionOperations.LookupRelevantSelectorActivationsExact
        (RegionOperation.assignAdvice column row witness :: body) ↔
      body.LookupRelevantSelectorActivationsExact := by
  simp [RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt, RegionOperation.ActivatesSelectorAt]

private theorem synthPieces_inputSelectorsExact
    (cfg : Config)
    (hLR : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qRunning.index)
    (hLB : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qBitshift.index)
    (hRB : cfg.lookupConfig.qRunning.index ≠
      cfg.lookupConfig.qBitshift.index)
    (input : Var Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((synthPieces cfg input).operations i) := by
  simp only [synthPieces, circuit_norm]
  repeat' apply And.intro
  all_goals first
    | apply witnessMessagePiece_inputSelectorsExact
    | (apply Zcash.Circuits.witnessShortCheck_inputSelectorsExact <;> assumption)

private theorem rangeCheckAtDecomposed_inputSelectorsExact
    (count : ℕ) (h13 : 13 ≤ count) (hpow : 10 * count ≤ 254)
    (cfg : LookupRangeCheck.Config 10)
    (input : Var unit Fp) (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupRelevantSelectorActivationsExact
      (((LookupRangeCheck.rangeCheckAtDecomposed count h13 hpow).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  apply RegionOperations.lookupRelevantSelectorActivationsExact_of_inputSelectorsEnabled
  simp only [LookupRangeCheck.rangeCheckAtDecomposed, circuit_norm]
  unfold RegionOperations.LookupInputSelectorsEnabled
  rw [List.forall_append]
  constructor
  · apply Zcash.Circuits.rangeCheckLoop_inputSelectorsEnabled
  · simp [RegionOperation.LookupInputSelectorsEnabled]

private theorem witnessCheckDecomposed_inputSelectorsExact
    (cfg : LookupRangeCheck.Config 10) (w : WitgenIR Fp 1)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((LookupRangeCheck.witnessCheckDecomposed cfg w).operations i) := by
  apply (Operations.LookupRelevantSelectorActivationsExact.region_singleton
    "Witness element" _).mpr
  change RegionOperations.LookupRelevantSelectorActivationsExact
    (RegionOperation.assignAdvice cfg.runningSum 0 w ::
      ((LookupRangeCheck.rangeCheckAtDecomposed 25 (by norm_num)
        (by norm_num)).call cfg 0 ()).operations i)
  rw [lookupExact_assignAdvice_cons]
  apply rangeCheckAtDecomposed_inputSelectorsExact

@[circuit_norm]
private theorem witnessCheck_nextRegionIndex
    (K count : ℕ) (strict : Bool) (cfg : LookupRangeCheck.Config K)
    (w : WitgenIR Fp 1) (i : RegionIndex) :
    (LookupRangeCheck.witnessCheck K count strict cfg w).nextRegionIndex i = i + 1 := by
  simp [LookupRangeCheck.witnessCheck, circuit_norm]

@[circuit_norm]
private theorem witnessCheckDecomposed_nextRegionIndex
    (cfg : LookupRangeCheck.Config 10) (w : WitgenIR Fp 1)
    (i : RegionIndex) :
    (LookupRangeCheck.witnessCheckDecomposed cfg w).nextRegionIndex i = i + 1 := by
  simp [LookupRangeCheck.witnessCheckDecomposed, circuit_norm]

private theorem yGateChild_inputSelectorsExact
    (wlsb : WitgenIR Fp 1)
    (originalInput : NoteCommit.YCanonicityCheck.Inputs (AssignedCell Fp))
    (cfg : NoteCommit.YCanonicity.Config)
    (input : Var NoteCommit.YCanonicity.Row Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((NoteCommit.YCanonicityCheck.gateChild wlsb originalInput).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp [NoteCommit.YCanonicityCheck.gateChild,
    NoteCommit.YCanonicity.bundle, FormalRegionCircuit.toFormal,
    Operations.LookupRelevantSelectorActivationsExact,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    Operation.LookupRelevantSelectorActivationsExact, circuit_norm]

private theorem yCircuit_inputSelectorsExact
    (wlsb : WitgenIR Fp 1)
    (cfg : NoteCommit.YCanonicity.Config × LookupRangeCheck.Config 10)
    (hLR : cfg.2.qLookup.index ≠ cfg.2.qRunning.index)
    (hLB : cfg.2.qLookup.index ≠ cfg.2.qBitshift.index)
    (hRB : cfg.2.qRunning.index ≠ cfg.2.qBitshift.index)
    (input : Var NoteCommit.YCanonicityCheck.Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((NoteCommit.YCanonicityCheck.circuit wlsb).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [NoteCommit.YCanonicityCheck.circuit,
    NoteCommit.YCanonicityCheck.synth, circuit_norm]
  repeat' apply And.intro
  · apply Zcash.Circuits.witnessShortCheck_inputSelectorsExact <;> assumption
  · apply Zcash.Circuits.witnessShortCheck_inputSelectorsExact <;> assumption
  · apply witnessCheckDecomposed_inputSelectorsExact
  · apply Action.commitIvkWitnessCheck_inputSelectorsExact
  · apply yGateChild_inputSelectorsExact

private theorem synthChecks_inputSelectorsExact
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config)
    (hLR : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qRunning.index)
    (hLB : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qBitshift.index)
    (hRB : cfg.lookupConfig.qRunning.index ≠
      cfg.lookupConfig.qBitshift.index)
    (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash : RegionIndex) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((synthChecks G R Q hQ cfg input pcs iHash).operations i) := by
  simp only [synthChecks, circuit_norm]
  repeat' apply And.intro
  · apply yCircuit_inputSelectorsExact <;> assumption
  · apply yCircuit_inputSelectorsExact <;> assumption
  · apply Action.commitIvkCommitDomain_inputSelectorsExact
  · apply Action.commitIvkWitnessCheck_inputSelectorsExact
  · apply Action.commitIvkWitnessCheck_inputSelectorsExact
  · apply Action.commitIvkWitnessCheck_inputSelectorsExact
  · apply Action.commitIvkWitnessCheck_inputSelectorsExact

private theorem toFormal_inputSelectorsExact
    {ConfigInput Config : Type} {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (bundle : FormalRegionCircuit Fp ConfigInput Config Input Output)
    (name : String) (cfg : Config) (input : Var Input Fp)
    (i : RegionIndex)
    (hlaw : RegionOperations.LookupRelevantSelectorActivationsExact
      ((bundle.synthesize cfg 0 input).operations i)) :
    Operations.LookupRelevantSelectorActivationsExact
      (((bundle.toFormal name).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  apply (Operations.LookupRelevantSelectorActivationsExact.region_singleton
    name _).mpr
  simpa only [FormalRegionCircuit.toFormal, circuit_norm] using hlaw

private theorem decomposeB_inputSelectorsExact
    (w : WitgenIR Fp 1) (cfg : NoteCommit.DecomposeB.Config)
    (input : Var NoteCommit.DecomposeB.Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((((NoteCommit.DecomposeB.bundle w).toFormal
        "NoteCommit MessagePiece b").call cfg input).operations i) := by
  apply toFormal_inputSelectorsExact
  simp [NoteCommit.DecomposeB.bundle,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt,
    RegionOperation.ActivatesSelectorAt, circuit_norm]

private theorem decomposeD_inputSelectorsExact
    (w : WitgenIR Fp 1) (cfg : NoteCommit.DecomposeD.Config)
    (input : Var NoteCommit.DecomposeD.Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((((NoteCommit.DecomposeD.bundle w).toFormal
        "NoteCommit MessagePiece d").call cfg input).operations i) := by
  apply toFormal_inputSelectorsExact
  simp [NoteCommit.DecomposeD.bundle,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt,
    RegionOperation.ActivatesSelectorAt, circuit_norm]

private theorem decomposeE_inputSelectorsExact
    (cfg : NoteCommit.DecomposeE.Config)
    (input : Var NoteCommit.DecomposeE.Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((NoteCommit.DecomposeE.bundle.toFormal
        "NoteCommit MessagePiece e").call cfg input).operations i) := by
  apply toFormal_inputSelectorsExact
  simp [NoteCommit.DecomposeE.bundle,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt,
    RegionOperation.ActivatesSelectorAt, circuit_norm]

private theorem decomposeG_inputSelectorsExact
    (w : WitgenIR Fp 1) (cfg : NoteCommit.DecomposeG.Config)
    (input : Var NoteCommit.DecomposeG.Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((((NoteCommit.DecomposeG.bundle w).toFormal
        "NoteCommit MessagePiece g").call cfg input).operations i) := by
  apply toFormal_inputSelectorsExact
  simp [NoteCommit.DecomposeG.bundle,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt,
    RegionOperation.ActivatesSelectorAt, circuit_norm]

private theorem decomposeH_inputSelectorsExact
    (w : WitgenIR Fp 1) (cfg : NoteCommit.DecomposeH.Config)
    (input : Var NoteCommit.DecomposeH.Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((((NoteCommit.DecomposeH.bundle w).toFormal
        "NoteCommit MessagePiece h").call cfg input).operations i) := by
  apply toFormal_inputSelectorsExact
  simp [NoteCommit.DecomposeH.bundle,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt,
    RegionOperation.ActivatesSelectorAt, circuit_norm]

private theorem gdCanonicity_inputSelectorsExact
    (cfg : NoteCommit.GdCanonicity.Config)
    (input : Var NoteCommit.GdCanonicity.Row Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((NoteCommit.GdCanonicity.bundle.toFormal
        "NoteCommit input g_d").call cfg input).operations i) := by
  apply toFormal_inputSelectorsExact
  simp [NoteCommit.GdCanonicity.bundle,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt,
    RegionOperation.ActivatesSelectorAt, circuit_norm]

private theorem pkdCanonicity_inputSelectorsExact
    (cfg : NoteCommit.PkdCanonicity.Config)
    (input : Var NoteCommit.PkdCanonicity.Row Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((NoteCommit.PkdCanonicity.bundle.toFormal
        "NoteCommit input pk_d").call cfg input).operations i) := by
  apply toFormal_inputSelectorsExact
  simp [NoteCommit.PkdCanonicity.bundle,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt,
    RegionOperation.ActivatesSelectorAt, circuit_norm]

private theorem valueCanonicity_inputSelectorsExact
    (cfg : NoteCommit.ValueCanonicity.Config)
    (input : Var NoteCommit.ValueCanonicity.Row Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((NoteCommit.ValueCanonicity.bundle.toFormal
        "NoteCommit input value").call cfg input).operations i) := by
  apply toFormal_inputSelectorsExact
  simp [NoteCommit.ValueCanonicity.bundle,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt,
    RegionOperation.ActivatesSelectorAt, circuit_norm]

private theorem rhoCanonicity_inputSelectorsExact
    (cfg : NoteCommit.RhoCanonicity.Config)
    (input : Var NoteCommit.RhoCanonicity.Row Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((NoteCommit.RhoCanonicity.bundle.toFormal
        "NoteCommit input rho").call cfg input).operations i) := by
  apply toFormal_inputSelectorsExact
  simp [NoteCommit.RhoCanonicity.bundle,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt,
    RegionOperation.ActivatesSelectorAt, circuit_norm]

private theorem psiCanonicity_inputSelectorsExact
    (cfg : NoteCommit.PsiCanonicity.Config)
    (input : Var NoteCommit.PsiCanonicity.Row Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((NoteCommit.PsiCanonicity.bundle.toFormal
        "NoteCommit input psi").call cfg input).operations i) := by
  apply toFormal_inputSelectorsExact
  simp [NoteCommit.PsiCanonicity.bundle,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt,
    RegionOperation.ActivatesSelectorAt, circuit_norm]

private theorem synthGates_inputSelectorsExact
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (iHash : RegionIndex) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((synthGates cfg input pcs ccs iHash).operations i) := by
  simp only [synthGates, circuit_norm]
  repeat' apply And.intro
  · apply decomposeB_inputSelectorsExact
  · apply decomposeD_inputSelectorsExact
  · apply decomposeE_inputSelectorsExact
  · apply decomposeG_inputSelectorsExact
  · apply decomposeH_inputSelectorsExact
  · apply gdCanonicity_inputSelectorsExact
  · apply pkdCanonicity_inputSelectorsExact
  · apply valueCanonicity_inputSelectorsExact
  · apply rhoCanonicity_inputSelectorsExact
  · apply psiCanonicity_inputSelectorsExact

theorem circuit_inputSelectorsExact
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config)
    (hLR : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qRunning.index)
    (hLB : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qBitshift.index)
    (hRB : cfg.lookupConfig.qRunning.index ≠
      cfg.lookupConfig.qBitshift.index)
    (input : Var Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((circuit G R Q hQ).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  change Operations.LookupRelevantSelectorActivationsExact
    ((synth G R Q hQ cfg input).operations i)
  simp only [synth, Circuit.operations_bind, Circuit.operations_pure,
    currentRegion_operations, currentRegion_output,
    currentRegion_nextRegionIndex,
    Operations.LookupRelevantSelectorActivationsExact.append,
    Operations.LookupRelevantSelectorActivationsExact.nil, true_and, and_true]
  exact
    ⟨synthPieces_inputSelectorsExact cfg hLR hLB hRB input i,
      synthChecks_inputSelectorsExact G R Q hQ cfg hLR hLB hRB input
        ((synthPieces cfg input).output i) (i + 27)
        ((synthPieces cfg input).nextRegionIndex i),
      synthGates_inputSelectorsExact cfg input
        ((synthPieces cfg input).output i)
        ((synthChecks G R Q hQ cfg input ((synthPieces cfg input).output i)
          (i + 27)).output ((synthPieces cfg input).nextRegionIndex i))
        (i + 27)
        ((synthChecks G R Q hQ cfg input ((synthPieces cfg input).output i)
          (i + 27)).nextRegionIndex
            ((synthPieces cfg input).nextRegionIndex i))⟩

private theorem witnessMessagePiece_noSimpleSelectors
    (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1)
    (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((Sinsemilla.HashToPoint.witnessMessagePiece cfg w).operations i) := by
  simp [Sinsemilla.HashToPoint.witnessMessagePiece,
    Operations.LookupInputsNoSimpleSelectors,
    RegionOperations.LookupInputsNoSimpleSelectors,
    Operation.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem synthPieces_noSimpleSelectors
    (cfg : Config)
    (hL : cfg.lookupConfig.qLookup.simple = false)
    (hR : cfg.lookupConfig.qRunning.simple = false)
    (input : Var Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((synthPieces cfg input).operations i) := by
  simp only [synthPieces, circuit_norm]
  repeat' apply And.intro
  all_goals first
    | apply witnessMessagePiece_noSimpleSelectors
    | (apply Zcash.Circuits.witnessShortCheck_noSimpleSelectors <;> assumption)

private theorem rangeCheckAtDecomposed_noSimpleSelectors
    (count : ℕ) (h13 : 13 ≤ count) (hpow : 10 * count ≤ 254)
    (cfg : LookupRangeCheck.Config 10)
    (hL : cfg.qLookup.simple = false)
    (hR : cfg.qRunning.simple = false)
    (input : Var unit Fp) (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      (((LookupRangeCheck.rangeCheckAtDecomposed count h13 hpow).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [LookupRangeCheck.rangeCheckAtDecomposed, circuit_norm]
  rw [List.forall_append]
  constructor
  · apply Zcash.Circuits.rangeCheckLoop_noSimpleSelectors <;> assumption
  · simp

private theorem witnessCheckDecomposed_noSimpleSelectors
    (cfg : LookupRangeCheck.Config 10)
    (hL : cfg.qLookup.simple = false)
    (hR : cfg.qRunning.simple = false)
    (w : WitgenIR Fp 1) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((LookupRangeCheck.witnessCheckDecomposed cfg w).operations i) := by
  apply (Operations.LookupInputsNoSimpleSelectors.region_singleton
    "Witness element" _).mpr
  change RegionOperations.LookupInputsNoSimpleSelectors
    (RegionOperation.assignAdvice cfg.runningSum 0 w ::
      ((LookupRangeCheck.rangeCheckAtDecomposed 25 (by norm_num)
        (by norm_num)).call cfg 0 ()).operations i)
  rw [show RegionOperations.LookupInputsNoSimpleSelectors
      (RegionOperation.assignAdvice cfg.runningSum 0 w ::
        ((LookupRangeCheck.rangeCheckAtDecomposed 25 (by norm_num)
          (by norm_num)).call cfg 0 ()).operations i) ↔
      RegionOperations.LookupInputsNoSimpleSelectors
        (((LookupRangeCheck.rangeCheckAtDecomposed 25 (by norm_num)
          (by norm_num)).call cfg 0 ()).operations i) by
    simp [RegionOperations.LookupInputsNoSimpleSelectors]]
  apply rangeCheckAtDecomposed_noSimpleSelectors <;> assumption

private theorem yGateChild_noSimpleSelectors
    (wlsb : WitgenIR Fp 1)
    (originalInput : NoteCommit.YCanonicityCheck.Inputs (AssignedCell Fp))
    (cfg : NoteCommit.YCanonicity.Config)
    (input : Var NoteCommit.YCanonicity.Row Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((NoteCommit.YCanonicityCheck.gateChild wlsb originalInput).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp [NoteCommit.YCanonicityCheck.gateChild,
    NoteCommit.YCanonicity.bundle, FormalRegionCircuit.toFormal,
    Operations.LookupInputsNoSimpleSelectors,
    RegionOperations.LookupInputsNoSimpleSelectors,
    Operation.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem yCircuit_noSimpleSelectors
    (wlsb : WitgenIR Fp 1)
    (cfg : NoteCommit.YCanonicity.Config × LookupRangeCheck.Config 10)
    (hL : cfg.2.qLookup.simple = false)
    (hR : cfg.2.qRunning.simple = false)
    (input : Var NoteCommit.YCanonicityCheck.Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((NoteCommit.YCanonicityCheck.circuit wlsb).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [NoteCommit.YCanonicityCheck.circuit,
    NoteCommit.YCanonicityCheck.synth, circuit_norm]
  repeat' apply And.intro
  · apply Zcash.Circuits.witnessShortCheck_noSimpleSelectors <;> assumption
  · apply Zcash.Circuits.witnessShortCheck_noSimpleSelectors <;> assumption
  · apply witnessCheckDecomposed_noSimpleSelectors <;> assumption
  · apply Action.commitIvkWitnessCheck_noSimpleSelectors <;> assumption
  · apply yGateChild_noSimpleSelectors

private theorem synthChecks_noSimpleSelectors
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config)
    (hL : cfg.lookupConfig.qLookup.simple = false)
    (hR : cfg.lookupConfig.qRunning.simple = false)
    (hS1 : cfg.hashConfig.qS1.simple = false)
    (input : Var Inputs Fp) (pcs : PieceCells)
    (iHash : RegionIndex) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((synthChecks G R Q hQ cfg input pcs iHash).operations i) := by
  simp only [synthChecks, circuit_norm]
  repeat' apply And.intro
  · apply yCircuit_noSimpleSelectors <;> assumption
  · apply yCircuit_noSimpleSelectors <;> assumption
  · apply Action.commitIvkCommitDomain_noSimpleSelectors
    exact hS1
  · apply Action.commitIvkWitnessCheck_noSimpleSelectors <;> assumption
  · apply Action.commitIvkWitnessCheck_noSimpleSelectors <;> assumption
  · apply Action.commitIvkWitnessCheck_noSimpleSelectors <;> assumption
  · apply Action.commitIvkWitnessCheck_noSimpleSelectors <;> assumption

private theorem toFormal_noSimpleSelectors
    {ConfigInput Config : Type} {Input Output : TypeMap}
    [ProvableType Input] [ProvableType Output]
    (bundle : FormalRegionCircuit Fp ConfigInput Config Input Output)
    (name : String) (cfg : Config) (input : Var Input Fp)
    (i : RegionIndex)
    (hlaw : RegionOperations.LookupInputsNoSimpleSelectors
      ((bundle.synthesize cfg 0 input).operations i)) :
    Operations.LookupInputsNoSimpleSelectors
      (((bundle.toFormal name).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  apply (Operations.LookupInputsNoSimpleSelectors.region_singleton name _).mpr
  simpa only [FormalRegionCircuit.toFormal, circuit_norm] using hlaw

private theorem decomposeB_noSimpleSelectors
    (w : WitgenIR Fp 1) (cfg : NoteCommit.DecomposeB.Config)
    (input : Var NoteCommit.DecomposeB.Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((((NoteCommit.DecomposeB.bundle w).toFormal
        "NoteCommit MessagePiece b").call cfg input).operations i) := by
  apply toFormal_noSimpleSelectors
  simp [NoteCommit.DecomposeB.bundle,
    RegionOperations.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem decomposeD_noSimpleSelectors
    (w : WitgenIR Fp 1) (cfg : NoteCommit.DecomposeD.Config)
    (input : Var NoteCommit.DecomposeD.Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((((NoteCommit.DecomposeD.bundle w).toFormal
        "NoteCommit MessagePiece d").call cfg input).operations i) := by
  apply toFormal_noSimpleSelectors
  simp [NoteCommit.DecomposeD.bundle,
    RegionOperations.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem decomposeE_noSimpleSelectors
    (cfg : NoteCommit.DecomposeE.Config)
    (input : Var NoteCommit.DecomposeE.Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((NoteCommit.DecomposeE.bundle.toFormal
        "NoteCommit MessagePiece e").call cfg input).operations i) := by
  apply toFormal_noSimpleSelectors
  simp [NoteCommit.DecomposeE.bundle,
    RegionOperations.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem decomposeG_noSimpleSelectors
    (w : WitgenIR Fp 1) (cfg : NoteCommit.DecomposeG.Config)
    (input : Var NoteCommit.DecomposeG.Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((((NoteCommit.DecomposeG.bundle w).toFormal
        "NoteCommit MessagePiece g").call cfg input).operations i) := by
  apply toFormal_noSimpleSelectors
  simp [NoteCommit.DecomposeG.bundle,
    RegionOperations.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem decomposeH_noSimpleSelectors
    (w : WitgenIR Fp 1) (cfg : NoteCommit.DecomposeH.Config)
    (input : Var NoteCommit.DecomposeH.Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((((NoteCommit.DecomposeH.bundle w).toFormal
        "NoteCommit MessagePiece h").call cfg input).operations i) := by
  apply toFormal_noSimpleSelectors
  simp [NoteCommit.DecomposeH.bundle,
    RegionOperations.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem gdCanonicity_noSimpleSelectors
    (cfg : NoteCommit.GdCanonicity.Config)
    (input : Var NoteCommit.GdCanonicity.Row Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((NoteCommit.GdCanonicity.bundle.toFormal
        "NoteCommit input g_d").call cfg input).operations i) := by
  apply toFormal_noSimpleSelectors
  simp [NoteCommit.GdCanonicity.bundle,
    RegionOperations.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem pkdCanonicity_noSimpleSelectors
    (cfg : NoteCommit.PkdCanonicity.Config)
    (input : Var NoteCommit.PkdCanonicity.Row Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((NoteCommit.PkdCanonicity.bundle.toFormal
        "NoteCommit input pk_d").call cfg input).operations i) := by
  apply toFormal_noSimpleSelectors
  simp [NoteCommit.PkdCanonicity.bundle,
    RegionOperations.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem valueCanonicity_noSimpleSelectors
    (cfg : NoteCommit.ValueCanonicity.Config)
    (input : Var NoteCommit.ValueCanonicity.Row Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((NoteCommit.ValueCanonicity.bundle.toFormal
        "NoteCommit input value").call cfg input).operations i) := by
  apply toFormal_noSimpleSelectors
  simp [NoteCommit.ValueCanonicity.bundle,
    RegionOperations.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem rhoCanonicity_noSimpleSelectors
    (cfg : NoteCommit.RhoCanonicity.Config)
    (input : Var NoteCommit.RhoCanonicity.Row Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((NoteCommit.RhoCanonicity.bundle.toFormal
        "NoteCommit input rho").call cfg input).operations i) := by
  apply toFormal_noSimpleSelectors
  simp [NoteCommit.RhoCanonicity.bundle,
    RegionOperations.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem psiCanonicity_noSimpleSelectors
    (cfg : NoteCommit.PsiCanonicity.Config)
    (input : Var NoteCommit.PsiCanonicity.Row Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((NoteCommit.PsiCanonicity.bundle.toFormal
        "NoteCommit input psi").call cfg input).operations i) := by
  apply toFormal_noSimpleSelectors
  simp [NoteCommit.PsiCanonicity.bundle,
    RegionOperations.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem synthGates_noSimpleSelectors
    (cfg : Config) (input : Var Inputs Fp) (pcs : PieceCells)
    (ccs : CheckCells) (iHash : RegionIndex) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((synthGates cfg input pcs ccs iHash).operations i) := by
  simp only [synthGates, circuit_norm]
  repeat' apply And.intro
  · apply decomposeB_noSimpleSelectors
  · apply decomposeD_noSimpleSelectors
  · apply decomposeE_noSimpleSelectors
  · apply decomposeG_noSimpleSelectors
  · apply decomposeH_noSimpleSelectors
  · apply gdCanonicity_noSimpleSelectors
  · apply pkdCanonicity_noSimpleSelectors
  · apply valueCanonicity_noSimpleSelectors
  · apply rhoCanonicity_noSimpleSelectors
  · apply psiCanonicity_noSimpleSelectors

theorem circuit_noSimpleSelectors
    (G : Generators) (R : FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : Config)
    (hL : cfg.lookupConfig.qLookup.simple = false)
    (hR : cfg.lookupConfig.qRunning.simple = false)
    (hS1 : cfg.hashConfig.qS1.simple = false)
    (input : Var Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((circuit G R Q hQ).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  change Operations.LookupInputsNoSimpleSelectors
    ((synth G R Q hQ cfg input).operations i)
  simp only [synth, Circuit.operations_bind, Circuit.operations_pure,
    currentRegion_operations, currentRegion_output,
    currentRegion_nextRegionIndex,
    Operations.LookupInputsNoSimpleSelectors.append,
    Operations.LookupInputsNoSimpleSelectors.nil, true_and, and_true]
  exact
    ⟨synthPieces_noSimpleSelectors cfg hL hR input i,
      synthChecks_noSimpleSelectors G R Q hQ cfg hL hR hS1 input
        ((synthPieces cfg input).output i) (i + 27)
        ((synthPieces cfg input).nextRegionIndex i),
      synthGates_noSimpleSelectors cfg input
        ((synthPieces cfg input).output i)
        ((synthChecks G R Q hQ cfg input ((synthPieces cfg input).output i)
          (i + 27)).output ((synthPieces cfg input).nextRegionIndex i))
        (i + 27)
        ((synthChecks G R Q hQ cfg input ((synthPieces cfg input).output i)
          (i + 27)).nextRegionIndex
            ((synthPieces cfg input).nextRegionIndex i))⟩

end Zcash.Circuits.NoteCommit.Main
