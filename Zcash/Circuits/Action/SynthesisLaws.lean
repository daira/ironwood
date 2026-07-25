import Clean.Halo2.TopLevel
import Zcash.Circuits.Action.Bundle

open Halo2

set_option maxHeartbeats 20000

attribute [circuit_norm]
  RegionCircuit.forRange'_forall
  RegionCircuit.forRangeVar'_forall

namespace Zcash.Circuits

private def RegionOperation.IsNotLookup : RegionOperation Fp → Prop
  | .enableLookup _ _ _ => False
  | _ => True

private irreducible_def RegionOperations.HaveNoLookups
    (body : RegionOperations Fp) : Prop :=
  body.Forall RegionOperation.IsNotLookup

private theorem RegionOperations.haveNoLookups_append
    (left right : RegionOperations Fp) :
    RegionOperations.HaveNoLookups (left ++ right) ↔
      RegionOperations.HaveNoLookups left ∧
        RegionOperations.HaveNoLookups right := by
  rw [RegionOperations.HaveNoLookups, RegionOperations.HaveNoLookups,
    RegionOperations.HaveNoLookups]
  simp

private theorem RegionOperations.forall_notLookup_of_haveNoLookups
    {body : RegionOperations Fp}
    (h : RegionOperations.HaveNoLookups body) :
    body.Forall RegionOperation.IsNotLookup := by
  rw [RegionOperations.HaveNoLookups] at h
  exact h

private theorem lookupExact_of_haveNoLookups
    {body : RegionOperations Fp} (h : RegionOperations.HaveNoLookups body) :
    body.LookupRelevantSelectorActivationsExact := by
  rw [RegionOperations.HaveNoLookups] at h
  simp only [RegionOperations.LookupRelevantSelectorActivationsExact,
    List.forall_iff_forall_mem]
  intro operation hoperation
  have hn := List.forall_iff_forall_mem.mp h operation hoperation
  cases operation <;> simp_all [RegionOperation.IsNotLookup]

private theorem lookupNoSimple_of_haveNoLookups
    {body : RegionOperations Fp} (h : RegionOperations.HaveNoLookups body) :
    body.LookupInputsNoSimpleSelectors := by
  rw [RegionOperations.HaveNoLookups] at h
  simp only [RegionOperations.LookupInputsNoSimpleSelectors,
    List.forall_iff_forall_mem]
  intro operation hoperation
  have hn := List.forall_iff_forall_mem.mp h operation hoperation
  cases operation <;> simp_all [RegionOperation.IsNotLookup]

private structure RegionOperations.LookupFreeCertificate
    (body : RegionOperations Fp) : Prop where
  exact : body.LookupRelevantSelectorActivationsExact
  noSimple : body.LookupInputsNoSimpleSelectors

private theorem RegionOperations.lookupFreeCertificate_of_haveNoLookups
    {body : RegionOperations Fp}
    (h : RegionOperations.HaveNoLookups body) :
    RegionOperations.LookupFreeCertificate body :=
  ⟨lookupExact_of_haveNoLookups h, lookupNoSimple_of_haveNoLookups h⟩

private theorem lookupExact_assignAdvice_cons
    (column : Column .advice) (row : ℕ) (witness : WitgenIR Fp 1)
    (body : RegionOperations Fp) :
    RegionOperations.LookupRelevantSelectorActivationsExact
        (RegionOperation.assignAdvice column row witness :: body) ↔
      body.LookupRelevantSelectorActivationsExact := by
  simp [RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt, RegionOperation.ActivatesSelectorAt]

private theorem shortRangeCheck_inputSelectorsExact
    (K n : ℕ) (cfg : LookupRangeCheck.Config K)
    (hLR : cfg.qLookup.index ≠ cfg.qRunning.index)
    (hLB : cfg.qLookup.index ≠ cfg.qBitshift.index)
    (hRB : cfg.qRunning.index ≠ cfg.qBitshift.index)
    (input : Var unit Fp) (i : RegionIndex) :
    RegionOperations.LookupRelevantSelectorActivationsExact
      (((LookupRangeCheck.shortRangeCheck K n).call cfg 0 input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [LookupRangeCheck.shortRangeCheck, LookupRangeCheck.rangeCheckLookup,
    LookupRangeCheck.bitshiftGate, circuit_norm]
  simp [hLR, Ne.symm hLB, Ne.symm hRB]

private theorem shortRangeCheck_noSimpleSelectors
    (K n : ℕ) (cfg : LookupRangeCheck.Config K)
    (hL : cfg.qLookup.simple = false)
    (hR : cfg.qRunning.simple = false)
    (input : Var unit Fp) (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      (((LookupRangeCheck.shortRangeCheck K n).call cfg 0 input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [LookupRangeCheck.shortRangeCheck, LookupRangeCheck.rangeCheckLookup,
    circuit_norm]
  simp [hL, hR]

theorem witnessShortCheck_inputSelectorsExact
    (K n : ℕ) (cfg : LookupRangeCheck.Config K)
    (hLR : cfg.qLookup.index ≠ cfg.qRunning.index)
    (hLB : cfg.qLookup.index ≠ cfg.qBitshift.index)
    (hRB : cfg.qRunning.index ≠ cfg.qBitshift.index)
    (w : WitgenIR Fp 1) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((LookupRangeCheck.witnessShortCheck K n cfg w).operations i) := by
  apply (Operations.LookupRelevantSelectorActivationsExact.region_singleton _ _).mpr
  simp only [List.singleton_append, List.append_nil]
  rw [lookupExact_assignAdvice_cons]
  exact shortRangeCheck_inputSelectorsExact K n cfg hLR hLB hRB () i

theorem witnessShortCheck_noSimpleSelectors
    (K n : ℕ) (cfg : LookupRangeCheck.Config K)
    (hL : cfg.qLookup.simple = false)
    (hR : cfg.qRunning.simple = false)
    (w : WitgenIR Fp 1) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((LookupRangeCheck.witnessShortCheck K n cfg w).operations i) := by
  apply (Operations.LookupInputsNoSimpleSelectors.region_singleton _ _).mpr
  simp only [circuit_norm]
  exact shortRangeCheck_noSimpleSelectors K n cfg hL hR () i

attribute [circuit_norm]
  witnessShortCheck_inputSelectorsExact
  witnessShortCheck_noSimpleSelectors

private theorem hashPieceRound_inputSelectorsEnabled
    (G : Specs.Sinsemilla.Generators) (r : ℕ)
    (cfg : Sinsemilla.HashPiece.Config)
    (piece : AssignedCell Fp) (offset : ℕ) (i : RegionIndex) :
    (((Sinsemilla.HashPiece.round G r).call cfg offset piece).operations i).Forall
      RegionOperation.LookupInputSelectorsEnabled := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.HashPiece.round, Sinsemilla.HashPiece.generatorLookup,
    Sinsemilla.HashPiece.qS3Expr, Sinsemilla.HashPiece.yPExpr,
    Sinsemilla.HashPiece.yAExpr, Sinsemilla.HashPiece.xRExpr, circuit_norm]
  simp

private theorem hashPieceRound_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators) (r : ℕ)
    (cfg : Sinsemilla.HashPiece.Config)
    (hcomplex : cfg.qS1.simple = false)
    (piece : AssignedCell Fp) (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      (((Sinsemilla.HashPiece.round G r).call cfg offset piece).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.HashPiece.round, Sinsemilla.HashPiece.generatorLookup,
    Sinsemilla.HashPiece.qS3Expr, Sinsemilla.HashPiece.yPExpr,
    Sinsemilla.HashPiece.yAExpr, Sinsemilla.HashPiece.xRExpr, circuit_norm]
  simp [hcomplex]

private theorem hashPieceLoop_inputSelectorsEnabled
    (G : Specs.Sinsemilla.Generators) (n : ℕ)
    (cfg : Sinsemilla.HashPiece.Config)
    (piece : AssignedCell Fp) (offset : ℕ) (i : RegionIndex) :
    (((Sinsemilla.HashPiece.loop G n).call cfg offset piece).operations i).Forall
      RegionOperation.LookupInputSelectorsEnabled := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.HashPiece.loop, circuit_norm]
  intro r
  exact hashPieceRound_inputSelectorsEnabled G r cfg piece _ i

private theorem hashPieceLoop_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators) (n : ℕ)
    (cfg : Sinsemilla.HashPiece.Config)
    (hcomplex : cfg.qS1.simple = false)
    (piece : AssignedCell Fp) (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      (((Sinsemilla.HashPiece.loop G n).call cfg offset piece).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.HashPiece.loop, circuit_norm]
  intro r
  exact hashPieceRound_noSimpleSelectors G r cfg hcomplex piece _ i

attribute [circuit_norm]
  hashPieceLoop_inputSelectorsEnabled
  hashPieceLoop_noSimpleSelectors

private theorem hashPieceCircuit_inputSelectorsEnabled
    (G : Specs.Sinsemilla.Generators) (w : ℕ) (final : Bool)
    (yaIn : Placed Environment Fp → Fp)
    (cfg : Sinsemilla.HashPiece.Config)
    (piece : AssignedCell Fp) (offset : ℕ) (i : RegionIndex) :
    (((Sinsemilla.HashPiece.circuit G w final yaIn).call
      cfg offset piece).operations i).Forall
        RegionOperation.LookupInputSelectorsEnabled := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.HashPiece.circuit,
    Sinsemilla.HashPiece.generatorLookup, Sinsemilla.HashPiece.qS3Expr,
    Sinsemilla.HashPiece.yPExpr, Sinsemilla.HashPiece.yAExpr,
    Sinsemilla.HashPiece.xRExpr, circuit_norm]
  rw [List.forall_append]
  constructor
  · exact hashPieceLoop_inputSelectorsEnabled G w cfg piece offset i
  · simp [RegionOperation.LookupInputSelectorsEnabled,
      Expression.selectorIndices, SelectorEnabledAtIndex]

private theorem hashPieceCircuit_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators) (w : ℕ) (final : Bool)
    (yaIn : Placed Environment Fp → Fp)
    (cfg : Sinsemilla.HashPiece.Config)
    (hcomplex : cfg.qS1.simple = false)
    (piece : AssignedCell Fp) (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      (((Sinsemilla.HashPiece.circuit G w final yaIn).call
        cfg offset piece).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.HashPiece.circuit,
    Sinsemilla.HashPiece.generatorLookup, Sinsemilla.HashPiece.qS3Expr,
    Sinsemilla.HashPiece.yPExpr, Sinsemilla.HashPiece.yAExpr,
    Sinsemilla.HashPiece.xRExpr, circuit_norm]
  rw [List.forall_append]
  constructor
  · exact hashPieceLoop_noSimpleSelectors G w cfg hcomplex piece offset i
  · simp [Expression.NoSimpleSelectors, hcomplex]

attribute [circuit_norm]
  hashPieceCircuit_inputSelectorsEnabled
  hashPieceCircuit_noSimpleSelectors

private theorem chainSlot_inputSelectorsEnabled
    (G : Specs.Sinsemilla.Generators) (ns : List ℕ)
    (yaIn : Placed Environment Fp → Fp) (j : ℕ)
    (cfg : Sinsemilla.HashPiece.Config)
    (piece : AssignedCell Fp) (offset : ℕ) (i : RegionIndex) :
  (((Sinsemilla.Chain.slot G ns yaIn j).call
      cfg offset piece).operations i).Forall
        RegionOperation.LookupInputSelectorsEnabled := by
  rw [FormalRegionCircuit.call_operations]
  rw [Sinsemilla.Chain.slot_synthesize_eq]
  simp only [Sinsemilla.Chain.slotSynthesize, circuit_norm]
  exact hashPieceCircuit_inputSelectorsEnabled G (ns.getD j 0)
    (decide (j = ns.length - 1)) _ cfg piece offset i

private theorem chainSlot_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators) (ns : List ℕ)
    (yaIn : Placed Environment Fp → Fp) (j : ℕ)
    (cfg : Sinsemilla.HashPiece.Config)
    (hcomplex : cfg.qS1.simple = false)
    (piece : AssignedCell Fp) (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      (((Sinsemilla.Chain.slot G ns yaIn j).call
        cfg offset piece).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  rw [Sinsemilla.Chain.slot_synthesize_eq]
  simp only [Sinsemilla.Chain.slotSynthesize, circuit_norm]
  exact hashPieceCircuit_noSimpleSelectors G (ns.getD j 0)
    (decide (j = ns.length - 1)) _ cfg hcomplex piece offset i

attribute [circuit_norm]
  chainSlot_inputSelectorsEnabled
  chainSlot_noSimpleSelectors

private theorem chainCircuit_inputSelectorsEnabled
    (G : Specs.Sinsemilla.Generators) (ns : List ℕ)
    (yaIn : Placed Environment Fp → Fp)
    (cfg : Sinsemilla.HashPiece.Config)
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (offset : ℕ) (i : RegionIndex) :
    (((Sinsemilla.Chain.circuit G ns yaIn).call
      cfg offset input).operations i).Forall
        RegionOperation.LookupInputSelectorsEnabled := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.Chain.circuit, circuit_norm]
  rw [List.forall_append]
  constructor
  · rw [RegionCircuit.forRangeVar'_forall]
    intro j
    simp only [circuit_norm]
    rw [List.forall_append]
    exact ⟨chainSlot_inputSelectorsEnabled G ns yaIn j cfg
      input.pieces[j]! _ i, by
        simp [RegionOperation.LookupInputSelectorsEnabled]⟩
  · simp [RegionOperation.LookupInputSelectorsEnabled]

private theorem chainCircuit_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators) (ns : List ℕ)
    (yaIn : Placed Environment Fp → Fp)
    (cfg : Sinsemilla.HashPiece.Config)
    (hcomplex : cfg.qS1.simple = false)
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      (((Sinsemilla.Chain.circuit G ns yaIn).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Sinsemilla.Chain.circuit, circuit_norm]
  rw [List.forall_append]
  constructor
  · rw [RegionCircuit.forRangeVar'_forall]
    intro j
    simp only [circuit_norm]
    rw [List.forall_append]
    exact ⟨chainSlot_noSimpleSelectors G ns yaIn j cfg hcomplex
      input.pieces[j]! _ i, by simp⟩
  · simp

attribute [circuit_norm]
  chainCircuit_inputSelectorsEnabled
  chainCircuit_noSimpleSelectors

theorem hashCircuit_inputSelectorsExact
    (G : Specs.Sinsemilla.Generators)
    (cfg : Sinsemilla.HashPiece.Config)
    (ns : List ℕ) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ [])
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((Sinsemilla.HashToPoint.hashCircuit G ns Q hQ hns).call
          cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  apply (Operations.LookupRelevantSelectorActivationsExact.region_singleton _ _).mpr
  apply RegionOperations.lookupRelevantSelectorActivationsExact_of_inputSelectorsEnabled
  simp only [RegionOperations.LookupInputSelectorsEnabled, circuit_norm]
  exact chainCircuit_inputSelectorsEnabled G ns (fun _ => Q.y)
    cfg input 0 i

theorem hashCircuit_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators)
    (cfg : Sinsemilla.HashPiece.Config)
    (hcomplex : cfg.qS1.simple = false)
    (ns : List ℕ) (Q : Point Fp) (hQ : Q.OnCurve)
    (hns : ns ≠ [])
    (input : Var (Sinsemilla.Chain.Inputs ns.length) Fp)
    (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((Sinsemilla.HashToPoint.hashCircuit G ns Q hQ hns).call
          cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  apply (Operations.LookupInputsNoSimpleSelectors.region_singleton _ _).mpr
  simp only [circuit_norm]
  exact chainCircuit_noSimpleSelectors G ns (fun _ => Q.y)
    cfg hcomplex input 0 i

attribute [circuit_norm]
  hashCircuit_inputSelectorsExact
  hashCircuit_noSimpleSelectors

private theorem merkleGate_inputSelectorsExact
    (l : Fp) (cfg : Sinsemilla.Merkle.Gate.Config)
    (input : Var Sinsemilla.Merkle.Gate.Inputs Fp)
    (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupRelevantSelectorActivationsExact
      (((Sinsemilla.Merkle.Gate.circuit l).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp [Sinsemilla.Merkle.Gate.circuit, Sinsemilla.Merkle.Gate.body,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt,
    RegionOperation.ActivatesSelectorAt, circuit_norm]

private theorem merkleGate_noSimpleSelectors
    (l : Fp) (cfg : Sinsemilla.Merkle.Gate.Config)
    (input : Var Sinsemilla.Merkle.Gate.Inputs Fp)
    (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      (((Sinsemilla.Merkle.Gate.circuit l).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp [Sinsemilla.Merkle.Gate.circuit, Sinsemilla.Merkle.Gate.body,
    RegionOperations.LookupInputsNoSimpleSelectors, circuit_norm]

attribute [circuit_norm]
  merkleGate_inputSelectorsExact
  merkleGate_noSimpleSelectors

private theorem hashLayer_inputSelectorsExact
    (G : Specs.Sinsemilla.Generators)
    (Q : Point Fp) (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (cfg : Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (hLR : cfg.2.qLookup.index ≠ cfg.2.qRunning.index)
    (hLB : cfg.2.qLookup.index ≠ cfg.2.qBitshift.index)
    (hRB : cfg.2.qRunning.index ≠ cfg.2.qBitshift.index)
    (input : Var Sinsemilla.Merkle.HashLayer.Input Fp)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((Sinsemilla.Merkle.HashLayer.circuit G Q hQ l hl).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Sinsemilla.Merkle.HashLayer.circuit,
    Sinsemilla.Merkle.HashLayer.synthesize, circuit_norm]
  repeat' apply And.intro
  all_goals first
    | apply witnessShortCheck_inputSelectorsExact <;> assumption
    | apply hashCircuit_inputSelectorsExact
    | apply merkleGate_inputSelectorsExact
    | simp [Sinsemilla.HashToPoint.witnessMessagePiece,
        Operations.LookupRelevantSelectorActivationsExact,
        RegionOperations.LookupRelevantSelectorActivationsExact,
        Operation.LookupRelevantSelectorActivationsExact,
        circuit_norm]

private theorem hashLayer_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators)
    (Q : Point Fp) (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (cfg : Sinsemilla.Merkle.Config × LookupRangeCheck.Config 10)
    (hL : cfg.2.qLookup.simple = false)
    (hR : cfg.2.qRunning.simple = false)
    (hS : cfg.1.sinsemilla.qS1.simple = false)
    (input : Var Sinsemilla.Merkle.HashLayer.Input Fp)
    (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((Sinsemilla.Merkle.HashLayer.circuit G Q hQ l hl).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Sinsemilla.Merkle.HashLayer.circuit,
    Sinsemilla.Merkle.HashLayer.synthesize, circuit_norm]
  repeat' apply And.intro
  all_goals first
    | apply witnessShortCheck_noSimpleSelectors <;> assumption
    | apply hashCircuit_noSimpleSelectors <;> assumption
    | apply merkleGate_noSimpleSelectors
    | simp [Sinsemilla.HashToPoint.witnessMessagePiece,
        Operations.LookupInputsNoSimpleSelectors,
        RegionOperations.LookupInputsNoSimpleSelectors,
        Operation.LookupInputsNoSimpleSelectors,
        circuit_norm]

attribute [circuit_norm]
  hashLayer_inputSelectorsExact
  hashLayer_noSimpleSelectors

private theorem condSwap_inputSelectorsExact
    (wsib : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config) (input : Var CondSwap.Input Fp)
    (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupRelevantSelectorActivationsExact
      (((CondSwap.swap wsib wswap).call cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp [CondSwap.swap, RegionOperations.LookupRelevantSelectorActivationsExact,
    RegionOperations.SelectorActivatedAt,
    RegionOperation.ActivatesSelectorAt, circuit_norm]

private theorem condSwap_noSimpleSelectors
    (wsib : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config) (input : Var CondSwap.Input Fp)
    (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      (((CondSwap.swap wsib wswap).call cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp [CondSwap.swap, RegionOperations.LookupInputsNoSimpleSelectors,
    circuit_norm]

attribute [circuit_norm]
  condSwap_inputSelectorsExact
  condSwap_noSimpleSelectors

private theorem layer_inputSelectorsExact
    (G : Specs.Sinsemilla.Generators)
    (Q : Point Fp) (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (wsib : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config × Sinsemilla.Merkle.Config ×
      LookupRangeCheck.Config 10)
    (hLR : cfg.2.2.qLookup.index ≠ cfg.2.2.qRunning.index)
    (hLB : cfg.2.2.qLookup.index ≠ cfg.2.2.qBitshift.index)
    (hRB : cfg.2.2.qRunning.index ≠ cfg.2.2.qBitshift.index)
    (input : Var Sinsemilla.Merkle.Layer.Input Fp)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((Sinsemilla.Merkle.Layer.circuit G Q hQ l hl wsib wswap).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Sinsemilla.Merkle.Layer.circuit, circuit_norm]
  constructor
  · apply (Operations.LookupRelevantSelectorActivationsExact.region_singleton "swap" _).mpr
    apply condSwap_inputSelectorsExact
  · exact hashLayer_inputSelectorsExact G Q hQ l hl
      (cfg.2.1, cfg.2.2) hLR hLB hRB _ _

private theorem layer_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators)
    (Q : Point Fp) (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (wsib : WitgenIR Fp 1)
    (wswap : Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config × Sinsemilla.Merkle.Config ×
      LookupRangeCheck.Config 10)
    (hL : cfg.2.2.qLookup.simple = false)
    (hR : cfg.2.2.qRunning.simple = false)
    (hS : cfg.2.1.sinsemilla.qS1.simple = false)
    (input : Var Sinsemilla.Merkle.Layer.Input Fp)
    (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((Sinsemilla.Merkle.Layer.circuit G Q hQ l hl wsib wswap).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Sinsemilla.Merkle.Layer.circuit, circuit_norm]
  constructor
  · apply (Operations.LookupInputsNoSimpleSelectors.region_singleton "swap" _).mpr
    apply condSwap_noSimpleSelectors
  · exact hashLayer_noSimpleSelectors G Q hQ l hl
      (cfg.2.1, cfg.2.2) hL hR hS _ _

attribute [circuit_norm]
  layer_inputSelectorsExact
  layer_noSimpleSelectors

private theorem calculateRoot_inputSelectorsExact
    (G : Specs.Sinsemilla.Generators)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (l₀ d : ℕ) (hld : l₀ + d ≤ 2 ^ 10)
    (wsib : ℕ → WitgenIR Fp 1)
    (wswap : ℕ → Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config × Sinsemilla.Merkle.Config ×
      LookupRangeCheck.Config 10)
    (hLR : cfg.2.2.qLookup.index ≠ cfg.2.2.qRunning.index)
    (hLB : cfg.2.2.qLookup.index ≠ cfg.2.2.qBitshift.index)
    (hRB : cfg.2.2.qRunning.index ≠ cfg.2.2.qBitshift.index)
    (input : Var Sinsemilla.Merkle.Layer.Input Fp)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((Sinsemilla.Merkle.CalculateRoot.circuit
        G Q hQ l₀ d hld wsib wswap).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations,
    Sinsemilla.Merkle.CalculateRoot.circuit_synthesize_operations]
  apply FormalCircuit.foldCall_lookupRelevantSelectorActivationsExact_of_forall
  intro j roundInput roundIndex
  apply layer_inputSelectorsExact G Q hQ
    ((l₀ + j) % 2 ^ 10) (Nat.mod_lt _ (by norm_num))
    (wsib j) (wswap j) cfg hLR hLB hRB roundInput roundIndex

private theorem calculateRoot_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators)
    (Q : Point Fp) (hQ : Q.OnCurve)
    (l₀ d : ℕ) (hld : l₀ + d ≤ 2 ^ 10)
    (wsib : ℕ → WitgenIR Fp 1)
    (wswap : ℕ → Placed ProverEnvironment Fp → Bool)
    (cfg : CondSwap.Config × Sinsemilla.Merkle.Config ×
      LookupRangeCheck.Config 10)
    (hL : cfg.2.2.qLookup.simple = false)
    (hR : cfg.2.2.qRunning.simple = false)
    (hS : cfg.2.1.sinsemilla.qS1.simple = false)
    (input : Var Sinsemilla.Merkle.Layer.Input Fp)
    (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((Sinsemilla.Merkle.CalculateRoot.circuit
        G Q hQ l₀ d hld wsib wswap).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations,
    Sinsemilla.Merkle.CalculateRoot.circuit_synthesize_operations]
  apply FormalCircuit.foldCall_lookupInputsNoSimpleSelectors_of_forall
  intro j roundInput roundIndex
  apply layer_noSimpleSelectors G Q hQ
    ((l₀ + j) % 2 ^ 10) (Nat.mod_lt _ (by norm_num))
    (wsib j) (wswap j) cfg hL hR hS roundInput roundIndex

attribute [circuit_norm]
  calculateRoot_inputSelectorsExact
  calculateRoot_noSimpleSelectors

private theorem rangeCheckRound_inputSelectorsEnabled
    (K : ℕ) (cfg : LookupRangeCheck.Config K)
    (element : AssignedCell Fp) (idx row : ℕ) (i : RegionIndex) :
    ((LookupRangeCheck.rangeCheckRound K cfg element idx row).operations i).Forall
      RegionOperation.LookupInputSelectorsEnabled := by
  simp only [LookupRangeCheck.rangeCheckRound,
    LookupRangeCheck.rangeCheckLookup, circuit_norm]
  simp

private theorem rangeCheckRound_noSimpleSelectors
    (K : ℕ) (cfg : LookupRangeCheck.Config K)
    (hL : cfg.qLookup.simple = false)
    (hR : cfg.qRunning.simple = false)
    (element : AssignedCell Fp) (idx row : ℕ) (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      ((LookupRangeCheck.rangeCheckRound K cfg element idx row).operations i) := by
  simp only [LookupRangeCheck.rangeCheckRound,
    LookupRangeCheck.rangeCheckLookup, circuit_norm]
  simp [hL, hR]

theorem rangeCheckLoop_inputSelectorsEnabled
    (K : ℕ) (cfg : LookupRangeCheck.Config K)
    (element : AssignedCell Fp) (offset count : ℕ) (i : RegionIndex) :
    ((LookupRangeCheck.rangeCheckLoop K cfg element offset count).operations i).Forall
      RegionOperation.LookupInputSelectorsEnabled := by
  unfold LookupRangeCheck.rangeCheckLoop
  rw [RegionCircuit.forRange'_forall]
  intro j
  apply rangeCheckRound_inputSelectorsEnabled

theorem rangeCheckLoop_noSimpleSelectors
    (K : ℕ) (cfg : LookupRangeCheck.Config K)
    (hL : cfg.qLookup.simple = false)
    (hR : cfg.qRunning.simple = false)
    (element : AssignedCell Fp) (offset count : ℕ) (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      ((LookupRangeCheck.rangeCheckLoop K cfg element offset count).operations i) := by
  unfold LookupRangeCheck.rangeCheckLoop
  unfold RegionOperations.LookupInputsNoSimpleSelectors
  rw [RegionCircuit.forRange'_forall]
  intro j
  apply rangeCheckRound_noSimpleSelectors <;> assumption

attribute [circuit_norm]
  rangeCheckLoop_inputSelectorsEnabled
  rangeCheckLoop_noSimpleSelectors

theorem rangeCheckAt_inputSelectorsExact
    (K count : ℕ) (strict : Bool)
    (cfg : LookupRangeCheck.Config K)
    (input : Var unit Fp) (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupRelevantSelectorActivationsExact
      (((LookupRangeCheck.rangeCheckAt K count strict).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  apply RegionOperations.lookupRelevantSelectorActivationsExact_of_inputSelectorsEnabled
  cases strict with
  | false =>
      simp only [LookupRangeCheck.rangeCheckAt, circuit_norm,
        Bool.false_eq_true, if_false]
      exact rangeCheckLoop_inputSelectorsEnabled K cfg
        (AssignedCell.of i offset cfg.runningSum) offset count i
  | true =>
      simp only [LookupRangeCheck.rangeCheckAt, circuit_norm, if_true]
      unfold RegionOperations.LookupInputSelectorsEnabled
      rw [List.forall_append]
      exact ⟨rangeCheckLoop_inputSelectorsEnabled K cfg
        (AssignedCell.of i offset cfg.runningSum) offset count i, by
          simp [RegionOperation.LookupInputSelectorsEnabled]⟩

theorem rangeCheckAt_noSimpleSelectors
    (K count : ℕ) (strict : Bool)
    (cfg : LookupRangeCheck.Config K)
    (hL : cfg.qLookup.simple = false)
    (hR : cfg.qRunning.simple = false)
    (input : Var unit Fp) (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      (((LookupRangeCheck.rangeCheckAt K count strict).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  cases strict with
  | false =>
      simp only [LookupRangeCheck.rangeCheckAt, circuit_norm,
        Bool.false_eq_true, if_false]
      exact rangeCheckLoop_noSimpleSelectors K cfg hL hR
        (AssignedCell.of i offset cfg.runningSum) offset count i
  | true =>
      simp only [LookupRangeCheck.rangeCheckAt, circuit_norm, if_true]
      rw [List.forall_append]
      exact ⟨rangeCheckLoop_noSimpleSelectors K cfg hL hR
        (AssignedCell.of i offset cfg.runningSum) offset count i, by simp⟩

attribute [circuit_norm]
  rangeCheckAt_inputSelectorsExact
  rangeCheckAt_noSimpleSelectors

private theorem rangeCheck_inputSelectorsExact
    (K count : ℕ) (strict : Bool)
    (cfg : LookupRangeCheck.Config K)
    (input : Var LookupRangeCheck.Inputs Fp) (offset : ℕ)
    (i : RegionIndex) :
    RegionOperations.LookupRelevantSelectorActivationsExact
      (((LookupRangeCheck.rangeCheck K count strict).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  apply
    RegionOperations.lookupRelevantSelectorActivationsExact_of_inputSelectorsEnabled
  unfold RegionOperations.LookupInputSelectorsEnabled
  cases strict with
  | false =>
      simp only [LookupRangeCheck.rangeCheck, circuit_norm,
        Bool.false_eq_true, if_false, List.forall_cons]
  | true =>
      simp only [LookupRangeCheck.rangeCheck, circuit_norm, if_true,
        List.forall_cons, List.forall_append]

private theorem rangeCheck_noSimpleSelectors
    (K count : ℕ) (strict : Bool)
    (cfg : LookupRangeCheck.Config K)
    (hL : cfg.qLookup.simple = false)
    (hR : cfg.qRunning.simple = false)
    (input : Var LookupRangeCheck.Inputs Fp) (offset : ℕ)
    (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      (((LookupRangeCheck.rangeCheck K count strict).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  unfold RegionOperations.LookupInputsNoSimpleSelectors
  cases strict with
  | false =>
      simp only [LookupRangeCheck.rangeCheck, circuit_norm,
        Bool.false_eq_true, if_false, List.forall_cons, true_and]
      exact rangeCheckLoop_noSimpleSelectors K cfg hL hR
        input.element offset count i
  | true =>
      simp only [LookupRangeCheck.rangeCheck, circuit_norm, if_true,
        List.forall_cons, List.forall_append, true_and]
      exact rangeCheckLoop_noSimpleSelectors K cfg hL hR
        input.element offset count i

private theorem copyCheck_inputSelectorsExact
    (K count : ℕ) (strict : Bool)
    (cfg : LookupRangeCheck.Config K)
    (input : Var LookupRangeCheck.Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((LookupRangeCheck.copyCheck K count strict).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [LookupRangeCheck.copyCheck, FormalRegionCircuit.toFormal, circuit_norm]
  have h := rangeCheck_inputSelectorsExact K count strict cfg input 0 i
  rw [FormalRegionCircuit.call_operations] at h
  exact h

private theorem copyCheck_noSimpleSelectors
    (K count : ℕ) (strict : Bool)
    (cfg : LookupRangeCheck.Config K)
    (hL : cfg.qLookup.simple = false)
    (hR : cfg.qRunning.simple = false)
    (input : Var LookupRangeCheck.Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((LookupRangeCheck.copyCheck K count strict).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [LookupRangeCheck.copyCheck, FormalRegionCircuit.toFormal, circuit_norm]
  have h := rangeCheck_noSimpleSelectors K count strict cfg hL hR input 0 i
  rw [FormalRegionCircuit.call_operations] at h
  exact h

attribute [circuit_norm]
  copyCheck_inputSelectorsExact
  copyCheck_noSimpleSelectors

private theorem mulOverflowCircuit_inputSelectorsExact
    (K : ℕ) (hKW : K * Ecc.MulOverflow.numWords K = 130)
    (cfg : Ecc.MulOverflow.Config K)
    (input : Var Ecc.MulOverflow.Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((Ecc.MulOverflow.circuit K hKW).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp [Ecc.MulOverflow.circuit, Ecc.MulOverflow.synthesize,
    Ecc.MulOverflow.gateRegion, circuit_norm]
  apply copyCheck_inputSelectorsExact

private theorem mulOverflowCircuit_noSimpleSelectors
    (K : ℕ) (hKW : K * Ecc.MulOverflow.numWords K = 130)
    (cfg : Ecc.MulOverflow.Config K)
    (hL : cfg.lookupConfig.qLookup.simple = false)
    (hR : cfg.lookupConfig.qRunning.simple = false)
    (input : Var Ecc.MulOverflow.Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((Ecc.MulOverflow.circuit K hKW).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp [Ecc.MulOverflow.circuit, Ecc.MulOverflow.synthesize,
    Ecc.MulOverflow.gateRegion, circuit_norm]
  apply copyCheck_noSimpleSelectors <;> assumption

attribute [circuit_norm]
  mulOverflowCircuit_inputSelectorsExact
  mulOverflowCircuit_noSimpleSelectors

private theorem mulIncompleteRound_haveNoLookups
    (r : ℕ) (cfg : Ecc.MulIncomplete.Config)
    (input : Var (Unconstrained field) Fp) (offset : ℕ)
    (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      (((Ecc.MulIncomplete.round r).call cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations, RegionOperations.HaveNoLookups]
  simp [Ecc.MulIncomplete.round, RegionOperation.IsNotLookup, circuit_norm]

private theorem mulIncompleteLoop_haveNoLookups
    (n w : ℕ) (cfg : Ecc.MulIncomplete.Config)
    (input : Var (Unconstrained field) Fp) (offset : ℕ)
    (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      (((Ecc.MulIncomplete.loop n w).call cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations, RegionOperations.HaveNoLookups]
  simp only [Ecc.MulIncomplete.loop, circuit_norm]
  intro r
  exact RegionOperations.forall_notLookup_of_haveNoLookups
    (mulIncompleteRound_haveNoLookups (w + r) cfg input _ i)

attribute [circuit_norm]
  mulIncompleteRound_haveNoLookups
  mulIncompleteLoop_haveNoLookups

private theorem mulIncompleteDoubleAndAdd_haveNoLookups
    (n w : ℕ) (cfg : Ecc.MulIncomplete.Config)
    (input : Var Ecc.MulIncomplete.Inputs Fp) (offset : ℕ)
    (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      (((Ecc.MulIncomplete.double_and_add n w).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations, RegionOperations.HaveNoLookups]
  simp [Ecc.MulIncomplete.double_and_add,
    RegionOperation.IsNotLookup, circuit_norm]
  exact RegionOperations.forall_notLookup_of_haveNoLookups
    (mulIncompleteLoop_haveNoLookups n w cfg input.alpha offset i)

private theorem eccAdd_haveNoLookups
    (cfg : Ecc.Add.Config) (offset : ℕ)
    (input : Var Ecc.Add.Inputs Fp) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.Add.add.call cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations, RegionOperations.HaveNoLookups]
  simp [Ecc.Add.add, RegionOperation.IsNotLookup, circuit_norm]

private theorem mulCompleteRound_haveNoLookups
    (w r : ℕ) (cfg : Ecc.MulComplete.Config)
    (input : Var Ecc.MulComplete.RoundInputs Fp) (offset : ℕ)
    (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      (((Ecc.MulComplete.round w r).call cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations, RegionOperations.HaveNoLookups]
  simp [Ecc.MulComplete.round, RegionOperation.IsNotLookup, circuit_norm]
  exact
    ⟨RegionOperations.forall_notLookup_of_haveNoLookups
        (eccAdd_haveNoLookups cfg.addConfig offset
          { p := { x := input.base.x,
                   y := AssignedCell.of i offset cfg.addConfig.yP },
            q := input.acc } i),
      RegionOperations.forall_notLookup_of_haveNoLookups
        (eccAdd_haveNoLookups cfg.addConfig (offset + 1)
          { p := input.acc,
            q := Ecc.Add.add.output cfg.addConfig offset
              { p := { x := input.base.x,
                       y := AssignedCell.of i offset cfg.addConfig.yP },
                q := input.acc } i } i)⟩

attribute [circuit_norm]
  mulCompleteRound_haveNoLookups

private theorem mulCompleteAssign3_haveNoLookups
    (w : ℕ) (cfg : Ecc.MulComplete.Config)
    (input : Var Ecc.MulComplete.Inputs Fp) (offset : ℕ)
    (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      (((Ecc.MulComplete.assign_region 3 w).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations, RegionOperations.HaveNoLookups]
  simp [Ecc.MulComplete.assign_region, RegionCircuit.foldRange,
    RegionCircuit.foldRangeVar, RegionCircuit.foldRangeVarAux, circuit_norm]
  constructor
  · simp [Ecc.MulComplete.startCopy, RegionOperation.IsNotLookup, circuit_norm]
  · repeat' apply And.intro
    all_goals
      apply RegionOperations.forall_notLookup_of_haveNoLookups
      apply mulCompleteRound_haveNoLookups

attribute [circuit_norm]
  eccAdd_haveNoLookups
  mulIncompleteDoubleAndAdd_haveNoLookups
  mulCompleteAssign3_haveNoLookups

private theorem mulMainCircuit_haveNoLookups
    (cfg : Ecc.Mul.Config) (input : Var Ecc.Mul.Inputs Fp)
    (offset : ℕ) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.Mul.mainCircuit.call cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations, RegionOperations.HaveNoLookups]
  simp [Ecc.Mul.mainCircuit, RegionOperation.IsNotLookup, circuit_norm]
  repeat' apply And.intro
  all_goals
    apply RegionOperations.forall_notLookup_of_haveNoLookups
    first
      | apply eccAdd_haveNoLookups
      | apply mulIncompleteDoubleAndAdd_haveNoLookups
      | apply mulCompleteAssign3_haveNoLookups

private theorem mulCircuit_inputSelectorsExact
    (cfg : Ecc.Mul.Config) (input : Var Ecc.Mul.Inputs Fp)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((Ecc.Mul.mul.call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Ecc.Mul.mul, Ecc.Mul.synthesize, circuit_norm]
  constructor
  · rw [FormalCircuit.call_operations]
    simp only [FormalRegionCircuit.toFormal, circuit_norm]
    have h := mulMainCircuit_haveNoLookups cfg input 0 i
    rw [FormalRegionCircuit.call_operations] at h
    exact lookupExact_of_haveNoLookups h
  · apply mulOverflowCircuit_inputSelectorsExact

private theorem mulCircuit_noSimpleSelectors
    (cfg : Ecc.Mul.Config)
    (hL : cfg.overflowConfig.lookupConfig.qLookup.simple = false)
    (hR : cfg.overflowConfig.lookupConfig.qRunning.simple = false)
    (input : Var Ecc.Mul.Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((Ecc.Mul.mul.call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Ecc.Mul.mul, Ecc.Mul.synthesize, circuit_norm]
  constructor
  · rw [FormalCircuit.call_operations]
    simp only [FormalRegionCircuit.toFormal, circuit_norm]
    have h := mulMainCircuit_haveNoLookups cfg input 0 i
    rw [FormalRegionCircuit.call_operations] at h
    exact lookupNoSimple_of_haveNoLookups h
  · apply mulOverflowCircuit_noSimpleSelectors <;> assumption

attribute [circuit_norm]
  mulCircuit_inputSelectorsExact
  mulCircuit_noSimpleSelectors

namespace Action

open Circuit

private theorem actionCircuit_synthesize_eq
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (cfg : Circuit.Config) :
    (circuit G B).synthesize cfg = mainPost G B cfg :=
  rfl

private theorem actionCircuit_configure_eq
    (G : Specs.Sinsemilla.Generators) (B : Bases) :
    (circuit G B).configure = fun _ => configure G :=
  rfl

theorem synthWitness_inputSelectorsExact
    (G : Specs.Sinsemilla.Generators) (W : Witnesses Fp)
    (cfg : Circuit.Config) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((synthWitness G W cfg).operations i) := by
  simp only [synthWitness, circuit_norm]
  repeat rw [FormalCircuit.call_operations]
  simp [Sinsemilla.load, loadPrivate,
    Ecc.WitnessPoint.pointFormal, Ecc.WitnessPoint.pointNonIdFormal,
    Ecc.WitnessPoint.point, Ecc.WitnessPoint.pointNonId,
    FormalRegionCircuit.toFormal, circuit_norm]

theorem synthWitness_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators) (W : Witnesses Fp)
    (cfg : Circuit.Config) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((synthWitness G W cfg).operations i) := by
  simp only [synthWitness, circuit_norm]
  repeat rw [FormalCircuit.call_operations]
  simp [Sinsemilla.load, loadPrivate,
    Ecc.WitnessPoint.pointFormal, Ecc.WitnessPoint.pointNonIdFormal,
    Ecc.WitnessPoint.point, Ecc.WitnessPoint.pointNonId,
    FormalRegionCircuit.toFormal, circuit_norm]

attribute [circuit_norm]
  synthWitness_inputSelectorsExact
  synthWitness_noSimpleSelectors

private theorem copyDecompose_haveNoLookups
    (W numWindows : ℕ) (cfg : DecomposeRunningSum.Config)
    (input : Var DecomposeRunningSum.Inputs Fp)
    (offset : ℕ) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      (((DecomposeRunningSum.copyDecompose W numWindows).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  rw [RegionOperations.HaveNoLookups]
  simp [DecomposeRunningSum.copyDecompose,
    DecomposeRunningSum.enableLoop, DecomposeRunningSum.assignLoop,
    RegionOperation.IsNotLookup, circuit_norm]

attribute [circuit_norm] copyDecompose_haveNoLookups

private theorem addIncomplete_haveNoLookups
    (cfg : Ecc.AddIncomplete.Config) (offset : ℕ)
    (input : Var Ecc.AddIncomplete.Inputs Fp) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.AddIncomplete.add.call cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  rw [RegionOperations.HaveNoLookups]
  simp [Ecc.AddIncomplete.add, RegionOperation.IsNotLookup, circuit_norm]

private theorem add_haveNoLookups
    (cfg : Ecc.Add.Config) (offset : ℕ)
    (input : Var Ecc.Add.Inputs Fp) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.Add.add.call cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  rw [RegionOperations.HaveNoLookups]
  simp [Ecc.Add.add, RegionOperation.IsNotLookup, circuit_norm]

attribute [circuit_norm]
  addIncomplete_haveNoLookups
  add_haveNoLookups

private theorem fixedConstantsLoop_haveNoLookups
    (toggle : Gate Fp) (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.Config) (offset numWindows : ℕ)
    (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.MulFixed.fixedConstantsLoop toggle B cfg
        offset numWindows).operations i) := by
  rw [RegionOperations.HaveNoLookups]
  simp only [Ecc.MulFixed.fixedConstantsLoop, circuit_norm]
  intro j
  simp [Ecc.MulFixed.fixedConstantsWindow,
    RegionOperation.IsNotLookup, circuit_norm]

private theorem windowChain_haveNoLookups
    (cfg : Ecc.MulFixed.Config)
    (processW : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp)))
    (offset numWindows : ℕ) (i : RegionIndex)
    (hprocess : ∀ w row,
      RegionOperations.HaveNoLookups ((processW w row).operations i)) :
    RegionOperations.HaveNoLookups
      ((Ecc.MulFixed.windowChain cfg processW offset numWindows).operations i) := by
  rw [RegionOperations.HaveNoLookups]
  simp [Ecc.MulFixed.windowChain, circuit_norm]
  refine
    ⟨RegionOperations.forall_notLookup_of_haveNoLookups (hprocess 0 offset),
      RegionOperations.forall_notLookup_of_haveNoLookups
        (hprocess 1 (offset + 1)),
      RegionOperations.forall_notLookup_of_haveNoLookups
        (addIncomplete_haveNoLookups _ _ _ _), ?_,
      RegionOperations.forall_notLookup_of_haveNoLookups
        (hprocess (numWindows - 1) _)⟩
  intro j
  exact
    ⟨RegionOperations.forall_notLookup_of_haveNoLookups
        (hprocess (j + 2) _),
      RegionOperations.forall_notLookup_of_haveNoLookups
        (addIncomplete_haveNoLookups _ _ _ _)⟩

private theorem shortInnerRegion_operations
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.Short.Config) (offset : ℕ)
    (magnitude : AssignedCell Fp) (i : RegionIndex) :
    (Ecc.MulFixed.Short.innerRegion B cfg offset magnitude).operations i =
      ((DecomposeRunningSum.copyDecompose 3 22).call
          cfg.superConfig.runningSumConfig offset
          { alpha := magnitude }).operations i ++
        (Ecc.MulFixed.fixedConstantsLoop
          (Ecc.MulFixed.coordsGate cfg.superConfig) B cfg.superConfig
          offset 22).operations i ++
        (Ecc.MulFixed.windowChain cfg.superConfig
          (Ecc.MulFixed.processWindow B
            (Ecc.MulFixed.Short.windowPoint B.point) cfg.superConfig magnitude)
          offset 22).operations i := by
  simp only [Ecc.MulFixed.Short.innerRegion, circuit_norm]

private theorem shortWindowChain_haveNoLookups
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.Short.Config) (offset : ℕ)
    (magnitude : AssignedCell Fp) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.MulFixed.windowChain cfg.superConfig
        (Ecc.MulFixed.processWindow B
          (Ecc.MulFixed.Short.windowPoint B.point) cfg.superConfig magnitude)
        offset 22).operations i) := by
  exact windowChain_haveNoLookups cfg.superConfig
    (Ecc.MulFixed.processWindow B
      (Ecc.MulFixed.Short.windowPoint B.point) cfg.superConfig magnitude)
    offset 22 i (by
      intro w row
      rw [RegionOperations.HaveNoLookups]
      simp [Ecc.MulFixed.processWindow, RegionOperation.IsNotLookup, circuit_norm])

private theorem shortFixedConstants_haveNoLookups
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.Short.Config) (offset : ℕ)
    (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.MulFixed.fixedConstantsLoop
        (Ecc.MulFixed.coordsGate cfg.superConfig) B cfg.superConfig
        offset 22).operations i) :=
  fixedConstantsLoop_haveNoLookups
    (Ecc.MulFixed.coordsGate cfg.superConfig) B cfg.superConfig offset 22 i

private theorem shortInnerRegion_haveNoLookups
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.Short.Config) (offset : ℕ)
    (magnitude : AssignedCell Fp) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.MulFixed.Short.innerRegion B cfg offset magnitude).operations i) := by
  rw [shortInnerRegion_operations]
  rw [RegionOperations.haveNoLookups_append,
    RegionOperations.haveNoLookups_append]
  exact
    ⟨⟨copyDecompose_haveNoLookups 3 22 cfg.superConfig.runningSumConfig
        { alpha := magnitude } offset i,
      shortFixedConstants_haveNoLookups B cfg offset i⟩,
    shortWindowChain_haveNoLookups B cfg offset magnitude i⟩

private theorem shortMswRegion_haveNoLookups
    (cfg : Ecc.MulFixed.Short.Config)
    (acc mulB : Point (AssignedCell Fp))
    (sign z21 : AssignedCell Fp) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.MulFixed.Short.mswRegion cfg acc mulB sign z21).operations i) := by
  rw [RegionOperations.HaveNoLookups]
  simp [Ecc.MulFixed.Short.mswRegion, RegionOperation.IsNotLookup, circuit_norm]
  exact RegionOperations.forall_notLookup_of_haveNoLookups
    (add_haveNoLookups _ _ _ _)

private theorem shortCircuit_inputSelectorsExact
    (B : Ecc.MulFixed.Short.FixedBase)
    (cfg : Ecc.MulFixed.Short.Config)
    (input : Var (Ecc.MulFixed.Short.Inputs) Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((Ecc.MulFixed.Short.circuit B).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Ecc.MulFixed.Short.circuit, Ecc.MulFixed.Short.synthesize,
    circuit_norm]
  constructor
  · exact lookupExact_of_haveNoLookups
      (shortInnerRegion_haveNoLookups B.toData cfg 0 input.magnitude i)
  · exact lookupExact_of_haveNoLookups
      (shortMswRegion_haveNoLookups cfg
        ((Ecc.MulFixed.Short.innerRegion B.toData cfg 0 input.magnitude).output i).acc
        ((Ecc.MulFixed.Short.innerRegion B.toData cfg 0 input.magnitude).output i).mulB
        input.sign
        ((Ecc.MulFixed.Short.innerRegion B.toData cfg 0 input.magnitude).output i).zs[21]
        (i + 1))

private theorem shortCircuit_noSimpleSelectors
    (B : Ecc.MulFixed.Short.FixedBase)
    (cfg : Ecc.MulFixed.Short.Config)
    (input : Var (Ecc.MulFixed.Short.Inputs) Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((Ecc.MulFixed.Short.circuit B).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Ecc.MulFixed.Short.circuit, Ecc.MulFixed.Short.synthesize,
    circuit_norm]
  constructor
  · exact lookupNoSimple_of_haveNoLookups
      (shortInnerRegion_haveNoLookups B.toData cfg 0 input.magnitude i)
  · exact lookupNoSimple_of_haveNoLookups
      (shortMswRegion_haveNoLookups cfg
        ((Ecc.MulFixed.Short.innerRegion B.toData cfg 0 input.magnitude).output i).acc
        ((Ecc.MulFixed.Short.innerRegion B.toData cfg 0 input.magnitude).output i).mulB
        input.sign
        ((Ecc.MulFixed.Short.innerRegion B.toData cfg 0 input.magnitude).output i).zs[21]
        (i + 1))

attribute [circuit_norm]
  shortCircuit_inputSelectorsExact
  shortCircuit_noSimpleSelectors

private theorem fullWitnessScalarLoop_haveNoLookups
    (cfg : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector
      (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset : ℕ) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.MulFixed.FullWidth.witnessScalarLoop
        cfg windows offset).operations i) := by
  rw [RegionOperations.HaveNoLookups]
  simp [Ecc.MulFixed.FullWidth.witnessScalarLoop,
    RegionOperation.IsNotLookup, circuit_norm]

private theorem fullWindowChain_haveNoLookups
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector
      (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset : ℕ) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.MulFixed.windowChain cfg.superConfig
        (Ecc.MulFixed.FullWidth.processWindowH B cfg windows)
        offset 85).operations i) := by
  exact windowChain_haveNoLookups cfg.superConfig
    (Ecc.MulFixed.FullWidth.processWindowH B cfg windows)
    offset 85 i (by
      intro w row
      rw [RegionOperations.HaveNoLookups]
      simp [Ecc.MulFixed.FullWidth.processWindowH,
        RegionOperation.IsNotLookup, circuit_norm])

private theorem fullInnerRegion_operations
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector
      (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset : ℕ) (i : RegionIndex) :
    (Ecc.MulFixed.FullWidth.innerRegion B cfg offset windows).operations i =
      (Ecc.MulFixed.FullWidth.witnessScalarLoop
          cfg windows offset).operations i ++
        (Ecc.MulFixed.fixedConstantsLoop
          (Ecc.MulFixed.FullWidth.fullWidthGate cfg) B cfg.superConfig
          offset 85).operations i ++
        (Ecc.MulFixed.windowChain cfg.superConfig
          (Ecc.MulFixed.FullWidth.processWindowH B cfg windows)
          offset 85).operations i := by
  simp only [Ecc.MulFixed.FullWidth.innerRegion, circuit_norm]

private theorem fullInnerRegion_haveNoLookups
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector
      (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset : ℕ) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.MulFixed.FullWidth.innerRegion B cfg offset windows).operations i) := by
  rw [fullInnerRegion_operations,
    RegionOperations.haveNoLookups_append,
    RegionOperations.haveNoLookups_append]
  exact
    ⟨⟨fullWitnessScalarLoop_haveNoLookups cfg windows offset i,
      fixedConstantsLoop_haveNoLookups
        (Ecc.MulFixed.FullWidth.fullWidthGate cfg) B cfg.superConfig
        offset 85 i⟩,
      fullWindowChain_haveNoLookups B cfg windows offset i⟩

private irreducible_def fullInnerOperations
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector
      (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset : ℕ) (i : RegionIndex) : RegionOperations Fp :=
  (Ecc.MulFixed.FullWidth.innerRegion B cfg offset windows).operations i

private theorem fullInnerOperations_eq
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector
      (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset : ℕ) (i : RegionIndex) :
    fullInnerOperations B cfg windows offset i =
      (Ecc.MulFixed.FullWidth.innerRegion B cfg offset windows).operations i := by
  rw [fullInnerOperations]

private theorem fullInnerOperations_lookupFreeCertificate
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector
      (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupFreeCertificate
      (fullInnerOperations B cfg windows offset i) := by
  apply RegionOperations.lookupFreeCertificate_of_haveNoLookups
  rw [fullInnerOperations_eq]
  exact fullInnerRegion_haveNoLookups B cfg windows offset i

private theorem add_inputSelectorsExact
    (cfg : Ecc.Add.Config) (offset : ℕ)
    (input : Var Ecc.Add.Inputs Fp) (i : RegionIndex) :
    RegionOperations.LookupRelevantSelectorActivationsExact
      ((Ecc.Add.add.call cfg offset input).operations i) :=
  lookupExact_of_haveNoLookups (add_haveNoLookups cfg offset input i)

private theorem add_noSimpleSelectors
    (cfg : Ecc.Add.Config) (offset : ℕ)
    (input : Var Ecc.Add.Inputs Fp) (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      ((Ecc.Add.add.call cfg offset input).operations i) :=
  lookupNoSimple_of_haveNoLookups (add_haveNoLookups cfg offset input i)

theorem addFormal_inputSelectorsExact
    (cfg : Ecc.Add.Config) (input : Var Ecc.Add.Inputs Fp)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((Ecc.Add.addFormal.call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp [Ecc.Add.addFormal, FormalRegionCircuit.toFormal, Ecc.Add.add,
    Operations.LookupRelevantSelectorActivationsExact,
    RegionOperations.LookupRelevantSelectorActivationsExact, circuit_norm]

theorem addFormal_noSimpleSelectors
    (cfg : Ecc.Add.Config) (input : Var Ecc.Add.Inputs Fp)
    (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((Ecc.Add.addFormal.call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp [Ecc.Add.addFormal, FormalRegionCircuit.toFormal, Ecc.Add.add,
    Operations.LookupInputsNoSimpleSelectors,
    RegionOperations.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem fullWidthSynthesize_inputSelectorsExact_iff
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector
      (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
        ((Ecc.MulFixed.FullWidth.synthesize B cfg windows).operations i) ↔
      RegionOperations.LookupRelevantSelectorActivationsExact
          ((Ecc.MulFixed.FullWidth.innerRegion B cfg 0 windows).operations i) ∧
        RegionOperations.LookupRelevantSelectorActivationsExact
          ((Ecc.Add.add.call cfg.superConfig.addConfig 0
            { p :=
                ((Ecc.MulFixed.FullWidth.innerRegion B cfg 0 windows).output i).mulB,
              q :=
                ((Ecc.MulFixed.FullWidth.innerRegion B cfg 0 windows).output i).acc }
            ).operations (i + 1)) := by
  simp only [Ecc.MulFixed.FullWidth.synthesize, circuit_norm]

private theorem fullWidthSynthesize_noSimpleSelectors_iff
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector
      (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
        ((Ecc.MulFixed.FullWidth.synthesize B cfg windows).operations i) ↔
      RegionOperations.LookupInputsNoSimpleSelectors
          ((Ecc.MulFixed.FullWidth.innerRegion B cfg 0 windows).operations i) ∧
        RegionOperations.LookupInputsNoSimpleSelectors
          ((Ecc.Add.add.call cfg.superConfig.addConfig 0
            { p :=
                ((Ecc.MulFixed.FullWidth.innerRegion B cfg 0 windows).output i).mulB,
              q :=
                ((Ecc.MulFixed.FullWidth.innerRegion B cfg 0 windows).output i).acc }
            ).operations (i + 1)) := by
  simp only [Ecc.MulFixed.FullWidth.synthesize, circuit_norm]

private theorem fullWidthSynthesize_inputSelectorsExact
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector
      (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((Ecc.MulFixed.FullWidth.synthesize B cfg windows).operations i) := by
  rw [fullWidthSynthesize_inputSelectorsExact_iff]
  constructor
  · rw [← fullInnerOperations_eq]
    exact (fullInnerOperations_lookupFreeCertificate B cfg windows 0 i).exact
  · exact add_inputSelectorsExact cfg.superConfig.addConfig 0
        { p :=
            ((Ecc.MulFixed.FullWidth.innerRegion B cfg 0 windows).output i).mulB,
          q :=
            ((Ecc.MulFixed.FullWidth.innerRegion B cfg 0 windows).output i).acc }
        (i + 1)

private theorem fullWidthSynthesize_noSimpleSelectors
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.FullWidth.Config)
    (windows : Vector
      (Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) 85)
    (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((Ecc.MulFixed.FullWidth.synthesize B cfg windows).operations i) := by
  rw [fullWidthSynthesize_noSimpleSelectors_iff]
  constructor
  · rw [← fullInnerOperations_eq]
    exact (fullInnerOperations_lookupFreeCertificate B cfg windows 0 i).noSimple
  · exact add_noSimpleSelectors cfg.superConfig.addConfig 0
        { p :=
            ((Ecc.MulFixed.FullWidth.innerRegion B cfg 0 windows).output i).mulB,
          q :=
            ((Ecc.MulFixed.FullWidth.innerRegion B cfg 0 windows).output i).acc }
        (i + 1)

theorem fullWidthCircuit_inputSelectorsExact
    (B : Ecc.MulFixed.FixedBase)
    (cfg : Ecc.MulFixed.FullWidth.Config)
    (input : Var UnconstrainedNat Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((Ecc.MulFixed.FullWidth.circuit B).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  exact fullWidthSynthesize_inputSelectorsExact B.toData cfg
    (Ecc.MulFixed.FullWidth.scalarWindows input) i

theorem fullWidthCircuit_noSimpleSelectors
    (B : Ecc.MulFixed.FixedBase)
    (cfg : Ecc.MulFixed.FullWidth.Config)
    (input : Var UnconstrainedNat Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((Ecc.MulFixed.FullWidth.circuit B).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  exact fullWidthSynthesize_noSimpleSelectors B.toData cfg
    (Ecc.MulFixed.FullWidth.scalarWindows input) i

attribute [circuit_norm]
  fullWidthCircuit_inputSelectorsExact
  fullWidthCircuit_noSimpleSelectors

private theorem valueCommit_inputSelectorsExact
    (V : Ecc.MulFixed.Short.FixedBase) (R : Ecc.MulFixed.FixedBase)
    (cfg : Ecc.MulFixed.Short.Config ×
      Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var ValueCommit.Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((ValueCommit.circuit V R).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [ValueCommit.circuit, circuit_norm]
  exact
    ⟨shortCircuit_inputSelectorsExact V cfg.1
        { magnitude := input.magnitude, sign := input.sign } i,
      fullWidthCircuit_inputSelectorsExact R cfg.2.1 input.rcv (i + 2),
      addFormal_inputSelectorsExact cfg.2.2
        { p :=
            (Ecc.MulFixed.Short.circuit V).output cfg.1
              { magnitude := input.magnitude, sign := input.sign } i,
          q :=
            (Ecc.MulFixed.FullWidth.circuit R).output cfg.2.1 input.rcv
              (i + 2) }
        (i + 2 + 2)⟩

private theorem valueCommit_noSimpleSelectors
    (V : Ecc.MulFixed.Short.FixedBase) (R : Ecc.MulFixed.FixedBase)
    (cfg : Ecc.MulFixed.Short.Config ×
      Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var ValueCommit.Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((ValueCommit.circuit V R).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [ValueCommit.circuit, circuit_norm]
  exact
    ⟨shortCircuit_noSimpleSelectors V cfg.1
        { magnitude := input.magnitude, sign := input.sign } i,
      fullWidthCircuit_noSimpleSelectors R cfg.2.1 input.rcv (i + 2),
      addFormal_noSimpleSelectors cfg.2.2
        { p :=
            (Ecc.MulFixed.Short.circuit V).output cfg.1
              { magnitude := input.magnitude, sign := input.sign } i,
          q :=
            (Ecc.MulFixed.FullWidth.circuit R).output cfg.2.1 input.rcv
              (i + 2) }
        (i + 2 + 2)⟩

attribute [circuit_norm]
  valueCommit_inputSelectorsExact
  valueCommit_noSimpleSelectors

private theorem baseFieldInnerRegion_operations
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.BaseFieldElem.Config)
    (offset : ℕ) (alpha : AssignedCell Fp) (i : RegionIndex) :
    (Ecc.MulFixed.BaseFieldElem.innerRegion B cfg offset alpha).operations i =
      ((DecomposeRunningSum.copyDecompose 3 85).call
          cfg.superConfig.runningSumConfig offset
          { alpha := alpha }).operations i ++
        (Ecc.MulFixed.fixedConstantsLoop
          (Ecc.MulFixed.coordsGate cfg.superConfig) B cfg.superConfig
          offset 85).operations i ++
        (Ecc.MulFixed.windowChain cfg.superConfig
          (Ecc.MulFixed.processWindow B
            (Ecc.MulFixed.windowPoint B.point) cfg.superConfig alpha)
          offset 85).operations i := by
  simp only [Ecc.MulFixed.BaseFieldElem.innerRegion, circuit_norm]

private theorem baseFieldWindowChain_haveNoLookups
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.BaseFieldElem.Config)
    (offset : ℕ) (alpha : AssignedCell Fp) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.MulFixed.windowChain cfg.superConfig
        (Ecc.MulFixed.processWindow B
          (Ecc.MulFixed.windowPoint B.point) cfg.superConfig alpha)
        offset 85).operations i) := by
  exact windowChain_haveNoLookups cfg.superConfig
    (Ecc.MulFixed.processWindow B
      (Ecc.MulFixed.windowPoint B.point) cfg.superConfig alpha)
    offset 85 i (by
      intro w row
      rw [RegionOperations.HaveNoLookups]
      simp [Ecc.MulFixed.processWindow, RegionOperation.IsNotLookup, circuit_norm])

private theorem baseFieldInnerRegion_haveNoLookups
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.BaseFieldElem.Config)
    (offset : ℕ) (alpha : AssignedCell Fp) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.MulFixed.BaseFieldElem.innerRegion B cfg offset alpha).operations i) := by
  rw [baseFieldInnerRegion_operations,
    RegionOperations.haveNoLookups_append,
    RegionOperations.haveNoLookups_append]
  exact
    ⟨⟨copyDecompose_haveNoLookups 3 85 cfg.superConfig.runningSumConfig
        { alpha := alpha } offset i,
      fixedConstantsLoop_haveNoLookups
        (Ecc.MulFixed.coordsGate cfg.superConfig) B cfg.superConfig
        offset 85 i⟩,
      baseFieldWindowChain_haveNoLookups B cfg offset alpha i⟩

private irreducible_def baseFieldInnerOperations
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.BaseFieldElem.Config)
    (offset : ℕ) (alpha : AssignedCell Fp) (i : RegionIndex) :
    RegionOperations Fp :=
  (Ecc.MulFixed.BaseFieldElem.innerRegion B cfg offset alpha).operations i

private theorem baseFieldInnerOperations_eq
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.BaseFieldElem.Config)
    (offset : ℕ) (alpha : AssignedCell Fp) (i : RegionIndex) :
    baseFieldInnerOperations B cfg offset alpha i =
      (Ecc.MulFixed.BaseFieldElem.innerRegion B cfg offset alpha).operations i := by
  rw [baseFieldInnerOperations]

private theorem baseFieldInner_lookupFreeCertificate
    (B : Ecc.MulFixed.FixedBaseData)
    (cfg : Ecc.MulFixed.BaseFieldElem.Config)
    (offset : ℕ) (alpha : AssignedCell Fp) (i : RegionIndex) :
    RegionOperations.LookupFreeCertificate
      (baseFieldInnerOperations B cfg offset alpha i) := by
  apply RegionOperations.lookupFreeCertificate_of_haveNoLookups
  rw [baseFieldInnerOperations_eq]
  exact baseFieldInnerRegion_haveNoLookups B cfg offset alpha i

private theorem baseFieldInner_inputSelectorsExact
    (B : Ecc.MulFixed.FixedBase)
    (cfg : Ecc.MulFixed.BaseFieldElem.Config)
    (offset : ℕ) (input : Var DecomposeRunningSum.Inputs Fp)
    (i : RegionIndex) :
    RegionOperations.LookupRelevantSelectorActivationsExact
      (((Ecc.MulFixed.BaseFieldElem.inner B).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Ecc.MulFixed.BaseFieldElem.inner]
  rw [← baseFieldInnerOperations_eq]
  exact (baseFieldInner_lookupFreeCertificate
    B.toData cfg offset input.alpha i).exact

private theorem baseFieldInner_noSimpleSelectors
    (B : Ecc.MulFixed.FixedBase)
    (cfg : Ecc.MulFixed.BaseFieldElem.Config)
    (offset : ℕ) (input : Var DecomposeRunningSum.Inputs Fp)
    (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      (((Ecc.MulFixed.BaseFieldElem.inner B).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [Ecc.MulFixed.BaseFieldElem.inner]
  rw [← baseFieldInnerOperations_eq]
  exact (baseFieldInner_lookupFreeCertificate
    B.toData cfg offset input.alpha i).noSimple

private theorem rangeCheckAtFalse_inputSelectorsEnabled
    (K count : ℕ) (cfg : LookupRangeCheck.Config K)
    (input : Var unit Fp) (offset : ℕ) (i : RegionIndex) :
    RegionOperations.LookupInputSelectorsEnabled
      (((LookupRangeCheck.rangeCheckAt K count false).call
        cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [LookupRangeCheck.rangeCheckAt, circuit_norm,
    Bool.false_eq_true, if_false]
  exact rangeCheckLoop_inputSelectorsEnabled K cfg
    (AssignedCell.of i offset cfg.runningSum) offset count i

private theorem witnessCheck13_inputSelectorsExact
    (cfg : LookupRangeCheck.Config 10) (w : WitgenIR Fp 1)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((Ecc.MulFixed.BaseFieldElem.witnessCheck13 cfg w).operations i) := by
  apply (Operations.LookupRelevantSelectorActivationsExact.region_singleton
    "Witness element" _).mpr
  apply RegionOperations.lookupRelevantSelectorActivationsExact_of_inputSelectorsEnabled
  simp only [circuit_norm]
  unfold RegionOperations.LookupInputSelectorsEnabled
  rw [List.forall_cons]
  constructor
  · trivial
  · exact rangeCheckAtFalse_inputSelectorsEnabled 10 13 cfg () 0 i

private theorem witnessCheck13_noSimpleSelectors
    (cfg : LookupRangeCheck.Config 10)
    (hL : cfg.qLookup.simple = false)
    (hR : cfg.qRunning.simple = false)
    (w : WitgenIR Fp 1) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((Ecc.MulFixed.BaseFieldElem.witnessCheck13 cfg w).operations i) := by
  apply (Operations.LookupInputsNoSimpleSelectors.region_singleton
    "Witness element" _).mpr
  simp only [circuit_norm]
  exact rangeCheckAt_noSimpleSelectors 10 13 false cfg hL hR () 0 i

attribute [circuit_norm]
  baseFieldInner_inputSelectorsExact
  baseFieldInner_noSimpleSelectors
  witnessCheck13_inputSelectorsExact
  witnessCheck13_noSimpleSelectors

private theorem canonicityRegion_haveNoLookups
    (cfg : Ecc.MulFixed.BaseFieldElem.Config)
    (alpha z84 alphaPrime z13 z44 z43 : AssignedCell Fp)
    (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Ecc.MulFixed.BaseFieldElem.canonicityRegion cfg
        alpha z84 alphaPrime z13 z44 z43).operations i) := by
  rw [RegionOperations.HaveNoLookups]
  simp [Ecc.MulFixed.BaseFieldElem.canonicityRegion,
    RegionOperation.IsNotLookup, circuit_norm]

private theorem canonicityRegion_inputSelectorsExact
    (cfg : Ecc.MulFixed.BaseFieldElem.Config)
    (alpha z84 alphaPrime z13 z44 z43 : AssignedCell Fp)
    (i : RegionIndex) :
    RegionOperations.LookupRelevantSelectorActivationsExact
      ((Ecc.MulFixed.BaseFieldElem.canonicityRegion cfg
        alpha z84 alphaPrime z13 z44 z43).operations i) :=
  lookupExact_of_haveNoLookups
    (canonicityRegion_haveNoLookups cfg alpha z84 alphaPrime z13 z44 z43 i)

private theorem canonicityRegion_noSimpleSelectors
    (cfg : Ecc.MulFixed.BaseFieldElem.Config)
    (alpha z84 alphaPrime z13 z44 z43 : AssignedCell Fp)
    (i : RegionIndex) :
    RegionOperations.LookupInputsNoSimpleSelectors
      ((Ecc.MulFixed.BaseFieldElem.canonicityRegion cfg
        alpha z84 alphaPrime z13 z44 z43).operations i) :=
  lookupNoSimple_of_haveNoLookups
    (canonicityRegion_haveNoLookups cfg alpha z84 alphaPrime z13 z44 z43 i)

attribute [circuit_norm]
  canonicityRegion_inputSelectorsExact
  canonicityRegion_noSimpleSelectors

private theorem baseFieldCircuit_inputSelectorsExact
    (B : Ecc.MulFixed.FixedBase)
    (cfg : Ecc.MulFixed.BaseFieldElem.Config)
    (input : AssignedCell Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((Ecc.MulFixed.BaseFieldElem.circuit B).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Ecc.MulFixed.BaseFieldElem.circuit,
    Ecc.MulFixed.BaseFieldElem.synthesize, circuit_norm]
  constructor
  · apply baseFieldInner_inputSelectorsExact
  · constructor
    · apply add_inputSelectorsExact
    · apply canonicityRegion_inputSelectorsExact

private theorem baseFieldCircuit_noSimpleSelectors
    (B : Ecc.MulFixed.FixedBase)
    (cfg : Ecc.MulFixed.BaseFieldElem.Config)
    (hL : cfg.lookupConfig.qLookup.simple = false)
    (hR : cfg.lookupConfig.qRunning.simple = false)
    (input : AssignedCell Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((Ecc.MulFixed.BaseFieldElem.circuit B).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Ecc.MulFixed.BaseFieldElem.circuit,
    Ecc.MulFixed.BaseFieldElem.synthesize, circuit_norm]
  constructor
  · apply baseFieldInner_noSimpleSelectors
  · constructor
    · apply add_noSimpleSelectors
    · constructor
      · apply witnessCheck13_noSimpleSelectors cfg.lookupConfig hL hR
      · apply canonicityRegion_noSimpleSelectors

attribute [circuit_norm]
  baseFieldCircuit_inputSelectorsExact
  baseFieldCircuit_noSimpleSelectors

private theorem poseidonInit_haveNoLookups
    (capacity : Fp) (cfg : Poseidon.Config)
    (offset : ℕ) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      (((Poseidon.initRegion capacity).call cfg offset ()).operations i) := by
  rw [FormalRegionCircuit.call_operations, RegionOperations.HaveNoLookups]
  simp [Poseidon.initRegion, RegionOperation.IsNotLookup, circuit_norm]

private theorem poseidonAddInput_haveNoLookups
    (cfg : Poseidon.Config) (offset : ℕ)
    (input : Var Poseidon.Sponge.AddInputInput Fp) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Poseidon.addInputRegion.call cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations, RegionOperations.HaveNoLookups]
  simp [Poseidon.addInputRegion, RegionOperation.IsNotLookup, circuit_norm]

private theorem poseidonFullRound_haveNoLookups
    (r : ℕ) (cfg : Poseidon.Config) (offset : ℕ)
    (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      (((Poseidon.fullRound r).call cfg offset ()).operations i) := by
  rw [FormalRegionCircuit.call_operations, RegionOperations.HaveNoLookups]
  simp [Poseidon.fullRound, RegionOperation.IsNotLookup, circuit_norm]

private theorem poseidonPartialRound_haveNoLookups
    (r : ℕ) (cfg : Poseidon.Config) (offset : ℕ)
    (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      (((Poseidon.partialRound r).call cfg offset ()).operations i) := by
  rw [FormalRegionCircuit.call_operations, RegionOperations.HaveNoLookups]
  simp [Poseidon.partialRound, RegionOperation.IsNotLookup, circuit_norm]

private theorem poseidonPermute_haveNoLookups
    (cfg : Poseidon.Config) (offset : ℕ)
    (input : Var Poseidon.Permute.State Fp) (i : RegionIndex) :
    RegionOperations.HaveNoLookups
      ((Poseidon.permuteRegion.call cfg offset input).operations i) := by
  rw [FormalRegionCircuit.call_operations, RegionOperations.HaveNoLookups]
  simp only [Poseidon.permuteRegion, circuit_norm]
  simp only [RegionOperation.IsNotLookup, true_and]
  rw [List.forall_append, List.forall_append]
  constructor
  · rw [RegionCircuit.forRange'_forall]
    intro j
    simp only [circuit_norm]
    exact RegionOperations.forall_notLookup_of_haveNoLookups
      (poseidonFullRound_haveNoLookups j cfg (offset + j * 1) i)
  · constructor
    · rw [RegionCircuit.forRange'_forall]
      intro j
      simp only [circuit_norm]
      exact RegionOperations.forall_notLookup_of_haveNoLookups
        (poseidonPartialRound_haveNoLookups (4 + 2 * j) cfg
          (offset + 4 + j * 1) i)
    · rw [RegionCircuit.forRange'_forall]
      intro j
      simp only [circuit_norm]
      exact RegionOperations.forall_notLookup_of_haveNoLookups
        (poseidonFullRound_haveNoLookups (60 + j) cfg
          (offset + 32 + j * 1) i)

private theorem poseidonHash_inputSelectorsExact
    (capacity : Fp) (cfg : Poseidon.Config)
    (input : Var Poseidon.Sponge.Rate2 Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((Poseidon.hash capacity).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Poseidon.hash, circuit_norm]
  exact
    ⟨lookupExact_of_haveNoLookups
        (poseidonInit_haveNoLookups capacity cfg 0 i),
      lookupExact_of_haveNoLookups
        (poseidonAddInput_haveNoLookups cfg 0 _ (i + 1)),
      lookupExact_of_haveNoLookups
        (poseidonPermute_haveNoLookups cfg 0 _ (i + 2))⟩

private theorem poseidonHash_noSimpleSelectors
    (capacity : Fp) (cfg : Poseidon.Config)
    (input : Var Poseidon.Sponge.Rate2 Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((Poseidon.hash capacity).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Poseidon.hash, circuit_norm]
  exact
    ⟨lookupNoSimple_of_haveNoLookups
        (poseidonInit_haveNoLookups capacity cfg 0 i),
      lookupNoSimple_of_haveNoLookups
        (poseidonAddInput_haveNoLookups cfg 0 _ (i + 1)),
      lookupNoSimple_of_haveNoLookups
        (poseidonPermute_haveNoLookups cfg 0 _ (i + 2))⟩

attribute [circuit_norm]
  poseidonHash_inputSelectorsExact
  poseidonHash_noSimpleSelectors

private theorem addChipFormal_inputSelectorsExact
    (cfg : AddChip.Config) (input : Var AddChip.Inputs Fp)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((AddChip.addFormal.call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp [AddChip.addFormal, FormalRegionCircuit.toFormal, AddChip.add,
    Operations.LookupRelevantSelectorActivationsExact,
    RegionOperations.LookupRelevantSelectorActivationsExact, circuit_norm]

private theorem addChipFormal_noSimpleSelectors
    (cfg : AddChip.Config) (input : Var AddChip.Inputs Fp)
    (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((AddChip.addFormal.call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp [AddChip.addFormal, FormalRegionCircuit.toFormal, AddChip.add,
    Operations.LookupInputsNoSimpleSelectors,
    RegionOperations.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem deriveNullifier_inputSelectorsExact
    (K : Ecc.MulFixed.FixedBase)
    (cfg : Poseidon.Config × AddChip.Config ×
      Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config)
    (input : Var DeriveNullifier.Input Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((DeriveNullifier.circuit K).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [DeriveNullifier.circuit, circuit_norm]
  repeat' apply And.intro
  · apply poseidonHash_inputSelectorsExact
  · apply addChipFormal_inputSelectorsExact
  · apply baseFieldCircuit_inputSelectorsExact
  · apply addFormal_inputSelectorsExact

private theorem deriveNullifier_noSimpleSelectors
    (K : Ecc.MulFixed.FixedBase)
    (cfg : Poseidon.Config × AddChip.Config ×
      Ecc.MulFixed.BaseFieldElem.Config × Ecc.Add.Config)
    (hL : cfg.2.2.1.lookupConfig.qLookup.simple = false)
    (hR : cfg.2.2.1.lookupConfig.qRunning.simple = false)
    (input : Var DeriveNullifier.Input Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((DeriveNullifier.circuit K).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [DeriveNullifier.circuit, circuit_norm]
  repeat' apply And.intro
  · apply poseidonHash_noSimpleSelectors
  · apply addChipFormal_noSimpleSelectors
  · apply baseFieldCircuit_noSimpleSelectors <;> assumption
  · apply addFormal_noSimpleSelectors

attribute [circuit_norm]
  deriveNullifier_inputSelectorsExact
  deriveNullifier_noSimpleSelectors

private theorem spendAuthority_inputSelectorsExact
    (G : Ecc.MulFixed.FixedBase)
    (cfg : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var SpendAuthority.Input Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((SpendAuthority.circuit G).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [SpendAuthority.circuit, circuit_norm]
  constructor
  · apply fullWidthCircuit_inputSelectorsExact
  · apply addFormal_inputSelectorsExact

private theorem spendAuthority_noSimpleSelectors
    (G : Ecc.MulFixed.FixedBase)
    (cfg : Ecc.MulFixed.FullWidth.Config × Ecc.Add.Config)
    (input : Var SpendAuthority.Input Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((SpendAuthority.circuit G).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [SpendAuthority.circuit, circuit_norm]
  constructor
  · apply fullWidthCircuit_noSimpleSelectors
  · apply addFormal_noSimpleSelectors

attribute [circuit_norm]
  spendAuthority_inputSelectorsExact
  spendAuthority_noSimpleSelectors

theorem witnessPointNonIdFormal_inputSelectorsExact
    (cfg : Ecc.WitnessPoint.Config)
    (input : Var (Unconstrained Point) Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((Ecc.WitnessPoint.pointNonIdFormal.call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp [Ecc.WitnessPoint.pointNonIdFormal, Ecc.WitnessPoint.pointNonId,
    FormalRegionCircuit.toFormal,
    Operations.LookupRelevantSelectorActivationsExact,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    Operation.LookupRelevantSelectorActivationsExact, circuit_norm]

theorem witnessPointNonIdFormal_noSimpleSelectors
    (cfg : Ecc.WitnessPoint.Config)
    (input : Var (Unconstrained Point) Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((Ecc.WitnessPoint.pointNonIdFormal.call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp [Ecc.WitnessPoint.pointNonIdFormal, Ecc.WitnessPoint.pointNonId,
    FormalRegionCircuit.toFormal,
    Operations.LookupInputsNoSimpleSelectors,
    RegionOperations.LookupInputsNoSimpleSelectors,
    Operation.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem addressIntegrity_inputSelectorsExact
    (cfg : Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (input : Var AddressIntegrity.Input Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((AddressIntegrity.circuit.call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [AddressIntegrity.circuit, circuit_norm]
  constructor
  · apply mulCircuit_inputSelectorsExact
  · apply witnessPointNonIdFormal_inputSelectorsExact

private theorem addressIntegrity_noSimpleSelectors
    (cfg : Ecc.Mul.Config × Ecc.WitnessPoint.Config)
    (hL : cfg.1.overflowConfig.lookupConfig.qLookup.simple = false)
    (hR : cfg.1.overflowConfig.lookupConfig.qRunning.simple = false)
    (input : Var AddressIntegrity.Input Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((AddressIntegrity.circuit.call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [AddressIntegrity.circuit, circuit_norm]
  constructor
  · apply mulCircuit_noSimpleSelectors <;> assumption
  · apply witnessPointNonIdFormal_noSimpleSelectors

attribute [circuit_norm]
  witnessPointNonIdFormal_inputSelectorsExact
  witnessPointNonIdFormal_noSimpleSelectors
  addressIntegrity_inputSelectorsExact
  addressIntegrity_noSimpleSelectors

theorem commitIvkCommitDomain_inputSelectorsExact
    (G : Specs.Sinsemilla.Generators) (ns : List ℕ)
    (R : Ecc.MulFixed.FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Ecc.MulFixed.FullWidth.Config ×
      Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (input : Var (Sinsemilla.CommitDomain.Input ns.length) Fp)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((Sinsemilla.CommitDomain.commit G ns R Q hQ hns).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Sinsemilla.CommitDomain.commit, circuit_norm]
  constructor
  · apply fullWidthCircuit_inputSelectorsExact
  · constructor
    · apply hashCircuit_inputSelectorsExact
    · apply addFormal_inputSelectorsExact

private theorem commitIvkWitnessMessagePiece_inputSelectorsExact
    (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((Sinsemilla.HashToPoint.witnessMessagePiece cfg w).operations i) := by
  simp [Sinsemilla.HashToPoint.witnessMessagePiece,
    Operations.LookupRelevantSelectorActivationsExact,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    Operation.LookupRelevantSelectorActivationsExact, circuit_norm]

private theorem commitIvkSynthPieces_inputSelectorsExact
    (cfg : CommitIvk.Main.Config)
    (hLR : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qRunning.index)
    (hLB : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qBitshift.index)
    (hRB : cfg.lookupConfig.qRunning.index ≠
      cfg.lookupConfig.qBitshift.index)
    (ak nk : AssignedCell Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((CommitIvk.Main.synthPieces cfg ak nk).operations i) := by
  simp only [CommitIvk.Main.synthPieces, circuit_norm]
  repeat' apply And.intro
  all_goals first
    | apply commitIvkWitnessMessagePiece_inputSelectorsExact
    | (apply witnessShortCheck_inputSelectorsExact <;> assumption)

theorem commitIvkWitnessCheck_inputSelectorsExact
    (K count : ℕ) (strict : Bool) (cfg : LookupRangeCheck.Config K)
    (w : WitgenIR Fp 1) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((LookupRangeCheck.witnessCheck K count strict cfg w).operations i) := by
  apply (Operations.LookupRelevantSelectorActivationsExact.region_singleton
    "Witness element" _).mpr
  change RegionOperations.LookupRelevantSelectorActivationsExact
    (RegionOperation.assignAdvice cfg.runningSum 0 w ::
      ((LookupRangeCheck.rangeCheckAt K count strict).call
        cfg 0 ()).operations i)
  rw [lookupExact_assignAdvice_cons]
  apply rangeCheckAt_inputSelectorsExact

private theorem commitIvkGateChild_inputSelectorsExact
    (wb1 wd1 : WitgenIR Fp 1) (cfg : CommitIvk.Config)
    (input : Var CommitIvk.Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((CommitIvk.Canonicity.gateChild wb1 wd1).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp [CommitIvk.Canonicity.gateChild, CommitIvk.bundle,
    FormalRegionCircuit.toFormal,
    Operations.LookupRelevantSelectorActivationsExact,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    Operation.LookupRelevantSelectorActivationsExact, circuit_norm]

private theorem commitIvkCanonicityCircuit_inputSelectorsExact
    (wb1 wd1 : WitgenIR Fp 1)
    (cfg : CommitIvk.Config × LookupRangeCheck.Config 10)
    (input : Var CommitIvk.Canonicity.Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((CommitIvk.Canonicity.circuit wb1 wd1).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [CommitIvk.Canonicity.circuit, CommitIvk.Canonicity.synth,
    circuit_norm]
  exact
    ⟨commitIvkWitnessCheck_inputSelectorsExact 10 13 false cfg.2
        (CommitIvk.Canonicity.aPrimeWit input.a) i,
      commitIvkWitnessCheck_inputSelectorsExact 10 14 false cfg.2
        (CommitIvk.Canonicity.b2CPrimeWit input.b2 input.c) (i + 1),
      commitIvkGateChild_inputSelectorsExact wb1 wd1 cfg.1
        { ak := input.ak, a := input.a, bWhole := input.bWhole,
          b0 := input.b0, b2 := input.b2, z13A := input.z13A,
          aPrime := (LookupRangeCheck.witnessCheck 10 13 false cfg.2
            (CommitIvk.Canonicity.aPrimeWit input.a)).output i |>.z0,
          z13APrime := (LookupRangeCheck.witnessCheck 10 13 false cfg.2
            (CommitIvk.Canonicity.aPrimeWit input.a)).output i |>.zLast,
          nk := input.nk, c := input.c, dWhole := input.dWhole,
          d0 := input.d0, z13C := input.z13C,
          b2CPrime := (LookupRangeCheck.witnessCheck 10 14 false cfg.2
            (CommitIvk.Canonicity.b2CPrimeWit input.b2 input.c)).output
              (i + 1) |>.z0,
          z14B2CPrime := (LookupRangeCheck.witnessCheck 10 14 false cfg.2
            (CommitIvk.Canonicity.b2CPrimeWit input.b2 input.c)).output
              (i + 1) |>.zLast }
        (i + 2)⟩

private theorem commitIvkCircuit_inputSelectorsExact
    (G : Specs.Sinsemilla.Generators)
    (R : Ecc.MulFixed.FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : CommitIvk.Main.Config)
    (hLR : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qRunning.index)
    (hLB : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qBitshift.index)
    (hRB : cfg.lookupConfig.qRunning.index ≠
      cfg.lookupConfig.qBitshift.index)
    (input : Var CommitIvk.Main.Inputs Fp) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      (((CommitIvk.Main.circuit G R Q hQ).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [CommitIvk.Main.circuit, CommitIvk.Main.synth, circuit_norm]
  exact
    ⟨commitIvkSynthPieces_inputSelectorsExact cfg hLR hLB hRB
        input.ak input.nk i,
      commitIvkCommitDomain_inputSelectorsExact G CommitIvk.Main.ns R Q hQ
        CommitIvk.Main.ns_ne_nil
        (cfg.mulConfig, cfg.hashConfig, cfg.addConfig)
        { pieces :=
            #v[((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).a,
              ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).b,
              ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).c,
              ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).d],
          r := input.rivk }
        ((CommitIvk.Main.synthPieces cfg input.ak input.nk).nextRegionIndex i),
      commitIvkCanonicityCircuit_inputSelectorsExact
        (NoteCommit.Main.brWit input.ak 254 1)
        (NoteCommit.Main.brWit input.nk 254 1)
        (cfg.gate, cfg.lookupConfig)
        { ak := input.ak,
          a := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).a,
          bWhole := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).b,
          b0 := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).b0,
          b2 := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).b2,
          z13A := CommitIvk.Main.zCell cfg.hashConfig (i + 9) 0 13,
          nk := input.nk,
          c := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).c,
          dWhole := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).d,
          d0 := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).d0,
          z13C := CommitIvk.Main.zCell cfg.hashConfig (i + 9) 2 13 }
        ((CommitIvk.Main.synthPieces cfg input.ak input.nk).nextRegionIndex i + 4)⟩

theorem commitIvkCommitDomain_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators) (ns : List ℕ)
    (R : Ecc.MulFixed.FixedBase)
    (Q : Point Fp) (hQ : Q.OnCurve) (hns : ns ≠ [])
    (cfg : Ecc.MulFixed.FullWidth.Config ×
      Sinsemilla.HashPiece.Config × Ecc.Add.Config)
    (hS1 : cfg.2.1.qS1.simple = false)
    (input : Var (Sinsemilla.CommitDomain.Input ns.length) Fp)
    (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((Sinsemilla.CommitDomain.commit G ns R Q hQ hns).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [Sinsemilla.CommitDomain.commit, circuit_norm]
  constructor
  · apply fullWidthCircuit_noSimpleSelectors
  · constructor
    · apply hashCircuit_noSimpleSelectors
      exact hS1
    · apply addFormal_noSimpleSelectors

private theorem commitIvkWitnessMessagePiece_noSimpleSelectors
    (cfg : Sinsemilla.HashPiece.Config) (w : WitgenIR Fp 1)
    (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((Sinsemilla.HashToPoint.witnessMessagePiece cfg w).operations i) := by
  simp [Sinsemilla.HashToPoint.witnessMessagePiece,
    Operations.LookupInputsNoSimpleSelectors,
    RegionOperations.LookupInputsNoSimpleSelectors,
    Operation.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem commitIvkSynthPieces_noSimpleSelectors
    (cfg : CommitIvk.Main.Config)
    (hL : cfg.lookupConfig.qLookup.simple = false)
    (hR : cfg.lookupConfig.qRunning.simple = false)
    (ak nk : AssignedCell Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((CommitIvk.Main.synthPieces cfg ak nk).operations i) := by
  simp only [CommitIvk.Main.synthPieces, circuit_norm]
  repeat' apply And.intro
  all_goals first
    | apply commitIvkWitnessMessagePiece_noSimpleSelectors
    | (apply witnessShortCheck_noSimpleSelectors <;> assumption)

theorem commitIvkWitnessCheck_noSimpleSelectors
    (K count : ℕ) (strict : Bool) (cfg : LookupRangeCheck.Config K)
    (hL : cfg.qLookup.simple = false)
    (hR : cfg.qRunning.simple = false)
    (w : WitgenIR Fp 1) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((LookupRangeCheck.witnessCheck K count strict cfg w).operations i) := by
  apply (Operations.LookupInputsNoSimpleSelectors.region_singleton
    "Witness element" _).mpr
  change RegionOperations.LookupInputsNoSimpleSelectors
    (RegionOperation.assignAdvice cfg.runningSum 0 w ::
      ((LookupRangeCheck.rangeCheckAt K count strict).call
        cfg 0 ()).operations i)
  rw [show RegionOperations.LookupInputsNoSimpleSelectors
      (RegionOperation.assignAdvice cfg.runningSum 0 w ::
        ((LookupRangeCheck.rangeCheckAt K count strict).call
          cfg 0 ()).operations i) ↔
      RegionOperations.LookupInputsNoSimpleSelectors
        (((LookupRangeCheck.rangeCheckAt K count strict).call
          cfg 0 ()).operations i) by
    simp [RegionOperations.LookupInputsNoSimpleSelectors]]
  apply rangeCheckAt_noSimpleSelectors <;> assumption

private theorem commitIvkGateChild_noSimpleSelectors
    (wb1 wd1 : WitgenIR Fp 1) (cfg : CommitIvk.Config)
    (input : Var CommitIvk.Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((CommitIvk.Canonicity.gateChild wb1 wd1).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp [CommitIvk.Canonicity.gateChild, CommitIvk.bundle,
    FormalRegionCircuit.toFormal,
    Operations.LookupInputsNoSimpleSelectors,
    RegionOperations.LookupInputsNoSimpleSelectors,
    Operation.LookupInputsNoSimpleSelectors, circuit_norm]

private theorem commitIvkCanonicityCircuit_noSimpleSelectors
    (wb1 wd1 : WitgenIR Fp 1)
    (cfg : CommitIvk.Config × LookupRangeCheck.Config 10)
    (hL : cfg.2.qLookup.simple = false)
    (hR : cfg.2.qRunning.simple = false)
    (input : Var CommitIvk.Canonicity.Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((CommitIvk.Canonicity.circuit wb1 wd1).call
        cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [CommitIvk.Canonicity.circuit, CommitIvk.Canonicity.synth,
    circuit_norm]
  exact
    ⟨commitIvkWitnessCheck_noSimpleSelectors 10 13 false cfg.2 hL hR
        (CommitIvk.Canonicity.aPrimeWit input.a) i,
      commitIvkWitnessCheck_noSimpleSelectors 10 14 false cfg.2 hL hR
        (CommitIvk.Canonicity.b2CPrimeWit input.b2 input.c) (i + 1),
      commitIvkGateChild_noSimpleSelectors wb1 wd1 cfg.1
        { ak := input.ak, a := input.a, bWhole := input.bWhole,
          b0 := input.b0, b2 := input.b2, z13A := input.z13A,
          aPrime := (LookupRangeCheck.witnessCheck 10 13 false cfg.2
            (CommitIvk.Canonicity.aPrimeWit input.a)).output i |>.z0,
          z13APrime := (LookupRangeCheck.witnessCheck 10 13 false cfg.2
            (CommitIvk.Canonicity.aPrimeWit input.a)).output i |>.zLast,
          nk := input.nk, c := input.c, dWhole := input.dWhole,
          d0 := input.d0, z13C := input.z13C,
          b2CPrime := (LookupRangeCheck.witnessCheck 10 14 false cfg.2
            (CommitIvk.Canonicity.b2CPrimeWit input.b2 input.c)).output
              (i + 1) |>.z0,
          z14B2CPrime := (LookupRangeCheck.witnessCheck 10 14 false cfg.2
            (CommitIvk.Canonicity.b2CPrimeWit input.b2 input.c)).output
              (i + 1) |>.zLast }
        (i + 2)⟩

private theorem commitIvkCircuit_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators)
    (R : Ecc.MulFixed.FixedBase) (Q : Point Fp) (hQ : Q.OnCurve)
    (cfg : CommitIvk.Main.Config)
    (hL : cfg.lookupConfig.qLookup.simple = false)
    (hR : cfg.lookupConfig.qRunning.simple = false)
    (hS1 : cfg.hashConfig.qS1.simple = false)
    (input : Var CommitIvk.Main.Inputs Fp) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      (((CommitIvk.Main.circuit G R Q hQ).call cfg input).operations i) := by
  rw [FormalCircuit.call_operations]
  simp only [CommitIvk.Main.circuit, CommitIvk.Main.synth, circuit_norm]
  exact
    ⟨commitIvkSynthPieces_noSimpleSelectors cfg hL hR input.ak input.nk i,
      commitIvkCommitDomain_noSimpleSelectors G CommitIvk.Main.ns R Q hQ
        CommitIvk.Main.ns_ne_nil
        (cfg.mulConfig, cfg.hashConfig, cfg.addConfig) hS1
        { pieces :=
            #v[((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).a,
              ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).b,
              ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).c,
              ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).d],
          r := input.rivk }
        ((CommitIvk.Main.synthPieces cfg input.ak input.nk).nextRegionIndex i),
      commitIvkCanonicityCircuit_noSimpleSelectors
        (NoteCommit.Main.brWit input.ak 254 1)
        (NoteCommit.Main.brWit input.nk 254 1)
        (cfg.gate, cfg.lookupConfig) hL hR
        { ak := input.ak,
          a := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).a,
          bWhole := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).b,
          b0 := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).b0,
          b2 := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).b2,
          z13A := CommitIvk.Main.zCell cfg.hashConfig (i + 9) 0 13,
          nk := input.nk,
          c := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).c,
          dWhole := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).d,
          d0 := ((CommitIvk.Main.synthPieces cfg input.ak input.nk).output i).d0,
          z13C := CommitIvk.Main.zCell cfg.hashConfig (i + 9) 2 13 }
        ((CommitIvk.Main.synthPieces cfg input.ak input.nk).nextRegionIndex i + 4)⟩

attribute [circuit_norm]
  commitIvkCircuit_inputSelectorsExact
  commitIvkCircuit_noSimpleSelectors

private theorem loadPrivate_inputSelectorsExact
    (column : Column .advice) (witness : WitgenIR Fp 1)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((loadPrivate column witness).operations i) := by
  simp [loadPrivate, Operations.LookupRelevantSelectorActivationsExact,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    Operation.LookupRelevantSelectorActivationsExact, circuit_norm]

private theorem loadPrivate_noSimpleSelectors
    (column : Column .advice) (witness : WitgenIR Fp 1)
    (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((loadPrivate column witness).operations i) := by
  simp [loadPrivate, Operations.LookupInputsNoSimpleSelectors,
    RegionOperations.LookupInputsNoSimpleSelectors,
    Operation.LookupInputsNoSimpleSelectors, circuit_norm]

attribute [circuit_norm]
  loadPrivate_inputSelectorsExact
  loadPrivate_noSimpleSelectors

theorem synthChecks_inputSelectorsExact
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (W : Witnesses Fp) (cfg : Circuit.Config)
    (hLR : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qRunning.index)
    (hLB : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qBitshift.index)
    (hRB : cfg.lookupConfig.qRunning.index ≠
      cfg.lookupConfig.qBitshift.index)
    (wc : WitnessCells) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((synthChecks G B W cfg wc).operations i) := by
  simp only [synthChecks, circuit_norm]
  constructor
  · apply calculateRoot_inputSelectorsExact G B.merkleQ B.merkleQ_onCurve
      0 16 (by norm_num) W.merkleSib W.merkleSwap
      (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig) hLR hLB hRB
  · constructor
    · apply calculateRoot_inputSelectorsExact G B.merkleQ B.merkleQ_onCurve
        16 16 (by norm_num) (fun j => W.merkleSib (16 + j))
        (fun j => W.merkleSwap (16 + j))
        (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig) hLR hLB hRB
    · constructor
      · apply valueCommit_inputSelectorsExact B.valueCommitV B.valueCommitR
          (cfg.eccConfig.mulFixedShort, cfg.eccConfig.mulFixedFull,
            cfg.eccConfig.add)
      · constructor
        · apply deriveNullifier_inputSelectorsExact B.nullifierK
            (cfg.poseidonConfig, cfg.addChipConfig,
              cfg.eccConfig.mulFixedBaseField, cfg.eccConfig.add)
        · constructor
          · apply spendAuthority_inputSelectorsExact B.spendAuthG
              (cfg.eccConfig.mulFixedFull, cfg.eccConfig.add)
          · repeat' apply And.intro
            all_goals first
              | (apply commitIvkCircuit_inputSelectorsExact <;> assumption)
              | apply addressIntegrity_inputSelectorsExact

theorem synthChecks_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (W : Witnesses Fp) (cfg : Circuit.Config)
    (hL : cfg.lookupConfig.qLookup.simple = false)
    (hR : cfg.lookupConfig.qRunning.simple = false)
    (hS1 : cfg.sinsemilla1.qS1.simple = false)
    (hM1 : cfg.merkle1.sinsemilla.qS1.simple = false)
    (hM2 : cfg.merkle2.sinsemilla.qS1.simple = false)
    (hBFL :
      cfg.eccConfig.mulFixedBaseField.lookupConfig.qLookup.simple = false)
    (hBFR :
      cfg.eccConfig.mulFixedBaseField.lookupConfig.qRunning.simple = false)
    (hML : cfg.eccConfig.mul.overflowConfig.lookupConfig.qLookup.simple = false)
    (hMR : cfg.eccConfig.mul.overflowConfig.lookupConfig.qRunning.simple = false)
    (wc : WitnessCells) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((synthChecks G B W cfg wc).operations i) := by
  simp only [synthChecks, circuit_norm]
  constructor
  · apply calculateRoot_noSimpleSelectors G B.merkleQ B.merkleQ_onCurve
      0 16 (by norm_num) W.merkleSib W.merkleSwap
      (cfg.merkle1.condSwap, cfg.merkle1, cfg.lookupConfig)
      hL hR hM1
  · constructor
    · apply calculateRoot_noSimpleSelectors G B.merkleQ B.merkleQ_onCurve
        16 16 (by norm_num) (fun j => W.merkleSib (16 + j))
        (fun j => W.merkleSwap (16 + j))
        (cfg.merkle2.condSwap, cfg.merkle2, cfg.lookupConfig)
        hL hR hM2
    · constructor
      · apply valueCommit_noSimpleSelectors
      · constructor
        · apply deriveNullifier_noSimpleSelectors <;>
            first | exact hBFL | exact hBFR
        · constructor
          · apply spendAuthority_noSimpleSelectors
          · repeat' apply And.intro
            all_goals first
              | (apply commitIvkCircuit_noSimpleSelectors <;> assumption)
              | (apply addressIntegrity_noSimpleSelectors <;> assumption)

theorem synthCrossAddressChecks_inputSelectorsExact
    (cfg : Circuit.Config) (input : Var AddressPoints Fp)
    (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((synthCrossAddressChecks cfg input).operations i) := by
  simp [synthCrossAddressChecks,
    Operations.LookupRelevantSelectorActivationsExact,
    RegionOperations.LookupRelevantSelectorActivationsExact,
    Operation.LookupRelevantSelectorActivationsExact, circuit_norm]

theorem synthCrossAddressChecks_noSimpleSelectors
    (cfg : Circuit.Config) (input : Var AddressPoints Fp)
    (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((synthCrossAddressChecks cfg input).operations i) := by
  simp [synthCrossAddressChecks,
    Operations.LookupInputsNoSimpleSelectors,
    RegionOperations.LookupInputsNoSimpleSelectors,
    Operation.LookupInputsNoSimpleSelectors, circuit_norm]

attribute [circuit_norm]
  synthCrossAddressChecks_inputSelectorsExact
  synthCrossAddressChecks_noSimpleSelectors

theorem configuredSynthesisSelectorFacts
    (G : Specs.Sinsemilla.Generators) :
    let cfg := (configure G {}).1
    (cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qRunning.index ∧
      cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qBitshift.index ∧
      cfg.lookupConfig.qRunning.index ≠ cfg.lookupConfig.qBitshift.index) ∧
    (cfg.lookupConfig.qLookup.simple = false ∧
      cfg.lookupConfig.qRunning.simple = false ∧
      cfg.eccConfig.mulFixedBaseField.lookupConfig.qLookup.simple = false ∧
      cfg.eccConfig.mulFixedBaseField.lookupConfig.qRunning.simple = false ∧
      cfg.eccConfig.mul.overflowConfig.lookupConfig.qLookup.simple = false ∧
      cfg.eccConfig.mul.overflowConfig.lookupConfig.qRunning.simple = false ∧
      cfg.sinsemilla1.qS1.simple = false ∧
      cfg.sinsemilla2.qS1.simple = false ∧
      cfg.merkle1.sinsemilla.qS1.simple = false ∧
      cfg.merkle2.sinsemilla.qS1.simple = false) := by
  change
    ((2 : ℕ) ≠ 3 ∧ (2 : ℕ) ≠ 4 ∧ (3 : ℕ) ≠ 4) ∧
    (false = false ∧ false = false ∧ false = false ∧
      false = false ∧ false = false ∧ false = false ∧
      false = false ∧ false = false ∧ false = false ∧ false = false)
  simp

end Action

end Zcash.Circuits
