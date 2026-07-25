import Zcash.Circuits.NoteCommit.SynthesisLaws

open Halo2

set_option maxHeartbeats 20000

namespace Zcash.Circuits.Action

open Circuit

theorem synthNotes_inputSelectorsExact
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (W : Witnesses Fp) (cfg : Circuit.Config)
    (hLR : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qRunning.index)
    (hLB : cfg.lookupConfig.qLookup.index ≠
      cfg.lookupConfig.qBitshift.index)
    (hRB : cfg.lookupConfig.qRunning.index ≠
      cfg.lookupConfig.qBitshift.index)
    (wc : WitnessCells) (cc : CheckCells) (i : RegionIndex) :
    Operations.LookupRelevantSelectorActivationsExact
      ((synthNotes G B W cfg wc cc).operations i) := by
  simp only [synthNotes, circuit_norm]
  constructor
  · apply NoteCommit.Main.circuit_inputSelectorsExact <;> assumption
  · constructor
    · apply witnessPointNonIdFormal_inputSelectorsExact
    · constructor
      · apply witnessPointNonIdFormal_inputSelectorsExact
      · apply NoteCommit.Main.circuit_inputSelectorsExact <;> assumption

theorem synthNotes_noSimpleSelectors
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (W : Witnesses Fp) (cfg : Circuit.Config)
    (hL : cfg.lookupConfig.qLookup.simple = false)
    (hR : cfg.lookupConfig.qRunning.simple = false)
    (hS1 : cfg.sinsemilla1.qS1.simple = false)
    (hS2 : cfg.sinsemilla2.qS1.simple = false)
    (wc : WitnessCells) (cc : CheckCells) (i : RegionIndex) :
    Operations.LookupInputsNoSimpleSelectors
      ((synthNotes G B W cfg wc cc).operations i) := by
  simp only [synthNotes, circuit_norm]
  constructor
  · apply NoteCommit.Main.circuit_noSimpleSelectors <;> assumption
  · constructor
    · apply witnessPointNonIdFormal_noSimpleSelectors
    · constructor
      · apply witnessPointNonIdFormal_noSimpleSelectors
      · apply NoteCommit.Main.circuit_noSimpleSelectors <;> assumption

attribute [circuit_norm]
  synthNotes_inputSelectorsExact
  synthNotes_noSimpleSelectors

private theorem actionCircuit_synthesize_eq
    (G : Specs.Sinsemilla.Generators) (B : Bases)
    (cfg : Circuit.Config) :
    (circuit G B).synthesize cfg = mainPost G B cfg :=
  rfl

private theorem actionCircuit_configure_eq
    (G : Specs.Sinsemilla.Generators) (B : Bases) :
    (circuit G B).configure = fun _ => configure G :=
  rfl

theorem actionCircuit_lookupRelevantSelectorActivationsExact
    (G : Specs.Sinsemilla.Generators) (B : Bases) :
    let cfg := (circuit G B).configure () {} |>.1
    Operations.LookupRelevantSelectorActivationsExact
      ((circuit G B).synthesize cfg () |>.operations 0) := by
  have h := configuredSynthesisSelectorFacts G
  simp only [actionCircuit_configure_eq] at h ⊢
  rcases h with ⟨⟨hLR, hLB, hRB⟩, _⟩
  simp only [actionCircuit_synthesize_eq, mainPost, circuit_norm]
  rw [FormalCircuit.call_operations]
  simp only [baseCircuit, main, CircuitPreIronwood.synthesize,
    Circuit.synthesizeBase, circuit_norm]
  exact
    ⟨synthChecks_inputSelectorsExact G B _ _ hLR hLB hRB _ _,
      synthNotes_inputSelectorsExact G B _ _ hLR hLB hRB _ _ _⟩

theorem actionCircuit_lookupInputsNoSimpleSelectors
    (G : Specs.Sinsemilla.Generators) (B : Bases) :
    let cfg := (circuit G B).configure () {} |>.1
    Operations.LookupInputsNoSimpleSelectors
      ((circuit G B).synthesize cfg () |>.operations 0) := by
  have h := configuredSynthesisSelectorFacts G
  simp only [actionCircuit_configure_eq] at h ⊢
  rcases h with
    ⟨_, hL, hR, hBFL, hBFR, hML, hMR, hS1, hS2, hM1, hM2⟩
  simp only [actionCircuit_synthesize_eq, mainPost, circuit_norm]
  rw [FormalCircuit.call_operations]
  simp only [baseCircuit, main, CircuitPreIronwood.synthesize,
    Circuit.synthesizeBase, circuit_norm]
  exact
    ⟨synthChecks_noSimpleSelectors G B _ _ hL hR hS1 hM1 hM2
        hBFL hBFR hML hMR _ _,
      synthNotes_noSimpleSelectors G B _ _ hL hR hS1 hS2 _ _ _⟩

end Zcash.Circuits.Action
