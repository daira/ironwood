import Clean.Halo2.TopLevel
import Zcash.Circuits.Action.PublicInput
import Zcash.Circuits.Action.RealBases
import Zcash.Circuits.Action.TopLevelSynthesisLaws

/-!
# The deployed Orchard Action as a closed top-level circuit
-/

namespace Zcash.Circuits.Action

open Halo2
open Specs.Sinsemilla (Generators)
open Circuit

set_option maxHeartbeats 20000

private theorem initialGeneratorTableIdx_mem
    (G : Generators) (B : Bases) (cfg : Config) (i : RegionIndex) :
    Operation.loadTable cfg.sinsemilla1.generatorTable.tableIdx
        ((List.range (2 ^ Specs.K)).map (Nat.cast : ℕ → Fp)) ∈
      (mainPost G B cfg ()).operations i := by
  simp only [mainPost, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil]
  apply List.mem_append_left
  rw [FormalCircuit.call_operations]
  simp only [baseCircuit, main, CircuitPreIronwood.synthesize, synthesizeBase,
    Circuit.operations_bind, Circuit.operations_pure, List.append_nil]
  apply List.mem_append_left
  simp only [synthWitness, Circuit.operations_bind, Circuit.operations_pure,
    List.append_nil]
  apply List.mem_append_left
  rw [Sinsemilla.load_operations]
  simp

private theorem configuredTableSharing (G : Generators) :
    let cfg := (configure G {}).1
    cfg.sinsemilla2.generatorTable = cfg.sinsemilla1.generatorTable ∧
    cfg.merkle1.sinsemilla.generatorTable = cfg.sinsemilla1.generatorTable ∧
    cfg.merkle2.sinsemilla.generatorTable = cfg.sinsemilla1.generatorTable ∧
    cfg.lookupConfig.tableIdx = cfg.sinsemilla1.generatorTable.tableIdx := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem configuredLookupSelectorIndices (G : Generators) :
    let cfg := (configure G {}).1
    cfg.lookupConfig.qLookup.index = 2 ∧
      cfg.lookupConfig.qRunning.index = 3 := by
  exact ⟨rfl, rfl⟩

private theorem configured_pureEnvironmentAssumptions
    (G : Generators) (env : Placed Environment Fp) :
    let cfg := (configure G {}).1
    Ecc.MulFixed.FullWidth.EnvAssumptions cfg.eccConfig.mulFixedFull env ∧
    Ecc.MulFixed.Short.EnvAssumptions cfg.eccConfig.mulFixedShort env ∧
    Ecc.MulFixed.BaseFieldElem.InnerEnvAssumptions
      cfg.eccConfig.mulFixedBaseField env ∧
    cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qRunning.index := by
  simp only [Ecc.MulFixed.FullWidth.EnvAssumptions,
    Ecc.MulFixed.Short.EnvAssumptions,
    Ecc.MulFixed.Short.InnerEnvAssumptions,
    Ecc.MulFixed.BaseFieldElem.InnerEnvAssumptions, circuit_norm]
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
  obtain ⟨hLookup, hRunning⟩ := configuredLookupSelectorIndices G
  omega

private theorem circuit_configure_eq (G : Generators) (B : Bases) :
    (circuit G B).configure = fun _ => configure G :=
  rfl

private theorem circuit_synthesize_eq (G : Generators) (B : Bases) (cfg : Config) :
    (circuit G B).synthesize cfg = mainPost G B cfg :=
  rfl

private theorem circuit_envAssumptions_eq (G : Generators) (B : Bases) (cfg : Config) :
    (circuit G B).EnvAssumptions cfg = EnvAssumptions cfg :=
  rfl

/--
The circuit compiler supplies the residual Action environment contract. Table
contents are deliberately absent: the circuit proofs derive those from their
respective operational hypotheses.
-/
private theorem configured_closesEnvironment
    (G : Generators) (B : Bases) (assignment : ProofAssignment Fp) :
    let formal := circuit G B
    formal.EnvAssumptions
      (TopLevelCompilation.config formal)
      (TopLevelCompilation.placedEnvironment formal assignment) := by
  let formal := circuit G B
  let env := TopLevelCompilation.placedEnvironment formal assignment
  change EnvAssumptions (configure G {}).1 env
  have htable :
      2 ^ Specs.K ≤ TopLevelCompilation.usedRows formal := by
    have hlength := Operations.loadTable_length_le_usedRows
      (TopLevelCompilation.operations formal)
      (configure G {}).1.sinsemilla1.generatorTable.tableIdx
      ((List.range (2 ^ Specs.K)).map (Nat.cast : ℕ → Fp))
      (by
        simpa only [formal, TopLevelCompilation.operations,
          TopLevelCompilation.config, circuit_configure_eq,
          circuit_synthesize_eq] using
          initialGeneratorTableIdx_mem
            G B (configure G {}).1 0)
    simpa only [List.length_map, List.length_range] using hlength
  have hUsable : 2 ^ Specs.K ≤ env.env.usableRows := by
    change
      2 ^ Specs.K ≤
        2 ^ TopLevelCompilation.domainExponent formal -
          (TopLevelCompilation.constraintSystem formal).blindingFactors - 1
    exact htable.trans
      (TopLevelCompilation.usedRows_le_usableRowsAt_domainExponent formal)
  obtain ⟨hs2, hm1, hm2, hlookup⟩ := configuredTableSharing G
  obtain ⟨hfull, hshort, hbaseField, hdistinct⟩ :=
    configured_pureEnvironmentAssumptions G env
  exact ⟨hUsable, hs2, hm1, hm2, hlookup, hfull, hshort,
    hbaseField, rfl, rfl, hdistinct⟩

/--
The proof-carrying Orchard Action circuit at arbitrary certified constants, closed as
a deployable `TopLevelCircuit`: unit public synthesis input, `True` verifier
assumptions, and no unfulfilled environment contract at its boundary.
-/
def topLevelCircuit (G : Generators) (B : Bases) :
    TopLevelCircuit Fp Config PublicInputs where
  formalCircuit := circuit G B
  publicInputLayout := PublicInputs.layout
  PrivateWitness := PrivateWitness
  extractPrivate := fun cfg env =>
    PrivateWitness.ofActionData (extractPost cfg () 0 env)
  combine := combine
  Spec := fun inputs privateWitness =>
    SpecPost G B () () (combine inputs privateWitness)
  spec_iff := by
    intros
    rfl
  extract_factorization := by
    dsimp
    intro env
    change combine
      (PublicInputs.layout.extract (configure G {}).1 env.env)
      (PrivateWitness.ofActionData (extractPost (configure G {}).1 () 0 env)) =
      extractPost (configure G {}).1 () 0 env
    rw [← PublicInputs.ofActionData_extractPost]
    exact combine_parts (extractPost (configure G {}).1 () 0 env)
  assumptions_eq := rfl
  lookupRelevantSelectorActivationsExact :=
    actionCircuit_lookupRelevantSelectorActivationsExact G B
  lookupInputsNoSimpleSelectors :=
    actionCircuit_lookupInputsNoSimpleSelectors G B
  closesEnvironment := configured_closesEnvironment G B

/-- The deployed Orchard Action circuit, instantiated at its real proven constants. -/
def orchardActionTopLevelCircuit :
    TopLevelCircuit Fp Config PublicInputs :=
  topLevelCircuit Specs.Sinsemilla.orchardGenerators orchardBases

@[simp] theorem orchardActionTopLevelCircuit_publicInputLayout :
    orchardActionTopLevelCircuit.publicInputLayout = PublicInputs.layout :=
  rfl

@[simp] theorem orchardActionTopLevelCircuit_config :
    orchardActionTopLevelCircuit.config =
      (configure Specs.Sinsemilla.orchardGenerators {}).1 :=
  rfl

end Zcash.Circuits.Action
