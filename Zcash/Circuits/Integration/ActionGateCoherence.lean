import Zcash.Circuits.Integration.ActionGateCoherenceCompute

/-!
# Action top-level gate coherence

This module packages the circuit-owned configure certificates and the small derived
layout computations into the generic static gate-coherence boundary.
-/

namespace Zcash.Circuits

open Halo2

namespace ActionGateCoherence

/-- The exact deployed configure program, named before it is made opaque. -/
def configureProgramSource : Configure Fp Action.Circuit.Config :=
  Action.Circuit.configure Specs.Sinsemilla.orchardGenerators

/-- An opaque handle carrying both the program and its source identification. -/
opaque configureHandle :
    {program : Configure Fp Action.Circuit.Config //
      program = configureProgramSource} :=
  ⟨configureProgramSource, rfl⟩

/--
The sealed program projection. Its state-monad body cannot be normalized unless the
source-identification theorem is used explicitly.
-/
def configureProgram : Configure Fp Action.Circuit.Config :=
  configureHandle.1

theorem configureProgram_eq :
    configureProgram = configureProgramSource :=
  configureHandle.2

theorem configureProgram_preservesGateWellFormedness :
    Configure.PreservesGateWellFormedness configureProgram := by
  rw [configureProgram_eq]
  simpa only [configureProgramSource] using
    (Action.Circuit.configure_preservesGateWellFormedness
      Specs.Sinsemilla.orchardGenerators)

theorem configureProgram_preservesGateSelectorsAllocated :
    Configure.PreservesGateSelectorsAllocated configureProgram := by
  rw [configureProgram_eq]
  simpa only [configureProgramSource] using
    (Action.Circuit.configure_preservesGateSelectorsAllocated
      Specs.Sinsemilla.orchardGenerators)

theorem configureProgram_gatesWellFormed :
    (configureProgram {}).2.GatesWellFormed :=
  Configure.PreservesGateWellFormedness.fromEmpty
    configureProgram_preservesGateWellFormedness

theorem configureProgram_gateSelectorsAllocated :
    (configureProgram {}).2.GateSelectorsAllocated :=
  Configure.PreservesGateSelectorsAllocated.fromEmpty
    configureProgram_preservesGateSelectorsAllocated

end ActionGateCoherence

end Zcash.Circuits

namespace Zcash.Snark

open Halo2 Keygen
open Zcash.Circuits
open Zcash.Circuits.Action (orchardActionTopLevelCircuit)

namespace ActionGateCoherence

set_option maxRecDepth 100000

private theorem gatesWellFormed_of_gates_eq
    {F : Type} [Field F] {source target : ConstraintSystem F}
    (heq : source.gates = target.gates)
    (h : target.GatesWellFormed) :
    source.GatesWellFormed := by
  unfold ConstraintSystem.GatesWellFormed at h ⊢
  rwa [heq]

private theorem gateSelectorsAllocated_of_data_eq
    {F : Type} {source target : ConstraintSystem F}
    (hgates : source.gates = target.gates)
    (hselectors : source.numSelectors = target.numSelectors)
    (h : target.GateSelectorsAllocated) :
    source.GateSelectorsAllocated := by
  unfold ConstraintSystem.GateSelectorsAllocated at h ⊢
  rwa [hgates, hselectors]

private theorem gatesWellFormed :
    orchardActionTopLevelCircuit.constraintSystem.GatesWellFormed :=
  gatesWellFormed_of_gates_eq
    (gateData_eq.1.trans (congrArg
      (fun program => (program {}).2.gates)
      Circuits.ActionGateCoherence.configureProgram_eq.symm))
    Circuits.ActionGateCoherence.configureProgram_gatesWellFormed

private theorem gateSelectorsAllocated :
    orchardActionTopLevelCircuit.constraintSystem.GateSelectorsAllocated :=
  gateSelectorsAllocated_of_data_eq
    (gateData_eq.1.trans (congrArg
      (fun program => (program {}).2.gates)
      Circuits.ActionGateCoherence.configureProgram_eq.symm))
    (gateData_eq.2.trans (congrArg
      (fun program => (program {}).2.numSelectors)
      Circuits.ActionGateCoherence.configureProgram_eq.symm))
    Circuits.ActionGateCoherence.configureProgram_gateSelectorsAllocated

private theorem adviceQueryCount
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    (orchardActionTopLevelCircuit.toVerifierKey pp urs).adviceQueryLayout.length =
      (pp.mergeDerived orchardActionTopLevelCircuit).numAdviceQueries :=
  orchardActionTopLevelCircuit.toVerifierKey_adviceQueryCount pp urs

private theorem fixedQueryCount
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    (orchardActionTopLevelCircuit.toVerifierKey pp urs).fixedQueryLayout.length =
      (pp.mergeDerived orchardActionTopLevelCircuit).numFixedQueries :=
  orchardActionTopLevelCircuit.toVerifierKey_fixedQueryCount pp urs

private theorem instanceQueryCount
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    (orchardActionTopLevelCircuit.toVerifierKey pp urs).instanceQueryLayout.length =
      (pp.mergeDerived orchardActionTopLevelCircuit).numInstanceQueries :=
  orchardActionTopLevelCircuit.toVerifierKey_instanceQueryCount pp urs

/--
The deployed Orchard Action circuit satisfies the complete static gate boundary
against its own derived verifying key.
-/
theorem topLevelGateCoherence
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    TopLevelGateCoherence orchardActionTopLevelCircuit pp urs where
  gatesWellFormed := gatesWellFormed
  gateSelectorsAllocated := gateSelectorsAllocated
  adviceQueryCount := adviceQueryCount pp urs
  fixedQueryCount := fixedQueryCount pp urs
  instanceQueryCount := instanceQueryCount pp urs
  domainExponent_lt := domainExponent_lt
  selectorDegree := selectorDegree

assert_no_sorry topLevelGateCoherence

end ActionGateCoherence

end Zcash.Snark
