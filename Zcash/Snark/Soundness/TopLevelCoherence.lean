import Zcash.Circuits.TopLevel
import Zcash.Snark.Soundness.OperationGates
import Zcash.Snark.Soundness.OperationLookups

/-!
# Top-level configure/synthesis coherence

`FormalCircuit` deliberately keeps configuration and synthesis independent. A
deployed top-level circuit therefore certifies once that every gate and lookup
activation emitted by synthesis was registered by configuration.

This module proves that the compact operation-level certificate supplies exactly
the membership facts needed by the generic gate and lookup bridges. No circuit,
placement, or verifying key is selected here.
-/

namespace Zcash.Snark

open Halo2
open Zcash.Circuits

set_option maxHeartbeats 20000

namespace OperationsKeygenCoherent

/-- A coherent region registers every extracted enabled gate. -/
theorem region_gate
    {F : Type} {cs : ConstraintSystem F}
    {self : RegionIndex} {body : RegionOperations F}
    (hcoherent :
      body.Forall (RegionOperation.KeygenCoherent cs))
    {enabled : EnabledGate F}
    (henabled : enabled ∈ regionEnabledGates self body) :
    enabled.gate ∈ cs.gates := by
  induction body with
  | nil => simp [regionEnabledGates] at henabled
  | cons operation rest ih =>
      rw [List.forall_cons] at hcoherent
      cases operation with
      | enableGate gate row =>
          simp only [RegionOperation.KeygenCoherent] at hcoherent
          simp only [regionEnabledGates, List.mem_cons] at henabled
          rcases henabled with rfl | henabled
          · exact hcoherent.1
          · exact ih hcoherent.2 henabled
      | assignAdvice column row witness =>
          exact ih hcoherent.2 henabled
      | assignFixed column row value =>
          exact ih hcoherent.2 henabled
      | enableLookup argument selectors row =>
          exact ih hcoherent.2 henabled
      | constrainEqual left right =>
          exact ih hcoherent.2 henabled
      | constrainConstant cell value =>
          exact ih hcoherent.2 henabled
      | constrainInstance cell column row =>
          exact ih hcoherent.2 henabled

/-- A coherent operation stream registers every extracted enabled gate. -/
theorem gate
    {F : Type} {cs : ConstraintSystem F}
    {operations : Operations F} {i : RegionIndex}
    (hcoherent : OperationsKeygenCoherent cs operations)
    {enabled : EnabledGate F}
    (henabled : enabled ∈ operationEnabledGates operations i) :
    enabled.gate ∈ cs.gates := by
  induction operations generalizing i with
  | nil => simp [operationEnabledGates] at henabled
  | cons operation rest ih =>
      rw [OperationsKeygenCoherent, List.forall_cons] at hcoherent
      rcases hcoherent with ⟨hoperation, hrest⟩
      cases operation with
      | region name body =>
          simp only [Operation.KeygenCoherent] at hoperation
          simp only [operationEnabledGates, List.mem_append] at henabled
          rcases henabled with henabled | henabled
          · exact region_gate hoperation henabled
          · exact ih hrest henabled
      | constrainInstance cell column row =>
          exact ih hrest henabled
      | loadTable table values =>
          exact ih hrest henabled

/-- A coherent region registers every extracted enabled lookup. -/
theorem region_lookup
    {F : Type} {cs : ConstraintSystem F}
    {self : RegionIndex} {body : RegionOperations F}
    (hcoherent :
      body.Forall (RegionOperation.KeygenCoherent cs))
    {enabled : EnabledLookup F}
    (henabled : enabled ∈ regionEnabledLookups self body) :
    enabled.argument ∈ cs.lookups := by
  induction body with
  | nil => simp [regionEnabledLookups] at henabled
  | cons operation rest ih =>
      rw [List.forall_cons] at hcoherent
      cases operation with
      | enableLookup argument selectors row =>
          simp only [RegionOperation.KeygenCoherent] at hcoherent
          simp only [regionEnabledLookups, List.mem_cons] at henabled
          rcases henabled with rfl | henabled
          · exact hcoherent.1
          · exact ih hcoherent.2 henabled
      | assignAdvice column row witness =>
          exact ih hcoherent.2 henabled
      | assignFixed column row value =>
          exact ih hcoherent.2 henabled
      | enableGate gate row =>
          exact ih hcoherent.2 henabled
      | constrainEqual left right =>
          exact ih hcoherent.2 henabled
      | constrainConstant cell value =>
          exact ih hcoherent.2 henabled
      | constrainInstance cell column row =>
          exact ih hcoherent.2 henabled

/-- A coherent operation stream registers every extracted enabled lookup. -/
theorem lookup
    {F : Type} {cs : ConstraintSystem F}
    {operations : Operations F} {i : RegionIndex}
    (hcoherent : OperationsKeygenCoherent cs operations)
    {enabled : EnabledLookup F}
    (henabled : enabled ∈ operationEnabledLookups operations i) :
    enabled.argument ∈ cs.lookups := by
  induction operations generalizing i with
  | nil => simp [operationEnabledLookups] at henabled
  | cons operation rest ih =>
      rw [OperationsKeygenCoherent, List.forall_cons] at hcoherent
      rcases hcoherent with ⟨hoperation, hrest⟩
      cases operation with
      | region name body =>
          simp only [Operation.KeygenCoherent] at hoperation
          simp only [operationEnabledLookups, List.mem_append] at henabled
          rcases henabled with henabled | henabled
          · exact region_lookup hoperation henabled
          · exact ih hrest henabled
      | constrainInstance cell column row =>
          exact ih hrest henabled
      | loadTable table values =>
          exact ih hrest henabled

end OperationsKeygenCoherent

end Zcash.Snark
