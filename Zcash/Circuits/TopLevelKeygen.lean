import Zcash.Circuits.TopLevel
import Clean.Halo2.Keygen

/-!
# Keygen data derived from a top-level circuit

The semantic `TopLevelCircuit` stays independent of any verifier implementation.
This module adds the circuit-owned keygen view: pinned constraint system, V1
placement, domain-fit quantities, and the generic proof that a fitting keygen domain
supplies `SynthesisWellFormed`.
-/

namespace Zcash.Circuits

open Halo2

namespace SynthesisWellFormed

variable {F : Type} [FiniteField F]

private theorem accumulator_le_foldl_max (values : List ℕ) (acc : ℕ) :
    acc ≤ values.foldl max acc := by
  induction values generalizing acc with
  | nil => exact Nat.le_refl acc
  | cons value values ih =>
      exact le_trans (Nat.le_max_left acc value) (ih (max acc value))

private theorem member_le_foldl_max (values : List ℕ) (value acc : ℕ)
    (hmember : value ∈ values) :
    value ≤ values.foldl max acc := by
  induction values generalizing acc with
  | nil => simp only [List.not_mem_nil] at hmember
  | cons head tail ih =>
      simp only [List.mem_cons] at hmember
      rcases hmember with hhead | htail
      · rw [hhead]
        exact le_trans (Nat.le_max_right acc head)
          (accumulator_le_foldl_max tail (max acc head))
      · exact ih (max acc head) htail

omit [FiniteField F] in
private theorem loadTable_length_le_usedRows
    (operations : Operations F) (table : TableColumn) (values : List F)
    (hload : Operation.loadTable table values ∈ operations) :
    values.length ≤ Halo2.usedRows operations := by
  let tableLengths := operations.filterMap fun operation =>
    match operation with
    | .loadTable _ loaded => some loaded.length
    | _ => none
  have hlength : values.length ∈ tableLengths := by
    apply List.mem_filterMap.mpr
    exact ⟨.loadTable table values, hload, rfl⟩
  have htable : values.length ≤ tableLengths.foldl max 0 :=
    member_le_foldl_max tableLengths values.length 0 hlength
  unfold Halo2.usedRows
  exact le_trans htable (Nat.le_max_right _ _)

/--
Every table block fits an environment whose usable rows cover the keygen operation
footprint.  This is the generic compiler/layout fact consumed by top-level circuit
closure.
-/
theorem of_usedRows
    (env : Environment F) (operations : Operations F)
    (hrows : Halo2.usedRows operations ≤ env.usableRows) :
    SynthesisWellFormed env operations where
  tablesFit table values hload :=
    le_trans (loadTable_length_le_usedRows operations table values hload) hrows

end SynthesisWellFormed

namespace TopLevelCircuit

variable
    {F : Type} [FiniteField F]
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]

/-- The pinned constraint system derived solely from the closed circuit. -/
def pinnedCS (self : TopLevelCircuit F ConfigInput Config Output) :
    PinnedConstraintSystem F :=
  self.formalCircuit.toPinnedCS self.configInput ()

/-- V1 region starts derived from the circuit's own operation stream. -/
def regionStarts (self : TopLevelCircuit F ConfigInput Config Output) : List ℕ :=
  FloorPlanner.V1.starts (self.operations 0)

/-- The circuit-owned V1 placement function. -/
def placement (self : TopLevelCircuit F ConfigInput Config Output) :
    RegionIndex → ℕ :=
  fun region => self.regionStarts.getD region 0

@[simp] theorem placement_apply
    (self : TopLevelCircuit F ConfigInput Config Output) (region : RegionIndex) :
    self.placement region = self.regionStarts.getD region 0 :=
  rfl

/-- The operation footprint that key generation requires to fit in usable rows. -/
def usedRows (self : TopLevelCircuit F ConfigInput Config Output) : ℕ :=
  Halo2.usedRows (self.operations 0)

/-- The smallest keygen domain exponent derived from this circuit's CS and operations. -/
def domainExponent (self : TopLevelCircuit F ConfigInput Config Output) : ℕ :=
  Halo2.minimalK self.constraintSystem (self.operations 0)

/-- The blinding-row count derived from the circuit's own configure run. -/
def blindingFactors (self : TopLevelCircuit F ConfigInput Config Output) : ℕ :=
  self.constraintSystem.blindingFactors

/-- Halo2's usable-row count at a proposed evaluation-domain exponent. -/
def usableRowsAt (self : TopLevelCircuit F ConfigInput Config Output) (k : ℕ) : ℕ :=
  2 ^ k - self.blindingFactors - 1

/-- The keygen fit assertion for a proposed domain exponent. -/
def FitsAt (self : TopLevelCircuit F ConfigInput Config Output) (k : ℕ) : Prop :=
  self.usedRows + self.blindingFactors + 1 ≤ 2 ^ k

theorem usedRows_le_usableRowsAt
    (self : TopLevelCircuit F ConfigInput Config Output) (k : ℕ)
    (hfit : self.FitsAt k) :
    self.usedRows ≤ self.usableRowsAt k := by
  unfold FitsAt at hfit
  unfold usableRowsAt
  omega

/--
A fitting circuit-owned keygen domain supplies the exact synthesis well-formedness
certificate expected by generic top-level soundness.
-/
theorem synthesisWellFormed
    (self : TopLevelCircuit F ConfigInput Config Output)
    (k : ℕ) (env : Environment F)
    (husable : env.usableRows = self.usableRowsAt k)
    (hfit : self.FitsAt k) :
    SynthesisWellFormed env (self.operations 0) := by
  apply SynthesisWellFormed.of_usedRows
  rw [husable]
  exact self.usedRows_le_usableRowsAt k hfit

end TopLevelCircuit

end Zcash.Circuits
