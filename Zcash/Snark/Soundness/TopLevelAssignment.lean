import Zcash.Bridge.VkProjection
import Zcash.Circuits.TopLevelKeygen
import Zcash.Snark.Soundness.PolynomialEnvironment

/-!
# Generic assignments for closed top-level circuits

A decoded verifier witness supplies commitment-ID-indexed column polynomials. A
`TopLevelCircuit` supplies the operation stream, V1 placement, blinding rows, and
table-fit proof. This module joins those two circuit-independent views without
accepting an arbitrary verifying key.

The domain exponent and proof index remain protocol parameters: one top-level circuit
is reused for every proof in a bundle. Once `FormalCircuit.toVerifyingKey` is
available, its field equations connect this assignment directly to the verifier-side
resolver.
-/

namespace Zcash.Snark

open Halo2 Polynomial
open Zcash.Circuits

set_option maxHeartbeats 20000

/--
The polynomial assignment for one member of a bundle of the same top-level circuit.

The circuit and domain exponent are indices, not stored choices. In particular there
is no caller-supplied `VerifyingKey`: the eventual decoded constructor uses the key
derived from `top.formalCircuit`.
-/
structure TopLevelAssignment
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (k numProofs : ℕ) where
  proofIndex : Fin numProofs
  polynomial : CommitmentId → Polynomial Fp

namespace TopLevelAssignment

variable
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]
    {top : TopLevelCircuit Fp ConfigInput Config Output}
    {k numProofs : ℕ}

/-- The row-indexed Clean environment for this bundle member. -/
def environment
    (assignment : TopLevelAssignment top k numProofs) : Environment Fp :=
  polynomialEnvironment (Zcash.Bridge.omegaOf k) (top.usableRowsAt k)
    (fun column => assignment.polynomial (.fixedCol column))
    (fun column => assignment.polynomial
      (.adviceCol assignment.proofIndex column))
    (fun column => assignment.polynomial
      (.instanceCol assignment.proofIndex column))

/-- The assignment placed by the circuit's own V1 floor-plan. -/
def placedEnvironment
    (assignment : TopLevelAssignment top k numProofs) :
    Placed Environment Fp :=
  ⟨top.placement, assignment.environment⟩

@[simp] theorem environment_usableRows
    (assignment : TopLevelAssignment top k numProofs) :
    assignment.environment.usableRows = top.usableRowsAt k :=
  rfl

@[simp] theorem environment_fixed
    (assignment : TopLevelAssignment top k numProofs)
    (column : Column .fixed) (row : ℤ) :
    assignment.environment.fixed column row =
      (assignment.polynomial (.fixedCol column.index)).eval
        (Zcash.Bridge.omegaOf k ^ row) :=
  rfl

@[simp] theorem environment_advice
    (assignment : TopLevelAssignment top k numProofs)
    (column : Column .advice) (row : ℤ) :
    assignment.environment.advice column row =
      (assignment.polynomial
        (.adviceCol assignment.proofIndex column.index)).eval
          (Zcash.Bridge.omegaOf k ^ row) :=
  rfl

@[simp] theorem environment_instance
    (assignment : TopLevelAssignment top k numProofs)
    (column : Column .instance) (row : ℤ) :
    assignment.environment.inst column row =
      (assignment.polynomial
        (.instanceCol assignment.proofIndex column.index)).eval
          (Zcash.Bridge.omegaOf k ^ row) :=
  rfl

/--
A fitting circuit domain supplies the synthesis well-formedness premise for this
assignment's environment.
-/
theorem synthesisWellFormed
    (assignment : TopLevelAssignment top k numProofs)
    (hfit : top.FitsAt k) :
    SynthesisWellFormed assignment.environment (top.operations 0) := by
  apply top.synthesisWellFormed k assignment.environment
  · rfl
  · exact hfit

end TopLevelAssignment

end Zcash.Snark
