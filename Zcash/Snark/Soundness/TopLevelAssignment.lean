import Zcash.Bridge.VkProjection
import Zcash.Circuits.TopLevelKeygen
import Zcash.Snark.Soundness.PolynomialEnvironment

/-!
# Generic assignments for closed top-level circuits

A decoded verifier witness supplies commitment-ID-indexed column polynomials. A
`TopLevelCircuit` supplies the operation stream, V1 placement, blinding rows, and
table-fit proof. This module joins those two circuit-independent views without
accepting an arbitrary verifying key.

The domain exponent comes from the top-level circuit's own keygen inputs. One
top-level circuit is reused for every proof in a bundle, and indexing the assignment
by its member prevents a bundle construction from silently selecting a different
member's columns. A decoded constructor connects this shell to the verifier-side
resolver using the key derived from the formal circuit; no accepted key is a free
input to this type.
-/

namespace Zcash.Snark

open Halo2 Polynomial
open Zcash.Circuits

set_option maxHeartbeats 20000

/--
The polynomial assignment for one member of a bundle of the same top-level circuit.

The circuit is an index, not a stored choice. In particular there is no
caller-supplied domain exponent or `VerifyingKey`: decoded constructors use the key
derived from `top.formalCircuit`.
-/
structure TopLevelAssignment
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (numProofs : ℕ) (proofIndex : Fin numProofs) where
  polynomial : CommitmentId → Polynomial Fp

namespace TopLevelAssignment

/--
One assignment for every proof in a bundle.

The dependent member index ensures that the assignment at `proofIndex` resolves
exactly that member's advice and instance columns.
-/
abbrev Bundle
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (numProofs : ℕ) :=
  (proofIndex : Fin numProofs) →
    TopLevelAssignment top numProofs proofIndex

variable
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]
    {top : TopLevelCircuit Fp ConfigInput Config Output}
    {numProofs : ℕ} {proofIndex : Fin numProofs}

/-- The circuit-derived domain generator has exact order `2^k`. -/
theorem domainRoot
    (hbound : top.domainExponent < 33) :
    Zcash.Bridge.omegaOf top.domainExponent ^
      (2 ^ top.domainExponent) = 1 := by
  simpa using Zcash.Bridge.omegaOf_domain
    top.domainExponent 1 (by omega)

/-- Circuit-derived domain row names are injective. -/
theorem domainRowsInjective
    (hbound : top.domainExponent < 33) :
    Function.Injective fun row : Fin (2 ^ top.domainExponent) =>
      Zcash.Bridge.omegaOf top.domainExponent ^ (row : ℕ) :=
  Zcash.Bridge.omegaOf_powers_injective
    top.domainExponent (by omega)

/-- The circuit-derived domain size is nonzero in the verifier scalar field. -/
theorem domainSizeCastNeZero
    (hbound : top.domainExponent < 33) :
    (((2 ^ top.domainExponent : ℕ) : Fp)) ≠ 0 :=
  Zcash.Bridge.domainSize_cast_ne_zero
    top.domainExponent (by omega)

/-- A fitting top-level circuit has fewer blinding rows than domain rows. -/
theorem blindingFactors_lt_domainSize
    (hbound : top.domainExponent < 33) :
    top.blindingFactors < 2 ^ top.domainExponent :=
  top.blindingFactors_lt_domainSize top.domainExponent
    (top.fitsAt_domainExponent hbound)

/--
A top-level circuit with a nonempty operation footprint has a nonempty active
prefix before its final usable row.
-/
theorem blindingFactors_succ_lt_domainSize
    (hbound : top.domainExponent < 33)
    (hused : 0 < top.usedRows) :
    top.blindingFactors + 1 < 2 ^ top.domainExponent :=
  top.blindingFactors_succ_lt_domainSize top.domainExponent
    (top.fitsAt_domainExponent hbound) hused

/-- The row-indexed Clean environment for this bundle member. -/
def environment
    (assignment : TopLevelAssignment top numProofs proofIndex) : Environment Fp :=
  polynomialEnvironment (Zcash.Bridge.omegaOf top.domainExponent)
    (top.usableRowsAt top.domainExponent)
    (fun column => assignment.polynomial (.fixedCol column))
    (fun column => assignment.polynomial
      (.adviceCol proofIndex column))
    (fun column => assignment.polynomial
      (.instanceCol proofIndex column))

/-- The assignment placed by the circuit's own V1 floor-plan. -/
def placedEnvironment
    (assignment : TopLevelAssignment top numProofs proofIndex) :
    Placed Environment Fp :=
  ⟨top.placement, assignment.environment⟩

@[simp] theorem environment_usableRows
    (assignment : TopLevelAssignment top numProofs proofIndex) :
    assignment.environment.usableRows =
      top.usableRowsAt top.domainExponent :=
  rfl

@[simp] theorem environment_fixed
    (assignment : TopLevelAssignment top numProofs proofIndex)
    (column : Column .fixed) (row : ℤ) :
    assignment.environment.fixed column row =
      (assignment.polynomial (.fixedCol column.index)).eval
        (Zcash.Bridge.omegaOf top.domainExponent ^ row) :=
  rfl

@[simp] theorem environment_advice
    (assignment : TopLevelAssignment top numProofs proofIndex)
    (column : Column .advice) (row : ℤ) :
    assignment.environment.advice column row =
      (assignment.polynomial
        (.adviceCol proofIndex column.index)).eval
          (Zcash.Bridge.omegaOf top.domainExponent ^ row) :=
  rfl

@[simp] theorem environment_instance
    (assignment : TopLevelAssignment top numProofs proofIndex)
    (column : Column .instance) (row : ℤ) :
    assignment.environment.inst column row =
      (assignment.polynomial
        (.instanceCol proofIndex column.index)).eval
          (Zcash.Bridge.omegaOf top.domainExponent ^ row) :=
  rfl

/--
A fitting circuit domain supplies the synthesis well-formedness premise for this
assignment's environment.
-/
theorem synthesisWellFormed
    (assignment : TopLevelAssignment top numProofs proofIndex)
    (hbound : top.domainExponent < 33) :
    SynthesisWellFormed assignment.environment (top.operations 0) := by
  apply top.synthesisWellFormed top.domainExponent assignment.environment
  · rfl
  · exact top.fitsAt_domainExponent hbound

end TopLevelAssignment

end Zcash.Snark
