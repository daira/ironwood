import Mathlib.Tactic

/-!
# Circuit and proof shapes

`CircuitShape` contains the counts fixed by a circuit and therefore shared by its
verifying key and every proof made against that key. `ProofParams` contains the two
counts chosen for one proof invocation. `Shape` combines the two for data structures
whose complete finite layout depends on both.
-/

namespace Zcash.Snark

/-- Counts fixed by a circuit and its verifying key. -/
structure CircuitShape where
  k : ℕ
  numAdviceColumns : ℕ
  numLookups : ℕ
  numPermutationSets : ℕ
  numPermutationColumns : ℕ
  numQuotientPieces : ℕ
  numInstanceQueries : ℕ
  numAdviceQueries : ℕ
  numFixedQueries : ℕ
deriving DecidableEq, Repr

/-- Counts chosen for one proof invocation rather than fixed by the circuit. -/
structure ProofParams where
  numProofs : ℕ
  numPointSets : ℕ
deriving DecidableEq, Repr

/-- The complete finite layout of a proof: its circuit shape plus invocation parameters. -/
structure Shape extends CircuitShape where
  numProofs : ℕ
  numPointSets : ℕ
deriving DecidableEq, Repr

instance : Coe Shape CircuitShape :=
  ⟨Shape.toCircuitShape⟩

/-- Extend circuit-fixed counts with the parameters of one proof invocation. -/
def CircuitShape.withProofParams (shape : CircuitShape) (pp : ProofParams) : Shape :=
  { toCircuitShape := shape
    numProofs := pp.numProofs
    numPointSets := pp.numPointSets }

@[simp] theorem CircuitShape.withProofParams_toCircuitShape
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).toCircuitShape = shape := by
  simp only [CircuitShape.withProofParams]

@[simp] theorem CircuitShape.withProofParams_numProofs
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).numProofs = pp.numProofs := by
  simp only [CircuitShape.withProofParams]

@[simp] theorem CircuitShape.withProofParams_numPointSets
    (shape : CircuitShape) (pp : ProofParams) :
    (shape.withProofParams pp).numPointSets = pp.numPointSets := by
  simp only [CircuitShape.withProofParams]

end Zcash.Snark
