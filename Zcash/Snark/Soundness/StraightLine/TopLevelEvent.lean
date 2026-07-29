import Zcash.Snark.Soundness.Composition.StraightLineConstraint
import Zcash.Snark.Soundness.StraightLine.TopLevelTerminal

/-!
# Straight-line semantic events for any top-level circuit

These predicates connect the circuit-independent straight-line constraint event
to the `Statement` owned by an arbitrary `TopLevelCircuit`. They contain no
circuit-specific correctness argument or numerical budget.
-/

namespace Zcash.Snark

open Halo2 Keygen

local instance topLevelStraightLineEventInhabitedVesta : Inhabited VestaG := ⟨0⟩

/-- The circuit statement or an explicit relation over the run's basis. -/
def topLevelStatementOrRelationDecoded
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived top))
    (inputs : Fin (pp.mergeDerived top).numProofs → PublicInput Fp) :
    (AugmentedIndex (2 ^ (pp.mergeDerived top).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived top) family.init.length 10
        + 3 * (pp.mergeDerived top).k) → Fp) → Prop :=
  fun basis _ =>
    Nonempty ((∀ proofIndex, top.Statement (inputs proofIndex)) ⊕'
      NontrivialRelation (F := Fp)
        (ursOfAugmentedBasis (pp.mergeDerived top).k basis).g
        (ursOfAugmentedBasis (pp.mergeDerived top).k basis).u
        (ursOfAugmentedBasis (pp.mergeDerived top).k basis).w)

/-- The exact semantic target: the circuit statement holds for every bundled proof. -/
def topLevelBundleStatementDecoded
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived top))
    (inputs : Fin (pp.mergeDerived top).numProofs → PublicInput Fp) :
    (AugmentedIndex (2 ^ (pp.mergeDerived top).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived top) family.init.length 10
        + 3 * (pp.mergeDerived top).k) → Fp) → Prop :=
  fun _ _ => ∀ proofIndex, top.Statement (inputs proofIndex)

/-- Runs on which an executable terminal finder returns relation coefficients. -/
def straightLineTerminalRelationEvent
    {shape : Shape}
    (family : ComputedStraightLineDeployedFSFamily shape)
    (finder :
      (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis)) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)) :=
  {q | (finder q.1 q.2).isSome}

end Zcash.Snark
