import Zcash.Circuits.Action.TopLevel

/-!
# Public statement of a deployed Orchard Action

The Action top-level circuit declares its ten public instance rows and exposes its
complete post-NU6.3 specification over those public values and the remaining private
witness. This module gives the resulting existential statement its protocol-facing
name.
-/

namespace Zcash.Circuits.Action

open Specs.Sinsemilla (Generators)
open Circuit

/--
The public semantic conclusion for one Action: some private witness satisfies the
complete Action specification at the supplied public input.
-/
def Statement (G : Generators) (B : Bases) (inputs : PublicInputs Fp) : Prop :=
  ∃ privateWitness : PrivateWitness,
    SpecPost G B () () (combine inputs privateWitness)

/-- The protocol-facing statement is exactly the statement owned by the Action
top-level circuit. -/
theorem topLevelStatement_iff
    (G : Generators) (B : Bases) (inputs : PublicInputs Fp) :
    (topLevelCircuit G B).Statement inputs ↔ Statement G B inputs :=
  Iff.rfl

/-- The external semantic conclusion for every Action proved in one Halo 2 bundle. -/
def BundleStatement
    (G : Generators) (B : Bases) {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInputs Fp) : Prop :=
  ∀ proofIndex, Statement G B (inputs proofIndex)

end Zcash.Circuits.Action
