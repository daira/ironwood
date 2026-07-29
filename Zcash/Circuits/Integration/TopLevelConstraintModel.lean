import Zcash.Snark.Keygen.Pipeline
import Zcash.Snark.Soundness.Canonical.ConstraintModel

/-!
# Circuit-derived canonical constraint models

This module closes the domain-law boundary between a Clean top-level circuit and
Ironwood's verifier-native canonical constraint model. Arbitrary verification
keys still require an explicit proof that their blinding rows fit the domain;
a key derived from `TopLevelCircuit` carries that fact by construction.
-/

namespace Halo2.TopLevelCircuit

open Zcash.Snark
open Zcash.Arithmetic (Fp URS)
open Zcash.Snark.Keygen
open Halo2 Polynomial

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/--
The canonical resolver model for a circuit's own verification key.

Unlike the arbitrary-key constructor, this interface has no domain-law
argument: domain fitting follows from the `TopLevelCircuit` compilation.
-/
def constraintModel
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (poly : CommitmentId → Polynomial Fp) :
    ConstraintPolyModel (pp.mergeDerived top).numProofs :=
  (top.toVerifierKey pp urs).constraintModel ch poly
    (top.toVerifierKey_blindingFactors_lt_n pp urs)

end Halo2.TopLevelCircuit
