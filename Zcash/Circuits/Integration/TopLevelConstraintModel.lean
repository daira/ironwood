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
    {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges k Fp)
    (poly : CommitmentId → Polynomial Fp) :
    ConstraintPolyModel pp.numProofs :=
  let vk := top.toVerifierKey pp urs
  let selectors :=
    canonicalLagrangePolynomials vk.omega
      (top.toVerifierKey_blindingFactors_lt_n pp urs)
  constraintModelOfResolver
    (numProofs := pp.numProofs)
    (k := k)
    vk ch poly
    (permutationSetsOfResolver vk poly)
    (permutationChunksOfResolver vk poly)
    selectors.1 selectors.2.1 selectors.2.2

/-- The top-level canonical model exposes the resolver construction used by its
verification key without requiring consumers to unfold circuit compilation. -/
theorem constraintModel_eq_constraintModelOfResolver
    {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges k Fp)
    (poly : CommitmentId → Polynomial Fp) :
    let selectors :=
      canonicalLagrangePolynomials
        (top.toVerifierKey pp urs).omega
        (top.toVerifierKey_blindingFactors_lt_n pp urs)
    top.constraintModel pp urs ch poly =
      constraintModelOfResolver
        (numProofs := pp.numProofs)
        (k := k)
        (top.toVerifierKey pp urs) ch poly
        (permutationSetsOfResolver
          (top.toVerifierKey pp urs) poly)
        (permutationChunksOfResolver
          (top.toVerifierKey pp urs) poly)
        selectors.1 selectors.2.1 selectors.2.2 := by
  rfl

@[simp] theorem constraintModel_l0
    {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges k Fp)
    (poly : CommitmentId → Polynomial Fp) :
    (top.constraintModel pp urs ch poly).l0 =
      (canonicalLagrangePolynomials
        (top.toVerifierKey pp urs).omega
        (top.toVerifierKey_blindingFactors_lt_n pp urs)).1 := by
  rfl

@[simp] theorem constraintModel_lLast
    {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges k Fp)
    (poly : CommitmentId → Polynomial Fp) :
    (top.constraintModel pp urs ch poly).lLast =
      (canonicalLagrangePolynomials
        (top.toVerifierKey pp urs).omega
        (top.toVerifierKey_blindingFactors_lt_n pp urs)).2.1 := by
  rfl

@[simp] theorem constraintModel_lBlind
    {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges k Fp)
    (poly : CommitmentId → Polynomial Fp) :
    (top.constraintModel pp urs ch poly).lBlind =
      (canonicalLagrangePolynomials
        (top.toVerifierKey pp urs).omega
        (top.toVerifierKey_blindingFactors_lt_n pp urs)).2.2 := by
  rfl

/-- The canonical top-level lookup selectors satisfy the verifier's usable-row
domain laws. -/
theorem resolverLookupDomain
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges top.domainExponent Fp)
    (poly : CommitmentId → Polynomial Fp)
    (husable :
      (top.toVerifierKey pp urs).blindingFactors + 1 <
        (top.toVerifierKey pp urs).n)
    (hrows : Function.Injective
      fun row : Fin (top.toVerifierKey pp urs).n =>
        (top.toVerifierKey pp urs).omega ^ (row : ℕ))
    (hroot :
      (top.toVerifierKey pp urs).omega ^
        (top.toVerifierKey pp urs).n = 1) :
    ResolverLookupDomain
      (top.toVerifierKey pp urs)
      (top.constraintModel pp urs ch poly).l0
      (top.constraintModel pp urs ch poly).lLast
      (top.constraintModel pp urs ch poly).lBlind
      (top.toVerifierKey pp urs).n
      ((top.toVerifierKey pp urs).n -
        (top.toVerifierKey pp urs).blindingFactors - 2) := by
  have hdomain :=
    ResolverLookupDomain.ofCanonicalConstraintModel
      (top.toVerifierKey pp urs)
      (by
        simpa only [Keygen.ProofParams.mergeDerived_k] using ch)
      poly husable hrows hroot
  simpa only [constraintModel, VerifyingKey.constraintModel,
    constraintModelOfResolver] using hdomain

end Halo2.TopLevelCircuit
