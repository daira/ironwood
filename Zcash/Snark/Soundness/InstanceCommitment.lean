import Zcash.Snark.Soundness.PolynomialEnvironment
import Zcash.Snark.Soundness.Multiopen.Decode
import Zcash.Snark.Soundness.Deployed.Binding
import Zcash.Snark.Soundness.Multiopen.Compat

/-!
# Public-instance commitment provenance

Halo 2 commits to public-instance values in the Lagrange basis, while the multiopen extractor
returns coefficient vectors in the monomial basis.  This file gives the basis-independent algebra
joining those two views.  It is generic in the evaluation domain, the commitment group, and the
public row vector; the Action circuit only decides which rows form its external statement.
-/

namespace Zcash.Snark

open Polynomial

set_option maxHeartbeats 20000

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The first `n` monomial coefficients of a polynomial. -/
def polynomialCoefficients (n : ℕ) (p : Polynomial Fp) : Fin n → Fp :=
  fun i => p.coeff (i : ℕ)

/-- A polynomial of degree below `n` is reconstructed by its length-`n` coefficient vector. -/
theorem coeffsToPoly_polynomialCoefficients {n : ℕ} {p : Polynomial Fp}
    (hdegree : p.natDegree < n) :
    coeffsToPoly (polynomialCoefficients n p) = p := by
  rw [coeffsToPoly]
  simpa only [polynomialCoefficients, ← Fin.sum_univ_eq_sum_range] using
    (p.as_sum_range_C_mul_X_pow' hdegree).symm

/-- Every row vector is the sum of its scaled coordinate vectors after interpolation. -/
theorem rowPolynomial_eq_sum_single {n : ℕ}
    (omega : Fp) (values : Fin n → Fp) :
    rowPolynomial omega values =
      ∑ i : Fin n, values i • rowPolynomial omega (Pi.single i 1) := by
  let interpolation :=
    Lagrange.interpolate Finset.univ (fun i : Fin n => omega ^ (i : ℕ))
  change interpolation values =
    ∑ i : Fin n, values i • interpolation (Pi.single i 1)
  calc
    interpolation values =
        interpolation (∑ i : Fin n, values i • Pi.single i 1) := by
          congr 1
          funext j
          rw [Fintype.sum_apply]
          symm
          calc
            (∑ i : Fin n, (values i • Pi.single i 1) j) =
                ∑ i : Fin n, Pi.single i (values i) j := by
                  apply Finset.sum_congr rfl
                  intro i _
                  by_cases hij : i = j
                  · subst i
                    simp
                  · simp [Pi.single_eq_of_ne (Ne.symm hij)]
            _ = values j := Fintype.sum_pi_single j values
    _ = ∑ i : Fin n, values i • interpolation (Pi.single i 1) := by
      simp only [map_sum, map_smul]

/-- Taking coefficients commutes with the coordinate decomposition of an interpolated row vector. -/
theorem polynomialCoefficients_rowPolynomial_eq_sum_single {n : ℕ}
    (omega : Fp) (values : Fin n → Fp) :
    polynomialCoefficients n (rowPolynomial omega values) =
      ∑ i : Fin n, values i •
        polynomialCoefficients n (rowPolynomial omega (Pi.single i 1)) := by
  rw [rowPolynomial_eq_sum_single]
  funext j
  simp [polynomialCoefficients]

/-- The monomial coefficient vector of the zero-padded public-instance row polynomial. -/
noncomputable def instanceCoefficients (n : ℕ)
    (omega : Fp) (values : List Fp) : Fin n → Fp :=
  polynomialCoefficients n (instanceRowPolynomial n omega values)

/-- The canonical instance coefficients decode to the zero-padded row polynomial. -/
theorem coeffsToPoly_instanceCoefficients {n : ℕ}
    {omega : Fp} {values : List Fp}
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hn : 0 < n) :
    coeffsToPoly (instanceCoefficients n omega values) =
      instanceRowPolynomial n omega values :=
  coeffsToPoly_polynomialCoefficients (rowPolynomial_natDegree_lt hrows hn)

/--
A Lagrange commitment key compatible with a monomial-basis URS.

The pointwise equation is the setup relation: generator `i` commits to the coefficients of the
Lagrange polynomial which is one at row `i` and zero at every other row.  It is independent of any
circuit or verifying key.
-/
structure LagrangeCommitmentKey (urs : URS G) (omega : Fp) where
  generators : Fin (2 ^ urs.k) → G
  generator_eq : ∀ i, generators i =
    commit urs (polynomialCoefficients (2 ^ urs.k)
      (rowPolynomial omega (Pi.single i 1)))

namespace LagrangeCommitmentKey

/-- Halo 2's public-instance commitment, including its blinding-generator component. -/
def commitRows {urs : URS G} {omega : Fp}
    (key : LagrangeCommitmentKey urs omega)
    (values : Fin (2 ^ urs.k) → Fp) (blind : Fp) : G :=
  commitGen key.generators values + blind • urs.w

/-- A compatible Lagrange commitment is the monomial commitment to the interpolated row polynomial. -/
theorem commitRows_eq {urs : URS G} {omega : Fp}
    (key : LagrangeCommitmentKey urs omega)
    (values : Fin (2 ^ urs.k) → Fp) (blind : Fp) :
    key.commitRows values blind =
      commit urs (polynomialCoefficients (2 ^ urs.k) (rowPolynomial omega values)) +
        blind • urs.w := by
  classical
  rw [commitRows, commitGen]
  simp_rw [key.generator_eq]
  rw [polynomialCoefficients_rowPolynomial_eq_sum_single]
  simp only [commit, Fintype.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

/-- Commit a finite public-instance column after zero-padding it to the full domain. -/
def commitInstance {urs : URS G} {omega : Fp}
    (key : LagrangeCommitmentKey urs omega)
    (values : List Fp) (blind : Fp) : G :=
  key.commitRows (zeroPaddedRows (n := 2 ^ urs.k) values) blind

/-- The finite-column spelling of `commitRows_eq`. -/
theorem commitInstance_eq {urs : URS G} {omega : Fp}
    (key : LagrangeCommitmentKey urs omega)
    (values : List Fp) (blind : Fp) :
    key.commitInstance values blind =
      commit urs (instanceCoefficients (2 ^ urs.k) omega values) +
        blind • urs.w := by
  simpa [commitInstance, instanceCoefficients, instanceRowPolynomial] using
    key.commitRows_eq (zeroPaddedRows (n := 2 ^ urs.k) values) blind

end LagrangeCommitmentKey

/--
Binding an augmented opening of a public-instance commitment identifies all three coordinates, or
computes a nontrivial relation among `(urs.g, urs.u, urs.w)`.
-/
theorem instanceOpening_eq_or_relation
    {urs : URS G} {omega : Fp}
    (key : LagrangeCommitmentKey urs omega)
    (values : List Fp) (blind : Fp)
    (decoded : Fin (2 ^ urs.k) → Fp) (uComp wComp : Fp)
    (hopen :
      commit urs decoded + uComp • urs.u + wComp • urs.w =
        key.commitInstance values blind) :
    (decoded = instanceCoefficients (2 ^ urs.k) omega values ∧
      uComp = 0 ∧ wComp = blind) ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  classical
  let expected := instanceCoefficients (2 ^ urs.k) omega values
  have hcollision :
      commitGen urs.g decoded + uComp • urs.u + wComp • urs.w =
        commitGen urs.g expected + (0 : Fp) • urs.u + blind • urs.w := by
    rw [← commit_eq_commitGen, ← commit_eq_commitGen]
    simpa [expected, key.commitInstance_eq values blind] using hopen
  by_cases heq : decoded = expected ∧ uComp = 0 ∧ wComp = blind
  · exact Or.inl heq
  · exact Or.inr <| HasNontrivialRelation.of_nontrivialRelation <|
      NontrivialRelation.ofCombinationCollision hcollision heq

/--
At the polynomial interface, an augmented opening of the statement-derived instance commitment is
the canonical zero-padded row polynomial, or it computes the same AGM relation.
-/
theorem coeffsToPoly_eq_instanceRowPolynomial_or_relation
    {urs : URS G} {omega : Fp}
    (key : LagrangeCommitmentKey urs omega)
    (values : List Fp) (blind : Fp)
    (decoded : Fin (2 ^ urs.k) → Fp) (uComp wComp : Fp)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) => omega ^ (i : ℕ))
    (hopen :
      commit urs decoded + uComp • urs.u + wComp • urs.w =
        key.commitInstance values blind) :
    coeffsToPoly decoded =
        instanceRowPolynomial (2 ^ urs.k) omega values ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases instanceOpening_eq_or_relation key values blind decoded uComp wComp hopen with
    hcoordinates | hrelation
  · exact Or.inl <| by
      rw [hcoordinates.1]
      exact coeffsToPoly_instanceCoefficients hrows (Nat.two_pow_pos urs.k)
  · exact Or.inr hrelation

end Zcash.Snark
