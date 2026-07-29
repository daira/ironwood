import Mathlib
import Zcash.Arithmetic
import Zcash.Snark.Verifier.Expressions
import Zcash.Snark.Verifier.Assemble
import CompPoly.Univariate.ToPoly
import CompPoly.Univariate.Linear

/-!
# Pilot: `Constraints` on the computable representation

A migration of `Zcash.Snark.Soundness.Constraints` from Mathlib `Polynomial Fp` to CompPoly's
`CPolynomial Fp`, with `Zcash.Common.ComputablePolynomial` removed entirely.

What disappears relative to the original: `polynomialEvalData` and its correctness lemma,
`constraintPolysData`/`constraintPolysData_eq`, and `combineConstraintsData`/
`combineConstraintsData_eq`.  Those exist only to re-run a ring-generic definition under a
hand-built computable `CommRing`; `CPolynomial`'s own `CommRing` is already executable, so the
single definition serves both roles.
-/

namespace Zcash.Snark.PilotC

open CompPoly

abbrev CPoly := CPolynomial Fp

/-- The Schwartz–Zippel bad set: the roots of the difference polynomial.  A root multiset is a
specification notion, so this stays on the Mathlib image and is noncomputable — it only ever
appears inside `Prop`s. -/
noncomputable def szBadSet (C : CPoly) : Finset Fp := C.toPoly.roots.toFinset

theorem mem_szBadSet {C : CPoly} {x : Fp} :
    x ∈ szBadSet C ↔ C ≠ 0 ∧ CPolynomial.eval x C = 0 := by
  simp [szBadSet, Polynomial.mem_roots', CPolynomial.toPoly_eq_zero_iff,
    ← CPolynomial.eval_toPoly]

theorem not_mem_szBadSet {C : CPoly} {x : Fp} :
    x ∉ szBadSet C ↔ (C ≠ 0 → CPolynomial.eval x C ≠ 0) := by
  rw [mem_szBadSet, not_and]

/-- Compute avoidance of one Schwartz–Zippel bad set.

Against `Polynomial Fp` this had to test `C.toFinsupp.support = ∅` as a stand-in for `C = 0`,
because Mathlib's decidable equality on polynomials is unavailable.  `CPolynomial` is canonical,
so `C = 0` is decidable and the test is written directly. -/
def szBadSetAvoidance? (C : CPoly) (x : Fp) :
    Option (PLift (x ∉ szBadSet C)) :=
  if hzero : C = 0 then
    some ⟨not_mem_szBadSet.mpr fun hne => absurd hzero hne⟩
  else if heval : CPolynomial.eval x C = 0 then
    none
  else
    some ⟨not_mem_szBadSet.mpr fun _ => heval⟩

theorem szBadSetAvoidance?_isSome_iff (C : CPoly) (x : Fp) :
    (szBadSetAvoidance? C x).isSome ↔ x ∉ szBadSet C := by
  unfold szBadSetAvoidance?
  split <;> rename_i hzero
  · simp [not_mem_szBadSet, hzero]
  · split <;> rename_i heval <;> simp [not_mem_szBadSet, hzero, heval]

/-- Root counting is unchanged: it is a fact about the Mathlib image. -/
theorem szBadSet_card_le (C : CPoly) : (szBadSet C).card ≤ C.natDegree :=
  le_trans (Multiset.toFinset_card_le _)
    (le_of_le_of_eq (Polynomial.card_roots' C.toPoly) (CPolynomial.natDegree_toPoly C).symm)

/-- Lift a gate `Expr` to a polynomial.  This was `noncomputable`; it is now a plain `def`. -/
def Expr.toCPoly (fixedCols adviceCols instanceCols : ℕ → CPoly) :
    Expr Fp → CPoly
  | .constant c => CPolynomial.C c
  | .fixed i => fixedCols i
  | .advice i => adviceCols i
  | .instance i => instanceCols i
  | .negated a => -(Expr.toCPoly fixedCols adviceCols instanceCols a)
  | .sum a b => Expr.toCPoly fixedCols adviceCols instanceCols a
      + Expr.toCPoly fixedCols adviceCols instanceCols b
  | .product a b => Expr.toCPoly fixedCols adviceCols instanceCols a
      * Expr.toCPoly fixedCols adviceCols instanceCols b
  | .scaled a c => Expr.toCPoly fixedCols adviceCols instanceCols a * CPolynomial.C c

/-- The gate expressions lifted to polynomials, in verifier order.  Plain `def`. -/
def gatePolys {n : ℕ} (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (gates : Fin n → Expr Fp) : List CPoly :=
  List.ofFn (fun i : Fin n => Expr.toCPoly fixedCols adviceCols instanceCols (gates i))

/-- The constraint numerator, folded in halo2's `acc * y + v` order.  Plain `def`. -/
def combineGates {n : ℕ} (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (y : Fp) (gates : Fin n → Expr Fp) : CPoly :=
  (gatePolys fixedCols adviceCols instanceCols gates).foldl
    (fun acc p => acc * CPolynomial.C y + p) 0

open CPolynomial in
/-- Every constraint value across the sub-proofs, as polynomials.

`allConstraints` is ring-generic, so instantiating it at `CPolynomial Fp` uses that type's own
executable `CommRing`.  The original needed a second copy of this definition
(`constraintPolysData`) under a hand-built instance, plus an equation relating the two. -/
def constraintPolys {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval CPoly))
    (chunks : Fin np → List (PermSetEval CPoly × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval CPoly × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta : Fp) (chunkLen : ℕ) (l0 lLast lBlind : CPoly) :
    List CPoly :=
  allConstraints fixedCols adviceCols instanceCols (gates.map (Expr.map C)) sets chunks
    (fun p => (lookups p).map (fun lk =>
      (lk.1, lk.2.1.map (Expr.map C), lk.2.2.map (Expr.map C))))
    (C beta) (C gamma) X (C delta) (C theta) chunkLen l0 lLast lBlind

/-- The full constraint fold.  Plain `def`; no `combineConstraintsData` twin. -/
def combineConstraints {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval CPoly))
    (chunks : Fin np → List (PermSetEval CPoly × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval CPoly × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind : CPoly) : CPoly :=
  (constraintPolys fixedCols adviceCols instanceCols gates sets chunks lookups
    beta gamma delta theta chunkLen l0 lLast lBlind).foldl
      (fun acc p => acc * CPolynomial.C y + p) 0

/-! ## Evaluation algebra

CompPoly proves `eval_C` and `eval_mul` but not the additive lemmas.  Rather than pushing every
proof onto the Mathlib image by hand, the missing ones are proved once here and, together with the
existing two, form the simp set the inductions below run on. -/

section EvalAlgebra
variable (x : Fp)

@[simp] theorem eval_zero : CPolynomial.eval x (0 : CPoly) = 0 := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_zero, Polynomial.eval_zero]

@[simp] theorem eval_add (p q : CPoly) :
    CPolynomial.eval x (p + q) = CPolynomial.eval x p + CPolynomial.eval x q := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_add, Polynomial.eval_add,
    ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]

@[simp] theorem eval_neg (p : CPoly) :
    CPolynomial.eval x (-p) = -CPolynomial.eval x p := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_neg, Polynomial.eval_neg,
    ← CPolynomial.eval_toPoly]

attribute [simp] CPolynomial.eval_C CPolynomial.eval_mul

end EvalAlgebra

/-- The lift commutes with evaluation.  The original proved this by `induction e <;> simp_all`
against Mathlib; here the same induction runs after pushing `CPolynomial.eval` onto the Mathlib
image, where the `@[grind =]` transport lemmas do the algebra. -/
theorem Expr.eval_toCPoly (fixedCols adviceCols instanceCols : ℕ → CPoly) (x : Fp)
    (e : Expr Fp) :
    CPolynomial.eval x (Expr.toCPoly fixedCols adviceCols instanceCols e)
      = e.eval (fun i => CPolynomial.eval x (fixedCols i))
          (fun i => CPolynomial.eval x (adviceCols i))
          (fun i => CPolynomial.eval x (instanceCols i)) := by
  induction e <;> simp_all [Expr.toCPoly, Expr.eval]

/-- Evaluation commutes with halo2's `acc * y + v` fold. -/
theorem eval_foldByY (y x : Fp) (acc : CPoly) (ps : List CPoly) :
    CPolynomial.eval x (ps.foldl (fun acc p => acc * CPolynomial.C y + p) acc)
      = (ps.map (fun p => CPolynomial.eval x p)).foldl (fun acc v => acc * y + v)
          (CPolynomial.eval x acc) := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
      simpa using ih (acc * CPolynomial.C y + p)

/-- The combined numerator is the halo2-order `y` fold of the gate evaluations. -/
theorem eval_combineGates {n : ℕ} (fixedCols adviceCols instanceCols : ℕ → CPoly)
    (y : Fp) (gates : Fin n → Expr Fp) (x : Fp) :
    CPolynomial.eval x (combineGates fixedCols adviceCols instanceCols y gates)
      = ((gatePolys fixedCols adviceCols instanceCols gates).map
          (fun p => CPolynomial.eval x p)).foldl (fun acc v => acc * y + v) 0 := by
  simp [combineGates, eval_foldByY]

end Zcash.Snark.PilotC
