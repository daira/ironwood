import Mathlib
import Zcash.Arithmetic
import Zcash.Snark.Verifier.Expressions
import Zcash.Snark.Verifier.Assemble
import CompPoly.Univariate.ToPoly
import CompPoly.Univariate.Linear
import CompPoly.Univariate.Roots.Enumeration

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
open CPolynomial.Roots.FiniteField
open Zcash.Arithmetic (scalarFieldOrder)

abbrev CPoly := CPolynomial Fp

/-! ## Root theory

Mathlib's root API, ported to `CPolynomial` once here.  `roots` is *computable*: it is an
enumeration filter, guarded at zero so it keeps Mathlib's convention that the zero polynomial has
no roots.  Nobody runs it -- the bad-set predicate is decided by a single evaluation -- but keeping
it computable means it can never poison a downstream `def`, which is the failure mode that
dominates this codebase. -/

/-- `Fp` enumerated by its residues. -/
def fpEnumeration : FieldEnumeration Fp where
  size := scalarFieldOrder
  elem := fun i => (i.val : Fp)
  complete := fun a => ⟨⟨a.val, ZMod.val_lt a⟩, by simp⟩

/-- The distinct roots of a computable polynomial. -/
def roots (p : CPoly) : Finset Fp :=
  if p = 0 then ∅ else (rootsInFieldByEnumeration fpEnumeration p).toList.toFinset

@[simp] theorem roots_zero : roots (0 : CPoly) = ∅ := by simp [roots]

theorem mem_roots {p : CPoly} {x : Fp} (hp : p ≠ 0) :
    x ∈ roots p ↔ CPolynomial.eval x p = 0 := by
  rw [roots, if_neg hp, List.mem_toFinset]
  exact ⟨fun h => rootsInFieldByEnumeration_sound h,
    fun h => rootsInFieldByEnumeration_complete _ h⟩

/-- The bridge to the Mathlib image: the two agree, so every Mathlib root theorem transfers. -/
theorem roots_eq_toFinset (p : CPoly) : roots p = p.toPoly.roots.toFinset := by
  by_cases hp : p = 0
  · simp [hp, CPolynomial.toPoly_zero]
  · ext x
    rw [mem_roots hp, Multiset.mem_toFinset,
      Polynomial.mem_roots (by rwa [Ne, CPolynomial.toPoly_eq_zero_iff]),
      Polynomial.IsRoot.def, ← CPolynomial.eval_toPoly]

/-- **Root counting.** A polynomial has at most `natDegree` distinct roots. -/
theorem card_roots_le (p : CPoly) : (roots p).card ≤ p.natDegree := by
  rw [roots_eq_toFinset, CPolynomial.natDegree_toPoly]
  exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)

/-! ## Degree arithmetic -/

@[simp] theorem toPoly_pow (p : CPoly) (n : ℕ) : (p ^ n).toPoly = p.toPoly ^ n := by
  induction n with
  | zero => simp [CPolynomial.toPoly_one]
  | succ n ih => rw [pow_succ, pow_succ, CPolynomial.toPoly_mul, ih]

theorem natDegree_sub_le (p q : CPoly) :
    (p - q).natDegree ≤ max p.natDegree q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly,
    CPolynomial.toPoly_sub]
  exact Polynomial.natDegree_sub_le _ _

theorem natDegree_mul_le (p q : CPoly) :
    (p * q).natDegree ≤ p.natDegree + q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly,
    CPolynomial.toPoly_mul]
  exact Polynomial.natDegree_mul_le

theorem natDegree_X_pow_le (n : ℕ) : ((CPolynomial.X : CPoly) ^ n).natDegree ≤ n := by
  rw [CPolynomial.natDegree_toPoly]
  simp [CPolynomial.X_toPoly]

theorem natDegree_one_le : ((1 : CPoly)).natDegree ≤ 0 := by
  rw [CPolynomial.natDegree_toPoly]
  simp [CPolynomial.toPoly_one]

/-- The Schwartz–Zippel bad set: the roots of the difference polynomial.  A root multiset is a
specification notion, so this stays on the Mathlib image and is noncomputable — it only ever
appears inside `Prop`s. -/
def szBadSet (C : CPoly) : Finset Fp := roots C

theorem mem_szBadSet {C : CPoly} {x : Fp} :
    x ∈ szBadSet C ↔ C ≠ 0 ∧ CPolynomial.eval x C = 0 := by
  rw [szBadSet]
  constructor
  · intro h
    have hC : C ≠ 0 := by
      intro h0
      rw [h0, roots_zero] at h
      simp at h
    exact ⟨hC, (mem_roots hC).mp h⟩
  · rintro ⟨hC, hx⟩
    exact (mem_roots hC).mpr hx

theorem not_mem_szBadSet {C : CPoly} {x : Fp} :
    x ∉ szBadSet C ↔ (C ≠ 0 → CPolynomial.eval x C ≠ 0) := by
  rw [mem_szBadSet, not_and]

/-- Bad-set membership is decidable without ever forming the root set: `C = 0` is decidable
because `CPolynomial` is canonical, and the other conjunct is one evaluation.  This is why
`szBadSet` itself has no reason to be computable -- nothing needs the set, only this predicate
and the cardinality bound. -/
instance decidableMemSzBadSet (C : CPoly) (x : Fp) : Decidable (x ∈ szBadSet C) :=
  decidable_of_iff _ mem_szBadSet.symm

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
  card_roots_le C

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

@[simp] theorem eval_X : CPolynomial.eval x (CPolynomial.X : CPoly) = x := by
  rw [CPolynomial.eval_toPoly, CPolynomial.X_toPoly, Polynomial.eval_X]

@[simp] theorem eval_pow (p : CPoly) (n : ℕ) :
    CPolynomial.eval x (p ^ n) = CPolynomial.eval x p ^ n := by
  induction n with
  | zero => simp [CPolynomial.eval_one]
  | succ n ih => rw [pow_succ, pow_succ, CPolynomial.eval_mul, ih]

attribute [simp] CPolynomial.eval_C CPolynomial.eval_mul CPolynomial.eval_one
  CPolynomial.eval_sub

/-- `toPoly` is injective.  CompPoly states this as `toPolyLinearEquiv.injective`, whose hypothesis
is phrased through the bundled coercion; this restates it directly on `toPoly` so callers do not
need a `change` at every use. -/
theorem toPoly_injective {p q : CPoly} (h : p.toPoly = q.toPoly) : p = q :=
  CPolynomial.toPolyLinearEquiv.injective h

/-- The constant embedding as a ring hom.  Mathlib has `Polynomial.C` bundled; CompPoly's `C` is a
bare function, and the bundled form is what every `eval₂`/`comp`-shaped construction needs. -/
def CRingHom : Fp →+* CPoly where
  toFun := CPolynomial.C
  map_one' := by
    apply toPoly_injective; simp [CPolynomial.C_toPoly, CPolynomial.toPoly_one]
  map_mul' := by
    intro a b
    apply toPoly_injective; simp [CPolynomial.C_toPoly, CPolynomial.toPoly_mul]
  map_zero' := by
    apply toPoly_injective; simp [CPolynomial.toPoly_zero]
  map_add' := by
    intro a b
    apply toPoly_injective; simp [CPolynomial.C_toPoly, CPolynomial.toPoly_add]

@[simp] theorem coe_CRingHom : ⇑CRingHom = CPolynomial.C := rfl

/-- Evaluation at `x` as a ring hom.  `allConstraints_map` and every other ring-hom-shaped
transport in the verifier layer needs this; on the Mathlib side it is `Polynomial.evalRingHom`. -/
def evalRingHom (x : Fp) : CPoly →+* Fp where
  toFun := CPolynomial.eval x
  map_one' := CPolynomial.eval_one x
  map_mul' := fun p q => CPolynomial.eval_mul p q x
  map_zero' := eval_zero x
  map_add' := eval_add x

@[simp] theorem coe_evalRingHom (x : Fp) :
    ⇑(evalRingHom x) = CPolynomial.eval x := rfl

attribute [simp] CPolynomial.toPoly_add CPolynomial.toPoly_mul CPolynomial.toPoly_sub
  CPolynomial.toPoly_neg CPolynomial.toPoly_one CPolynomial.toPoly_zero
  CPolynomial.C_toPoly CPolynomial.X_toPoly

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

/-! ## The vanishing / quotient check -/

/-- The verifier's quotient check at the challenge `x`. -/
@[reducible] def quotientCheck (numerator h : CPoly) (n : ℕ) (x : Fp) : Prop :=
  CPolynomial.eval x numerator = CPolynomial.eval x h * (x ^ n - 1)

theorem quotientCheck_complete (numerator h : CPoly) (n : ℕ)
    (heq : numerator = h * (CPolynomial.X ^ n - 1)) (x : Fp) :
    quotientCheck numerator h n x := by
  simp [quotientCheck, heq]

/-- When the identity fails, the accepting challenges are exactly the bad set. -/
theorem quotientCheck_filter_eq_szBadSet (numerator h : CPoly) (n : ℕ)
    (hne : numerator ≠ h * (CPolynomial.X ^ n - 1)) :
    (Finset.univ.filter fun x => quotientCheck numerator h n x)
      = szBadSet (numerator - h * (CPolynomial.X ^ n - 1)) := by
  have hC : numerator - h * (CPolynomial.X ^ n - 1) ≠ 0 := sub_ne_zero.mpr hne
  ext x
  simp [mem_szBadSet, hC, quotientCheck, sub_eq_zero]

/-- **Constraint soundness (Schwartz–Zippel).** -/
theorem quotientCheck_sound (numerator h : CPoly) (n : ℕ)
    (hne : numerator ≠ h * (CPolynomial.X ^ n - 1)) :
    ((Finset.univ.filter fun x => quotientCheck numerator h n x).card : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0)
      ≤ ((numerator - h * (CPolynomial.X ^ n - 1)).natDegree : ℚ≥0) / (scalarFieldOrder : ℚ≥0) := by
  rw [quotientCheck_filter_eq_szBadSet numerator h n hne]
  gcongr
  exact_mod_cast szBadSet_card_le _

/-- The concrete degree bound at the vanishing-check site. -/
theorem szBadSet_quotient_card_le (numerator h : CPoly) (n : ℕ) :
    (szBadSet (numerator - h * (CPolynomial.X ^ n - 1))).card
      ≤ max numerator.natDegree (h.natDegree + n) := by
  refine (szBadSet_card_le _).trans ((natDegree_sub_le _ _).trans ?_)
  refine max_le_max le_rfl ((natDegree_mul_le _ _).trans (Nat.add_le_add_left ?_ _))
  exact (natDegree_sub_le _ _).trans (by
    simpa using max_le (natDegree_X_pow_le n) (le_trans natDegree_one_le (Nat.zero_le n)))

/-- **The constraint identity, derived from acceptance.** -/
theorem constraint_identity_of_accept (numerator h : CPoly) (n : ℕ) (x : Fp)
    (hcheck : quotientCheck numerator h n x)
    (hgood : numerator ≠ h * (CPolynomial.X ^ n - 1) →
      CPolynomial.eval x (numerator - h * (CPolynomial.X ^ n - 1)) ≠ 0) :
    numerator = h * (CPolynomial.X ^ n - 1) := by
  by_contra hne
  apply hgood hne
  simp only [quotientCheck] at hcheck
  simp [hcheck]

/-- The same, shaped for callers whose fold equation ends in a relation branch. -/
theorem constraint_identity_of_hfold {numerator hpoly : CPoly} {n : ℕ} {x : Fp} {R : Prop}
    (hfold : CPolynomial.eval x numerator
        = CPolynomial.eval x hpoly * (x ^ n - 1) ∨ R)
    (hgood : numerator ≠ hpoly * (CPolynomial.X ^ n - 1) →
      CPolynomial.eval x (numerator - hpoly * (CPolynomial.X ^ n - 1)) ≠ 0) :
    numerator = hpoly * (CPolynomial.X ^ n - 1) ∨ R := by
  rcases hfold with h | hr
  · exact Or.inl (constraint_identity_of_accept numerator hpoly n x h hgood)
  · exact Or.inr hr

/-! ## Evaluation of the assembled constraint list -/

open CPolynomial in
/-- Evaluating the constraint polynomials lands back on the verifier's own constraint list.
This is `allConstraints_map` at `evalRingHom`, exactly as the Mathlib version used
`Polynomial.evalRingHom`. -/
theorem eval_constraintPolys {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval CPoly))
    (chunks : Fin np → List (PermSetEval CPoly × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval CPoly × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta : Fp) (chunkLen : ℕ) (l0 lLast lBlind : CPoly) (x : Fp) :
    (constraintPolys fixedCols adviceCols instanceCols gates sets chunks lookups
        beta gamma delta theta chunkLen l0 lLast lBlind).map (fun q => CPolynomial.eval x q)
      = allConstraints (fun i => CPolynomial.eval x (fixedCols i))
          (fun p i => CPolynomial.eval x (adviceCols p i))
          (fun p i => CPolynomial.eval x (instanceCols p i)) gates
          (fun p => (sets p).map (PermSetEval.map (fun q => CPolynomial.eval x q)))
          (fun p => (chunks p).map (fun c => (c.1.map (fun q => CPolynomial.eval x q),
            c.2.map (fun q => (CPolynomial.eval x q.1, CPolynomial.eval x q.2)))))
          (fun p => (lookups p).map (fun lk =>
            (lk.1.map (fun q => CPolynomial.eval x q), lk.2.1, lk.2.2)))
          beta gamma x delta theta chunkLen (CPolynomial.eval x l0)
          (CPolynomial.eval x lLast) (CPolynomial.eval x lBlind) := by
  have hmap : (fun q : CPoly => CPolynomial.eval x q) = ⇑(evalRingHom x) := rfl
  rw [constraintPolys, hmap, allConstraints_map (evalRingHom x)]
  simp [List.map_map, Function.comp_def, Expr.map_map, Expr.map_id, PermSetEval.map,
    LookupEval.map]

/-- The numerator at `x` is the `y` fold of the verifier's own constraint values. -/
theorem eval_combineConstraints {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval CPoly))
    (chunks : Fin np → List (PermSetEval CPoly × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval CPoly × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta y : Fp) (chunkLen : ℕ) (l0 lLast lBlind : CPoly) (x : Fp) :
    CPolynomial.eval x (combineConstraints fixedCols adviceCols instanceCols gates sets chunks
        lookups beta gamma delta theta y chunkLen l0 lLast lBlind)
      = (allConstraints (fun i => CPolynomial.eval x (fixedCols i))
          (fun p i => CPolynomial.eval x (adviceCols p i))
          (fun p i => CPolynomial.eval x (instanceCols p i)) gates
          (fun p => (sets p).map (PermSetEval.map (fun q => CPolynomial.eval x q)))
          (fun p => (chunks p).map (fun c => (c.1.map (fun q => CPolynomial.eval x q),
            c.2.map (fun q => (CPolynomial.eval x q.1, CPolynomial.eval x q.2)))))
          (fun p => (lookups p).map (fun lk =>
            (lk.1.map (fun q => CPolynomial.eval x q), lk.2.1, lk.2.2)))
          beta gamma x delta theta chunkLen (CPolynomial.eval x l0)
          (CPolynomial.eval x lLast) (CPolynomial.eval x lBlind)).foldl
          (fun acc v => acc * y + v) 0 := by
  rw [combineConstraints, eval_foldByY, eval_constraintPolys]
  simp

/-! ## Reading individual constraints off the assembled list -/

open CPolynomial in
/-- A permutation constraint of one sub-proof is one of the polynomial constraints. -/
theorem mem_constraintPolys_of_mem_permutationExpressions {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval CPoly))
    (chunks : Fin np → List (PermSetEval CPoly × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval CPoly × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta : Fp) (chunkLen : ℕ) (l0 lLast lBlind : CPoly)
    (p : Fin np) {v : CPoly}
    (h : v ∈ permutationExpressions (sets p) (chunks p) (C beta) (C gamma) X (C delta) chunkLen
      l0 lLast lBlind) :
    v ∈ constraintPolys fixedCols adviceCols instanceCols gates sets chunks lookups
        beta gamma delta theta chunkLen l0 lLast lBlind := by
  rw [constraintPolys]
  apply mem_allConstraints_of_mem_subProofConstraints (p := p)
  apply mem_subProofConstraints_of_mem_permutationExpressions
  exact h

open CPolynomial in
/-- A lookup constraint of one sub-proof is one of the polynomial constraints. -/
theorem mem_constraintPolys_of_mem_lookupExpressions {np : ℕ} (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin np → ℕ → CPoly) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval CPoly))
    (chunks : Fin np → List (PermSetEval CPoly × List (CPoly × CPoly)))
    (lookups : Fin np → List (LookupEval CPoly × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta : Fp) (chunkLen : ℕ) (l0 lLast lBlind : CPoly)
    (p : Fin np) {lk : LookupEval CPoly × List (Expr Fp) × List (Expr Fp)}
    (hlk : lk ∈ lookups p) {v : CPoly}
    (h : v ∈ lookupExpressions lk.1 (lk.2.1.map (Expr.map C)) (lk.2.2.map (Expr.map C))
      fixedCols (adviceCols p) (instanceCols p) (C theta) (C beta) (C gamma) l0 lLast lBlind) :
    v ∈ constraintPolys fixedCols adviceCols instanceCols gates sets chunks lookups
        beta gamma delta theta chunkLen l0 lLast lBlind := by
  have h1 : v ∈ subProofConstraints fixedCols (adviceCols p) (instanceCols p)
      (gates.map (Expr.map C)) (sets p) (chunks p)
      ((lookups p).map (fun l => (l.1, l.2.1.map (Expr.map C), l.2.2.map (Expr.map C))))
      (C beta) (C gamma) X (C delta) (C theta) chunkLen l0 lLast lBlind :=
    mem_subProofConstraints_of_mem_lookupExpressions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (List.mem_map_of_mem hlk) h
  rw [constraintPolys]
  exact mem_allConstraints_of_mem_subProofConstraints _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p h1

/-- The gate fold at the claimed evaluations satisfies the verifier's quotient check. -/
theorem quotientCheck_of_claimed {ng : ℕ}
    (fixedCols adviceCols instanceCols : ℕ → CPoly) (y : Fp) (gates : Fin ng → Expr Fp)
    (hpoly : CPoly) (deg : ℕ) (x : Fp)
    (fixedClaimed adviceClaimed instanceClaimed : ℕ → Fp)
    (hfixed : ∀ i, CPolynomial.eval x (fixedCols i) = fixedClaimed i)
    (hadvice : ∀ i, CPolynomial.eval x (adviceCols i) = adviceClaimed i)
    (hinstance : ∀ i, CPolynomial.eval x (instanceCols i) = instanceClaimed i)
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval fixedClaimed adviceClaimed instanceClaimed)).foldl
          (fun acc v => acc * y + v) 0 = CPolynomial.eval x hpoly * (x ^ deg - 1)) :
    quotientCheck (combineGates fixedCols adviceCols instanceCols y gates) hpoly deg x := by
  have hf : (fun k => CPolynomial.eval x (fixedCols k)) = fixedClaimed := funext hfixed
  have ha : (fun k => CPolynomial.eval x (adviceCols k)) = adviceClaimed := funext hadvice
  have hi : (fun k => CPolynomial.eval x (instanceCols k)) = instanceClaimed := funext hinstance
  rw [quotientCheck, eval_combineGates]
  simp only [gatePolys, List.map_ofFn, Function.comp_def, Expr.eval_toCPoly, hf, ha, hi]
  exact hfold

end Zcash.Snark.PilotC
