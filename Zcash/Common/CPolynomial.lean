import Zcash.Arithmetic
import CompPoly.Univariate.ToPoly
import CompPoly.Univariate.Linear
import CompPoly.Univariate.Roots.Enumeration

/-!
# General theory for the computable polynomial representation

`CompPoly.CPolynomial R` is `{ p : Array R // no trailing zeros }`: a canonical representation, so
`DecidableEq` is available and every ring operation is executable.  `CPolynomial.toPoly` is one
half of a proven ring isomorphism onto Mathlib's `Polynomial R`, which is what lets the two views
be identified freely.

This file collects the theory the Zcash development needs on top of what CompPoly already proves.
Everything in the `CompPoly.CPolynomial` namespace below is stated generically and is intended to
be upstreamed; it is kept here only so the migration does not block on an external repository.
The Zcash-specific part is the `Fp` instantiation at the end.

## Why this exists at all

Mathlib's `Polynomial` instances live in a `noncomputable section`.  A definition that touches
one becomes `noncomputable`, and that marker propagates through every downstream definition
without being visible at any of their definition sites.  Nothing here is `noncomputable`.
-/

namespace CompPoly.CPolynomial

variable {R : Type*}

/-! ## Evaluation algebra

CompPoly proves `eval_C`, `eval_mul`, `eval_one` and `eval_sub`; the additive and `X`/`pow` cases
are proved here.  Together they form a simp set that discharges the evaluation inductions in the
verifier layer without any manual transport to the Mathlib image. -/

@[simp]
theorem eval_zero [Semiring R] [BEq R] [LawfulBEq R] (x : R) :
    eval x (0 : CPolynomial R) = 0 := by
  rw [eval_toPoly, toPoly_zero, Polynomial.eval_zero]

@[simp]
theorem eval_add [Semiring R] [BEq R] [LawfulBEq R] (x : R) (p q : CPolynomial R) :
    eval x (p + q) = eval x p + eval x q := by
  rw [eval_toPoly, toPoly_add, Polynomial.eval_add, ← eval_toPoly, ← eval_toPoly]

@[simp]
theorem eval_neg [Ring R] [BEq R] [LawfulBEq R] (x : R) (p : CPolynomial R) :
    eval x (-p) = -eval x p := by
  rw [eval_toPoly, toPoly_neg, Polynomial.eval_neg, ← eval_toPoly]

@[simp]
theorem eval_X [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (x : R) :
    eval x (X : CPolynomial R) = x := by
  rw [eval_toPoly, X_toPoly, Polynomial.eval_X]

@[simp]
theorem eval_pow [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (x : R) (p : CPolynomial R) (n : ℕ) :
    eval x (p ^ n) = eval x p ^ n := by
  induction n with
  | zero => simp [eval_one]
  | succ n ih => rw [pow_succ, pow_succ, eval_mul, ih]

attribute [simp] eval_C eval_mul eval_one eval_sub

/-! ## Transport to the Mathlib image

These are the `simp` lemmas that push `toPoly` inwards, so a goal about the computable
representation becomes a goal about `Polynomial R` in one `simp` call. -/

attribute [simp] toPoly_add toPoly_mul toPoly_sub toPoly_neg toPoly_one toPoly_zero
  C_toPoly X_toPoly

/-- `toPoly` of a list product.  CompPoly has the `Finset` versions (`toPoly_prod`, `toPoly_sum`);
the row-polynomial constructions build their products over `List.ofFn`, where a `Finset` reindexing
would only be noise. -/
theorem toPoly_list_prod [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (l : List (CPolynomial R)) : l.prod.toPoly = (l.map toPoly).prod :=
  map_list_prod (ringEquiv : CPolynomial R ≃+* Polynomial R) l

/-- `toPoly` of a list sum. -/
theorem toPoly_list_sum [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (l : List (CPolynomial R)) : l.sum.toPoly = (l.map toPoly).sum :=
  map_list_sum (ringEquiv : CPolynomial R ≃+* Polynomial R) l

/-- `toPoly` is injective.  CompPoly states this as `toPolyLinearEquiv.injective`, whose hypothesis
is phrased through the bundled coercion; this restates it directly on `toPoly` so callers do not
need a `change` at every use. -/
theorem toPoly_injective [Semiring R] [BEq R] [LawfulBEq R] {p q : CPolynomial R}
    (h : p.toPoly = q.toPoly) : p = q :=
  toPolyLinearEquiv.injective h

/-! ## Degree arithmetic -/

theorem natDegree_sub_le [Ring R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) :
    (p - q).natDegree ≤ max p.natDegree q.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly, natDegree_toPoly, toPoly_sub]
  exact Polynomial.natDegree_sub_le _ _

theorem natDegree_mul_le [Semiring R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) :
    (p * q).natDegree ≤ p.natDegree + q.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly, natDegree_toPoly, toPoly_mul]
  exact Polynomial.natDegree_mul_le

theorem natDegree_X_pow_le [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (n : ℕ) :
    ((X : CPolynomial R) ^ n).natDegree ≤ n := by
  rw [natDegree_toPoly, toPoly_pow, X_toPoly]
  simp

theorem natDegree_one_le [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    (1 : CPolynomial R).natDegree ≤ 0 := by
  rw [natDegree_toPoly, toPoly_one]
  simp

/-! ## Bundled homomorphisms

Mathlib's `Polynomial.C` and `Polynomial.evalRingHom` are bundled; CompPoly's `C` and `eval` are
bare functions.  Every `eval₂`-shaped construction, and every ring-hom transport in the verifier
layer, needs the bundled forms. -/

/-- The constant embedding as a ring hom. -/
def CRingHom [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : R →+* CPolynomial R where
  toFun := C
  map_one' := by apply toPoly_injective; simp
  map_mul' := by intro a b; apply toPoly_injective; simp
  map_zero' := by apply toPoly_injective; simp
  map_add' := by intro a b; apply toPoly_injective; simp

@[simp]
theorem coe_CRingHom [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    ⇑(CRingHom : R →+* CPolynomial R) = C := rfl

/-- Evaluation at `x` as a ring hom. -/
def evalRingHom [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (x : R) :
    CPolynomial R →+* R where
  toFun := eval x
  map_one' := eval_one x
  map_mul' := fun p q => eval_mul p q x
  map_zero' := eval_zero x
  map_add' := eval_add x

@[simp]
theorem coe_evalRingHom [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (x : R) :
    ⇑(evalRingHom x) = eval x := rfl

/-! ## Composition

CompPoly has `eval₂` but no `comp`.  With the constant embedding bundled, composition is `eval₂`
at that hom, and the Mathlib characterisation follows from `eval₂_toPoly` together with
`Polynomial.hom_eval₂` transported along `ringEquiv`. -/

/-- Polynomial composition: `comp p q` is `p ∘ q`. -/
def comp [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (p q : CPolynomial R) :
    CPolynomial R :=
  eval₂ CRingHom q p

theorem toPoly_comp [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p q : CPolynomial R) : (comp p q).toPoly = p.toPoly.comp q.toPoly := by
  have hring :
      ((ringEquiv : CPolynomial R ≃+* Polynomial R) : CPolynomial R →+* Polynomial R).comp
          CRingHom = Polynomial.C := by
    refine RingHom.ext fun c => ?_
    show (C c : CPolynomial R).toPoly = Polynomial.C c
    exact C_toPoly c
  rw [comp, eval₂_toPoly]
  have h := Polynomial.hom_eval₂ p.toPoly CRingHom
    ((ringEquiv : CPolynomial R ≃+* Polynomial R) : CPolynomial R →+* Polynomial R) q
  rw [hring] at h
  exact h.trans rfl

theorem eval_comp [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p q : CPolynomial R) (x : R) :
    eval x (comp p q) = eval (eval x q) p := by
  rw [eval_toPoly, toPoly_comp, Polynomial.eval_comp, ← eval_toPoly, ← eval_toPoly]

theorem natDegree_comp [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [NoZeroDivisors R]
    (p q : CPolynomial R) :
    (comp p q).natDegree = p.natDegree * q.natDegree := by
  rw [natDegree_toPoly, toPoly_comp, Polynomial.natDegree_comp, ← natDegree_toPoly,
    ← natDegree_toPoly]

/-! ## Rotation

Composition with `C w * X` is the column rotation the halo2 verifier performs; it is worth naming
because both of its properties are used at every rotated-column site. -/

/-- Evaluating a rotated column rescales the point. -/
theorem eval_comp_C_mul_X [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) (w x : R) :
    eval x (comp p (C w * X)) = eval (w * x) p := by
  rw [eval_comp, eval_mul, eval_C, eval_X]

/-- Rotation by a nonzero factor preserves degree. -/
theorem natDegree_comp_C_mul_X [Field R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) {w : R} (hw : w ≠ 0) :
    (comp p (C w * X)).natDegree = p.natDegree := by
  have hq : ((C w * X : CPolynomial R)).natDegree = 1 := by
    rw [natDegree_toPoly, toPoly_mul, C_toPoly, X_toPoly, Polynomial.natDegree_C_mul hw,
      Polynomial.natDegree_X]
  rw [natDegree_comp, hq, Nat.mul_one]

/-! ## Roots

`Polynomial.roots` is a `Multiset` obtained by repeated factorisation and is `noncomputable`.  Over
an enumerable field the set of *distinct* roots is a filter over the enumeration, so it can be a
plain `def`.  Keeping it computable costs nothing and means it can never poison a downstream
definition — the failure mode that motivated this migration.

To be clear about what "computable" buys: nobody *runs* this.  The enumeration has
`scalarFieldOrder` elements, so evaluating it would exhaust memory.  It only ever appears inside
`Prop`s, where the bad-set predicate is decided by a single evaluation instead
(`Zcash.Snark.decidableMemSzBadSet`).  The point is that a `def` mentioning it stays a `def`.

The guard at zero preserves Mathlib's convention that the zero polynomial has no roots, which is
what makes `roots_eq_toFinset` an unconditional equality. -/

open Roots.FiniteField in
/-- The distinct roots of a computable polynomial over an enumerated field. -/
def rootsBy [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] (e : FieldEnumeration R)
    (p : CPolynomial R) : Finset R :=
  if p = 0 then ∅ else (rootsInFieldByEnumeration e p).toList.toFinset

open Roots.FiniteField in
@[simp]
theorem rootsBy_zero [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] (e : FieldEnumeration R) :
    rootsBy e (0 : CPolynomial R) = ∅ := by
  simp [rootsBy]

open Roots.FiniteField in
theorem mem_rootsBy [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] {e : FieldEnumeration R}
    {p : CPolynomial R} {x : R} (hp : p ≠ 0) :
    x ∈ rootsBy e p ↔ eval x p = 0 := by
  rw [rootsBy, if_neg hp, List.mem_toFinset]
  exact ⟨fun h => rootsInFieldByEnumeration_sound h,
    fun h => rootsInFieldByEnumeration_complete _ h⟩

open Roots.FiniteField in
/-- The bridge to the Mathlib image: the two agree, so every Mathlib root theorem transfers. -/
theorem rootsBy_eq_toFinset [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] (e : FieldEnumeration R)
    (p : CPolynomial R) : rootsBy e p = p.toPoly.roots.toFinset := by
  by_cases hp : p = 0
  · simp [hp]
  · ext x
    rw [mem_rootsBy hp, Multiset.mem_toFinset,
      Polynomial.mem_roots (by rwa [Ne, toPoly_eq_zero_iff]),
      Polynomial.IsRoot.def, ← eval_toPoly]

open Roots.FiniteField in
/-- **Root counting.** A polynomial has at most `natDegree` distinct roots. -/
theorem card_rootsBy_le [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] (e : FieldEnumeration R)
    (p : CPolynomial R) : (rootsBy e p).card ≤ p.natDegree := by
  rw [rootsBy_eq_toFinset, natDegree_toPoly]
  exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)

end CompPoly.CPolynomial

/-! ## The `Fp` instantiation -/

namespace Zcash

open CompPoly
open Zcash.Arithmetic (scalarFieldOrder)

/-- The computable polynomial ring over the scalar field. -/
abbrev CPoly := CPolynomial Fp

/-- `Fp` enumerated by its residues. -/
def fpEnumeration : CPolynomial.Roots.FiniteField.FieldEnumeration Fp where
  size := scalarFieldOrder
  elem := fun i => (i.val : Fp)
  complete := fun a => ⟨⟨a.val, ZMod.val_lt a⟩, by simp⟩

/-- The distinct roots of a polynomial over the scalar field. -/
def roots (p : CPoly) : Finset Fp := CPolynomial.rootsBy fpEnumeration p

@[simp] theorem roots_zero : roots (0 : CPoly) = ∅ := CPolynomial.rootsBy_zero _

theorem mem_roots {p : CPoly} {x : Fp} (hp : p ≠ 0) :
    x ∈ roots p ↔ CPolynomial.eval x p = 0 := CPolynomial.mem_rootsBy hp

theorem roots_eq_toFinset (p : CPoly) : roots p = p.toPoly.roots.toFinset :=
  CPolynomial.rootsBy_eq_toFinset _ p

theorem card_roots_le (p : CPoly) : (roots p).card ≤ p.natDegree :=
  CPolynomial.card_rootsBy_le _ p

end Zcash
