import Mathlib.Tactic
import CompPoly.Univariate.ToPoly
import Zcash.Common.CPolynomial

/-!
# The grand-product-to-multiset kernel (permutation & lookup soundness)

The shared algebraic core that both halo2's permutation and lookup *argument* soundness reduce to.
Both arguments enforce their relation by a **grand product of factors linear in the challenges**, and
the soundness step is the same: such a product, equal at the random challenge, forces the underlying
multiset identity.

This file isolates that core over Mathlib `Polynomial`. Nothing here needs computability. The proof
leans on Mathlib's roots / unique-factorization theory:

* `prod_X_add_u_inj` (**products can represent multisets**): equal products of the monic linear
  factors `X + uᵢ` force equal multisets `{uᵢ}` — a product is determined by its roots.
* `card_eval_prod_eq_le` (**univariate Schwartz–Zippel at a point**): for distinct multisets, the
  challenges where the field products collide form a bad set of size `≤ max |s| |t|`.
* `prod_pair_inj` (**products can represent multisets of pairs**): the same for factors carrying
  `(value, name)` pairs, by running the first lemma over `R = F[β]` — what the permutation
  argument needs; the lookup argument uses `prod_X_add_u_inj` twice with independent `β`, `γ`.

The per-argument wrappers — telescoping the running product over the domain, the boundary / blinding-row
rules, and (for lookup) the permuted-column structure — build on this in `Permutation.lean` /
`Lookup.lean`, where the structural steps are proven and the telescoping step remains open.
-/

namespace Zcash.Snark

open Polynomial

/-- Helper to view `X + u` terms as `X - (-u)`, so that Mathlib lemmas apply. -/
private theorem map_X_add_u_eqPoly {R : Type*} [CommRing R] (m : Multiset R) :
    m.map (fun u => X + C u) = (m.map (fun u => -u)).map (fun a => X - C a) := by
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl (fun u _ => by simp [Function.comp, sub_neg_eq_add])

/-- The roots of `∏ (X + uᵢ)` are the negated elements `{-uᵢ}` (over a domain). -/
private theorem roots_prod_X_add_uPoly {R : Type*} [CommRing R] [IsDomain R] (m : Multiset R) :
    (m.map (fun u => X + C u)).prod.roots = m.map (fun u => -u) := by
  rw [map_X_add_u_eqPoly, roots_multiset_prod_X_sub_C]

/-- Evaluating the polynomial product at `β` gives the field product of the shifted factors:
`(∏ (X + uᵢ)).eval β = ∏ (β + uᵢ)`. The bridge from the polynomial world (where `prod_X_add_u_inj`
lives) to the verifier's field-element products. -/
private theorem eval_prod_X_add_uPoly {R : Type*} [CommRing R] (m : Multiset R) (β : R) :
    ((m.map (fun u => X + C u)).prod).eval β = (m.map (fun x => β + x)).prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod
    (Multiset.map_congr rfl (fun u _ => by simp [Function.comp, eval_add, eval_X, eval_C]))

/-- `∏ (X + uᵢ)` has degree `|m|` (a product of `|m|` monic linear factors). -/
theorem natDegree_prod_X_add_uPoly {R : Type*} [CommRing R] [IsDomain R] (m : Multiset R) :
    ((m.map (fun u => X + C u)).prod).natDegree = Multiset.card m := by
  rw [map_X_add_u_eqPoly, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]

/-- **Multiset-from-product, over an integral domain.**
Products of the monic linear factors `X + uᵢ` are equal iff the multisets of the `uᵢ` agree — the
reusable kernel behind both the permutation and lookup soundness arguments. Idea: over a domain a
product is determined by its roots, here `{-uᵢ}`, and negation is injective. -/
theorem prod_X_add_u_injPoly {R : Type*} [CommRing R] [IsDomain R] {s t : Multiset R}
    (h : (s.map (fun u => X + C u)).prod = (t.map (fun u => X + C u)).prod) : s = t := by
  have heq : s.map (fun u => -u) = t.map (fun u => -u) := by
    rw [← roots_prod_X_add_uPoly s, ← roots_prod_X_add_uPoly t, h]
  exact Multiset.map_injective neg_injective heq

/-- **Univariate Schwartz–Zippel at a point.** For `s ≠ t` over a finite field, the challenges `β`
at which the shifted-factor products `∏ (xᵢ + β)` agree form a "bad set" of size `≤ max |s| |t|` —
the roots of the (nonzero, by `prod_X_add_u_inj`) difference polynomial. That is, product-equality
at a random `β` forces the multiset identity except on a negligible bad set. -/
theorem card_eval_prod_eq_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {s t : Multiset F} (hst : s ≠ t) :
    (Finset.univ.filter
      (fun β => (s.map (fun x => β + x)).prod = (t.map (fun x => β + x)).prod)).card
      ≤ max (Multiset.card s) (Multiset.card t) := by
  -- the difference polynomial is nonzero, since `s ≠ t` (`prod_X_add_u_inj` contrapositive)
  have hD : (s.map (fun u => X + C u)).prod - (t.map (fun u => X + C u)).prod ≠ 0 :=
    fun h0 => hst (prod_X_add_u_injPoly (sub_eq_zero.mp h0))
  calc (Finset.univ.filter
          (fun β => (s.map (fun x => β + x)).prod = (t.map (fun x => β + x)).prod)).card
      ≤ ((s.map (fun u => X + C u)).prod
          - (t.map (fun u => X + C u)).prod).roots.toFinset.card := by
        -- every "bad" β is a root of the difference polynomial
        apply Finset.card_le_card
        intro β hβ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
        rw [Multiset.mem_toFinset, mem_roots']
        refine ⟨hD, ?_⟩
        show ((s.map (fun u => X + C u)).prod - (t.map (fun u => X + C u)).prod).eval β = 0
        rw [eval_sub, eval_prod_X_add_uPoly s β, eval_prod_X_add_uPoly t β, hβ, sub_self]
    _ ≤ Multiset.card ((s.map (fun u => X + C u)).prod
          - (t.map (fun u => X + C u)).prod).roots := Multiset.toFinset_card_le _
    _ ≤ ((s.map (fun u => X + C u)).prod - (t.map (fun u => X + C u)).prod).natDegree :=
          card_roots' _
    _ ≤ max ((s.map (fun u => X + C u)).prod).natDegree
            ((t.map (fun u => X + C u)).prod).natDegree := natDegree_sub_le _ _
    _ = max (Multiset.card s) (Multiset.card t) := by
          rw [natDegree_prod_X_add_uPoly s, natDegree_prod_X_add_uPoly t]

/-- Encode a pair `(v, n)` as the `F[β]`-element `v + n·β` (here `β = X`).
Injective, since `v` and `n` are its degree-0 and degree-1 coefficients. -/
def encPair {F : Type*} [Field F] [BEq F] [LawfulBEq F] (p : F × F) : CompPoly.CPolynomial F :=
  CompPoly.CPolynomial.C p.1 + CompPoly.CPolynomial.C p.2 * CompPoly.CPolynomial.X

@[simp] theorem toPoly_encPair {F : Type*} [Field F] [BEq F] [LawfulBEq F] (p : F × F) :
    (encPair p).toPoly = C p.1 + C p.2 * X := by
  rw [encPair, CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_mul,
    CompPoly.CPolynomial.C_toPoly, CompPoly.CPolynomial.C_toPoly,
    CompPoly.CPolynomial.X_toPoly]

theorem encPair_injective {F : Type*} [Field F] [BEq F] [LawfulBEq F] :
    Function.Injective (encPair (F := F)) := by
  intro p q hpq
  have hpq' := congrArg CompPoly.CPolynomial.toPoly hpq
  rw [toPoly_encPair, toPoly_encPair] at hpq'
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · simpa [coeff_add, coeff_C, coeff_C_mul, coeff_X_zero] using
      congrArg (Polynomial.coeff · 0) hpq'
  · simpa [coeff_add, coeff_C, coeff_C_mul, coeff_X_one] using
      congrArg (Polynomial.coeff · 1) hpq'

/-- **Multisets of pairs.** `∏ (vᵢ + nᵢ·β + γ) = ∏ (cⱼ + dⱼ·β + γ) ⟹ {(vᵢ,nᵢ)} = {(cⱼ,dⱼ)}`.
The factor `vᵢ + nᵢ·β + γ` is `X + C (encPair (vᵢ,nᵢ))` over `R = F[β]` (variable `X = γ`), so this is
just `prod_X_add_u_inj` over the domain `F[β]` followed by `encPair`-injectivity. This is the multiset
identity the permutation argument needs (pairs of `(value, name)`, not just sums). -/
private theorem prod_pair_injPoly {F : Type*} [Field F] [BEq F] [LawfulBEq F] {sp tp : Multiset (F × F)}
    (h : (sp.map (fun p => X + C (encPair p).toPoly)).prod
       = (tp.map (fun p => X + C (encPair p).toPoly)).prod) : sp = tp := by
  have conv : ∀ (m : Multiset (F × F)),
      (m.map (fun p => X + C (encPair p).toPoly)).prod
        = ((m.map (fun p => (encPair p).toPoly)).map (fun u => X + C u)).prod := by
    intro m; simp only [Multiset.map_map, Function.comp_def]
  rw [conv sp, conv tp] at h
  refine Multiset.map_injective (fun p q hpq => encPair_injective ?_) (prod_X_add_u_injPoly h)
  exact CompPoly.CPolynomial.toPolyLinearEquiv.injective hpq

end Zcash.Snark

/-! ## The computable interface

Everything above is stated over Mathlib's `Polynomial`, because the proof borrows its roots and
unique-factorisation theory. None of that escapes: the exports below say the same things about
`CPolynomial`, and each one is the Mathlib statement carried across `toPoly`. -/

namespace Zcash.Snark

open CompPoly CompPoly.CPolynomial

variable {R : Type*} [CommRing R] [IsDomain R] [BEq R] [LawfulBEq R]

/-- The Mathlib image of a product of computable linear factors. -/
private theorem toPoly_cprod_X_add_u (m : Multiset R) :
    ((m.map (fun u => X + C u)).prod).toPoly
      = (m.map (fun u => Polynomial.X + Polynomial.C u)).prod := by
  rw [toPoly_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun u _ => by simp)

/-- Evaluating a product of linear factors is the product of the shifted points. -/
theorem eval_cprod_X_add_u (m : Multiset R) (β : R) :
    eval β (m.map (fun u => X + C u)).prod = (m.map (fun x => β + x)).prod := by
  rw [eval_toPoly, toPoly_cprod_X_add_u]
  exact eval_prod_X_add_uPoly m β

/-- `∏ (X + uᵢ)` has degree `|m|`. -/
theorem natDegree_cprod_X_add_u (m : Multiset R) :
    ((m.map (fun u => X + C u)).prod).natDegree = Multiset.card m := by
  rw [natDegree_toPoly, toPoly_cprod_X_add_u]
  exact natDegree_prod_X_add_uPoly m

/-- **Multiset-from-product.** Equal products of the monic linear factors `X + uᵢ` force equal
multisets — the kernel behind both permutation and lookup soundness. -/
theorem prod_cX_add_u_inj {s t : Multiset R}
    (h : (s.map (fun u => X + C u)).prod = (t.map (fun u => X + C u)).prod) : s = t := by
  refine prod_X_add_u_injPoly ?_
  rw [← toPoly_cprod_X_add_u, ← toPoly_cprod_X_add_u, h]

/-- **The lookup split.** The two lookup products live over separate indeterminates, so equality
forces both column multisets to agree: the leading coefficient in the outer variable is each side's
inner product, and cancelling it leaves the outer one. -/
theorem prod_split_inj {F : Type*} [Field F] [BEq F] [LawfulBEq F] {a s inp tbl : Multiset F}
    (h : C (a.map (fun u => X + C u)).prod * (s.map (fun u => X + C (C u))).prod
       = (C (inp.map (fun u => X + C u)).prod * (tbl.map (fun u => X + C (C u))).prod
           : CompPoly.CPolynomial (CompPoly.CPolynomial F))) : a = inp ∧ s = tbl := by
  have hmonic : ∀ m : Multiset F,
      (m.map (fun u => Polynomial.X + Polynomial.C (Polynomial.C u))).prod.Monic := fun m =>
    Polynomial.monic_multiset_prod_of_monic _ _ fun u _ => Polynomial.monic_X_add_C _
  have hzero : ∀ m : Multiset F,
      (m.map (fun u => Polynomial.X + Polynomial.C u)).prod ≠ 0 := fun m =>
    (Polynomial.monic_multiset_prod_of_monic _ _ fun u _ => Polynomial.monic_X_add_C u).ne_zero
  have hinner : ∀ m : Multiset F,
      nestedPoly (C (m.map (fun u => X + C u)).prod)
        = Polynomial.C (m.map (fun u => Polynomial.X + Polynomial.C u)).prod := by
    intro m
    rw [nestedPoly_C, toPoly_multiset_prod, Multiset.map_map]
    simp
  have houter : ∀ m : Multiset F,
      nestedPoly ((m.map (fun u => (X + C (C u) :
          CompPoly.CPolynomial (CompPoly.CPolynomial F)))).prod)
        = (m.map (fun u => Polynomial.X + Polynomial.C (Polynomial.C u))).prod := by
    intro m
    rw [nestedPoly_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun u _ => ?_)
    rw [Function.comp_apply, nestedPoly_add, nestedPoly_X, nestedPoly_C, C_toPoly]
  have heq := congrArg nestedPoly h
  rw [nestedPoly_mul, nestedPoly_mul, hinner a, hinner inp, houter s, houter tbl] at heq
  have hlead := congrArg Polynomial.leadingCoeff heq
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    Polynomial.leadingCoeff_C, (hmonic s).leadingCoeff, (hmonic tbl).leadingCoeff,
    _root_.mul_one, _root_.mul_one] at hlead
  refine ⟨prod_X_add_u_injPoly hlead, ?_⟩
  rw [hlead] at heq
  have hCne : (Polynomial.C (inp.map (fun u => Polynomial.X + Polynomial.C u)).prod :
      Polynomial (Polynomial F)) ≠ 0 := Polynomial.C_ne_zero.mpr (hzero inp)
  have hQ := mul_left_cancel₀ hCne heq
  have hmap : ∀ m : Multiset F,
      (m.map Polynomial.C).map (fun v => Polynomial.X + Polynomial.C v)
        = m.map (fun u => Polynomial.X + Polynomial.C (Polynomial.C u)) := by
    intro m; simp [Multiset.map_map]
  refine Multiset.map_injective (Polynomial.C_injective (R := F)) (prod_X_add_u_injPoly ?_)
  rw [hmap s, hmap tbl]; exact hQ

/-- **Multisets of pairs.** The same, for factors carrying `(value, name)` pairs, run over the
computable coefficient ring `CPolynomial F`. -/
theorem prod_cpair_inj {F : Type*} [Field F] [BEq F] [LawfulBEq F] {sp tp : Multiset (F × F)}
    (h : (sp.map (fun p => (X + C (encPair p) : CompPoly.CPolynomial (CompPoly.CPolynomial F)))).prod
       = (tp.map (fun p => (X + C (encPair p) : CompPoly.CPolynomial (CompPoly.CPolynomial F)))).prod) : sp = tp := by
  refine prod_pair_injPoly ?_
  have hfac : ∀ m : Multiset (F × F),
      nestedPoly ((m.map (fun p =>
          (X + C (encPair p) : CompPoly.CPolynomial (CompPoly.CPolynomial F)))).prod)
        = (m.map (fun p => Polynomial.X + Polynomial.C (encPair p).toPoly)).prod := by
    intro m
    rw [nestedPoly_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun p _ => ?_)
    rw [Function.comp_apply, nestedPoly_add, nestedPoly_X, nestedPoly_C]
  rw [← hfac, ← hfac, h]

end Zcash.Snark
