import Mathlib
import Zcash.Snark.Soundness.GrandProduct
import Zcash.Snark.Soundness.Constraints

/-!
# From the verifier's product check to the multiset identity

`GrandProduct` proves that a product of linear factors determines a multiset — but over polynomials,
with `β` and `γ` as indeterminates. The verifier does not check a polynomial identity. It checks one
field element, the product evaluated at the two challenges it actually sampled.

This module is that bridge, and it costs two Schwartz–Zippel steps, one per challenge:

* `map_eq_of_prod_eval_eq` — a good `γ` turns the field product identity into equality of the
  multisets of `value + β·name`. The bad set is the roots of the difference in `γ`.
* `multiset_pair_eq_of_map_eq` — a good `β` turns that into equality of the multisets of
  `(value, name)` *pairs*. The bad set is the roots of one coefficient of `pairProdDiff`, the
  difference `prod_pair_inj` shows is nonzero whenever the pairs differ.
* `multiset_pair_eq_of_prod_eval_eq` — the two composed, which is what the permutation argument
  consumes: a product identity at the sampled challenges gives the multiset of pairs that
  `perm_copy_constraints` turns into the copy constraints.

Both bad sets are root sets of nonzero polynomials of degree at most the multiset sizes, so each is
counted by `szBadSet_card_le` exactly like the vanishing check's.
-/

namespace Zcash.Snark

open Polynomial

/-- The difference of the two pair-encoded products, a polynomial in `γ` with coefficients in
`Fp[β]`. -/
noncomputable def pairProdDiff (sp tp : Multiset (Fp × Fp)) : Polynomial (Polynomial Fp) :=
  (sp.map (fun p => X + C (encPair p))).prod - (tp.map (fun p => X + C (encPair p))).prod

/-- The difference is nonzero whenever the multisets of pairs differ — this is `prod_pair_inj` read
contrapositively, and it is what makes the `β` bad set below a genuine root set. -/
theorem pairProdDiff_ne_zero {sp tp : Multiset (Fp × Fp)} (h : sp ≠ tp) :
    pairProdDiff sp tp ≠ 0 :=
  fun h0 => h (prod_pair_inj (sub_eq_zero.mp h0))

/-- The difference of the two `γ`-products once `β` is fixed. -/
noncomputable def linProdDiff (s t : Multiset Fp) : Polynomial Fp :=
  (s.map (fun u => X + C u)).prod - (t.map (fun u => X + C u)).prod

/-- **The `γ` step.** A challenge outside the difference's roots turns the verifier's field product
identity into equality of the multisets of `value + β·name`. -/
theorem map_eq_of_prod_eval_eq {sp tp : Multiset (Fp × Fp)} {β γ : Fp}
    (hgoodγ : γ ∉ szBadSet (linProdDiff (sp.map (fun p => p.1 + p.2 * β))
      (tp.map (fun p => p.1 + p.2 * β))))
    (h : (sp.map (fun p => γ + (p.1 + p.2 * β))).prod
       = (tp.map (fun p => γ + (p.1 + p.2 * β))).prod) :
    sp.map (fun p => p.1 + p.2 * β) = tp.map (fun p => p.1 + p.2 * β) := by
  set s := sp.map (fun p => p.1 + p.2 * β) with hs
  set t := tp.map (fun p => p.1 + p.2 * β) with ht
  by_contra hne
  have hD : linProdDiff s t ≠ 0 := fun h0 => hne (prod_X_add_u_inj (sub_eq_zero.mp h0))
  refine (not_mem_szBadSet.mp hgoodγ) hD ?_
  have hsv : (s.map (fun x => γ + x)).prod = (t.map (fun x => γ + x)).prod := by
    simpa [hs, ht, Multiset.map_map, Function.comp_def] using h
  rw [linProdDiff, eval_sub, eval_prod_X_add_u s γ, eval_prod_X_add_u t γ, hsv, sub_self]

/-- **The `β` step.** A challenge outside the roots of every coefficient of `pairProdDiff` turns
equality of the `value + β·name` multisets into equality of the `(value, name)` pairs. -/
theorem multiset_pair_eq_of_map_eq {sp tp : Multiset (Fp × Fp)} {β : Fp}
    (hgoodβ : ∀ j, β ∉ szBadSet ((pairProdDiff sp tp).coeff j))
    (h : sp.map (fun p => p.1 + p.2 * β) = tp.map (fun p => p.1 + p.2 * β)) :
    sp = tp := by
  by_contra hne
  have hD : pairProdDiff sp tp ≠ 0 := pairProdDiff_ne_zero hne
  obtain ⟨j, hj⟩ : ∃ j, (pairProdDiff sp tp).coeff j ≠ 0 := by
    by_contra hall
    exact hD (Polynomial.ext fun j => by simpa using not_exists.mp hall j)
  refine (not_mem_szBadSet.mp (hgoodβ j)) hj ?_
  -- mapping `β` through the coefficients kills the whole difference, hence every coefficient
  have hmapped : (pairProdDiff sp tp).map (evalRingHom β) = 0 := by
    have hconv : ∀ m : Multiset (Fp × Fp),
        ((m.map (fun p => X + C (encPair p))).prod).map (evalRingHom β)
          = ((m.map (fun p => p.1 + p.2 * β)).map (fun u => X + C u)).prod := by
      intro m
      rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun p _ => ?_)
      simp [encPair, Polynomial.map_add, Polynomial.map_mul]
    rw [pairProdDiff, Polynomial.map_sub, hconv sp, hconv tp, h, sub_self]
  have := congrArg (fun q => Polynomial.coeff q j) hmapped
  simpa [Polynomial.coeff_map] using this

/-- **The bridge.** The verifier's product identity at the sampled challenges gives the multiset of
`(value, name)` pairs, provided both challenges avoid their bad sets. This is what the permutation
argument feeds to `perm_copy_constraints`. -/
theorem multiset_pair_eq_of_prod_eval_eq {sp tp : Multiset (Fp × Fp)} {β γ : Fp}
    (hgoodγ : γ ∉ szBadSet (linProdDiff (sp.map (fun p => p.1 + p.2 * β))
      (tp.map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet ((pairProdDiff sp tp).coeff j))
    (h : (sp.map (fun p => γ + (p.1 + p.2 * β))).prod
       = (tp.map (fun p => γ + (p.1 + p.2 * β))).prod) :
    sp = tp :=
  multiset_pair_eq_of_map_eq hgoodβ (map_eq_of_prod_eval_eq hgoodγ h)

/-- The `γ` bad set is small: at most the larger multiset's size. -/
theorem szBadSet_linProdDiff_card_le (s t : Multiset Fp) :
    (szBadSet (linProdDiff s t)).card ≤ max (Multiset.card s) (Multiset.card t) := by
  refine (szBadSet_card_le _).trans ?_
  refine (natDegree_sub_le _ _).trans ?_
  rw [natDegree_prod_X_add_u s, natDegree_prod_X_add_u t]

end Zcash.Snark
