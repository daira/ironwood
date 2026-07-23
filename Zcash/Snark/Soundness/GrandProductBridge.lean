import Mathlib
import Zcash.Snark.Soundness.GrandProduct
import Zcash.Snark.Soundness.RunningProduct
import Zcash.Snark.Soundness.Permutation
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


/-! ## The permutation argument, from the row recurrence to the copy constraints

Composing the two halves. `RunningProduct` turns the verifier's per-row recurrence into a product
over every cell; the bridge above turns that product into the multiset of `(value, name)` pairs;
`Soundness.Permutation.perm_copy_constraints` turns the multiset into the copy constraints. One
branch survives all the way: a vanishing factor, meaning the running product ended at zero or a
`value + β·name + γ` collided. It stays in the conclusion rather than being assumed away. -/

/-- The `(value, name)` pair of every cell of an `m × k` table. -/
noncomputable def cellPairs (m k : ℕ) (value nm : ℕ → ℕ → Fp) : Multiset (Fp × Fp) :=
  (Finset.univ : Finset (Fin m × Fin k)).val.map
    (fun c => (value (c.1 : ℕ) (c.2 : ℕ), nm (c.1 : ℕ) (c.2 : ℕ)))

open Finset in
/-- A product over the cell pairs is the row-by-row product the telescoping produces. -/
theorem prod_map_cellPairs (m k : ℕ) (value nm : ℕ → ℕ → Fp) (f : Fp × Fp → Fp) :
    ((cellPairs m k value nm).map f).prod
      = ∏ i ∈ range m, ∏ j ∈ range k, f (value i j, nm i j) := by
  rw [cellPairs, Multiset.map_map, ← Finset.prod_eq_multiset_prod, Fintype.prod_prod_type]
  simp only [Function.comp_apply]
  rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ range k, f (value i j, nm i j)) m]
  exact prod_congr rfl fun i _ => Fin.prod_univ_eq_prod_range
    (fun j => f (value (i : ℕ) j, nm (i : ℕ) j)) k

open Finset in
/-- **The permutation argument's multiset identity.** The verifier's per-row recurrence on the
running product, with the boundary values it also checks, gives equality of the `(value, name)`
multisets — *either* that, *or* one of the identity-side factors vanished. -/
theorem cellPairs_eq_of_running_product {m k : ℕ} (z : ℕ → Fp)
    (value nm sigmaName : ℕ → ℕ → Fp) (β γ : Fp)
    (hrec : ∀ i < m, z (i + 1) * ∏ j ∈ range k, (value i j + β * sigmaName i j + γ)
        = z i * ∏ j ∈ range k, (value i j + β * nm i j + γ))
    (hz0 : z 0 = 1) (hzm : z m = 0 ∨ z m = 1)
    (hgoodγ : γ ∉ szBadSet (linProdDiff
      ((cellPairs m k value sigmaName).map (fun p => p.1 + p.2 * β))
      ((cellPairs m k value nm).map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet
      ((pairProdDiff (cellPairs m k value sigmaName) (cellPairs m k value nm)).coeff j)) :
    cellPairs m k value sigmaName = cellPairs m k value nm
      ∨ ∃ p ∈ range m ×ˢ range k, value p.1 p.2 + β * nm p.1 p.2 + γ = 0 := by
  rcases grandProduct_eq_or_cell_eq_zero z
      (fun i j => value i j + β * nm i j + γ) (fun i j => value i j + β * sigmaName i j + γ)
      hrec hz0 hzm with hprod | hzero
  · refine Or.inl (multiset_pair_eq_of_prod_eval_eq hgoodγ hgoodβ ?_)
    rw [prod_map_cellPairs, prod_map_cellPairs]
    rw [← prod_range_prod_range (fun i j => value i j + β * sigmaName i j + γ),
      ← prod_range_prod_range (fun i j => value i j + β * nm i j + γ)] at hprod
    calc ∏ i ∈ range m, ∏ j ∈ range k, (γ + (value i j + sigmaName i j * β))
        = ∏ i ∈ range m, ∏ j ∈ range k, (value i j + β * sigmaName i j + γ) := by
          exact prod_congr rfl fun i _ => prod_congr rfl fun j _ => by ring
      _ = ∏ i ∈ range m, ∏ j ∈ range k, (value i j + β * nm i j + γ) := hprod
      _ = ∏ i ∈ range m, ∏ j ∈ range k, (γ + (value i j + nm i j * β)) := by
          exact prod_congr rfl fun i _ => prod_congr rfl fun j _ => by ring
  · exact Or.inr hzero

open Finset in
/-- **The copy constraints, from the verifier's checks.** Cells in the same cycle of `σ` hold equal
values. `hσ` says the left-hand names are the `σ`-relabelled ones, `hnm` is the name distinctness the
keygen provides, and the surviving branch is a vanishing factor. This is the permutation argument's
soundness statement with the product step supplied rather than assumed. -/
theorem perm_copy_constraints_of_running_product {m k : ℕ} (z : ℕ → Fp)
    (value nm sigmaName : ℕ → ℕ → Fp) (β γ : Fp) (σ : Equiv.Perm (Fin m × Fin k))
    (hσ : ∀ c : Fin m × Fin k,
      sigmaName (c.1 : ℕ) (c.2 : ℕ) = nm ((σ c).1 : ℕ) ((σ c).2 : ℕ))
    (hnm : Function.Injective fun c : Fin m × Fin k => nm (c.1 : ℕ) (c.2 : ℕ))
    (hrec : ∀ i < m, z (i + 1) * ∏ j ∈ range k, (value i j + β * sigmaName i j + γ)
        = z i * ∏ j ∈ range k, (value i j + β * nm i j + γ))
    (hz0 : z 0 = 1) (hzm : z m = 0 ∨ z m = 1)
    (hgoodγ : γ ∉ szBadSet (linProdDiff
      ((cellPairs m k value sigmaName).map (fun p => p.1 + p.2 * β))
      ((cellPairs m k value nm).map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet
      ((pairProdDiff (cellPairs m k value sigmaName) (cellPairs m k value nm)).coeff j))
    {c d : Fin m × Fin k} (hcd : σ.SameCycle c d) :
    value (c.1 : ℕ) (c.2 : ℕ) = value (d.1 : ℕ) (d.2 : ℕ)
      ∨ ∃ p ∈ range m ×ˢ range k, value p.1 p.2 + β * nm p.1 p.2 + γ = 0 := by
  rcases cellPairs_eq_of_running_product z value nm sigmaName β γ hrec hz0 hzm hgoodγ hgoodβ with
    hmulti | hzero
  · have hmulti' : cellPairs m k value nm = cellPairs m k value sigmaName := hmulti.symm
    simp only [cellPairs] at hmulti'
    refine Or.inl (perm_copy_constraints σ hnm (fun c => value (c.1 : ℕ) (c.2 : ℕ)) ?_ hcd)
    calc (Finset.univ : Finset (Fin m × Fin k)).val.map
            (fun c => (value (c.1 : ℕ) (c.2 : ℕ), nm (c.1 : ℕ) (c.2 : ℕ)))
        = (Finset.univ : Finset (Fin m × Fin k)).val.map
            (fun c => (value (c.1 : ℕ) (c.2 : ℕ), sigmaName (c.1 : ℕ) (c.2 : ℕ))) := hmulti'
      _ = _ := Multiset.map_congr rfl fun c _ => by rw [hσ c]
  · exact Or.inr hzero

end Zcash.Snark
