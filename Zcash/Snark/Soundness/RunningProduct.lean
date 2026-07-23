import Mathlib
import Zcash.Snark.Soundness.GrandProduct

/-!
# Telescoping the running product

Both the permutation and the lookup argument work the same way. The prover commits to a running
product `z`, and the verifier checks a one-row recurrence: `z` at the next row times one product of
factors equals `z` at this row times another. The verifier also pins `z` at the first row to `1` and
at the last row to `0` or `1`.

Multiplying the recurrence across the rows cancels every interior `z`, leaving the two whole-column
products related by the boundary values. That is the step from what the verifier checks (a per-row
identity) to what the soundness kernel consumes (a product identity, which `GrandProduct` turns into
a multiset identity).

The `z`-ends-at-`0` branch is not vacuous and is not silently dropped: it forces one of the factors
to be zero, which for the arguments' factors `v + β·name + γ` is a collision on the challenges. So
the results here end in *either* the product identity *or* an explicit vanishing factor, and the
caller prices the second branch.
-/

namespace Zcash.Snark

open Finset

variable {F : Type*}

/-- **Telescoping.** A one-row recurrence multiplied across `m` rows: every interior `z` cancels,
leaving the boundary values times the two products. -/
theorem telescope_running_product [CommRing F] (z A B : ℕ → F) {m : ℕ}
    (hrec : ∀ i < m, z (i + 1) * B i = z i * A i) :
    z m * ∏ i ∈ range m, B i = z 0 * ∏ i ∈ range m, A i := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep := hrec m (Nat.lt_succ_self m)
      calc z (m + 1) * ∏ i ∈ range (m + 1), B i
          = (z (m + 1) * B m) * ∏ i ∈ range m, B i := by
            rw [prod_range_succ]; ring
        _ = (z m * A m) * ∏ i ∈ range m, B i := by rw [hstep]
        _ = (z m * ∏ i ∈ range m, B i) * A m := by ring
        _ = (z 0 * ∏ i ∈ range m, A i) * A m := by
            rw [ih fun i hi => hrec i (Nat.lt_succ_of_lt hi)]
        _ = z 0 * ∏ i ∈ range (m + 1), A i := by rw [prod_range_succ]; ring

/-- **The product identity the kernel consumes.** With `z` pinned to `1` at the first row and to `0`
or `1` at the last, telescoping gives *either* the two products are equal *or* one factor on the
right vanished — the case `z` ended at `0`. -/
theorem prod_eq_or_factor_eq_zero [Field F] (z A B : ℕ → F) {m : ℕ}
    (hrec : ∀ i < m, z (i + 1) * B i = z i * A i)
    (hz0 : z 0 = 1) (hzm : z m = 0 ∨ z m = 1) :
    (∏ i ∈ range m, B i = ∏ i ∈ range m, A i) ∨ ∃ i ∈ range m, A i = 0 := by
  have htel := telescope_running_product z A B hrec
  rw [hz0, one_mul] at htel
  rcases hzm with hzm | hzm
  · rw [hzm, zero_mul] at htel
    exact Or.inr (prod_eq_zero_iff.mp htel.symm)
  · exact Or.inl (by rw [hzm, one_mul] at htel; exact htel)

/-- Telescoping with the last-row value known to be `1`: the two products agree outright. This is
the branch the honest prover is in. -/
theorem prod_eq_of_running_product [CommRing F] (z A B : ℕ → F) {m : ℕ}
    (hrec : ∀ i < m, z (i + 1) * B i = z i * A i) (hz0 : z 0 = 1) (hzm : z m = 1) :
    ∏ i ∈ range m, B i = ∏ i ∈ range m, A i := by
  have htel := telescope_running_product z A B hrec
  rwa [hz0, hzm, one_mul, one_mul] at htel

/-! ## Rows of several columns

Each row's factor is itself a product over that row's columns, so the telescoped identity is a
product over `row × column` pairs. Rewriting it as a product over one index set is what lets
`prod_pair_inj` read it as a multiset of `(value, name)` pairs. -/

/-- A row-wise product of column factors, flattened to a single product over `row × column`. -/
theorem prod_range_prod_range [CommRing F] (f : ℕ → ℕ → F) (m k : ℕ) :
    (∏ i ∈ range m, ∏ j ∈ range k, f i j) = ∏ p ∈ range m ×ˢ range k, f p.1 p.2 := by
  rw [prod_product]

/-- **The grand product of a running-product argument.** Each row's recurrence multiplies the row's
column factors; across all rows the result is a single product over every cell, related by the
boundary values. Either the two whole-table products agree, or some right-hand cell factor
vanished. -/
theorem grandProduct_eq_or_cell_eq_zero [Field F] (z : ℕ → F) (a b : ℕ → ℕ → F) {m k : ℕ}
    (hrec : ∀ i < m, z (i + 1) * ∏ j ∈ range k, b i j = z i * ∏ j ∈ range k, a i j)
    (hz0 : z 0 = 1) (hzm : z m = 0 ∨ z m = 1) :
    (∏ p ∈ range m ×ˢ range k, b p.1 p.2 = ∏ p ∈ range m ×ˢ range k, a p.1 p.2)
      ∨ ∃ p ∈ range m ×ˢ range k, a p.1 p.2 = 0 := by
  rcases prod_eq_or_factor_eq_zero z (fun i => ∏ j ∈ range k, a i j)
      (fun i => ∏ j ∈ range k, b i j) hrec hz0 hzm with h | ⟨i, hi, hzero⟩
  · exact Or.inl (by rw [← prod_range_prod_range, ← prod_range_prod_range]; exact h)
  · obtain ⟨j, hj, hj0⟩ := prod_eq_zero_iff.mp hzero
    exact Or.inr ⟨(i, j), mem_product.mpr ⟨hi, hj⟩, hj0⟩


/-! ## Chunks

halo2 splits the permutation columns into chunks, each with its own running product, chained so that
each chunk starts where the previous one ended. That chain is itself a running product over the
chunk index, so the same telescoping applies a second time and the whole table is one product. -/

/-- **Chunk stitching.** Per-chunk recurrences plus the chaining rule telescope across the chunks:
the boundary values of the first and last chunk relate the two whole-table products. -/
theorem telescope_chunks [CommRing F] (Z : ℕ → ℕ → F) (A B : ℕ → ℕ → ℕ → F) {nc m k : ℕ}
    (hrec : ∀ c < nc, ∀ i < m,
      Z c (i + 1) * ∏ j ∈ range k, B c i j = Z c i * ∏ j ∈ range k, A c i j)
    (hchain : ∀ c < nc, Z (c + 1) 0 = Z c m) :
    Z nc 0 * ∏ p ∈ range nc ×ˢ range m, ∏ j ∈ range k, B p.1 p.2 j
      = Z 0 0 * ∏ p ∈ range nc ×ˢ range m, ∏ j ∈ range k, A p.1 p.2 j := by
  have hstep : ∀ c < nc, Z (c + 1) 0 * ∏ i ∈ range m, ∏ j ∈ range k, B c i j
      = Z c 0 * ∏ i ∈ range m, ∏ j ∈ range k, A c i j := by
    intro c hc
    rw [hchain c hc]
    exact telescope_running_product (Z c) (fun i => ∏ j ∈ range k, A c i j)
      (fun i => ∏ j ∈ range k, B c i j) fun i hi => hrec c hc i hi
  have hall := telescope_running_product (fun c => Z c 0)
    (fun c => ∏ i ∈ range m, ∏ j ∈ range k, A c i j)
    (fun c => ∏ i ∈ range m, ∏ j ∈ range k, B c i j) hstep
  rw [← prod_range_prod_range (fun c i => ∏ j ∈ range k, B c i j),
    ← prod_range_prod_range (fun c i => ∏ j ∈ range k, A c i j)]
  exact hall


/-- **Chunks flattened.** Reading the chunks end to end as a single running product — step `t` is row
`t % m` of chunk `t / m` — satisfies the one-step recurrence throughout, because the chaining rule is
exactly what holds at a chunk boundary. -/
theorem flat_recurrence [CommRing F] (Z : ℕ → ℕ → F) (A B : ℕ → ℕ → ℕ → F) {nc m k : ℕ}
    (hm : 0 < m)
    (hrec : ∀ c < nc, ∀ i < m,
      Z c (i + 1) * ∏ j ∈ range k, B c i j = Z c i * ∏ j ∈ range k, A c i j)
    (hchain : ∀ c < nc, Z (c + 1) 0 = Z c m)
    {t : ℕ} (ht : t < nc * m) :
    Z ((t + 1) / m) ((t + 1) % m) * ∏ j ∈ range k, B (t / m) (t % m) j
      = Z (t / m) (t % m) * ∏ j ∈ range k, A (t / m) (t % m) j := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < m ∧ t = m * q + r :=
    ⟨t / m, t % m, Nat.mod_lt _ hm, (Nat.div_add_mod t m).symm⟩
  have hq : q < nc := by
    by_contra hle
    exact absurd ht (by push_neg at hle ⊢; calc nc * m ≤ q * m := Nat.mul_le_mul_right m hle
      _ ≤ m * q + r := by rw [mul_comm]; omega)
  have hdiv : (m * q + r) / m = q := by rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hr, add_zero]
  have hmod : (m * q + r) % m = r := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  rw [hdiv, hmod]
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hr) with hlast | hmid
  · -- last row of chunk `q`: the next step is row `0` of chunk `q + 1`
    have hsum : m * q + r + 1 = m * (q + 1) := by rw [mul_add, mul_one]; omega
    rw [hsum, Nat.mul_div_cancel_left _ hm, Nat.mul_mod_right, hchain q hq, ← hlast]
    exact hrec q hq r hr
  · -- interior row: the next step is the next row of the same chunk
    have hsum : m * q + r + 1 = m * q + (r + 1) := by omega
    rw [hsum, Nat.mul_add_div hm, Nat.div_eq_of_lt hmid, add_zero, Nat.mul_add_mod,
      Nat.mod_eq_of_lt hmid]
    exact hrec q hq r hr

end Zcash.Snark
