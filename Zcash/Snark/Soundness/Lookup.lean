import Mathlib
import Zcash.Snark.Soundness.GrandProduct

/-!
# Lookup argument soundness

(Towards #14.) The [lookup argument](https://zcash.github.io/halo2/design/proving-system/lookup.html)
proves multiset inclusion {input} ⊆ {table}. Its soundness combines the grand-product → multiset kernel
(`GrandProduct.lean`, giving {A′} = {input} and {S′} = {table}) with the **permuted-column run-structure**
proved here: the verifier's ℓ_0·(A′ − S′) and active·(A′ − S′)·(A′ − A′_prev) constraints force every A′
value to coincide with some S′ value, which together with the multiset equalities yields {input} ⊆ {table}.

This file currently provides `run_structure` (the run-structure step over the usable rows); the
grand-product ⟹ multiset equalities and the final assembly will follow.
-/

namespace Zcash.Snark

/-- **Run-structure for the lookup argument**. This verifies part of the abstract argument, not yet
the mapping to constraints.

We allow the prover to supply permutation columns of A and S — called A′, S′ in the Halo 2 book, and
`a`, `s` here. As in the book, ℓ_i evaluates to 1 at row i and 0 otherwise, and the running-product
constraint refers to the previous row A′_prev = A′(ω⁻¹·), which at row 0 wraps cyclically to the last
blinding row, an arbitrary value `aPrev`.

The constraints checked by the verifier are:

* `a_0 = s_0`, from ℓ_0·(A′ - S′) = 0.
* `a_0 = s_0 ∨ a_0 = aPrev`, from active·(A′ - S′)·(A′ - A′_prev) = 0 at row 0, with `aPrev` arbitrary.
* `a_{i+1} = s_{i+1} ∨ a_{i+1} = a_i`, the later-row instances of the same constraint.

The first two together are equivalent to just `a_0 = s_0` for any `aPrev` (the wrapped predecessor is
harmless), so row 0 is matched. With every later row matched or A′ repeating its predecessor, every
`a_i` equals some `s_j`. So the permuted-input column A′ is elementwise contained in the permuted
table S′ — the membership the lookup argument needs.

Indices are `Fin (n + 1)` so the index set is nonempty (row 0 always exists), and the proof uses
`Fin.induction` so the `succ` case's hypothesis is exactly the predecessor row `i.castSucc`. -/
theorem run_structure {F : Type*} {n : ℕ} (a s : Fin (n + 1) → F) (aPrev : F)
    (h0 : a 0 = s 0)
    (hstep0 : a 0 = s 0 ∨ a 0 = aPrev)
    (hstep : ∀ i : Fin n, a i.succ = s i.succ ∨ a i.succ = a i.castSucc) :
    ∀ i, ∃ j, a i = s j := by
  intro i
  induction i using Fin.induction with
  | zero =>
    -- the row-0 running constraint with the arbitrary wrapped predecessor is subsumed by `a 0 = s 0`
    rcases hstep0 with h | _
    · exact ⟨0, h⟩
    · exact ⟨0, h0⟩
  | succ i ih =>
    rcases hstep i with hm | hr
    · exact ⟨i.succ, hm⟩
    · obtain ⟨j, hj⟩ := ih
      exact ⟨j, hr.trans hj⟩

end Zcash.Snark
