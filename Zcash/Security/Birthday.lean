import Mathlib

/-!
# Birthday-bound counting for random-oracle ±-collisions

Following the counting-fraction style of `Fingerprint/SchwartzZippel.lean`: a "probability" is the
fraction of a finite ambient space on which a bad event occurs, expressed in `ℚ≥0`, with no
probability monad. Here the ambient space is `F × F` (two independent uniform random-oracle outputs)
and the bad event is the ±-collision `G₁ = ±G₂` that the key-binding reduction bottoms out in.

The per-pair count `≤ 2·|F|` (one outcome per sign) gives the `2/|F|` per-pair, per-sign term; the
diagonal count `|F|` gives the `1/|F|` residual (both-internal upstream collision). Summed over the
`C(q,2)` pairs of an adversary's `q` queries this is the `3·q(q-1)/(2·r)` bound of the ZIP 2005
key-binding theorem (ROM).
-/

namespace Zcash.Security.Birthday

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The ±-collision set in `F × F` has at most `2·|F|` elements: for each first coordinate `a`, only
`b ∈ {a, -a}` collides. This is the per-pair, per-sign heart of the birthday bound. -/
theorem card_pm_collision_le :
    (univ.filter fun p : F × F => p.1 = p.2 ∨ p.1 = -p.2).card ≤ 2 * Fintype.card F := by
  have hsub : (univ.filter fun p : F × F => p.1 = p.2 ∨ p.1 = -p.2) ⊆
      (univ.image fun a : F => (a, a)) ∪ (univ.image fun a : F => (a, -a)) := by
    intro p hp
    rw [mem_filter] at hp
    rw [mem_union]
    rcases hp.2 with h | h
    · exact Or.inl (mem_image.2 ⟨p.1, mem_univ _, Prod.ext rfl h⟩)
    · refine Or.inr (mem_image.2 ⟨p.1, mem_univ _, Prod.ext rfl ?_⟩)
      rw [h, neg_neg]
  calc (univ.filter fun p : F × F => p.1 = p.2 ∨ p.1 = -p.2).card
      ≤ ((univ.image fun a : F => (a, a)) ∪ (univ.image fun a : F => (a, -a))).card :=
        card_le_card hsub
    _ ≤ (univ.image fun a : F => (a, a)).card + (univ.image fun a : F => (a, -a)).card :=
        card_union_le _ _
    _ ≤ Fintype.card F + Fintype.card F := by
        gcongr <;> · rw [← card_univ]; exact card_image_le
    _ = 2 * Fintype.card F := (two_mul _).symm

omit [Field F] in
/-- The diagonal of `F × F` has at most `|F|` elements. This is the residual "both-internal upstream
collision" event `rivk_ext₁ = rivk_ext₂` at distinct upstream queries — the `1/|F|` residual term. -/
theorem card_diag_le :
    (univ.filter fun p : F × F => p.1 = p.2).card ≤ Fintype.card F := by
  calc (univ.filter fun p : F × F => p.1 = p.2).card
      ≤ (univ.image fun a : F => (a, a)).card := by
        apply card_le_card
        intro p hp
        rw [mem_filter] at hp
        exact mem_image.2 ⟨p.1, mem_univ _, Prod.ext rfl hp.2⟩
    _ ≤ Fintype.card F := by rw [← card_univ]; exact card_image_le

omit [DecidableEq F] in
/-- The field's cardinality is nonzero (a field is nonempty). -/
private theorem card_ne_zero : (Fintype.card F : ℚ≥0) ≠ 0 := by
  exact_mod_cast Fintype.card_pos.ne'

/-- **Per-pair, per-sign fraction.** Over two independent uniform outputs `(G₁, G₂) ∈ F × F`, the
fraction on which the ±-collision `G₁ = ±G₂` holds is at most `2/|F|`. -/
theorem pm_collision_fraction_le :
    ((univ.filter fun p : F × F => p.1 = p.2 ∨ p.1 = -p.2).card : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ 2
      ≤ 2 / (Fintype.card F : ℚ≥0) := by
  have hc : ((univ.filter fun p : F × F => p.1 = p.2 ∨ p.1 = -p.2).card : ℚ≥0)
      ≤ 2 * (Fintype.card F : ℚ≥0) := by exact_mod_cast card_pm_collision_le
  calc ((univ.filter fun p : F × F => p.1 = p.2 ∨ p.1 = -p.2).card : ℚ≥0) / (Fintype.card F) ^ 2
      ≤ (2 * (Fintype.card F : ℚ≥0)) / (Fintype.card F) ^ 2 := by gcongr
    _ = 2 / (Fintype.card F : ℚ≥0) := by rw [pow_two, mul_div_mul_right _ _ card_ne_zero]

/-- **Residual fraction.** The diagonal event `G₁ = G₂` has fraction at most `1/|F|`. -/
theorem diag_fraction_le :
    ((univ.filter fun p : F × F => p.1 = p.2).card : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ 2
      ≤ 1 / (Fintype.card F : ℚ≥0) := by
  have hc : ((univ.filter fun p : F × F => p.1 = p.2).card : ℚ≥0) ≤ (Fintype.card F : ℚ≥0) := by
    exact_mod_cast card_diag_le
  calc ((univ.filter fun p : F × F => p.1 = p.2).card : ℚ≥0) / (Fintype.card F) ^ 2
      ≤ (Fintype.card F : ℚ≥0) / (Fintype.card F) ^ 2 := by gcongr
    _ = 1 / (Fintype.card F : ℚ≥0) := by rw [pow_two, div_mul_eq_div_div, div_self card_ne_zero]

omit [Field F] [DecidableEq F] in
/-- **Per-pair break bound.** The `±`-collision term (`2/|F|`, `pm_collision_fraction_le`) and the
residual term (`1/|F|`, `diag_fraction_le`) sum to the `3/|F|` per-pair break bound. -/
theorem perPair_bound_eq :
    2 / (Fintype.card F : ℚ≥0) + 1 / (Fintype.card F : ℚ≥0) = 3 / (Fintype.card F : ℚ≥0) := by
  rw [← add_div]; norm_num

omit [Field F] [DecidableEq F] in
/-- **Birthday-bound closed form.** Union-bounding the per-pair break bound `3/|F|` over the
`C(q,2) = q(q-1)/2` unordered pairs of an adversary's `q` random-oracle queries yields the
[ZIP 2005 key-binding theorem (ROM)](https://zips.z.cash/zip-2005#thm-key-binding-rom) bound
`3·q·(q-1)/(2·|F|)`. (This states the arithmetic of the union-bound *sum*; the union bound itself
— that the break probability is at most the sum of the per-pair probabilities — is the standard step
over the joint query space, applied to the per-pair bounds above.) -/
theorem birthday_closed_form (q : ℕ) :
    (q.choose 2 : ℚ) * (3 / (Fintype.card F : ℚ)) = 3 * q * (q - 1) / (2 * Fintype.card F) := by
  rw [Nat.cast_choose_two]
  ring

end Zcash.Security.Birthday
