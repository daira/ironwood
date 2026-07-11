import Zcash.Snark.Soundness.CommitFold

/-!
# Binding as a discrete-log-relation reduction over the augmented generators

`Zcash.Snark.Soundness.CommitFold` models commitment binding at the URS generators `g` as a
reduction to discrete-log-relation (DLR) hardness (`relation_of_collision`,
`commitmentBinding_iff_no_relation`). The deployed verifier additionally folds the inner-product
generator `U` and the blinding generator `W` into one group equation, so soundness there needs
binding over the *augmented* system `(g, U, W)`. This module extends the reduction:

* `HasNontrivialRelation g U W` — a nontrivial discrete-log relation among the augmented
  generators.
* `separate_or_relation` — a combined `(g, U, W)`-equation is read off coordinate-wise *or*
  exhibits such a relation: the augmented analog of `relation_of_collision`, and the step that
  ties the deployed peel (`Zcash.Snark.Soundness.Deployed.IpaPeel`) to binding rather than to a
  discarded uniqueness conjunct.

For why the statements are reductions rather than independence assumptions — and why the
disjunction is nonetheless vacuous at the concrete curve — see `The reduction form` in
`Zcash.Snark.Soundness.Main`.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A nontrivial discrete-log relation among the augmented generators `(g, U, W)`: scalars
`(a, α, β)`, not all zero, with `⟨a, g⟩ + α • U + β • W = 0`. One always exists at a concrete
curve — see `The reduction form` in `Zcash.Snark.Soundness.Main`. -/
def HasNontrivialRelation {n : ℕ} (g : Fin n → G) (U W : G) : Prop :=
  ∃ (a : Fin n → F) (α β : F), (a ≠ 0 ∨ α ≠ 0 ∨ β ≠ 0) ∧ commitGen g a + α • U + β • W = 0

/-- **The augmented binding reduction.** Two `(g, U, W)`-combinations equal as group elements
*either* agree coordinate-wise *or* exhibit a nontrivial discrete-log relation among `(g, U, W)`
(the reduction form — see `Soundness.Main`). -/
theorem separate_or_relation {n : ℕ} (g : Fin n → G) (U W : G)
    (a a' : Fin n → F) (α α' β β' : F)
    (e : commitGen g a + α • U + β • W = commitGen g a' + α' • U + β' • W) :
    (a = a' ∧ α = α' ∧ β = β') ∨ HasNontrivialRelation (F := F) g U W := by
  by_cases h : a = a' ∧ α = α' ∧ β = β'
  · exact Or.inl h
  · refine Or.inr ⟨a - a', α - α', β - β', ?_, ?_⟩
    · -- the difference is nontrivial: otherwise the coordinates would all agree, contradicting `h`
      rcases Classical.em (a = a') with ha | ha
      · rcases Classical.em (α = α') with hα | hα
        · exact Or.inr (Or.inr (sub_ne_zero.mpr (fun hβ => h ⟨ha, hα, hβ⟩)))
        · exact Or.inr (Or.inl (sub_ne_zero.mpr hα))
      · exact Or.inl (sub_ne_zero.mpr ha)
    · -- the difference is a relation: it is the (zero) difference of the two equal combinations
      have hrw : commitGen g (a - a') + (α - α') • U + (β - β') • W
          = (commitGen g a + α • U + β • W) - (commitGen g a' + α' • U + β' • W) := by
        rw [commitGen_sub, sub_smul, sub_smul]; abel
      rw [hrw, e, sub_self]

end Zcash.Snark
