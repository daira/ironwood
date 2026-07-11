import Zcash.Snark.Soundness.CommitFold

/-!
# Binding as a discrete-log-relation reduction over the augmented generators

`Zcash.Snark.Soundness.CommitFold` models commitment binding at the URS generators `g` as a
reduction to discrete-log-relation (DLR) hardness (`relation_of_collision`,
`commitmentBinding_iff_no_relation`). The deployed verifier additionally folds the inner-product
generator `U` and the blinding generator `W` into one group equation, so soundness there needs
binding over the *augmented* system `(g, U, W)`. This module extends the reduction, per the
breaks-as-computed-data convention (`Zcash.Security.RandomOracle`):

* `NontrivialRelation g U W` — a nontrivial discrete-log relation among the augmented
  generators, as data.
* `NontrivialRelation.ofCombinationCollision` — a combined `(g, U, W)`-equation whose
  coordinates do not all agree *computes* such a relation: the augmented analog of
  `relation_of_collision`, and the step that ties the deployed peel
  (`Zcash.Snark.Soundness.Deployed.IpaPeel`) to binding rather than to a discarded uniqueness
  conjunct.

For why the reduction produces the relation as data — an ∃-closed Prop would be vacuous at the
concrete curve — see `The reduction form` in `Zcash.Snark.Soundness.Main`.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A nontrivial discrete-log relation among the augmented generators `(g, U, W)`, as data:
scalars `(a, α, β)`, not all zero, with `⟨a, g⟩ + α • U + β • W = 0`. Such a relation always
*exists* propositionally at a concrete curve, so an ∃-closed Prop version would be vacuous; the
reductions *compute* one (see `The reduction form` in `Zcash.Snark.Soundness.Main`). -/
structure NontrivialRelation {n : ℕ} (g : Fin n → G) (U W : G) where
  a : Fin n → F
  α : F
  β : F
  nontrivial : a ≠ 0 ∨ α ≠ 0 ∨ β ≠ 0
  relation : commitGen g a + α • U + β • W = 0

/-- **The augmented binding reduction, as a computed relation.** Two `(g, U, W)`-combinations
equal as group elements, with coordinates that do not all agree, compute a nontrivial
discrete-log relation: the coordinate differences `(a − a', α − α', β − β')`. -/
def NontrivialRelation.ofCombinationCollision [DecidableEq F] {n : ℕ} {g : Fin n → G} {U W : G}
    {a a' : Fin n → F} {α α' β β' : F}
    (e : commitGen g a + α • U + β • W = commitGen g a' + α' • U + β' • W)
    (hne : ¬(a = a' ∧ α = α' ∧ β = β')) : NontrivialRelation (F := F) g U W where
  a := a - a'
  α := α - α'
  β := β - β'
  nontrivial := by
    by_cases ha : a = a'
    · by_cases hα : α = α'
      · exact Or.inr (Or.inr (sub_ne_zero.mpr (fun hβ => hne ⟨ha, hα, hβ⟩)))
      · exact Or.inr (Or.inl (sub_ne_zero.mpr hα))
    · exact Or.inl (sub_ne_zero.mpr ha)
  relation := by
    have hrw : commitGen g (a - a') + (α - α') • U + (β - β') • W
        = (commitGen g a + α • U + β • W) - (commitGen g a' + α' • U + β' • W) := by
      rw [commitGen_sub, sub_smul, sub_smul]; abel
    rw [hrw, e, sub_self]

end Zcash.Snark
