import Zcash.Snark.Soundness.CommitFold
import Zcash.Common.DiscreteLogRelation

/-!
# Binding as a discrete-log-relation reduction over the augmented generators

`Zcash.Snark.Soundness.CommitFold` models commitment binding at the URS generators `g` as a
reduction to discrete-log-relation (DLR) hardness (`relation_of_collision`,
`commitmentBinding_iff_no_relation`). The deployed verifier additionally folds the inner-product
generator `U` and the blinding generator `W` into one group equation, so soundness there needs
binding over the *augmented* system `(g, U, W)`. That system is the shared `Zcash.NontrivialRelation`
(its `∑ i, a i • g i` is the Snark commitment `commitGen g a`); this module computes the relation per
the breaks-as-computed-data convention (`Zcash.Security.RandomOracle`):

* `NontrivialRelation.ofCombinationCollision` — a combined `(g, U, W)`-equation whose coordinates do
  not all agree *computes* a relation: the augmented analog of `relation_of_collision`, and the step
  that ties the deployed peel (`Zcash.Snark.Soundness.Deployed.IpaPeel`) to binding.

For why the reduction produces the relation as data — an ∃-closed `Prop` would be vacuous at the
concrete curve — see `The reduction form` in `Zcash.Snark.Soundness.Main`.
-/

namespace Zcash.Snark

open Zcash.Arithmetic

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

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
    show commitGen g (a - a') + (α - α') • U + (β - β') • W = 0
    have hrw : commitGen g (a - a') + (α - α') • U + (β - β') • W
        = (commitGen g a + α • U + β • W) - (commitGen g a' + α' • U + β' • W) := by
      rw [commitGen_sub, sub_smul, sub_smul]; abel
    rw [hrw, e, sub_self]

end Zcash.Snark
