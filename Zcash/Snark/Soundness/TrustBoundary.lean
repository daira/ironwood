import Zcash.Snark.Soundness.CommitFold
import Mathlib.Util.AssertNoSorry

/-!
# Checked trust boundary of the SNARK binding reductions

Build-time enforcement of the breaks-as-computed-data discipline (see
`Zcash.Security.RandomOracle` and the Ironwood Book's Formal Verification page) for the
`NontrivialDLRelation` reductions: `assert_no_sorry` walks the elaborated dependency graph
of each reduction, and `#guard_msgs`-pinned `#print axioms` freezes their axiom sets.
Computability is compiler-enforced (plain `def`s). `Classical.choice` enters only through
erased `Prop` certificate fields; the relation coefficients are direct terms of the inputs,
so the data cannot have been conjured from mere propositional existence.
-/

open Zcash.Snark

assert_no_sorry NontrivialDLRelation.ofCollision
assert_no_sorry NontrivialDLRelation.ofIpaOpenings

/-- info: 'Zcash.Snark.NontrivialDLRelation.ofCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialDLRelation.ofCollision

/-- info: 'Zcash.Snark.NontrivialDLRelation.ofIpaOpenings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialDLRelation.ofIpaOpenings
