import Zcash.Security.BindingSignature.Orchard
import Zcash.Security.BindingSignature.Sapling
import Mathlib.Util.AssertNoSorry

/-!
# Checked trust boundary of the binding-signature relation reductions

Build-time enforcement of the breaks-as-computed-data discipline (see
`Zcash.Security.RandomOracle`) for the `NontrivialRelation` reductions: `assert_no_sorry`
walks the elaborated dependency graph of each reduction, and `#guard_msgs`-pinned
`#print axioms` freezes their axiom sets. Computability is compiler-enforced (plain `def`s).

Unlike the ledger break reductions (`Zcash.Security.Ledger.TrustBoundary`), these pins
include `Classical.choice`. It enters only through erased `Prop` certificate fields (the
arithmetic side proofs); the relation coefficients themselves are direct terms of the
inputs, and the definitions compile as plain `def`s, so the data cannot have been conjured
from mere propositional existence.
-/

open Zcash.Security.BindingSignature

assert_no_sorry NontrivialRelation.ofImbalance
assert_no_sorry NontrivialRelation.ofBundleModImbalance
assert_no_sorry NontrivialRelation.ofBundleIntImbalance
assert_no_sorry NontrivialRelation.ofOrchardImbalance
assert_no_sorry NontrivialRelation.ofSaplingImbalance

/-- info: 'Zcash.Security.BindingSignature.NontrivialRelation.ofImbalance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofImbalance

/-- info: 'Zcash.Security.BindingSignature.NontrivialRelation.ofBundleModImbalance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofBundleModImbalance

/-- info: 'Zcash.Security.BindingSignature.NontrivialRelation.ofBundleIntImbalance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofBundleIntImbalance

/-- info: 'Zcash.Security.BindingSignature.NontrivialRelation.ofOrchardImbalance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofOrchardImbalance

/-- info: 'Zcash.Security.BindingSignature.NontrivialRelation.ofSaplingImbalance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofSaplingImbalance
