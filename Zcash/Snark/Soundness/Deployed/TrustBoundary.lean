import Zcash.Snark.Soundness.Vesta
import Mathlib.Util.AssertNoSorry

/-!
# Checked trust boundary of the deployed binding-reduction breaks

Build-time enforcement of the breaks-as-computed-data discipline (see
`Zcash.Security.RandomOracle`), following `Zcash.Security.Ledger.TrustBoundary`. The reductions'
computability is compiler-enforced — they are plain `def`s, so a `noncomputable` dependency
fails the build. What a build does not otherwise pin down is a `sorry` reached through some
dependency, or an unexpected axiom; both checks below follow the elaborated dependency graph.

The pinned sets include `Classical.choice`, entering only through Mathlib lemmas cited by the
erased `Prop` certificate fields (`nontrivial`/`relation`) — harmless per the convention: had
choice touched the break *data*, the definitions could not have compiled as plain `def`s. The
Vesta specialization additionally pins CompElliptic's one `native_decide` fact (the prime-order
witness `p_nsmul_Gpt` behind the curve order), likewise reached only through `Prop` positions.
-/

open Zcash.Snark

assert_no_sorry NontrivialRelation.ofCombinationCollision
assert_no_sorry NontrivialRelation.ofFoldedGens
assert_no_sorry NontrivialRelation.ofLeafPeel
assert_no_sorry NontrivialRelation.ofDeployedTree
assert_no_sorry NontrivialRelation.ofUnopenedFork
assert_no_sorry NontrivialRelation.ofUnopenedForkVesta

/-- info: 'Zcash.Snark.NontrivialRelation.ofCombinationCollision' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofCombinationCollision

/-- info: 'Zcash.Snark.NontrivialRelation.ofFoldedGens' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofFoldedGens

/-- info: 'Zcash.Snark.NontrivialRelation.ofLeafPeel' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofLeafPeel

/-- info: 'Zcash.Snark.NontrivialRelation.ofDeployedTree' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofDeployedTree

/-- info: 'Zcash.Snark.NontrivialRelation.ofUnopenedFork' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofUnopenedFork

/-- info: 'Zcash.Snark.NontrivialRelation.ofUnopenedForkVesta' depends on axioms: [propext,
Classical.choice,
Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofUnopenedForkVesta
