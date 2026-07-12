import Zcash.Security.Ledger.Statement
import Mathlib.Util.AssertNoSorry

/-!
# Checked trust boundary of the ledger-layer break reductions

Build-time enforcement of the breaks-as-computed-data discipline (see
`Zcash.Security.RandomOracle`), following the pattern of
`Zcash.Snark.Fixtures.SingleAction.TrustBoundary`. The reductions' computability is already
compiler-enforced: they are plain `def`s, so a `noncomputable` dependency fails the build.
What a build does not otherwise pin down is a `sorry` reached through some dependency, or an
unexpected axiom. Both checks below follow the elaborated dependency graph, so they see
holes anywhere in the transitive closure.

The pinned axiom sets record that the data-producing reductions rest on `propext` and
`Quot.sound` only — in particular **no `Classical.choice`**, so the break data cannot have
been conjured from mere propositional existence.
-/

open Zcash.Security.Ledger Zcash.Security.RandomOracle

assert_no_sorry Collision.upToSign
assert_no_sorry Merkle.collisionOfWrongLeaf
assert_no_sorry noteCommitBreakOfNe

/-- info: 'Zcash.Security.RandomOracle.Collision.upToSign' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Collision.upToSign

/-- info: 'Zcash.Security.Ledger.Merkle.collisionOfWrongLeaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Merkle.collisionOfWrongLeaf

/-- info: 'Zcash.Security.Ledger.noteCommitBreakOfNe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms noteCommitBreakOfNe
