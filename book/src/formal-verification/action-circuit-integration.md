# Action circuit integration roadmap

This note maps the missing semantic last mile between the deployed Halo 2 verifier
model in `Zcash/Snark` and the proved post-NU6.3 Action circuit in
`Zcash/Circuits/Action`.

For each supplied public Action, constructively
extract `ActionData` whose ten public fields equal that Action's instance column, prove
the complete §4.17.4 Action statement, and prove the post-NU6.3 cross-address
condition.

## Upstream open-PR landscape

Four open pull requests on
[`zcash/ironwood`](https://github.com/zcash/ironwood) carry most of the relevant
implementation:

- [#89, Add Ironwood circuit formalization](https://github.com/zcash/ironwood/pull/89),
  supplies the Action circuit, `soundnessPost`, and the executable Rust/Clean CS and
  layout comparisons. It is the base of this integration.
- [#30, Bind IPA witness to verifier columns](https://github.com/zcash/ironwood/pull/30),
  implements the deployed `x₄` and `x₁` decode, member-commitment and
  claimed-evaluation binding, and decoded-column capstone foundations.
- [#91, Permutation and lookup arguments](https://github.com/zcash/ironwood/pull/91),
  extends #30's polynomial constraint model with the verifier's permutation and lookup
  expressions, splits the combined constraint check, reads the arguments row by row,
  telescopes their running products, and reaches copy-equality and lookup-inclusion
  endpoints. It is a draft stacked on #30's `decode-witness` branch, not on `main`.
- [#85, Derive instance commitments](https://github.com/zcash/ironwood/pull/85),
  removes statement-derived instance commitments from the circuit-fixed VK, derives
  them from public inputs, and exercises the result with single- and multi-Action
  fixtures.

Two administrative PRs identify the eventual landing surface:
[#79](https://github.com/zcash/ironwood/pull/79) consolidates the checked trust-boundary
census, and [#82](https://github.com/zcash/ironwood/pull/82) makes the proof map point at
the current computed capstone. Neither proves a semantic bridge.

The integration branch combines these APIs while preserving #85's architectural
split: the verifying key contains circuit-fixed data, and statement-derived instance
commitments remain explicit inputs to the verifier and soundness stack.

## Stable semantic endpoint

`Action.Circuit.soundnessPost` already proves

```text
Clean environment assumptions
  + exact synthesized-operation constraints
  -> SpecPost realGenerators realBases extractedActionData.
```

The intended final adapter is small once those premises are available:

```text
placed Clean environment satisfying `mainPost`
  -> ActionStatement public
  -> the hencodes conclusion expected by SnarkRelation.
```

The final implementation should define the high-level public input/statement types and
the direct `soundnessPost` adapter alongside the concrete decoded-member-to-Clean
construction. The following work items decompose that construction.

### 1. Recover the committed columns from multiopen

**Status: substantially implemented by
[#30](https://github.com/zcash/ironwood/pull/30), with
[#85](https://github.com/zcash/ironwood/pull/85)'s statement-derived instance
commitments threaded through the combined stack.**

The `a` in the current `SnarkRelation` is an opening of the final `x₄`-collapsed,
`x₁`-compressed multiopen commitment. It is not an advice-column vector and cannot be
read directly as an Action witness.

#30 now connects the Vandermonde-style recovery to the deployed
`assembleOpening`/`constructIntermediateSets` shape. Its `x4BatchCommitments`,
`x4BatchEvals`, `decodedCols`, `x1DecodeCols`, `deployed_witness_member_binding`, and
budgeted node-binding results recover the point-set aggregates, unbatch their member
columns, and bind those members to the routed commitments and claimed evaluations.
The transcript-prefix and multiopen-challenge rewinds are modeled as well.

The remaining work is:

1. produce #30's batch/member-decode data from the live computed experiment without
   the remaining family-wide `hExtract`/adaptive-coupling supply premise;
2. route the recovered members into the full constraint model from #91 and then into
   the Clean Action assignment described below.

### 2. Replace the free column decoders

**Status: polynomial/query-level decoding is implemented by
[#30](https://github.com/zcash/ironwood/pull/30); the generic Clean row decoder is now
implemented on this branch, while its concrete Action instantiation remains open.**

The deployed/member capstones use canonical decoding through `coeffsToPoly`,
`decodedCols`, `x1DecodeCols`, query-layout member selection, and `rotatedFeed`. The
extracted opening and the polynomials consumed by those capstones are therefore not
independent.

`PolynomialEnvironment` is the canonical decoder from those polynomials to values on
the size-`2^k` evaluation domain. It evaluates column `c` at row `r` as
`c(ω^r)` and proves that Clean's rotated advice, fixed, and instance queries agree
with the verifier's rotated polynomials. `resolverEnvironment` selects fixed,
per-proof advice, and per-proof instance columns from the shared `CommitmentId`
resolver.

The concrete Action construction still has to prove that:

- column/query indices match the VK query layouts;
- instance values are the supplied Action public inputs;
- usable and blinding rows are treated exactly as Halo 2 treats them.

Then expose the result as the row-indexed Clean `Environment` used by
`Action.Circuit.soundnessPost`. The remaining gap is not the old free-polynomial
decoder; it is the polynomial/query representation to Clean row/placement
representation.

### 3. Prove reusable VK correctness

**Status: executable coverage in
[#89](https://github.com/zcash/ironwood/pull/89) and public-instance provenance in
[#85](https://github.com/zcash/ironwood/pull/85); the projection's *semantics* are now
proven on this branch, but the fixture-equality side still has no reusable theorem.**

`Zcash.Circuits.Fixtures.ProjectSemantics` proves that the VK-match projection
preserves meaning: selector compression is evaluation under the root-finding
replacement valuation (`substSelectorMap_eval`, with the packed-column case algebra
`selReplacement_eval_of_root`/`_of_other`/`_of_zero`), and the query-index erasure walk
evaluates to the original gate expression whenever the evaluation families interpret
the walk's final query layout (`eraseExpr_eval`; composed per gate as
`eraseExpr_substSelectorMap_eval`). The projection now targets the verifier's own gate
AST (the shared `Zcash/Common/Expr.lean`), so no translation layer separates the two
sides. What remains here is the *syntactic* linking:

The circuit subtree already contains strong executable checks:

- `TestVkMatchAction` compares the projected Clean `ConstraintSystem` with the Rust
  pre- and post-selector-compression dumps;
- `TestVkLayoutAction` compares placements, ordered copies, permutation σ, and fixed
  columns with the Rust layout dump.

They are build-time `IO` Boolean checks over JSON fixtures, not propositions reusable
by soundness. Refactor the projections and fixture values so kernel-checked theorems
state that the actual `VerifyingKey` fields used by `Zcash.Snark` correspond to:

- **done on this branch**: `Zcash.Circuits.Fixtures.PartialPinnedConstraintSystem`
  models the sub-record of halo2's `PinnedConstraintSystem` the capture certifies, and
  its derivation from a Clean constraint system (`derive`, taking the two keygen
  witnesses — registration seed and selector-compression map — as explicit inputs
  until the keygen ports compute them); `Fixtures.SingleAction.PinnedCsMatch`/
  `VkMatch` compute the captured VK's pinned CS equal to the derived Action circuit
  (per-field `native_decide` on the fast CS-data dump, `capturedPinnedCs_eq_derived`
  over the full record — counts, constants, and minimum degree included — with
  `VkMatch` exporting the per-field verifying-key links), and `derive_gates_eval`
  hands every VK gate's evaluation to the Clean gate expressions. The
  selector-compression map is now *derived* from the circuit
  (`deriveSelCompressMap`, the `compress_selectors` port, checked equal to the Rust
  dump by `TestSelMapDerivation`); pending: the floor-planner placement port (making
  the derivation's activation input circuit-side) and the permutation columns (with
  the commitment-matching phase);
- `Action.Circuit.configure orchardGenerators` after selector compression;
- the post-NU6.3 `mainPost` layout at `orchardBases`;
- the fixed commitments, permutation commitments, and query/chunk ordering produced
  by key generation.

#85 makes the correct architectural split: `VerifyingKey` contains circuit-fixed data,
while `assembleQueries` receives per-proof instance commitments derived by
`commitLagrange` from public inputs. Its captured-fixture theorem proves that derivation
for the fixtures. The reusable theorem still needs to connect the actual Action public
input vectors to that generic derivation and connect the remaining VK fields to #89's
Clean configuration and layout.

#30 currently carries `hadviceLayout`, `hinstanceLayout`, quotient routing, and related
facts as capstone hypotheses. The VK theorem should discharge those facts rather than
merely restating fixture equality.

### 4. Strengthen circuit satisfaction beyond custom gates

**Status: the protocol mathematics is implemented by draft
[#91](https://github.com/zcash/ironwood/pull/91); deployed reachability and the mapping
to Clean operations remain open.**

#30's decoded capstones record only the combined custom-gate quotient identity. #91
defines the full gate/permutation/lookup constraint list over polynomials, proves that
evaluation commutes with its builders, and identifies its `y` fold with the verifier's
own `allExpressions`/`expected_h_eval` fold. This removes the former permutation/lookup
fingerprint premise at the quotient check. Its latest stack additionally proves:

- a good `y` splits the combined check into divisibility of every individual
  constraint;
- the permutation row equations telescope through each chunk and across chunks;
- the resulting multiset identity gives equal values on each permutation cycle;
- the lookup row equations and product identity imply every input value occurs in the
  table.

This integration branch now packages the deployed flat list as
`ConstraintPolyModel.constraints`, turns the split theorem into the family-separated
`ConstraintSatisfaction` record, and exposes named membership/divisibility facts for
each selected lookup's five constraints. `LookupRows` reads those five polynomial
constraints over the evaluation domain and closes the lookup endpoint, including the
explicit zero-factor branch when the running product ends at zero.
`LookupInstantiation` now constructs those coherent lookup entries from an arbitrary
VK and a `CommitmentId`-keyed polynomial resolver, proves that openings for the actual
assembled lookup queries give the verifier's five claimed evaluations, and specializes
`ConstraintSatisfaction` to the compact five-constraint record consumed by that
endpoint. `Multiopen.ConstraintResolver` now constructs that resolver from
`OpenedMemberDecode` columns and a partial commitment-ID-to-member routing, and turns
the existing member-node binding into uniform query openings or the existing
nontrivial-relation branch. It feeds the clean branch directly into the lookup
instantiation theorem. The grouping layer now proves claimed-value faithfulness on
the verifier's non-duplicate path, constructs the commitment-ID route automatically,
and derives its coverage and non-duplication premises from a successful `assemble?`.
`PermutationInstantiation` now supplies the analogous permutation layer. It maps
running products through `permProduct`, maps each chunk's value-side `ColumnRef`
through the corresponding VK query-layout entry, maps its σ-side through
`permCommon`, and proves that evaluating the resulting polynomial records reproduces
`subProofPermSets` and `subProofPermChunks`. The decoded-member specialization retains
the nontrivial-relation branch. Its resolver-backed constraint model and
`ResolverPermutationConstraints` package extract the exact step, inter-set chain,
start, and end divisibility facts consumed by
`deployed_perm_copy_constraints_all_chunks`. `PermutationSemantics` now completes the
generic semantic call: `ResolverPermutationDomain` isolates the concrete VK/domain
facts, `ResolverPermutationCycle` carries the replayed global cell permutation and
the common-polynomial naming equation, and
`ResolverPermutationGoodChallenges` carries the separately priced `β`/`γ`
exclusions. Given those records,
`ConstraintSatisfaction.resolverPermutationCopyConstraints` yields equality on every
keygen permutation cycle (or the theorem's explicit zero-factor branch). The same
module flattens variable-width chunks to global columns and derives chunk-name
injectivity from the standard root-of-unity/coset hypotheses. The generic keygen
construction is now present as well: `replayKeygenPermutation` performs the
source-ordered cycle merges and proves that its cycles are exactly the copy-equivalence
classes; `chunkPermutationOfFlat` conjugates that flat permutation through an
arbitrary concrete chunk layout; and
`keygenSigmaColumn` interpolates the permuted cell names over the evaluation domain.
Its node-evaluation and degree-bound theorems prove that these are exactly the
degree-`< n` common permutation polynomials required by Halo2.
`ResolverPermutationCycle.ofKeygenColumns` then restricts the full-domain keygen
permutation to the active rows and constructs the semantic cycle record; its only
polynomial-identification premise says that each resolver-selected common polynomial
equals the corresponding generated σ column. Keeping the full `n`-row interpolation
separate from the `m` active-row copy theorem is essential: the VK commits to the
former even though soundness reads only the latter.

The active item-4 sequence is:

1. prove a generic grouping theorem that, on the verifier's non-duplicate path, routes
   every flat query to the grouped member carrying its `CommitmentId`, opening point,
   and claimed evaluation;
2. use that theorem to construct `DeployedQueryRoute` automatically for the decoded
   resolver, eliminating its remaining assembled-query bookkeeping premise;
3. instantiate the permutation set/chunk polynomials from the same resolver and feed
   `deployed_perm_copy_constraints_all_chunks`;
4. package the resulting gate, copy, and lookup conclusions as the full
   circuit-satisfaction interface consumed by the Clean-operation bridge.

Steps 1 and 2 are complete, and both generic halves of step 3 are complete: decoded
polynomials instantiate the four permutation constraint families, and the structured
semantic endpoint feeds them to the all-chunks copy theorem. Concrete closure now
means constructing its records for the Action VK. In detail: the chunks must match
the permutation-set count; every chunk `ColumnRef` must select an in-range,
rotation-zero query-layout entry and every `permCommon` index must be in range;
`ω^m` must be the verifier's last-row rotation; the replayed keygen σ must map each
cell to the permutation-column name interpolated by the decoded common polynomial;
and the remaining domain/coset facts must be discharged. The `β`/`γ` exclusions stay
with the forking/bad-set accounting. These facts are deliberately separate from
polynomial routing: most are circuit/VK computations or the VK-to-σ interpolation
theorem, not multiopen claims.

The interpolation theorem itself is no longer concrete work. Once the Action
permutation data lands, it remains to build the flat-to-chunk equivalence, instantiate
the generated columns, and prove that their commitments are the concrete VK's
`permutationCommonCommitment`s. Commitment binding then supplies the
`ofKeygenColumns` polynomial equalities (or the existing nontrivial-relation branch).

The residual zero-factor branch is now closed generically as well.
`additiveZeroBadSet` observes that, after `β` and the committed cell values are fixed,
each factor `value + β·name + γ` excludes exactly one value of the later `γ`
challenge. `resolverPermutationZeroFactorBadSet` collects those exclusions,
`uniformChallenge_resolverPermutationGammaBadSet` combines their active-cell count
with the existing Schwartz–Zippel root budget, and
`resolverPermutationCopyConstraints` now concludes cycle equality directly under the
combined good-`γ` condition. Thus concrete Action work need not propagate a
zero-product disjunction; it only supplies the already explicit challenge-avoidance
premise at the correct transcript squeeze.

After that, translate the endpoints to the exact relations that Clean's
`Halo2.Constraints` requires: declared `constrainEqual`/`constrainInstance` copies,
`RegionOperation.enableLookup` membership with the exact loaded tables, fixed
assignments and selector activations, and all synthesized regions under their actual
placement. Replace the gate-only circuit predicate with a full satisfaction record;
custom gates alone still cannot imply the Action operation trace.

The generic target and copy half of that translation are now in place.
`FullCircuitSatisfaction` splits the authoritative `Halo2.Constraints` predicate into
gate, copy, lookup, and fixed/table fields and proves exact equivalence in both
directions. `operationDeclaredCopies` extracts equality, instance, and constant copies from the
complete operation stream; `copy_constraints_iff_declaredCopies` proves that their
satisfaction is exactly the full record's copy field. Finally,
`copy_constraints_or_bad_of_replay` transports equality from the generic keygen
permutation cycles to every declared copy while preserving the caller's shared
exceptional event (for example commitment binding). Permutation zero factors
themselves are already eliminated by the priced `γ` exclusion above. The concrete
layout instantiation only has to encode endpoints as keygen cells (including
constants-column allocations) and identify their environment reads.

The generic lookup and reassembly halves are now present too.
`operationEnabledLookups` extracts every placed `enableLookup` activation and
`lookup_constraints_iff_enabledLookups` proves that their tuple membership is exactly
the full record's lookup field. `resolverLookupSubset` joins the five resolver-backed
constraint families to the deployed row theorem. Its `β`/`γ` zero-product branch is
eliminated by `lookupColumnZeroBadSet`, at one excluded challenge value per usable
row. `foldPoly_injective_of_length_eq` then proves the separate `θ` step:
equal-length tuples with equal compressions are equal outside their explicit
compression-difference root set. `EnabledLookup.thetaBadSet` unions those roots over
the usable table rows and bounds the event by
`usableRows × tupleArity / |Fp|`.

`EnabledLookup.DeployedWitness` packages the remaining representation facts for one
activation: the matching resolver input/table polynomials, row-evaluation coherence,
usable-row count, tuple arity, scalar subset, and good `θ`. Finally,
`FullCircuitBridge` combines those lookup witnesses with gate/fixed satisfaction and
the copy-replay witness. Its `satisfaction_or_bad` theorem returns the exact
`FullCircuitSatisfaction` record, and `constraints_or_bad` returns Clean's single
ground-truth `Halo2.Constraints`. The remaining Action-specific work is therefore
construction of these records, not another semantic proof.

The per-gate half of that translation is proven
(`eraseExpr_substSelectorMap_eval` plus the packed-selector row algebra), and the
reassembly should be stated *generically*: one theorem by induction
over an arbitrary `Halo2.Operations` list, taking gate vanishing, copy equalities,
lookup membership, and fixed-column data as inputs, with the circuit-specific facts
isolated into decidable coherence side conditions — every enabled gate registered in
the constraint system, gate polynomials linear in their own selector and free of
foreign selectors, co-packed selectors never co-enabled, the activation table matching
the packed fixed columns, rows within bounds. Those side conditions are discharged for
the Action instance computationally (the same `native_decide`-style work the VK-match
and layout tests already do), not by an Action-specific proof walk. The
`Fixtures.Layout` reconstruction is already generic over operations, so σ-cycle
correctness of its replayed keygen merge is likewise a once-and-for-all lemma. A useful
de-risking step is to instantiate the generic theorem first for the small `AddChip`
fixtures before the full Action circuit.

### 5. Construct the Clean assignment

**Status: open. [#89](https://github.com/zcash/ironwood/pull/89) supplies the target
semantics, while [#30](https://github.com/zcash/ironwood/pull/30) and
[#91](https://github.com/zcash/ironwood/pull/91) supply most of the prospective source
data.**

From the recovered per-column row values, build:

- `Environment.get` for advice, fixed, and instance columns;
- `Environment.usableRows` from `n` and the VK blinding factor;
- the post-NU6.3 floor-planner placement;
- the concrete `Config` returned by `Action.Circuit.configure`;
- an arbitrary `PrivateInputs.Var` (soundness does not inspect its verifier value;
  extraction reads the environment).

Then prove `Action.Circuit.EnvAssumptions`, including generator-table exactness, all
table-loaded facts, fixed-base environment assumptions, and selector distinctness.
No current open PR performs this construction. This is the central Action-specific
representation bridge.

Note that most of `EnvAssumptions` should come out of the transported `Constraints`
themselves rather than separate VK-fixed-data facts: `GeneratorTableExact` is defined
as the `Constraints` of the generator-table load, and the Action circuit's own
operations contain the `loadTable`/`assignFixed` steps whose transported clauses pin
the same fixed cells the table-loaded and fixed-base assumptions read.

### 6. Generalize from one Action to an Orchard bundle

**Status: verifier-side substrate is generic in #30/#91 and exercised by
[#85](https://github.com/zcash/ironwood/pull/85); the semantic conclusion remains
single-Action.**

A deployed proof covers `shape.numProofs` Actions. Generalize `PublicInputs`,
`Assignment`, and `ActionStatement` to a `Fin shape.numProofs` family and decode one
Clean assignment per sub-proof. The shared fixed columns and VK are common, while
advice/instance columns and protocol statements are per Action. The final conclusion
should quantify over or return the high-level statement for every supplied Action.

#85's multi-Action fixture derives each proof's instance commitment and proves that
sub-proof commitment slots remain disjoint. #30 and #91 already build much of their
verifier-side data over `Fin shape.numProofs`, but #30's member capstone selects a
single `pp : Fin shape.numProofs`. The integration theorem must turn that parametric
single-index result into a family of Clean assignments and Action statements.

### 7. Thread the bridge into the live capstone

**Status: substantial foundations in
[#30](https://github.com/zcash/ironwood/pull/30),
[#91](https://github.com/zcash/ironwood/pull/91), and
[#85](https://github.com/zcash/ironwood/pull/85); no end-to-end Action theorem yet.**

Once the direct semantic bridge exists, instantiate the Vesta constraint capstones
with the concrete high-level Action statement. Then thread that same concrete
statement through the computed Fiat–Shamir/AGM endpoint.

#30 adds `orchard_verifier_sound_vesta_computed`, whose original circuit predicate was
the concrete gate check over decoded member columns rather than a free decoder. This
branch now strengthens that endpoint's extracted relation with exact
`FullCircuitSatisfaction` of the same witness and carries both facts in
`circuitSatViaGatesAndOperations`. This is type-level plumbing, not yet the final
derivation: the endpoint currently receives the full-satisfaction proof and decoded
environment as inputs. Supplying them from the deployed constraint split and the
Action records is the next representation step.

The computed endpoint still receives batch/decode/gate/layout data by hand, and its
quantitative endpoint remains conditional on the family-wide
`hExtract`/adaptive-coupling data-supply premise. #85 threads statement-derived
instance commitments through the live verifier. #82 documents the computed capstone
and #79 provides the eventual trust-boundary census location.

The final theorem should say, modulo the explicitly priced Fiat–Shamir, polynomial
identity, and discrete-log failure events, that acceptance by the modeled deployed
verifier with the post-NU6.3 Action VK yields the high-level statement for every Action
whose public inputs were committed by the verifier.

## Suggested implementation order

1. Complete: instantiate #91's constraint split at the deployed list, route the
   permutation and lookup members to its proved endpoints, and expose a full
   circuit-satisfaction record in the computed endpoint.
2. Make #89's post-compression CS and layout fixtures available as reusable Lean data,
   and prove VK/layout equality theorems that discharge #30's routing hypotheses.
3. The canonical polynomial-to-row decoder is complete. Construct its placed Action
   environment and prove `Action.Circuit.EnvAssumptions`.
4. Prove the decomposed full-satisfaction-to-Action bridge, first for one selected
   Action and then for every `Fin shape.numProofs`.
5. Supply the decoded/full-satisfaction data inside the computed experiment, close the
   remaining adaptive-coupling/`hExtract` obligation, instantiate the endpoint with
   `ActionStatement`, and add the theorem to the consolidated trust boundary.
