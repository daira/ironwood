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
[#30](https://github.com/zcash/ironwood/pull/30); Clean row decoding remains open.**

The deployed/member capstones use canonical decoding through `coeffsToPoly`,
`decodedCols`, `x1DecodeCols`, query-layout member selection, and `rotatedFeed`. The
extracted opening and the polynomials consumed by those capstones are therefore not
independent.

The Action bridge still needs a canonical decoder from those polynomials to values on
the size-`2^k` evaluation domain. Prove that:

- row rotations match `omega` multiplication;
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
  (`vk_pinnedCs_eq_derived`, per-field `native_decide` on the fast CS-data dump), and
  `derive_gates_eval` hands every VK gate's evaluation to the Clean gate expressions.
  Pending for the full pinned record: counts (dumper emission requested), permutation
  columns and constants (with the commitment-matching phase);
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
instantiation theorem. The remaining multiopen bookkeeping must derive the routing
evidence (including grouped claimed-value faithfulness) from `assembleQueries` and
`constructIntermediateSets`; the analogous permutation-set/chunk routing into
`deployed_perm_copy_constraints_all_chunks` also remains.

After that, translate the endpoints to the exact relations that Clean's
`Halo2.Constraints` requires: declared `constrainEqual`/`constrainInstance` copies,
`RegionOperation.enableLookup` membership with the exact loaded tables, fixed
assignments and selector activations, and all synthesized regions under their actual
placement. Replace the gate-only circuit predicate with a full satisfaction record;
custom gates alone still cannot imply the Action operation trace.

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

#30 adds `orchard_verifier_sound_vesta_computed`, whose circuit predicate is the
concrete gate check over decoded member columns rather than a free decoder. It still
receives batch/decode/gate/layout data by hand, and its quantitative endpoint remains
conditional on the family-wide `hExtract` data-supply premise. #91 derives the full
constraint fold, splits it under a good `y`, and proves the permutation/lookup semantic
endpoints, but does not yet call them from the deployed list; it also records the
adaptive `x`-challenge coupling as standing work. #85 threads statement-derived
instance commitments through the live verifier. #82 documents the computed capstone
and #79 provides the eventual trust-boundary census location; neither changes these
proof obligations.

The final theorem should say, modulo the explicitly priced Fiat–Shamir, polynomial
identity, and discrete-log failure events, that acceptance by the modeled deployed
verifier with the post-NU6.3 Action VK yields the high-level statement for every Action
whose public inputs were committed by the verifier.

## Suggested implementation order

1. Instantiate #91's constraint split at the deployed list, route the permutation and
   lookup members to its proved endpoints, and expose a full circuit-satisfaction
   record instead of the gate-only predicate.
2. Make #89's post-compression CS and layout fixtures available as reusable Lean data,
   and prove VK/layout equality theorems that discharge #30's routing hypotheses.
3. Define the canonical polynomial-to-row decoder, construct the placed Clean
   environment, and prove `Action.Circuit.EnvAssumptions`.
4. Prove the decomposed full-satisfaction-to-Action bridge, first for one selected
   Action and then for every `Fin shape.numProofs`.
5. Supply the decoded/full-satisfaction data inside the computed experiment, close the
   remaining adaptive-coupling/`hExtract` obligation, instantiate the endpoint with
   `ActionStatement`, and add the theorem to the consolidated trust boundary.
