# Action circuit integration spike

This note maps the missing semantic last mile between the deployed Halo 2 verifier
model in `Zcash/Snark` and the proved post-NU6.3 Action circuit in
`Zcash/Circuits/Action`.

A short executable blueprint previously recorded this destination against the legacy
free-decoder capstone API. It was intentionally removed before integrating #30/#91:
adapting its `Decoder` and monolithic gate-to-Action proposition would preserve the
wrong abstraction more expensively than rebuilding the small semantic adapter against
the decoded-member and full-constraint interfaces.

The durable destination is unchanged: for each supplied public Action, constructively
extract `ActionData` whose ten public fields equal that Action's instance column, prove
the complete §4.17.4 Action statement, and prove the post-NU6.3 cross-address
condition.

## Upstream open-PR landscape

This roadmap was reconciled with the open pull requests on
[`zcash/ironwood`](https://github.com/zcash/ironwood) on 2026-07-23. Four PRs carry
most of the relevant implementation:

- [#89, Add Ironwood circuit formalization](https://github.com/zcash/ironwood/pull/89),
  supplies the Action circuit, `soundnessPost`, and the executable Rust/Clean CS and
  layout comparisons. It is the base of this spike.
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

These are coverage notes about open, unmerged work, not assumptions that the branches
already compose. In particular, #30 and #85 both change the verifier and soundness
signatures, while #91 inherits #30's pre-#85 API. They must be reconciled before the
last-mile Action integration can depend on all three.

## Stable semantic endpoint

`Action.Circuit.soundnessPost` already proves

```text
Clean environment assumptions
  + exact synthesized-operation constraints
  -> SpecPost realGenerators realBases extractedActionData.
```

The discarded blueprint checked that the intended final adapter is small once those
premises are available:

```text
placed Clean environment satisfying `mainPost`
  -> ActionStatement public
  -> the hencodes conclusion expected by SnarkRelation.
```

No replacement declarations should be introduced until the #30/#85/#91 interfaces
have been reconciled. The final implementation should define the high-level public
input/statement types and the direct `soundnessPost` adapter alongside the concrete
decoded-member-to-Clean construction, rather than installing another abstract decoder
or monolithic bridge. The following work items decompose that construction.

### 1. Recover the committed columns from multiopen

**Status: substantially implemented by
[#30](https://github.com/zcash/ironwood/pull/30); instance-commitment provenance is
improved by [#85](https://github.com/zcash/ironwood/pull/85).**

The `a` in the current `SnarkRelation` is an opening of the final `x₄`-collapsed,
`x₁`-compressed multiopen commitment. It is not an advice-column vector and cannot be
read directly as an Action witness.

#30 now connects the Vandermonde-style recovery to the deployed
`assembleOpening`/`constructIntermediateSets` shape. Its `x4BatchCommitments`,
`x4BatchEvals`, `decodedCols`, `x1DecodeCols`, `deployed_witness_member_binding`, and
budgeted node-binding results recover the point-set aggregates, unbatch their member
columns, and bind those members to the routed commitments and claimed evaluations.
The transcript-prefix and multiopen-challenge rewinds are modeled as well.

The remaining work is integration rather than another decode:

1. reconcile #30 with #85 so the decoded instance members are bound to commitments
   derived from the supplied public inputs, not a VK field;
2. produce #30's batch/member-decode data from the live computed experiment without
   the remaining family-wide `hExtract`/adaptive-coupling supply premise;
3. route the recovered members into the full constraint model from #91 and then into
   the Clean Action assignment described below.

### 2. Replace the free column decoders

**Status: polynomial/query-level decoding is implemented by
[#30](https://github.com/zcash/ironwood/pull/30); Clean row decoding remains open.**

The legacy `circuitSatViaGates` capstones accept arbitrary `decodeAdvice` and
`decodeInstance` functions. #30's newer deployed/member capstones instead use canonical
decoding through `coeffsToPoly`, `decodedCols`, `x1DecodeCols`, query-layout member
selection, and `rotatedFeed`. The extracted opening and the polynomials consumed by
those capstones are therefore no longer independent.

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
[#85](https://github.com/zcash/ironwood/pull/85), but no reusable bridge theorem.**

The circuit subtree already contains strong executable checks:

- `TestVkMatchAction` compares the projected Clean `ConstraintSystem` with the Rust
  pre- and post-selector-compression dumps;
- `TestVkLayoutAction` compares placements, ordered copies, permutation σ, and fixed
  columns with the Rust layout dump.

They are build-time `IO` Boolean checks over JSON fixtures, not propositions reusable
by soundness. Refactor the projections and fixture values so kernel-checked theorems
state that the actual `VerifyingKey` fields used by `Zcash.Snark` correspond to:

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

Those links are not yet chained from the deployed constraint list: the split theorem
has no deployed instantiation, and the copy/lookup endpoints have no callers. The
immediate generic task is to add the membership lemmas and plumbing that feed
`constraints_dvd_of_good_y` into `deployed_perm_copy_constraints` and
`lookup_subset_of_prod_eval_eq`.

After that, translate the endpoints to the exact relations that Clean's
`Halo2.Constraints` requires: declared `constrainEqual`/`constrainInstance` copies,
`RegionOperation.enableLookup` membership with the exact loaded tables, fixed
assignments and selector activations, and all synthesized regions under their actual
placement. Replace the gate-only circuit predicate with a full satisfaction record;
custom gates alone still cannot imply the Action operation trace.

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
with the concrete high-level Action statement. Then thread the same semantic
conclusion through the computed Fiat–Shamir/AGM endpoint, rather than stopping at a
legacy propositional wrapper.

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

1. Reconcile #85's public-instance API with the combined #30/#91 decoded-column and
   full-constraint stack.
2. Reuse #30's two-level decode and budgeted member binding; do not rebuild the
   `x₄`/`x₁` recovery locally.
3. Instantiate #91's constraint split at the deployed list, route the permutation and
   lookup members to its proved endpoints, and expose a full circuit-satisfaction
   record instead of the gate-only predicate.
4. Make #89's post-compression CS and layout fixtures available as reusable Lean data,
   and prove VK/layout equality theorems that discharge #30's routing hypotheses.
5. Define the canonical polynomial-to-row decoder, construct the placed Clean
   environment, and prove `Action.Circuit.EnvAssumptions`.
6. Prove the decomposed full-satisfaction-to-Action bridge, first for one selected
   Action and then for every `Fin shape.numProofs`.
7. Supply the decoded/full-satisfaction data inside the computed experiment, close the
   remaining adaptive-coupling/`hExtract` obligation, instantiate the endpoint with
   `ActionStatement`, and add the theorem to the consolidated trust boundary.
