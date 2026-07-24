# Action circuit integration roadmap

This note maps the missing semantic last mile between the deployed Halo 2 verifier
model in `Zcash/Snark` and the proved post-NU6.3 Action circuit in
`Zcash/Circuits/Action`.

For each supplied public Action, constructively
extract `ActionData` whose ten public fields equal that Action's instance column, prove
the complete §4.17.4 Action statement, and prove the post-NU6.3 cross-address
condition.

## Upstream PR landscape

Two open implementation pull requests on
[`zcash/ironwood`](https://github.com/zcash/ironwood) carry the remaining verifier
work:

- [#30, Bind IPA witness to verifier columns](https://github.com/zcash/ironwood/pull/30),
  implements the deployed `x₄` and `x₁` decode, member-commitment and
  claimed-evaluation binding, and decoded-column capstone foundations.
- [#91, Permutation and lookup arguments](https://github.com/zcash/ironwood/pull/91),
  extends #30's polynomial constraint model with the verifier's permutation and lookup
  expressions, splits the combined constraint check, reads the arguments row by row,
  telescopes their running products, and reaches copy-equality and lookup-inclusion
  endpoints. It is stacked on #30's `decode-witness` branch, not on `main`.

Three directly relevant PRs are now merged into `main`:

- [#89, Add Ironwood circuit formalization](https://github.com/zcash/ironwood/pull/89)
  supplies the Action circuit, `soundnessPost`, and the executable Rust/Clean CS and
  layout comparisons. It was the original base of this integration.
- [#85, Derive instance commitments](https://github.com/zcash/ironwood/pull/85),
  removes statement-derived instance commitments from the circuit-fixed VK, derives
  them from public inputs, and exercises the result with single- and multi-Action
  fixtures.
- [#79](https://github.com/zcash/ironwood/pull/79) consolidates the checked
  trust-boundary census into `Zcash/TrustBoundary.lean` and enforces explicit axiom
  tiers through the `AxiomCheck` macros.

The still-open [#82](https://github.com/zcash/ironwood/pull/82) makes the proof map
point at the current computed capstone; it does not prove a semantic bridge.

The integration branch combines these APIs while preserving #85's architectural
split: the verifying key contains circuit-fixed data, and statement-derived instance
commitments remain explicit inputs to the verifier and soundness stack.

## Stable semantic endpoint

`Action.Circuit.soundnessPost` already proves

```text
Clean environment assumptions
  + exact constraints of the closed, unit-input synthesis
  -> SpecPost realGenerators realBases extractedActionData.
```

Both proof-carrying Action circuits now expose `unit` input. Their prover choices are
the fixed `Action.Circuit.hintWitnesses` program: field, point, scalar, and Merkle-path
values are read from the runtime `ProverHint` through `hintGet` (the existing native
Merkle-swap function reads the same hint environment). The raw
`synthesizeBase ... W` function remains useful for internal circuit lemmas, but neither
the base nor post-Ironwood `FormalCircuit` lets its caller select `W`.

Correspondingly, `Bridge.actionOperations` is synthesized from the real
`orchardActionCircuit` at unit input. The separate synthetic
`Bridge.keygenWitnesses` value has been removed.

The intended final adapter is small once the remaining premises are available:

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

Public-instance row provenance now has a canonical target as well.
`instanceRowPolynomial` Lagrange-interpolates a zero-padded list of public values over
the `ω` domain, `instanceRowPolynomial_eval` proves that it reads those rows back, and
`resolverEnvironment_instance_of_rowPolynomial` transports a decoded-polynomial
identity directly to the corresponding Clean instance reads.

The generic cryptographic step is now complete in `InstanceCommitment`.
`LagrangeCommitmentKey` states the circuit-independent setup relation between each
Lagrange generator and the monomial URS. `commitRows_eq` proves that Halo 2's
Lagrange-basis public-instance commitment is the monomial commitment of the
interpolated coefficient vector. Consequently,
`coeffsToPoly_eq_instanceRowPolynomial_or_relation` proves that any augmented
`(g, U, W)` opening of that commitment is the canonical zero-padded row polynomial,
or computes the existing nontrivial-relation branch. At the deployed endpoint,
`OpenedMemberDecode.commitment` supplies that opening for the routed instance member.
The verifier grouping now preserves enough indexed provenance to close the intervening
step generically: `constructIntermediateSets_member_provenance` shows that a grouped
commitment and its retained identity arise from the same assembled query,
`assembleQueries_instance_commitment` identifies every `.instanceCol p column` query
with the statement-derived commitment, and
`deployedMemberRef_eq_instanceCommitment` composes those facts for any deployed
member slot. None of these theorems mentions Action placement or operations.

`actionPublicInputs_of_instanceRowPolynomial` then performs the only Action-specific
row mapping: the first ten reads of the configured primary column are exactly the
structured `Action.PublicInputs`.
`CanonicalMemberConstraintRelation.instanceColumn_eq_rowPolynomial_or_relation`
now performs the deployed representation step generically. It follows an assembled
instance query through the canonical grouped-member route, identifies that member's
commitment with the verifier-supplied instance commitment, and concludes that the
decoded polynomial is the canonical row polynomial or computes the shared nontrivial
relation. The binding-aware Action endpoint invokes this theorem internally; it no
longer accepts the decoded-polynomial equality as a premise. Its remaining concrete
instance inputs are the parameters' `LagrangeCommitmentKey`, the public-input
commitment equation, and coverage of the configured primary column by the derived
instance query layout. The endpoint now states that last fact in the circuit's native
language—registration of the primary column in its synthesis-closed constraint
system. The generic query compiler proves that configure-registered layouts survive
packed-selector insertion and the gate/lookup erasure walks, and then the generic
layout-to-assembly lemma supplies the actual proof- and challenge-dependent query.
The endpoint also derives evaluation-domain injectivity and size equalities from
`TopLevelCircuit` plus the existing supported-`k` bound.

The exported fixture contains only the ten Lagrange generators reachable by Action
public rows, rather than the whole 2048-row domain. `LagrangeCommitmentKey.ofPrefix`
matches that representation: it turns a certified exported prefix into a full key by
using canonical monomial-URS commitments beyond the prefix. Thus the concrete setup
certificate needs ten generator equations, not 2048; zero padding ensures the
synthetic suffix cannot affect the instance commitment.
`ofPrefix_commitInstance_eq` proves this last step generically and matches the
fixture's finite-prefix commitment computation directly.
`commitPrefixNat_eq_commitPrefix` additionally discharges the representational
difference between the fixture's executable `c.val • point` natural-scalar sums and
the abstract `Fp`-module commitment, leaving only the ten actual generator equations
as concrete setup data.

The concrete Action construction still has to prove that:

- the configured primary column occurs in the circuit-derived instance query layout;
- the verifier-supplied commitment is the Lagrange commitment of the supplied Action
  public inputs;
- the exported Lagrange generators certify the compatible commitment key;
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
- the closed post-NU6.3 `mainPost` layout at `orchardBases`, whose operation stream is
  now derived directly from `orchardActionCircuit`;
- the fixed commitments, permutation commitments, and query/chunk ordering produced
  by key generation.

#85 makes the correct architectural split: `VerifyingKey` contains circuit-fixed data,
while `assembleQueries` receives per-proof instance commitments derived by
`commitLagrange` from public inputs. Its captured-fixture theorem proves that derivation
for the fixtures. The generic basis-conversion and binding theorem is now reusable;
the concrete setup certificate still has to identify the exported Lagrange generators
with the monomial URS relation. The remaining VK fields still need to be connected to
#89's Clean configuration and layout.

#30 currently carries `hadviceLayout`, `hinstanceLayout`, quotient routing, and related
facts as capstone hypotheses. The VK theorem should discharge those facts rather than
merely restating fixture equality.

### 4. Strengthen circuit satisfaction beyond custom gates

**Status: the protocol mathematics and generic Clean-operation adapters are
implemented. Concrete Action closure now consists of fixed/selector realization,
copy replay packaging, lookup challenge data, and assembly of those families.**

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
`ConstraintSatisfaction.of_circuitSatViaConstraints` now also connects the capstone
identity directly to that record: a good folding challenge splits
`circuitSatViaConstraints` into divisibility of every modeled constraint. This is the
generic deterministic seam at which [#96](https://github.com/zcash/ironwood/pull/96)'s
extraction/probability result can hand its witness to this PR. #96 deliberately keeps
the final encoding relation abstract; this PR's completion criterion is to eliminate
those free `hencodes`/statement parameters by deriving the concrete Action bundle
statement.

That endpoint now has a canonical, bundle-wide type.
`CanonicalMemberConstraintRelation` derives its commitment-ID polynomial resolver
from the decoded members and the deployed assembled-query route, then constructs the
entire constraint model from the accepted VK. Fixed columns, permutation sets/chunks,
lookups, and selector polynomials are no longer free relation parameters.
`actionBundleStatement_of_canonicalRelation` consumes this relation and concludes
the concrete `Action.BundleStatement`, with no abstract `S` or `hencodes` premise and
with the key locked to `orchardActionTopLevelCircuit.toVerifierKey`. It now derives
the complete gate family internally from canonical constraint satisfaction and the
circuit-owned gate/selector coherence package. Its remaining explicit inputs are the
copy, lookup, and fixed operation families. Deriving those three families, rather
than accepting a generic reconstruction function, is now the precise deterministic
completion criterion for `hencodes`.
The binding-aware
`actionBundleStatement_or_relation_of_canonicalRelation` additionally derives the
selector and fixed/table families from `TopLevelFixedCoherence`; its only remaining
operation-family premises are copy and lookup satisfaction. It also derives the
public-instance polynomial from the routed member and supplied Lagrange commitment
data. A fixed- or instance-column mismatch returns the shared augmented
commitment-relation event instead of becoming a silent binding assumption.
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
The Clean-facing representation step is now generic as well.
`LookupProjection` proves that the circuit-derived VK's selected input and table
expressions evaluate like their configured Clean expressions.
`TopLevelLookups` routes every synthesis-enabled lookup to that configured index,
projects its exact selector-substituted tuples into the resolver's compressed
input/table polynomials, and constructs both one `EnabledLookup.DeployedWitness` and
the complete witness family consumed by `FullCircuitBridge`. Its remaining concrete
inputs are deliberately explicit: realization of the packed selector values, the
activation-row fit fact, and the separately priced `β`/`γ`/`θ` exclusions. The first
two are compiler/fixed-layout facts; they are not Action semantic assumptions.
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

The current item-4 sequence is:

1. **complete:** route every assembled query through the canonical decoded-member
   resolver and instantiate the full deployed constraint model;
2. **complete, including Action:** derive the complete gate family from
   circuit-derived query layouts, selector compression, and canonical constraint
   satisfaction; `ActionGateCoherence.topLevelGateCoherence` supplies the deployed
   circuit's static package;
3. **generic layer complete:** route every enabled lookup to its configured argument,
   project its input/table tuples into the resolver polynomials, and construct the
   complete `EnabledLookup.DeployedWitness` family;
4. **generic replay/witness construction complete, Action adapter open:** use the
   proved equality between the executable keygen assembly and
   `replayKeygenPermutation`, plus pairwise resolver-value agreement, to construct the
   concrete `CopyReplayWitness`;
5. instantiate `TopLevelFixedCoherence`, use it to realize packed selectors and fixed
   tables, and discharge the lookup selector-projection fields;
6. combine gate, copy, lookup, and fixed results in `FullCircuitBridge`.

The permutation side has moved past the former “Action permutation data” placeholder.
The Action chunk/domain certificates, decoded σ-column identification, and executable
assembly simulation are present. `runAssembly_getPair` proves that the final assembly
mapping is exactly the action of `replayKeygenPermutation` over the same ordered
copies. `CopyReplayWitness.ofPairCycles` and `.ofPairValues` now perform the generic
packaging. The remaining copy task is the narrow Action representation adapter:
encode Clean copy endpoints as assembly cells, identify their resolver-environment
values, and prove pairwise equality (or the shared exceptional event). The `β`/`γ`
exclusions remain with the explicit bad-set accounting rather than becoming circuit
assumptions.

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

The evaluation-domain selector side is now generic too.
`rowSelectorPolynomial` and `blindSelectorPolynomial` define the canonical `l₀`,
`l_last`, and `l_blind` row polynomials. Their evaluation theorems discharge the
first-row, last-row, and active-row selector premises shared by
`ResolverPermutationDomain` and `ResolverLookupDomain`. The remaining provenance step
is to identify the verifier-side Lagrange polynomials with these canonical
polynomials; it does not depend on Action placement or operations.
`ResolverPermutationDomain.ofCanonicalSelectors` and
`ResolverLookupDomain.ofCanonicalSelectors` now perform this generic discharge:
their callers retain only the actual domain bounds, root facts, and the
permutation-specific chunk/last-rotation facts.

The transcript-side provenance is now explicit rather than assumed.
`domainNodal_eq_vanishing` identifies the interpolation nodes' nodal polynomial
with `X^n - 1`, `domainNodalWeight_eq` computes the corresponding barycentric
weight, and
`rowSelectorPolynomial_eval_eq_lagrangeBasisValue_of_rotation` proves that the
fixed row-selector polynomial evaluates to the verifier's deployed
`lagrangeBasisValue` formula at any rotation naming that row. The blinding
selector is separately identified as the sum of all row selectors after the
last usable row. `blindingDomainRowEquiv` performs the generic finite reindexing
between those rows and the verifier's negative blinding rotations, and
`canonicalLagrangePolynomials_eval` packages the result: away from the
evaluation domain, evaluating the fixed canonical polynomial triple is exactly
the deployed `lagrangeBasis` computation. No Action-specific selector
provenance remains.

`canonicalConstraintModelOfPermutationResolver` now installs that fixed triple
directly into the generic commitment-ID resolver model, eliminating the option
for a downstream caller to pair accepted verifier evaluations with unrelated
selector polynomials. Its selector-evaluation theorem supplies all three
deployed matching equations together.
`ResolverPermutationDomain.ofCanonicalConstraintModel` additionally derives
the last-row rotation, while
`ResolverLookupDomain.ofCanonicalConstraintModel` derives the lookup active-row
boundary. Concrete instantiation retains only the genuine VK chunk counts and
the generic root/domain facts.

Those remaining domain facts are now exposed directly from every fitting
`TopLevelCircuit`. `TopLevelAssignment.domainRoot`,
`domainRowsInjective`, and `domainSizeCastNeZero` provide the root, row
injectivity, and nonzero field-size premises at the circuit-derived exponent.
The two `blindingFactors_*_domainSize` theorems derive the selector and
active-prefix bounds from keygen's existing `FitsAt` certificate (with a
nonempty-operation premise only for the stronger lookup bound).
`TopLevelCircuit.toVerifierKey` now constructs the verifier key from exactly this
circuit-owned keygen data, so no Action arithmetic or separately supplied key is
needed to instantiate the canonical resolver model.

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

The lookup representation boundary is now generic.
`LookupProjection` follows the actual threaded `eraseLookups` compiler walk, selects
the configured argument corresponding to any lookup index, and proves that both
derived pinned tuples evaluate like their selector-substituted Clean source
expressions under the final resolver query layouts. `TopLevelLookups` then routes an
enabled operation through configure/synthesis closure, proves that its compressed
resolver input and table polynomials evaluate to the concrete Clean tuples, and
constructs the one-lookup and whole-operation-stream deployed witness families.
The remaining concrete selector fact is intentionally stronger than the gate
analogue: lookup selectors must have their exact zero/one activation values, not
merely a nonzero scale. Orchard's lookup selectors are complex/lookup-only selectors,
so the fixed-layout constructor should derive that exact projection from their packed
columns rather than expose it as an Action assumption.

The generic gate and fixed/table operation layers are now implemented as well.
`operationEnabledGates` extracts every placed activation and
`gate_constraints_iff_enabledGates` proves exact equivalence with the gate family.
`EnabledGate.PolynomialWitness` identifies each enabled Clean constraint with one
member of #91's selected polynomial gate family up to a certified nonzero scale;
domain divisibility then proves the Clean constraint directly. The scale is essential:
selector compression replaces an enabled selector by a root-finding expression whose
value at its packed root is nonzero, but is not generally one.
`operationFixedRequirements` similarly extracts fixed assignments and table loads,
with `fixed_constraints_iff_requirements` proving exact equivalence to the fixed
family. `FullCircuitBridge.ofPolynomialWitnesses` assembles these gate/fixed witnesses
with the existing copy and lookup witnesses.

Configure/synthesis registration coherence is now enforced at the generic keygen
boundary rather than certified by each concrete circuit. `ConstraintSystem.closeWithOperations`
preserves the raw configure order and appends the first occurrence of every gate or
lookup enabled only by synthesis, including the query registrations that affect
blinding factors. `FormalCircuit.toConstraintSystem` exposes that closed system and
`toPinnedCS` uses it consistently for domain sizing, selector compression, and
projection. For faithful circuits such as Action the closure is inert, as checked by
the existing VK/layout fixtures. `OperationsKeygenCoherent.closeWithOperations` proves
the former registration premise once by construction, and `TopLevelCircuit.keygenCoherent`
instantiates it without an Action certificate. `OperationsKeygenCoherent.gate` and
`.lookup` still provide the convenient transport from an extracted activation to
membership in the closed CS. The separate question whether registered gate
expressions satisfy `Gate.WellFormed` is intentionally unchanged.

The scaling algebra is now proved in `GateProjection`.
`Expression.GatedBy` captures exactly the required gate shape: linear in the gate's
own selector and independent of foreign selectors. It composes across sums and
multiplication by selector-free expressions.
`eval_substSelectorMap_eq_scale_queryEval` then proves that a compressed verifier gate
evaluates to the packed selector scale times Clean's enabled-gate evaluation whenever
the fixed/advice/instance query valuations agree. `ConstraintSystem.GatesWellFormed`
packages the remaining static configure certificate and projects the property to
every registered constraint.

The resolver representation now follows Halo2's query indexing exactly. An `Expr`
leaf indexes a VK query-layout entry `(column, rotation)`, so
`constraintModelOfResolver` feeds it the decoded base column composed with
`ω^rotation · X`, rather than incorrectly treating the query index as a column index.
`resolverQueryFeeds_interpret` proves that these three rotated feeds interpret Clean's
row environment on every domain row. `enabledGatePolynomialWitnessOfResolver` then
combines that interpretation, pinned-CS gate equality, configure coherence, and
selector compression into the `EnabledGate.PolynomialWitness` consumed by the generic
gate-satisfaction bridge.

The compact static configure interface is now compositional.
`Gate.wellFormed_of_withSelector` certifies the standard Halo 2 gate constructor from
selector-free bodies, while `Configure.PreservesGateWellFormedness` is a semantic
StateM invariant with `pure` and `bind` composition laws. All primitive configure
actions preserve it; `createGate` requires only the supplied gate's local
`Gate.WellFormed` proof, and lookup registration preserves the already-established
gate invariant. Consequently the Action proof can follow its nested chip boundaries
and never reduce the giant completed `Action.Circuit.configure` term.

`Action.GateCoherence` now supplies local `Gate.WellFormed` certificates for all 37
distinct custom-gate definitions reachable from Action configuration. This includes
the manually associated witness-point constraints, the fold-built running-range
checks, every NoteCommit gate, and the shared/final fixed-base gates. Small
selector-freedom lemmas for `rangeCheckExpr`, `windowPow`, and `coordsCheck` keep those
proofs structural rather than evaluating concrete field data.

The configure lift is complete as well. Each gate-producing leaf has a
`PreservesGateWellFormedness` certificate; the composite NoteCommit, variable- and
fixed-base multiplication, ECC, Poseidon, Sinsemilla, Merkle, and finally
`Action.Circuit.configure` theorems follow the actual configure call graph. The final
Action theorem is a certificate about the configure program, not a kernel reduction
of the finished constraint system. `PreservesGateWellFormedness.fromEmpty` specializes
such a certificate to the standard empty Halo 2 builder state when the downstream
bridge needs the concrete `GatesWellFormed` fact.

The selector compiler layer is now generic as well. The greedy packing proof shows
that every compression-map entry has a positive assigned root, that the root is at
most its combination length, and—more tightly—that every combination length is
bounded by the constraint system's compression degree. Consequently
`selectorRootsWellFormed_deriveSelCompressMap` proves `SelectorRootsWellFormed` from
the minimal field-size condition `csDegree cs < scalarFieldOrder`, independent of the
total selector count. This avoids normalizing the Action configure program merely to
discover that it has 56 selectors; the required bound is the ordinary generic
keygen-degree bound instead, not an Action-specific fact or fixture computation.
The complementary coverage theorem
`deriveSelCompressMap_lookup_isSome_of_lt` proves that this same generic compiler
produces a compression-map entry for every allocated selector index
`selector < cs.numSelectors`: the greedy partition may regroup selectors into packed
columns, but cannot drop one. This closes map coverage independently of Action. A
distinct configure-side obligation still has to show that selector atoms occurring
syntactically in configured gate expressions are allocated indices; semantic
`Gate.WellFormed` alone intentionally does not imply that stronger syntactic fact.
`ConstraintSystem.GateSelectorsAllocated` now states that obligation precisely:
each gate's distinguished selector and every selector atom in every constraint are
below `cs.numSelectors`. The monotonicity lemma for `selectorsCovered` and
`gateSelectorsCovered_deriveSelCompressMap` then turn that single configure
certificate into the exact projection-coverage premise. There is no Action-specific
compression-map computation or selector-count proof left.

For activations, `mem_selectorFixed_of_activation` proves that every synthesized
`(selector, row)` with a compression-map entry is emitted by the generic
`Fixtures.Layout.selectorFixed` compiler as the expected packed fixed assignment.
`selectorActivationsRealized_of_selectorFixed` then reduces
`SelectorActivationsRealized` to one precise downstream obligation: the environment's
fixed-column reads realize those emitted assignments. The incoming circuit-owned VK
construction can discharge that obligation by identifying its fixed polynomials with
the layout compiler output; no Action-specific activation-placement argument remains.
The polynomial side of that connection is already generic:
`selectorActivationsRealized_of_fixedRowPolynomials` takes dense fixed-row lists,
their common domain length, valid selector roots, and the expected sparse-to-dense
cell equalities, then uses canonical Lagrange interpolation to prove that the
resulting polynomial environment realizes every selector activation. It needs no
separate placement-bound premise: an out-of-domain dense-list read would be zero,
contradicting the valid selector root's proved nonzeroness. Its converse compiler
lemma establishes independently that an emitted selector assignment cannot invent a
row absent from the source activation list. Thus the circuit-owned VK need only
expose its dense fixed rows and prove the ordinary layout/scatter equations; selector
semantics does not enter VK assembly.

The same polynomial-to-layout step now covers the complete fixed family, not only
selector activations. `FixedLayout.constraints_of_fixedRowPolynomials` proves that
canonical row interpolation satisfies every table load and placed fixed assignment
emitted by the layout compiler, provided the dense rows contain those sparse entries
and the emitted rows fit the domain. The remaining fixed-side work is therefore to
derive those two compiler facts from `TopLevelCircuit` keygen data and feed this
theorem to `FullCircuitBridge.ofPolynomialWitnesses`.

The commitment-provenance half of that work is now generic too.
`assembleQueries_fixed_commitment` proves that an assembled `.fixedCol` query carries
the corresponding commitment from the accepted VK, and the canonical member route
retains that identity at the decoded member position.
`fixedColumn_eq_rowPolynomial_or_relation` compares the member's augmented opening
with the Lagrange commitment to the keygen row vector. It returns either equality
with the canonical interpolated row polynomial or a computed nontrivial relation
among `(g, U, W)`. Consequently fixed and selector satisfaction will not silently
assume commitment binding: the integration theorem exposes the same exceptional
branch that the deployed probability layer must price.
`TopLevelFixedCoherence` packages the proof-independent keygen data—dense rows,
their Lagrange commitments, static fixed-query-layout coverage, and sparse-to-dense
layout correctness. Generic layout-to-assembly routing turns that static coverage
into the actual verifier query for any proof string and challenges.
`topLevelFixedConstraints_or_relation` uses that package to discharge
both selector activations and all fixed/table operations for a resolver assignment.
The remaining constructor work is to instantiate this package from the generic
`TopLevelCircuit.toVerifierKey` pipeline.

The generic operation walk already proves that every extracted enabled gate occurs in
the floor-planner activation table, and `selectorScale_ne_zero_of_enabledGate` turns
the two contracts into the required nonzero scale. The remaining gate work is now to
connect circuit-derived fixed rows and polynomials to the emitted layout assignments,
with only the generic degree-below-field-order condition. The evaluation and
resolver-membership algebra is no longer circuit-specific.

`TopLevelCircuit.selectorActivations` and `.selectorMap` now expose those two keygen
objects directly, and `pinnedCS_eq_derive` identifies the circuit's existing pinned
constraint system with that exact map. The final pinned query state is also proved to
extend the intermediate gate-erasure state (`derive_queryState_extends_gates`), so
lookup projection may append query entries without forcing a false equality between
the VK's final layouts and the earlier gate state.

`TopLevelGateCoherence` is the generic static boundary to the circuit-owned verifying
key. It is now parameterized by proof parameters and a URS, and all of its
verifier-side objects use `top.toVerifierKey pp urs`; an arbitrary key cannot be paired
with a circuit. Gate expressions and query layouts are therefore obtained in keygen's
construction direction rather than restated as caller hypotheses. Its
`polynomialWitness` theorem derives the resolver witness for every enabled constraint
using only the top-level circuit's own operations, placement, selector map, pinned
projection, and the decoded fixed-polynomial realization.
`TopLevelGateCoherence.constraints` then supplies the complete gate field of Clean's
constraint satisfaction. The remaining constructor work is to prove the compact
configure certificates (`GatesWellFormed` and `GateSelectorsAllocated`) and connect
the derived VK's dense fixed rows to `SelectorActivationsRealized`.

The configure proof for `GateSelectorsAllocated` now has a reusable local interface.
`Gate.SelectorsOwned` says a gate mentions no selector other than its distinguished
one, and `Gate.selectorsOwned_of_withSelector` derives it structurally from the same
selector-free bodies already used by the semantic gate-shape proof. Allocation is
monotone as selector counters increase. `PreservesGateSelectorsAllocated` supplies
the ordinary state-monad preservation rules and direct certificates for the common
simple- or complex-selector/create-gate leaf patterns. Generic relational rules retain
fresh-index facts across multi-selector gate groups, mixed selector/lookup programs,
and child programs that consume a selector allocated by their parent. The
continuation form of the selector/create-gate rule also avoids elaborating a large
reassociated state-monad term while keeping the 20,000-heartbeat debugging bound.

`Action.SelectorCoherence` now completes the circuit instantiation without touching
the VK path. It proves ownership and configure preservation for the ordinary leaves,
LookupRangeCheck, variable- and fixed-base ECC (including the parent-allocated
running-sum selector), Poseidon, NoteCommit, both Sinsemilla gate forms, and Merkle,
then composes them in the exact `Action.Circuit.configure` registration order. Thus
`Action.Circuit.configure_preservesGateSelectorsAllocated` is the compact
circuit-derived certificate required by `TopLevelGateCoherence`; callers can apply
the generic `fromEmpty` rule directly, without an Action-specific wrapper theorem.
This closes the configure-side selector-allocation obligation. It does not claim the
separate lookup-expression selector-coverage property required by
`TopLevelLookupCoherence`; that property and exact packed-selector realization remain
part of the lookup/fixed compiler boundary.

The `Fixtures.Layout` reconstruction is generic over operations, and σ-cycle
correctness of its replayed keygen merge is now proved once and for all:
`runAssembly_getPair` identifies the executable assembly mapping with
`replayKeygenPermutation`.

### 5. Construct the Clean assignment

**Status: the generic VK-free assignment shell and a circuit-derived Action
decoded-member constructor are implemented. The merged
[#89](https://github.com/zcash/ironwood/pull/89) supplies the target semantics, while
[#30](https://github.com/zcash/ironwood/pull/30) and
[#91](https://github.com/zcash/ironwood/pull/91) supply most of the prospective source
data.**

From the recovered per-column row values, build:

- `Environment.get` for advice, fixed, and instance columns;
- `Environment.usableRows` from `n` and the VK blinding factor;
- the post-NU6.3 floor-planner placement;
- the concrete `Config` returned by `Action.Circuit.configure`;
- the unit input of the closed Action circuit.

The generic top-level boundary and the Action-side closure are now implemented.
`TopLevelCircuit` holds a unit-input `FormalCircuit`, requires its public
`Assumptions` predicate to be exactly `True`, fixes the result of its own `configure`
run, and provides verifier- and prover-side theorems with no exposed
`EnvAssumptions` premise. `SynthesisWellFormed` currently records the generic layout
fact needed by table loaders: every declared table block fits in `usableRows`.
`TopLevelCircuit.Statement` names the semantic proposition extracted from a placed
environment, so the SNARK bridge can target an arbitrary closed formal circuit
without mentioning its circuit-specific `Spec`.

The generic keygen layer now derives from the top-level circuit itself:

- `TopLevelCircuit.pinnedCS` runs `FormalCircuit.toPinnedCS` on the circuit's fixed
  configuration input and unit synthesis input;
- `regionStarts` and `placement` run the V1 floor planner over the circuit's own
  operation stream;
- `domainExponent` runs `minimalK` on the same configured CS and operation stream;
  `usedRows`, `blindingFactors`, `usableRowsAt`, and `FitsAt` state the keygen domain
fit entirely in circuit-owned terms;
- `TopLevelCircuit.synthesisWellFormed` proves that a fitting domain supplies the
  table-fit contract required by top-level soundness.

`TopLevelCircuit.fitsAt_domainExponent` closes the remaining generic arithmetic:
`minimalK` searches exponents `0` through `32` and uses `33` only as its failure
sentinel, so any derived exponent below `33` satisfies the operation-footprint and
blinding-row fit inequality. `TopLevelAssignment.synthesisWellFormed` therefore needs
only this standard supported-domain bound, not a separately reconstructed row proof.

The fixed-data bridge now reaches the keygen layout compiler as well.
`FixedLayout.mem_tableFixed_of_loadTable_of_lt` and `_of_fill` cover both the explicit
table block and Halo 2's default-filled tail, while
`mem_regionAssignFixed_of_requirement` connects each extracted region requirement to
its V1 absolute row. Consequently `FixedLayout.constraints_of_entries` proves the
entire Clean `.fixed` family from realization of the raw sparse entries emitted by
`Layout.tableFixed ++ Layout.regionAssignFixed`. The remaining representation step is
intentionally narrow: the circuit-owned key builder must show that its
deduplicated/scattered dense fixed rows, and then their interpolated polynomials,
realize those raw entries. No Action operation-list proof remains.

The domain algebra is kernel-reusable as well. `Bridge.powFast_eq_pow` connects the
executable binary exponentiation to ordinary powers, and
`omegaOf_isPrimitiveRoot`, `omegaOf_domain`, and `omegaOf_powers_injective` derive the
size-`2^k` root, vanishing-domain equation, and distinct row nodes from CompElliptic's
certified Pasta `2^32` root for every supported `k`. A single native-tier equality
connects the executable generator spelling to that certified root; `omegaOf` itself
remains pure, so generic assignment and Action semantic theorems retain their standard
axiom tier. Concrete Action proofs no longer need fixture-specific hypotheses for
these domain facts.

`TopLevelAssignment` is the corresponding verifier-to-Clean assignment shell. It is
indexed by a bundle proof index and stores only the commitment-ID polynomial resolver;
a family `∀ p, TopLevelAssignment top numProofs p` therefore cannot silently read a
different member's advice or instance columns. The top-level circuit supplies its
operations, V1 placement, derived domain exponent, blinding rows, and usable-row fit;
`Bridge.omegaOf top.domainExponent` supplies the protocol domain root. Consequently
the type has neither an arbitrary domain nor a `VerifyingKey` argument, and
`TopLevelAssignment.synthesisWellFormed` discharges the layout premise directly from
`TopLevelCircuit.FitsAt k`.

`TopLevelAssignment.ofActionDecodedMembers` now constructs this shell directly from
the deployed decoded-member resolver. It never accepts an arbitrary verifying key:
the decoder uses
`orchardActionTopLevelCircuit.toVerifierKey pp urs`, whose shape, scalar, gates,
query layouts, fixed commitments, permutation commitments and lookup data are all
derived from the configured Action circuit and supplied URS. The constructor no
longer accepts a separate shape or a shape/domain coherence premise. The reusable
derivation remains independent of the captured fixture; the deliberately expensive
`VkCommit.Certificate` separately proves that the captured deployed key equals that
derived key.

On the SNARK side, `FullCircuitSatisfaction.topLevelSoundness` composes exact
gate/copy/lookup/fixed satisfaction with that generic top-level endpoint.
`FullCircuitBridge.topLevelSoundness_or_bad` performs the same composition while
preserving the bridge's shared exceptional event. Neither theorem mentions the
Action circuit, an Action-specific placement, or Action-specific operations.

The small Action-specific semantic adapter is also complete.
`Action.PublicInputs` names the ten instance-column rows in protocol order and
`Action.Statement` says that some extracted `ActionData` has exactly those public
fields and satisfies the complete `SpecPost`. The theorem
`Action.statement_of_topLevelStatement` specializes the generic top-level conclusion
to that external statement. It is parameterized by a top-level circuit and the
identity of its underlying Action `FormalCircuit`, rather than mentioning the
concrete proof-carrying `Action.topLevelCircuit` record in its type. It does not
repeat any circuit proof; the remaining public-input obligation is solely to
identify the decoded instance polynomial's first ten domain values with the values
supplied to the verifier.

That row-identification lemma now consumes `TopLevelAssignment` directly. Its domain
root is `Bridge.omegaOf k`, its instance column is selected by the assignment's proof
index, and it no longer accepts an arbitrary verifier key. This is the intentionally
small Action-specific part: it only maps the first ten rows into `Action.PublicInputs`;
assignment construction and domain/layout choices remain generic.

`Action.topLevelCircuit` instantiates that boundary. It projects the initial
Sinsemilla generator-table load from the real `mainPost` operation stream and derives:

- exact generator-table contents and all four shared Sinsemilla table-loaded facts;
- the shared 10-bit range table from the generator table's index column;
- the fixed-base configuration equalities and lookup-selector distinctness produced
  by `Action.Circuit.configure`.

The prover-side closure projects the same load from `ExtendsWitnesses` and converts
its fixed-table clauses to the corresponding constraints. The deployed
`orchardActionTopLevelCircuit` specializes this generic Action construction to the
real generators and certified bases.

The legacy `ActionAssignment` has been deleted. Its decoded constructor now returns
the generic `TopLevelAssignment` indexed by `orchardActionTopLevelCircuit`, so
placement, operations, domain exponent, blinding factors, and usable rows all come
from the top-level circuit. The only Action-specific work left in this layer is the
deployed decoder routing; the verifier key itself is now obtained generically from
the top-level circuit.

The compositional base and post-Ironwood `FormalCircuit`s intentionally retain their
`EnvAssumptions`: child circuits may state contracts that a parent fulfills.
`TopLevelCircuit` is the separate deployment boundary that closes those contracts.
The generic `SynthesisWellFormed` and full-satisfaction-to-statement steps are now
complete. The circuit-derived decoded assignment and rotated resolver environment are
now connected generically. Gate and lookup witness construction are generic; the
remaining representation work is to instantiate their compact fixed/selector
coherence inputs, construct `CopyReplayWitness`, supply the lookup challenge
conditions, and feed the resulting families to
`FullCircuitBridge.topLevelSoundness_or_bad`.

After #79's merge, the generic circuit-integration declarations are checked in the
single `Zcash/TrustBoundary.lean` census with explicit standard or Vesta-native axiom
budgets. The concrete Action adapter is not independently claimed at the standard
SNARK tier: mentioning the Action `FormalCircuit` intentionally reaches the circuit
formalization's existing Pallas/native facts. The eventual end-to-end Action capstone
must price that concrete circuit trust once, at the final boundary, rather than
smuggling it into a supposedly generic adapter.

Note that most of `EnvAssumptions` should come out of the transported `Constraints`
themselves rather than separate VK-fixed-data facts: `GeneratorTableExact` is defined
as the `Constraints` of the generator-table load, and the Action circuit's own
operations contain the `loadTable`/`assignFixed` steps whose transported clauses pin
the same fixed cells the table-loaded and fixed-base assumptions read.

### 6. Generalize from one Action to an Orchard bundle

**Status: verifier-side substrate is generic in #30/#91 and exercised by the merged
[#85](https://github.com/zcash/ironwood/pull/85). The assignment, external statement,
canonical relation, and Action endpoint are bundle-indexed. Discharging the remaining
copy/lookup/fixed operation families for every member remains open.**

A deployed proof covers `shape.numProofs` Actions. Generalize `PublicInputs`,
`Assignment`, and `ActionStatement` to a `Fin shape.numProofs` family and decode one
Clean assignment per sub-proof. The shared fixed columns and VK are common, while
advice/instance columns and protocol statements are per Action. The final conclusion
should quantify over or return the high-level statement for every supplied Action.

`TopLevelAssignment.Bundle top numProofs` is the dependent family
`∀ p, TopLevelAssignment top numProofs p`, so each member is forced to resolve the
columns named by its own index. `Action.BundleStatement G B inputs` is the matching
external conclusion `∀ p, Action.Statement G B (inputs p)`. No separate monolithic
bundle witness is required: fixed columns and the circuit-derived VK remain shared,
while decoded advice/instance polynomials and extracted `ActionData` remain
per-member.

#85's multi-Action fixture derives each proof's instance commitment and proves that
sub-proof commitment slots remain disjoint. #30 and #91 already build much of their
verifier-side data over `Fin shape.numProofs`, but #30's member capstone selects a
single `pp : Fin shape.numProofs`. The integration theorem must turn that parametric
single-index result into a family of Clean assignments and Action statements.

### 7. Thread the bridge into the live capstone

**Status: the canonical relation now reaches a concrete bundle-wide Action theorem,
but the live Vesta/Fiat–Shamir capstone still accepts `hencodes`. Substantial
foundations are in
[#30](https://github.com/zcash/ironwood/pull/30),
[#91](https://github.com/zcash/ironwood/pull/91), and
the merged [#85](https://github.com/zcash/ironwood/pull/85).**

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
`hExtract`/adaptive-coupling data-supply premise. The merged #85 threads
statement-derived instance commitments through the live verifier. #82 documents the computed capstone
and #79 provides the eventual trust-boundary census location.

The final theorem should say, modulo the explicitly priced Fiat–Shamir, polynomial
identity, and discrete-log failure events, that acceptance by the modeled deployed
verifier with the post-NU6.3 Action VK yields the high-level statement for every Action
whose public inputs were committed by the verifier.

## Suggested implementation order

0. **Complete:** close both Action circuit inputs to `unit`, instantiate prover choices
   through the hint-backed witness program, and derive the operation stream from the
   real proof-carrying circuit.
1. **Complete:** instantiate the full constraint split at the canonical deployed
   resolver, including the domain-selector, permutation, and lookup semantic
   endpoints.
2. **Complete generically:** derive the pinned CS, V1 placement, domain, verifying key,
   polynomial row environment, gate witnesses, and lookup witnesses from
   `TopLevelCircuit`. The executable permutation assembly is now proved equal to the
   abstract copy replay.
3. **Current parallel work:** instantiate Action `TopLevelFixedCoherence`; specialize
   the generic copy-replay constructors to the Action endpoint encoding; derive exact
   lookup selector projection, activation-row fit, and priced lookup challenge
   conditions; and finish the Lagrange-prefix/instance-commitment certificate. The
   Action `TopLevelGateCoherence` constructor is complete.
4. Assemble those components for one proof index in `FullCircuitBridge`, then quantify
   the same construction over every `Fin shape.numProofs`. The external
   `Action.Statement` and `Action.BundleStatement` adapters are already implemented.
5. Replace the live computed capstone's free `S`/`hencodes` argument with that concrete
   bundle bridge and add the resulting theorem to the consolidated trust boundary.
   The family-wide adaptive-coupling/`hExtract` supply problem is a distinct
   probability-layer task and may remain an explicitly conditional or residual term
   while the deterministic `hencodes` gap is closed.
