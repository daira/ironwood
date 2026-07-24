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
structured `Action.PublicInputs`. The remaining concrete work is to identify the
routed member's column number with `Action.Config.primary` and provide the parameters'
`LagrangeCommitmentKey` setup certificate. Once those two facts are supplied, the
decoded member's `OpenedMemberDecode.commitment` equation can be passed directly to
`coeffsToPoly_eq_instanceRowPolynomial_or_relation`; the tiny equality composition is
intended to remain inline at that use site.

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
last usable row. What remains here is the generic finite reindexing that matches
those rows to the verifier's negative blinding rotations.

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

The generic gate and fixed/table operation layers are now implemented as well.
`operationEnabledGates` extracts every placed activation and
`gate_constraints_iff_enabledGates` proves exact equivalence with the gate family.
`EnabledGate.PolynomialWitness` identifies each enabled Clean constraint with one
member of #91's selected polynomial gate family; domain divisibility then proves the
Clean constraint directly. `operationFixedRequirements` similarly extracts fixed
assignments and table loads, with `fixed_constraints_iff_requirements` proving exact
equivalence to the fixed family. `FullCircuitBridge.ofPolynomialWitnesses` assembles
these gate/fixed witnesses with the existing copy and lookup witnesses.

The remaining gate work is therefore the circuit-specific packed-selector row algebra:
every enabled gate must be registered in the constraint system, gate polynomials must
be linear in their own selector and free of foreign selectors, co-packed selectors
must never be co-enabled, and the activation table must match the packed fixed columns.
Those side conditions are discharged for the Action instance computationally (the
same `native_decide`-style work the VK-match and layout tests already do), not by an
Action-specific proof walk. The
`Fixtures.Layout` reconstruction is already generic over operations, so σ-cycle
correctness of its replayed keygen merge is likewise a once-and-for-all lemma. A useful
de-risking step is to instantiate the generic theorem first for the small `AddChip`
fixtures before the full Action circuit.

### 5. Construct the Clean assignment

**Status: the generic VK-free assignment shell is implemented; its decoded-member
constructor remains open. The merged
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

The incoming `FormalCircuit.toVerifyingKey` completes this seam rather than changing
it: prove that its `omega`, `n`, and blinding fields are the domain values above, then
define the decoded-member constructor using that circuit-derived key. The external
accepted key appears only through its equality certificate with the derived key.

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

The existing `ActionAssignment` still packages one proof member's
fixed/advice/instance polynomials through `resolverEnvironment`, but its API predates
the circuit-owned keygen layer: it takes a `VerifyingKey` and repeats Action placement
and usable-row choices. It is temporary. Once `FormalCircuit.toVerifyingKey` is
available, move its decoded constructor onto `TopLevelAssignment` and delete the
legacy Action-specific type. The external accepted Action VK then enters only through
a certificate that it equals (or has the required fields equal to) the derived VK.

The compositional base and post-Ironwood `FormalCircuit`s intentionally retain their
`EnvAssumptions`: child circuits may state contracts that a parent fulfills.
`TopLevelCircuit` is the separate deployment boundary that closes those contracts.
The generic `SynthesisWellFormed` and full-satisfaction-to-statement steps are now
complete. The remaining assignment work is to connect the circuit-derived VK/domain
to the resolver environment, then construct the gate/copy/lookup/fixed witnesses that
feed `FullCircuitBridge.topLevelSoundness_or_bad`.

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
[#85](https://github.com/zcash/ironwood/pull/85). The assignment and external
statement interfaces are now bundle-indexed; constructing every decoded member and
feeding the family through the capstone remains open.**

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

**Status: substantial foundations in
[#30](https://github.com/zcash/ironwood/pull/30),
[#91](https://github.com/zcash/ironwood/pull/91), and
the merged [#85](https://github.com/zcash/ironwood/pull/85); no end-to-end Action
theorem yet.**

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

0. Complete: close both Action circuit inputs to `unit`, instantiate all prover choices
   with the fixed hint-backed witness program, and derive `actionOperations` from the
   real proof-carrying circuit.
1. Complete: instantiate #91's constraint split at the deployed list, route the
   permutation and lookup members to its proved endpoints, and expose a full
   circuit-satisfaction record in the computed endpoint.
2. Make #89's post-compression CS and layout fixtures available as reusable Lean data,
   and prove VK/layout equality theorems that discharge #30's routing hypotheses.
3. The canonical polynomial-to-row decoder, Action top-level environment closure,
   circuit-owned pinned CS/V1 placement/domain fit, and generic
   full-satisfaction-to-`TopLevelCircuit.Statement` endpoint are complete. Replace the
   legacy Action assignment with a generic circuit-owned-VK assignment and discharge
   its resolver representation facts.
4. Instantiate the generic decomposed bridge for one selected Action, adapt
   `TopLevelCircuit.Statement` to the external Action statement, and then generalize
   it to every `Fin shape.numProofs`. The semantic adapter and generic decoded
   instance-value provenance are complete; routed-member identification, the concrete
   Lagrange-key certificate, and the remaining bridge witnesses remain.
5. Supply the decoded/full-satisfaction data inside the computed experiment, close the
   remaining adaptive-coupling/`hExtract` obligation, instantiate the endpoint with
   `ActionStatement`, and add the theorem to the consolidated trust boundary.
