# Clean circuit framework improvements

## Status and scope

This note specifies the refactoring arc that replaces concrete, whole-Action
computational certificates with reusable Halo2-Clean lawfulness and compiler theorems.
The certificates that could be eliminated by generalizing their consumers are gone
([#145](https://github.com/zcash/ironwood/pull/145)); the compositional-lawfulness side
is in progress ([#202](https://github.com/zcash/ironwood/pull/202)).

The arc serves three purposes:

* **Generality.** Lawfulness is proved once for Clean's primitives and preserved by its
  circuit combinators, so that the framework can handle further top-level circuits
  without comparable rework — at present, each new circuit would need its own
  hand-written whole-circuit certificate modules.
* **Error reporting.** An incorrectly expressed circuit should fail the local proof
  obligation that names its mistake, rather than be silently repaired by the keygen
  model or surface only as an unexplained mismatch against a captured verifying key.
* **Claim hygiene.** Concrete computation should be confined to checking deployment
  identity, so that a concrete check cannot silently stand in for a well-formedness
  property it does not establish.

The deployed verifying-key equality is intentionally **not** part of this cleanup.
Checking that the circuit-derived key equals the deployed Orchard key is a legitimate
concrete trust-boundary check. It must not, however, double as evidence that the Clean
formal circuit is internally lawful.

The visible certificate list understates the architectural debt, for example:

* some certificates bundle independent facts;
* further wellformedness checks hide inside the VK-match bundle;
* `ConstraintSystem.closeWithOperations` silently repairs a missing configure/synthesis
  fact without proving that the repair is inactive (the verifier MSM match is against
  the repaired circuit that is actually proven, as it should be, but the repair impedes
  comparing the Lean code against the Rust implementation and should be unnecessary).

The guiding rule is:

> A concrete VK comparison may establish deployment identity. It must not establish
> that a formal circuit is well formed.

## Why `closeWithOperations` belongs in this inventory

Clean currently defines `FormalCircuit.toConstraintSystem` by taking the raw result of
`configure` and applying `ConstraintSystem.closeWithOperations` to the circuit's
synthesis stream. Closure:

1. appends gates enabled by synthesis but absent from `configure`;
2. appends lookups enabled by synthesis but absent from `configure`;
3. registers queries for those appended arguments; and
4. increases `numSelectors` when lookup expressions use selectors beyond the bound
   allocated by `configure`.

This produces a self-consistent internal object, but it is not the algorithm Halo2
uses. In Halo2, synthesis can enable only a gate or lookup already established by
configuration. If closure changes the raw constraint system, the model has repaired
an invalid formal circuit instead of rejecting it.

The problem is not cured by comparing the resulting pinned CS with a captured VK.
Such a comparison says that the *repaired derivation* matches the deployed data; it
does not say that the repair was inactive. In particular, semantically redundant or
projection-equivalent repairs need not be observable in every downstream pinned
field.

The desired endpoint is:

```text
rawCS := (c.configure ci {}).2
ops   := c.toOperations ci input

FormalCircuit lawfulness proves:
  every enabled gate is in rawCS.gates
  every enabled lookup is in rawCS.lookups
  every lookup selector is below rawCS.numSelectors

c.toConstraintSystem ci input = rawCS
c.toPinnedCS ci input = PinnedConstraintSystem.ofClosedOperations rawCS ops
```

`closeWithOperations` can remain as a diagnostic or migration helper, but it should
not define the canonical keygen semantics. A useful transition theorem is that lawful
circuits satisfy

```text
rawCS.closeWithOperations ops = rawCS.
```

That theorem makes the current and intended pipelines coincide while callers migrate.
After migration, the raw configure result should be used directly.

The query-registration folds in closure are not a separate atomic obligation. Once
both missing-argument lists are empty, those folds are inactive. The selector maximum
is separate: it can change even with no missing lookup when a configured lookup
mentions an unallocated selector.

## The concrete computations that remain

The computations that were generically provable, and those that existed only because
downstream code demanded Action constants, are gone
([#145](https://github.com/zcash/ironwood/pull/145)). Where their names survive, they
are corollaries derived from the facts below, or they live inside the
deployment-identity certificate (`Zcash/Snark/Keygen/Certificate.lean`) — the
intended end state, since deployment identity is the one legitimate concrete check.

Two kinds of concrete computation remain, and the axiom census pins both:

* the law-dependent obligations, discharged for the concrete Action circuit by the
  compute modules under `Zcash/Circuits/Integration/`: gate coherence and constraint
  degree, fixed-column coverage and realization, copy addressing, constant
  allocation, and permutation routing over the derived domain; and
* one exact permutation fact, the circuit's permutation-column count. The current
  circuit interfaces do not bound it — columns carry unbounded `Nat` indices and
  `Configure` is an arbitrary state function — so eliminating it needs either a
  configure law ensuring a duplicate-free in-range column list or an explicit
  supported-column-count law on the top-level keygen interface. That is a design
  decision for the lawfulness side of the arc, not another consumer generalization.

Replacing the first kind with compositional lawfulness is the substance of this
note, and [#202](https://github.com/zcash/ironwood/pull/202) is that work in
progress.

## Withdrawn synthesis laws and the residual fidelity gap

`TopLevelCircuit` once carried two static synthesis obligations: that a lookup
operation's recorded enabled selectors exactly match the relevant selectors activated
in its complete region at that row, and that lookup input expressions contain no
simple selectors. They were proved at the wrong abstraction layer — as fields of
`TopLevelCircuit` rather than of `FormalCircuit`, backed by sidecars that retraced
the entire Action and NoteCommit synthesis call graphs — and nothing consumed them,
so they were withdrawn rather than relocated.

That withdrawal leaves a known fidelity gap. Halo 2 rejects simple selectors supplied
to a lookup argument — lookup registration panics on one — and Clean no longer models
that rejection anywhere. Nothing in the present chain becomes unsound as a result,
because nothing claims it; but a keygen-fidelity theorem relating Clean's
`configure`/`synthesize` output to halo2's own key generation cannot be stated
faithfully without it. Such a theorem will need a no-simple-selectors premiss
reintroduced explicitly.

When that happens, the premiss should not be reinstated in the withdrawn shape. These
are laws of `FormalCircuit.synthesize`: the obligation belongs locally on
lookup-emitting bundles, preserved compositionally by the circuit combinators, rather
than reproved across a whole synthesis call graph and reattached at the top-level
wrapper.

## Proposed lawfulness interfaces

### 1. Exact gate query support

For a gate, the list supplied as `queriedCells` records Rust closure-call order, while
expression traversal records syntactic use order and may repeat atoms differently.
The right law is therefore support equality, not list equality:

```text
Gate.QueryExact gate :=
  every entry of gate.queriedCells is an advice/fixed/instance query
  ∧ constraintQuerySupport gate.constraints
      = gate.queriedCells.toFinset
  ∧ constraintSelectorSupport gate.constraints
      = {gate.selector}
```

This captures the intent: the cells in the constraints are exactly the declared
queries, plus the gate selector. If future Halo2 APIs deliberately permit valid but
unused closure queries, equality can be relaxed to the required subset direction.
Start with equality because it detects both missing and stale declarations.

The existing `Gate.WellFormed` selector discipline and `QueryExact` should become
parts of a single gate lawfulness interface. Construction should retain current call
syntax through default proof arguments and tactics.

Consequences should include:

* no invalid `queriedCells`;
* every expression query receives the intended registered query index;
* query coverage for every semantically consumed gate fixed column;
* expression projection is independent of an unrelated concrete VK check.

### 2. Lookup query support

Lookups need the analogous law:

```text
LookupArgument.QueryExact argument declaredQueries :=
  querySupport (argument.inputs ++ argument.tables)
    = declaredQueries.toFinset
```

It composes with the existing lookup properties: table expressions are selector-free,
input selectors are disciplined, tuple arities match, and activation rows are exact.
The declaration must reflect the actual configure closure-call order when that order
affects query indices.

### 3. Configure/synthesis registration

The raw configure result and synthesis stream need a packaged law such as:

```text
FormalCircuit.RegisteredIn :=
  let rawCS := (configure configInput {}).2
  let ops := toOperations configInput input
  OperationsKeygenCoherent rawCS ops
  ∧ LookupSelectorsAllocated rawCS
```

The name and exact factorization can change, but the property must live on
`FormalCircuit` (or a construction it contains), not beside each Action subcircuit.
As with Clean's other lawfulness fields, primitives should prove it once and
combinators should preserve it. A default tactic should solve ordinary bundles from
those compositional lemmas.

This law gives:

* `missingEnabledGates rawCS ops = []`;
* `missingEnabledLookups rawCS ops = []`;
* the closure selector maximum equals `rawCS.numSelectors`;
* `rawCS.closeWithOperations ops = rawCS`; and
* canonical `toConstraintSystem` and `toPinnedCS` can use `rawCS` directly.

This is stricter and more faithful than merely baking synthesis-enabled arguments into
the derived CS.

### 4. Configure permutation and constant laws

Configure should also expose:

* every equality-enabled column has the zero-rotation query required by permutation
  routing;
* every constant column is equality-enabled;
* every instance column targeted by synthesis is equality-enabled; and
* allocated column/selector counters are monotone and references are in range.

These are good candidates for proof-by-construction in a restricted append-only
configure monad. Until then, they should be fields preserved by configure primitives
and discharged compositionally.

### 5. Region-operation lawfulness

Each region should certify locally:

* every referenced cell was allocated in that region;
* referenced offsets are below the measured region extent;
* repeated writes to the same local fixed cell agree; and
* copy endpoints use equality-enabled columns.

The V1 planner already proves that regions sharing a measured column receive
non-overlapping column-and-row intervals. That generic theorem turns local fixed-write
consistency into cross-region consistency. Regions may share row numbers; what cannot
overlap is a cell in a shared column.

Tables, constant allocation, and selector packing are separate compiler stages, not
exceptions. Each stage needs a small consistency theorem and a composition theorem
showing that its writes do not conflict with region writes or with the other stages.

### 6. Operation-stream lawfulness

Reintroduce the two lookup synthesis laws on `FormalCircuit`, with compositional
support in circuit and subcircuit constructors. The same formal-circuit lawfulness
package should grow to cover:

* table loads for the same destination are consistent;
* constants are allocatable;
* instance constraints target enabled columns; and
* region-local laws hold for every synthesized region.

These should compose through operation-list append and circuit calls, so a top-level
circuit inherits them without enumerating every Action subcircuit in one theorem.

### 7. Supported domain

`TopLevelCircuit` should expose a supported-domain fact:

```text
∃ k ≤ fieldTwoAdicity, top.FitsAt k
```

Ideally this follows from per-region or per-bundle footprint bounds and generic
planner bounds. If the complete structural proof is too large initially, a concrete
domain check may remain only as a prominently marked interim certificate with this
replacement named.

## Generic compiler proofs still required

Even a fully lawful circuit does not eliminate all work. The compiler needs reusable
proofs that:

1. permutation column lookup, chunking, and address encoding round-trip;
2. V1 placement transports region-local bounds and consistency to placed cells; and
3. selector compression covers every selector of a lawful gate or lookup.

These are generic algorithms over small abstract inputs. They should be proved with
behavioral simp lemmas and induction, not `rfl`/`whnf` through a concrete Action
definition.

## Recommended implementation sequence

### Phase A — make raw configure authoritative

1. Define the configure/synthesis registration and selector-allocation laws.
2. Prove closure is inactive for lawful circuits.
3. Put the law on `FormalCircuit` with compositional primitive/bundle support.
4. Change canonical `toConstraintSystem`/`toPinnedCS` to use raw configure output.
5. Retain `closeWithOperations` only as a migration/diagnostic helper.

This phase replaces gate closure, lookup closure, and selector-bound closure and
prevents the VK capture from hiding a modeling error.

### Phase B — remove concrete downstream demands (done)

Generalize permutation replay and domain consumers, leaving exact deployed constants
visible only in the VK identity check. This landed in
[#145](https://github.com/zcash/ironwood/pull/145); what survives of it is the
law-dependent permutation-column count described above.

### Phase C — gate, lookup, and configure lawfulness

Add exact query support, degree bounds, permutation-column registration, constant
column laws, and instance registration. This addresses query coverage, constant-cell
routing, degree safety, permutation routing, primary-instance registration, invalid
query declarations, and the local premiss of selector-compression coverage.

### Phase D — generic projection and algebra (largely done)

Prove query-layout projection, constant-stream value preservation,
selector-compression coverage, and delta-power injectivity. The first, second, and
fourth landed in [#145](https://github.com/zcash/ironwood/pull/145);
selector-compression coverage remains.

### Phase E — region, copy, constants, and fixed realization

Build region-local allocation/write laws and generic placement transfer, then compose
the fixed-producing stages. This addresses the region, copy, constant, and
fixed-realization obligations.

### Phase F — supported domain

Derive the top-level domain bound compositionally. This can proceed in parallel with
much of Phase E once the footprint interface is settled.

## Completion criteria

This arc is complete when:

* the canonical Clean keygen pipeline does not repair configure/synthesis mismatch;
* the lawfulness obligations are discharged generically or compositionally;
* lookup synthesis laws are carried by every `FormalCircuit` and preserved by its
  combinators;
* the Action integration capstone imports no concrete certificate theorems;
* no whole-Action `native_decide` remains for circuit correctness, layout
  consistency, query registration, routing, or domain safety;
* any retained concrete computation checks only deployment identity or fixture data;
  and
* adding another lawful top-level Halo2 circuit requires no analogous hand-written
  certificate module.

## Non-goals

This work does not remove the deployed Action VK capture, prove fixture provenance,
or change verifier/soundness semantics to speak in Clean-native terms. It strengthens
the Clean-to-Ironwood boundary so that the circuit interface arrives with the
Ironwood-facing properties that soundness needs.
