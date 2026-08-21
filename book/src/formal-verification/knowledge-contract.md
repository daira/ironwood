# The Knowledge-Soundness Contract

The Action circuit's knowledge-soundness result is one theorem,
`orchard_action_adaptiveStatement_knowledge_error_bound`. Reading it tells you a probability is
bounded — not *what* is bounded, what a successful extraction hands back, or what that thing
certifies. Those live in the layers that prove it.

`Zcash/Snark/Contract/` gathers them: `KnowledgeContract` is a record with one field per question
an auditor must answer, and `actionKnowledgeContract` is its instance for the deployed circuit.
The layer proves nothing new — it re-exports the definitions the theorem is stated in and applies
the theorem itself unchanged, which is why its census pin carries exactly the endpoint's axiom
footprint. The one substantive demand the record makes of an instance is the `witness_statement`
field, discussed below. This page reads the instance in order.

## The six questions

### 1. What is a run?

A generator random-oracle table and one Fiat–Shamir transcript, drawn independently. The URS
basis is *read from* the table by `orchardGeneratorROBasis`, modelling halo2's parameter
derivation ($g_i = H(0 \| i)$, $W = H(1)$, $U = H(2)$) — a
[modelling assumption](security-models.md#fixed-bases-hash-to-curve-and-the-reference-string),
not a theorem.

The adversary is *adaptive in the statement*: it outputs the public inputs and the proof
together, and both the canonical verifying key and every selected instance commitment enter the
transcript before the first challenge, so the statement cannot be chosen after seeing it. The
adversary is also [*algebraic*](security-models.md#the-algebraic-adversary-restriction): its
output type requires every emitted group element to carry a representation over the basis. That
is a restriction on which adversaries the bound covers at all, not an assumption that can be
discharged.

### 2. When does the verifier accept?

`ComputedAdaptiveActionStatementFSFamily.accepts`: halo2's checked acceptance at the adversary's
own selected inputs and proof, over the URS read from the oracle table. This is
`DeployedAccepts`, the verifier's entire check collapsed into one multiscalar multiplication —
acceptance means the assembly succeeds and that MSM evaluates to zero. It is the deployed
verifier's own condition, not a reformulation chosen to be convenient.

### 3. What does extraction return?

An `ActionTerminal.ActionBundleWitness`: the private witnesses of every Action in the bundle,
packaged with proofs that they satisfy `ActionSpec` at the public inputs the adversary selected.
It lives in `Type` — data a program can hold and inspect, not a proposition that a witness exists
somewhere. The extractor is a total function; returning `none` is what extraction failure means,
and that failure is the only event the bound is about.

("Executable" describes the extractor where the proving layer defines and checks it. The
contract record is `noncomputable` — its law is a `PMF`, which Lean cannot run — and neither
adds nor needs a computability check of its own.)

### 4. What does a returned witness certify?

`BundleStatement`: every Action in the bundle satisfies the circuit's statement at the public
inputs the adversary selected. This field carries the weight — a bound on "accepted but
extraction returned nothing" is worthless if extraction may return junk. `witness_statement`
forecloses that: a returned witness *entails* the statement, and stating it as a field means no
instance can quietly omit it.

### 5. What is the failure event?

Accepted, yet extraction returned nothing. Both conjuncts matter: a rejected run is not a
failure, and neither is an accepted run that yielded a witness.

### 6. What is the error?

The endpoint's compositional formula: the adversary's
[discrete-log advantage](definitions.md#adv-dlog) at its query and group-work counts, plus
$1/|\mathbb{F}|$, plus a per-query term collecting the Schwartz–Zippel budgets of each challenge
surface. At the $2^{123}$ work-factor target it lands on
$\mathrm{Adv}_{\mathrm{DLOG}}(2^{126}, 2^{126}) + 2^{-83}$, whose two arguments are the
random-oracle query count and the group-operation count.

## What the contract does not say

**Completeness is not implied.** That some run accepts, or that an honest prover's proof
extracts, is a separate property. Nothing here rules out the vacuous case: a contract whose
acceptance predicate holds nowhere satisfies every field. Read the contract as a bound on the
adversary, never as evidence that the circuit works.

**Ordinary soundness is not advertised separately — because it is free.** On a false statement
the extractor must have returned `none`, since a returned witness would have entailed it. So
`acceptFalseStatement_le` gives the soundness bound at the same error for every contract, and no
separate endpoint is advertised for it.

**The ledger security capstones do not follow from it.** The contract ends at
`ActionBundleWitness`. The formal continuation begins, per Action, at
`Zcash.Security.Ledger.Bridge.actionSpec_to_ledger`, which consumes the public input, private
witness, and `ActionSpec` proof — and returns an `ActionBreak` or an existentially witnessed
ledger statement in `Prop`, not an executable ledger witness. The
[ledger security capstones](ledger-security-games.md) build on that handoff, and they *depend on*
knowledge soundness rather than settle for less: they are stated in the witness-level model, over
ledger actions that already carry witnesses, and extraction is what supplies those for a merely
proof-carrying bundle. What this contract does not do is discharge that step for the deployed
circuit — the witness-level model abstracts Halo 2 knowledge soundness away, and relating the two
is a separate reduction on the different Halo 2 bases.

**The assumptions are not fields of the record.** They are the arguments of
`actionKnowledgeContract`: a nonzero generator, an injective oracle-parameter query, the
family-construction obligations, and the generic `AdaptiveStatementDlogProfile`, whose
`proverGroupWork` and `reductionGroupWork` are caller-supplied labels with `finderAdvantageLE`
the corresponding DLOG advantage bound. (The operationally accounted route is separate:
`AdaptiveStatementAdversaryCostCertificate` and `CertifiedAdaptiveStatementDlogProfile` feed
`orchard_action_adaptiveStatement_certified_knowledge_error_bound`.) Two more conditions are
structural, carried by the adversary's *type*: the algebraic restriction above and the
random-oracle modelling of the challenge schedule. What trusting each of these means is the
subject of [Security Models](security-models.md), and the
[Guide to the Ironwood Formalization](guide.md#what-you-are-trusting) states them in plain language.

## Why the record is not Action-specific

`KnowledgeContract` is stated for any circuit. Action is its only instance because it is the
only circuit carrying an advertised capstone — the other circuits are components composed into
its specification. And the shape already recurs: the
[ledger security games](ledger-security-games.md) pair a break event, a containment showing the
event covers the property, and a bound — the same three moves as `failure`, `witness_statement`,
and `knowledge_sound`. Keeping the record generic is what stops the second circuit's contract
from becoming a second bespoke tree.
