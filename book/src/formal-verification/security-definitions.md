# Security Models

The [ledger security games](ledger-security-games.md) under `Zcash/Security/` and the
verifier-soundness capstones under `Zcash/Snark/` traced by the [proof map](proof-map.md)
share one methodology. This page describes it: the shape every argument follows, the
adversary models the theorems are stated in, and where hardness judgements actually live.

Every argument has the same shape, the development-wide
[*breaks as computed data*](../formal-verification.md#breaks-as-computed-data) convention:

> A security property, if violated, **exhibits** a concrete break of an underlying
> primitive — a discrete-log relation, a hash collision, a commitment-opening collision —
> computed as data. Hardness is assumed only at the computational layer, against the
> exhibited break.

So each definition sits on a three-layer stack:

- **Layer A — vocabulary.** The break events, as structures carrying their data
  (`RandomOracle.Collision`, `NontrivialRelation`, `NoteCommitBreak`). Deterministic; no
  probability.
- **Layer B — reduction.** A computable `def` that turns a property violation into a
  Layer-A break (`NontrivialRelation.ofImbalance`, `Merkle.collisionOfWrongLeaf`,
  `noteCommitBreakOfNe`). Deterministic; no hardness assumption.
- **Layer C — probability.** The bound that producing the break is hard: the birthday bound
  `q(q-1)/|𝔽|`, or the discrete-log advantage. The only layer that consumes an assumption.

## Fixed bases and the reference-string heuristic

Several reductions above bottom out at discrete log by treating a set of group elements as
*independent* — for example the value-commitment bases $\mathcal{V}$ and $\mathcal{R}$, the
Sinsemilla generators, and the proof system's inner-product reference string. Independence
is what turns "find a nontrivial relation among these elements" into the discrete-log game:
the reduction models each base as a random multiple of one generator and embeds its
discrete-log challenge into that randomness.

In the deployed protocol, though, these bases are *fixed*. Each is produced once, by
hashing public strings to the curve, and the resulting outputs are baked into the protocol
as a Uniform Reference String. The gap between the two is the standard gap for protocols
with a URS. We prove security for the family of protocols that sample the bases at
random, over the distribution of that randomness. Then we argue heuristically that the
deployed protocol, which fixes them via hash-to-curve, inherits it — provided that the
hash-to-curve scheme admits no attack more efficient than the generic ones bounded by the
proven reductions. The same heuristic underlies every use of hash-to-curve for fixed bases
here, of which the value and note commitments, the Merkle hash, and the proof system's
reference string are examples.

This heuristic comes with an important caveat: an adversary has the protocol's *entire
lifetime* to attack that one specific reference string. A bound that holds for random
bases does not preclude an attack tuned to the deployed bases, and the cost of finding
one is amortized over every transaction ever made against them. That is a known,
acknowledged limitation of this development.

This sharpens the potential threat from quantum computers or other discrete-log attacks:
a single discrete-log computation is catastrophic to the protocol as a whole, rather than
localized to a specific user or key. Against these fixed bases, **one** discrete-log
computation is sufficient to break binding/knowledge-soundness properties for the
entire protocol, not just for a single transaction or user. That includes Balance
properties, Spendability, and Spend authority, although not privacy. Migrating away
from reliance on discrete-log binding/knowledge-soundness is therefore a whole-protocol
concern, not a per-transaction one. See
[ZIP 2005](https://zips.z.cash/zip-2005#effectsofdiscrete-logarithm-breakingattacksbeforetheswitchtotherecoveryprotocol)
for further discussion.

New to the shorthand? See the [**Glossary**](glossary.md). &nbsp;·&nbsp; For the property
statements, the [**Ledger Security Games**](ledger-security-games.md). &nbsp;·&nbsp; For
the verifier-soundness half, the [**Proof Map**](proof-map.md).
