# Security Models

The [ledger security games](ledger-security-games.md) under `Zcash/Security/` and the
verifier-soundness capstones under `Zcash/Snark/` traced by the [proof map](proof-map.md)
share one methodology. This page describes it: the shape every argument follows, the
adversary models the theorems are stated in, and where hardness judgements actually live.

Every argument has the same shape, the development-wide
[*breaks as computed data*](../formal-verification.md#breaks-as-computed-data) convention:

> The security arguments are reduction-style: a theorem shows that a violation of a
> protocol property *exhibits* a concrete break of an underlying primitive — for example
> a discrete-log relation, a hash collision, or a commitment-opening collision. Hardness
> assumptions are consumed only at the computational layer, against the exhibited break.

So each definition sits on a three-layer stack:

- **Layer A — vocabulary.** The break events, as structures carrying their data
  (`RandomOracle.Collision`, `NontrivialRelation`, `NoteCommitBreak`). Deterministic; no
  probability.
- **Layer B — reduction.** A computable `def` that turns a property violation into a
  Layer-A break (`NontrivialRelation.ofImbalance`, `Merkle.collisionOfWrongLeaf`,
  `noteCommitBreakOfNe`). Deterministic; no hardness assumption.
- **Layer C — probability.** The bound that producing the break is hard: the birthday
  bound $q \cdot (q-1)/|\mathbb{F}|$, or the discrete-log advantage. The only layer that
  consumes an assumption.

## What a reduction in these models says

The capstones are reductions in idealized models: the challenge hash is modelled as
a random oracle, and on the [generator-RO](definitions.md#generator-ro) endpoints the
adversary is restricted to be [algebraic](#the-algebraic-adversary-restriction).
A theorem of this kind says: an *algebraic adversary in the random-oracle model* that
wins the protocol game, under the stated conditions, would need to be able to compute
a nontrivial discrete-log relation —tightly equivalent to computing a discrete log
(Jaeger–Tessaro,
[Expected-Time Cryptography: Generic Techniques and Applications to Concrete Soundness](https://eprint.iacr.org/2020/1213),
Lemma 3)— with an advantage and resource cost that is related in terms of concrete
efficiency. The same
content is sometimes stated as: an adversary that wins the game either exhibits a
discrete-log break *or* falls outside the modelled class — an inclusive or, since an
adversary that wins the game by non-algebraic means could potentially do so by breaking
the underlying problem.

What such a theorem does not say is "assuming (among other things) that discrete log is
hard, the protocol is secure". Discrete-log hardness is not a premiss of the theorem,
and it could not be one. Zcash is defined over fixed curves and hash sizes; it is not a
family of protocols indexed by a security parameter. Even if it were, what we care about
is the security of the concrete deployed system. Defining concrete efficiency is not
the obstacle — resources can be counted directly, with no need for polynomial time as a
proxy. The obstacle is that the relations among the deployed bases are fixed constants:
an adversary that hard-codes, say, the discrete log of $\mathcal{R}$ base $\mathcal{V}$
is concretely tiny, so "no efficient adversary finds a nontrivial relation among the
deployed bases" is false as stated, even though we conjecture that nobody can exhibit
such an adversary. More subtly, there are also adversaries that hard-code the results
of an infeasibly expensive precomputation, allowing discrete logarithms to be computed
cheaply even at targets not fixed in advance (Bernstein–Lange, section 3 of
[Non-uniform cracks in the concrete: the power of free precomputation](https://eprint.iacr.org/2012/318), Asiacrypt 2013).

Restricting the adversary's access until such bounds become provable is exactly the
generic-group model — but the resulting theorem would then be restricted to generic
adversaries (Shoup,
[Lower bounds for discrete logarithms and related problems](https://www.shoup.net/papers/dlbounds1.pdf), Eurocrypt 1997),
and would not say anything about the protocol's security for its instantiated curves
such as Pallas and Vesta.

There are two different techniques that can help to overcome this problem in a
concrete-security development:

1. We can present an explicit computable reduction, with exact resource accounting, from
   winning the game to an exhibited discrete-log solver.
2. We can consider the adversary's advantage against a family of protocols ranging over
   the choices of random bases, modelling hash functions as random oracles where
   necessary. These bases can be on the actual curves, and the random oracles can have
   the same input and output types as in the actual protocol.

At least one of the two is needed to defuse the hard-coded adversary, and either would
technically suffice:
* Under 2, the bases are sampled inside the experiment; the adversary does not know
  them when it starts, and so a hard-coded constant is useless.
* Under 1, no hardness claim is stated at all, and the reduction returning a
  nontrivial relation is a meaningful security argument whether or not a winning
  adversary hard-coded its discrete log.

Our approach is to use 1 for all reductions, and 2 when it allows obtaining a tighter
reduction. We always use 1 because it is essentially free: in a development where we
take the effort to make some reductions computable, it is consistent to make all of them
computable. We sometimes additionally use 2 because, using 1 alone, there is sometimes
no known way to obtain a tightly efficient reduction: against fixed bases the reduction
has no randomness into which to embed its discrete-log challenge, so extraction must
rewind the adversary — the forking route, with the tightness losses that brings.
Sampling the bases, on the other hand, lets the reduction embed the challenge into the
basis randomness and extract straight-line, with no multiplicative loss.

Embedding the challenge into the basis randomness is legitimate because it does not
change the game. Given a discrete-log challenge $(B, C)$ —seeking the $z$ with
$C = z \,•\, B$— the reduction sets each base to $x \,•\, B + y \,•\, C$ with its own
fresh uniform pair $(x, y)$ per base. Such bases are exactly uniform: the adversary's
view is identical to the honestly sampled game, so its success probability is unchanged,
and the challenge is hidden perfectly rather than computationally. What the reduction
gains is private knowledge of the pairs. A returned relation among the bases then becomes
a linear equation in $z$, solvable unless the relation's coefficients land on the single
$1/|\mathbb{F}|$ hyperplane where the $y$ component cancels — the form of reduction the
definitions page calls [programmed-basis](definitions.md#programmed-basis). The argument is
Jaeger–Tessaro's proof of their Lemma 3, presented there as a careful use of
self-reducibility techniques.

The judgement that the exhibited solver is beyond reach is a statement about the current
state of cryptanalytic knowledge, supplied by the reader rather than by the mathematics —
Rogaway's "human ignorance" approach
([Formalizing Human Ignorance](https://eprint.iacr.org/2006/281), Vietcrypt 2006). Even
outside formalization, time-bounded universal hardness claims for a fixed primitive are
subtle: free precomputation converts memory into online speed at a quantified exchange
rate (Corrigan-Gibbs–Kogan,
[The Discrete-Logarithm Problem with Preprocessing](https://eprint.iacr.org/2017/1113),
Eurocrypt 2018: generic preprocessing attacks with advice $S$ and online time $T$
achieve success $ε$ with $S \cdot T^2$ on the order of $ε \cdot N$, and this is
tight); non-uniform definitions admit unrealistic counterexample algorithms, as
discussed above
(Bernstein–Lange); and whether the non-uniform model is the right one at all is itself
debated (Koblitz–Menezes, [Another look at non-uniformity](https://eprint.iacr.org/2012/359)).

The Lean interface encodes this division of labour — the mathematics exhibits the
reduction, and the reader supplies the hardness judgement. `TextbookDLAdvantageLE` and
its coin-carrying variant bound the winning-coins measure of one named algorithm —the
relation finder the reduction constructs— and the finite-security profiles instantiate
that bound with a caller-supplied advantage function, evaluated at the finder's
accounted resources. The advantage function is arbitrary, and the theorems are generic
in it: nothing about the difficulty of discrete log is assumed anywhere in the
development. A capstone converts a belief about achievable discrete-log advantage at a
given cost into a bound on the protocol game; it does not certify the belief.

### The resource numbers are coverage parameters

The Snark-side capstones quote concrete numbers: the covered adversary makes at most
$2^{123}$ random-oracle queries and performs at most $2^{125}$ group operations, the
latter certified by a staged cost program. The statistical remainder ($2^{-83}$ for
the consensus-generic Action capstone) is proved for every workload up to the full
covered budget. The endpoints count the reduction's work additively, by a proved
counter composition: the reduction adds at most $2^{123}$ group operations and 22 oracle
queries to the adversary's own, and the advantage is evaluated at $2^{124}$ queries and
$2^{126}$ group operations after rounding up to powers of two. The accounting overhead
is a fraction of a bit of group work: before rounding, $2^{125}$ becomes at most
$2^{125} + 2^{123} \approx 2^{125.32}$.

It is easy to misread the $2^{126}$ target as an estimate of Vesta's discrete-log cost;
it is in fact a coverage parameter. The target is as large as is useful —past roughly
$2^{126}$ group operations an adversary can compute Vesta discrete logs directly,
voiding every binding property here (see the lifetime caveat below)— and no smaller,
so that no adversary with a meaningful guarantee is excluded.

The near-coincidence with Pollard rho's estimated cost on Vesta (about $2^{126}$, using
the curve's automorphisms) is therefore a stopping rationale, not a dependence: a revised
attack estimate would change the interpretation, not the theorem. And the quoted bound is
the worst covered point: the theorems evaluate the advantage function at the finder's
exact accounted counts, and substituting the larger rounded budgets can only increase
it. Since generic-attack success falls off steeply below its threshold, an adversary far
below the target gets a far stronger interpreted bound.
Reading resource-parameterized claims this way —as attack-cost curves rather than
single thresholds— follows Bernstein,
[Understanding brute force](https://cr.yp.to/snuffle/bruteforce-20050425.pdf), 2005.

## The algebraic-adversary restriction

An algebraic adversary is one that, whenever it outputs a group element, also supplies a
representation: coefficients expressing that element over the elements it has received
(Fuchsbauer–Kiltz–Loss,
[The Algebraic Group Model and its Applications](https://eprint.iacr.org/2017/620),
Crypto 2018). Only
the provenance of output group elements is restricted. The computation deciding the
coefficients is unrestricted — the adversary may inspect encodings, branch on bits, and
use any structure it can see. In this development the restriction is part of the
adversary's *type* in the online-AGM layer, not a named hypothesis on any capstone —
which is why this page states it: conditions carried by the quantifier domain are as
load-bearing as named hypotheses, and less visible in theorem statements.

Like the random-oracle model, this is a heuristic restriction of the adversary's
strategy class, not an assumption that could be true or false of Pallas or Vesta.
Random-oracle non-instantiability (Canetti–Goldreich–Halevi,
[The Random Oracle Methodology, Revisited](https://eprint.iacr.org/1998/011)) is the
standing warning against reading
in-model theorems as instantiated guarantees. The heuristic earns its keep only if two
supporting claims hold. First, re-expression: an adversary that is only *incidentally*
non-algebraic must be re-expressible as an algebraic one at similar cost. Every generic
adversary is algebraic —it only ever combines the elements it received— so the
algebraic-adversary restriction is strictly weaker than the generic-group one; the
substance is the claim that the concrete curves offer no useful operations that are
neither generic nor algebraic. Second, the *known* deviations of the curves from generic
must not obstruct the re-expression. Pasta's efficient endomorphism is the sharp
example: it acts as scalar multiplication by a known cube root of unity, so an adversary
using it remains algebraic — its outputs still carry representations. The same
structure genuinely cheapens the best generic attacks (the automorphism-class rho walk
behind the $2^{126}$ figure above), which the coverage parameters absorb. Deviating from
generic and obstructing algebraicity are different failures, and the endomorphism is the
first (since it can reduce the number of group operations required) without being the
second.

The remaining supporting claim is that the modelled basis covers everything a realistic
adversary can obtain. That is a claim about hash-to-curve, and it belongs with the
reference-string discussion below.

## Fixed bases, hash-to-curve, and the reference string

Several reductions bottom out at discrete log by treating a set of group elements as
*independent* — for example the value-commitment bases $\mathcal{V}$ and $\mathcal{R}$, the
Sinsemilla generators, and the proof system's inner-product reference string. Independence
is what turns "find a nontrivial relation among these elements" into the discrete-log game:
the reduction models each base as a random multiple of one generator and embeds its
discrete-log challenge into that randomness.

In the deployed protocol, though, these bases are *fixed*. Each is produced once, by
hashing public strings to the curve with `GroupHash` (spec
[§5.4.9.8](https://zips.z.cash/protocol/protocol.pdf#concretegrouphashpallasandvesta)),
and the resulting outputs are baked into the protocol as a Uniform Reference String. The
gap between the two is the standard gap for protocols with a URS. We prove security for
the family of protocols that sample the bases at random, over the distribution of that
randomness. Then we argue heuristically that the deployed protocol, which fixes them via
hash-to-curve, inherits it — provided that the hash-to-curve scheme admits no attack
more efficient than the algebraic ones bounded by the proven reductions. The
[group-hash indifferentiability development](group-hash-indifferentiability.md)
supplies the formal half of that judgement: the deployed group hash is
indifferentiable from a random oracle into the group, under a named Weil-bound
hypothesis, with the simulator exhibited as an algorithm. No Lean
theorem instantiates the soundness endpoints at the deployed bases; identifying Halo2's
hash-to-curve outputs with the sampled basis is the heuristic step
(`Zcash/TrustBoundary.lean` records this scope). The same heuristic underlies every
fixed-base use of hash-to-curve here, including the value and note commitments, the
Merkle hash, and the proof system's reference string. The same primitive also produces
bases on demand: `DiversifyHash` derives each diversified address base from `GroupHash`
at key generation.

This heuristic comes with an important caveat: an adversary has the protocol's *entire
lifetime* to attack that one specific reference string — for example, to search for a
discrete log relating the value-commitment bases $\mathcal{V}$ and $\mathcal{R}$. Such
an attack could have started as soon as Orchard was designed, long before any particular
transaction it would compromise. A bound that holds for random bases does not preclude
an attack tuned to the deployed bases, and the cost of finding one is amortized over
every transaction ever made against them. The caveat is not speculative: a rational
adversary would certainly prefer this strategy, since it dominates all others based on
breaking discrete logs — it does not provide free precomputation, but it gives the
adversary more time over which to pay the cost. That is a known, acknowledged limitation
of this development.

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

What makes a hash-to-curve output a good base is that it comes with no known
representation over previously received elements. The same property cuts the other way
for the adversary model. A realistic adversary can evaluate `GroupHash` directly on
inputs of its choice, and every output it obtains is a group element held with no
representation over a fixed basis — so an adversary with that access is not algebraic
over any fixed finite basis. The faithful modelling makes hash-to-curve itself an oracle
of the game: the adversary may query it, each fresh output joins the AGM basis as a new
independent element, and the reduction may embed its challenge in programmed outputs.
The development does not currently model that access. Each game fixes an enumerated
basis of the generators its honest algorithms use, and its theorems quantify over
adversaries algebraic over that basis. Two consequences should be stated plainly. For
games whose honest parties themselves call `DiversifyHash` —Spendability and Spend
Authority, where key generation derives the diversified base— the modelled adversary
cannot express strategies a realistic adversary performs routinely, so those games need
the oracle in the adversary's interface before their capstones carry their intended
weight; the indifferentiability result is what licenses giving them that oracle as a
random oracle. And enumerating, per game, the generators judged relevant leaves out fixed bases
from other protocol components that a deployed adversary can obtain; nothing known
suggests they help, but "nothing known suggests" is itself a heuristic judgement, and it
should be visible rather than implicit. Both are known limitations of the current
modelling ([#188](https://github.com/zcash/ironwood/issues/188)).

These models and their limitations are part of every statement in the development: a
capstone's bound is no stronger than the adversary class it quantifies over. For the
property statements the models scope, see the
[**Ledger Security Games**](ledger-security-games.md); for the verifier-soundness half,
the [**Proof Map**](proof-map.md); for the coined terms, the [**Definitions**](definitions.md).
