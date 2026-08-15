# Group-Hash Indifferentiability

The Zcash security arguments model the Pasta group hashes as random oracles into
the curve groups. This page explains what justifies that modelling, and what the
formalization does and does not establish. It is written for a reader who has
not seen an indifferentiability proof before; no prior acquaintance with the
notion is assumed.

The counting that the argument rests on lives in
[CompElliptic](https://github.com/daira/CompElliptic) (`Hashing/TwoTermUniformity.lean`,
`Hashing/PastaSSWU.lean`); the probabilistic argument on this page lives under
`Zcash/Security/GroupHash/`.

## The deployed hash

Let $\Group$ be an elliptic curve group, $\Field$ its field of definition
(base field), and $\Domain$ a convenient input domain. The deployed group hash
$H \typecolon \Domain \to \Group$ is

$$H(m) = f(u_0) + f(u_1), \qquad (u_0, u_1) = \mathsf{hash\_to\_field}(m, 2),$$

where $f = \mathsf{mapToCurve} \typecolon \Field \to \Group$ sends a field element
to a curve point, and the sum is the group law.

We model $\mathsf{hash\_to\_field}(\cdot, 2) \typecolon \Domain \to \Field \times \Field$
as a random oracle: an idealized hash whose output on each new input is a fresh
uniform pair. The question is whether $H$ itself may then be modelled as a random
oracle into the group $\Group$. But first, we'll try to explain why a simpler
construction does not suffice.

## Mapping to a curve

How can we map from a field to an elliptic curve group? In the case of short
Weierstrass curves, each non-identity point has coordinates
$(x, y) \typecolon \Field \times \Field$ satisfying the curve equation:

$$y^2 = x^3 + a \cdot x + b$$

An obvious candidate for a map from a field element $u$ to a curve element
would be to choose one of the points with $x = u$ using a deterministic square
root function $\possqrt{\cdot}$, i.e. $(u, \possqrt{u^3 + a \cdot u + b})$.

Sapling used twisted Edwards curves which have a different equation, but that
is essentially what it did — pick one of the coordinates, and then the equation
in the other is quadratic. It's easy to construct a hash into the field with
low bias using a conventional hash function with a large enough output size, by
taking its output as an integer modulo the field size. Then the mapping above
is bijective, so its output points will be approximately evenly distributed,
although only among *half* of the curve points — the half chosen by the
deterministic $\possqrt{\cdot}$.

The problem is that then not all $x$-coordinates, and therefore not all inputs
to the hash, map to a point. For each $x$-coordinate, we have 0, 1, or 2
solutions for $y$ depending on the number of square roots of $x^3 + a \cdot x + b$.
Heuristically, roughly half of the $x$-coordinates should have no solutions
for $y$, roughly half of them should have two solutions, and a negligible
proportion (only the case
<span style="white-space: nowrap">$y^2 = 0 = x^3 + a \cdot x + b$</span>, which
may not happen at all for a particular curve) have one solution. That is in fact
what happens in practice. If the curve has $N$ points with $q = |\Field|$, and
$N$ is odd —as it is for Pallas and Vesta— then the number of
$x$-coordinates that correspond to a point on the curve is exactly $(N - 1)/2$.
The *proportion* that correspond to a point is $(N - 1)/2q$.
The [Hasse bound](https://en.wikipedia.org/wiki/Hasse%27s_theorem_on_elliptic_curves),
$|N - (q + 1)| \leq 2\sqrt{\mathstrut q}$, makes the heuristic precise:
$(N - 1)/2q$ is within $1/\sqrt{\mathstrut q}$ of $1/2$.

For fixed generators, having a group hash that is not a total function is not
so much of a problem: we can extend it to a total function by repeated hashing with
an index. Since there are only a fixed set of generators and they are found off-line,
non-constant timing due to the variable number of iterations is not an issue.
But Sapling had introduced *diversified addresses*, which require on-line use
of the group hash in order to derive an address from a diversifier. We avoided
timing attacks in Sapling by not doing repeated hashing, and accepting that
only half of all diversifiers would be valid. But we had encountered complications
in the application protocol ([ZIP 32](https://zips.z.cash/zip-0032) and its usage)
due to this abstraction leak from the underlying cryptography. We wanted to avoid
that when designing Orchard.

Fortunately, an Informational RFC for deterministic, constant-time Hashing to
Elliptic Curves was close enough to ready (it was in a
[late draft](https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-10.html),
and in fact did not change significantly before the final version,
[RFC 9380](https://www.rfc-editor.org/rfc/rfc9380.html)). The scheme we analyse
here is that standard, specialized to Pallas and Vesta.

## What 𝑓 looks like

So how does $f$, or as RFC 9380 calls it `map_to_curve`, work? A naive approach
would be to try to "fill in" the other half of the curve points that were missed
by the deterministic square root, using the other half of the $x$-coordinates.
But there is no known way of doing so (in fact, if there were then it would
indicate undesired structure and potential cryptographic weaknesses in the curve).

The basic idea of having two different cases depending on whether a given input
yields solutions for a square root, however, is exactly what RFC 9380's
"[Simplified SWU](https://www.rfc-editor.org/rfc/rfc9380.html#name-simplified-shallue-van-de-w)"
construction does. For now we will ignore a complication that arises for short
Weierstrass curves with $a = 0$, like Pallas and Vesta; we'll get to that
later. Then, ignoring negligible cases we have:

$$f(u) = \begin{cases}
  g(u),&\textsf{for half of the } u \\
  h(u),&\textsf{for the other half.}
\end{cases}$$

The Simplified SWU construction arranges that the two candidate curve-equation
values differ by a nonsquare factor, so exactly one of the two branches is
available for each input $u$.

It also fixes the sign at the end: the output's $y$-coordinate is negated if
necessary so that its sign matches the sign of the input, in the convention
that RFC 9380 calls `sgn0`. This makes $f$ *odd*, that is, $f(-u) = -f(u)$
for $u \neq 0$. Oddness carries weight below: it is what splits an input pair
$\{u, -u\}$ across a point and its negation, and the character-sum analysis
relies on it too.

The images of $g$ and $h$ are not disjoint; for Simplified SWU they in fact
coincide, apart from a negligible proportion of exceptional points. To see why,
fix a target point $P$. Whether any input reaches $P$ via $g$ comes down to a
quadratic equation in $t = Z \cdot u^2$; the equation depends only on the
$x$-coordinate of $P$, which $P$ shares with $-P$. A solution $t$ yields inputs
precisely when $t/Z$ is a square —that is, when $t$ really is $Z \cdot u^2$ for
some input $u$— and then, since $f$ is odd, the input pair $\{u, -u\}$ has one
member mapping to $P$ and the other to $-P$. So each realizable solution
contributes exactly one preimage of $P$. Reaching $P$ via $h$ comes down to a
second quadratic in $t$, in the same way. Now, two facts connect the branches:

- $t$ solves the $g$-equation exactly when $1/t$ solves the $h$-equation;
- $t/Z$ is a square iff $(1/t)/Z$ is, because their product is the square $1/Z^2$.

So input $u$ reaching $P$ via $g$ corresponds to the inputs $\pm 1/(Z \cdot u)$
reaching $P$ via $h$ and vice versa. Hence $P$ is reached via $g$ iff it is reached
via $h$.

This coexists with the exact halves above because those partition the *inputs*,
not the outputs. The correspondence $u \mapsto \pm 1/(Z \cdot u)$ carries the
$g$-half of the inputs into the $h$-half and back, preserving the point reached.
About $\fraction{3}{8}$ of the output space is reached
—with 2 or 4 preimages per reached point excluding exceptional cases— and
the remaining $\fraction{5}{8}$ by neither map. (These proportions are heuristic;
we confirmed them by exact computation on small curves, and they can be proven
with error $O(1/\sqrt{\mathstrut q})$ by counting points on the branch varieties —
Lang–Weil, "Number of Points of Varieties in Finite Fields",
*Amer. J. Math.* 76(4), 1954, [doi:10.2307/2372655](https://doi.org/10.2307/2372655).
A modern exposition of that paper is Tao,
[The Lang-Weil bound](https://terrytao.wordpress.com/2012/08/31/the-lang-weil-bound/),
2012.)

```admonish info title="Where the ⅜ comes from"
Fix a target point and consider the quadratic in $t$ deciding whether it is
reached — the branch-$g$ one, say. (The branch-$h$ one behaves identically under
$t \mapsto 1/t$.) Two coin flips decide the outcome.

- The quadratic has two roots when its discriminant is a square: probability
  about $\fraction{1}{2}$.
- Given a split, each root $t_i$ yields an input pair $\pm u_i$ exactly when
  $t_i/Z$ is a square. These two events are perfectly correlated, because the
  product $t_1 \cdot t_2$ is fixed by the quadratic's coefficients: writing the
  quadratic character $\chi(\cdot)$ as $+1$ on nonzero squares and $-1$ on
  nonsquares, we have $\chi(t_1/Z) \cdot \chi(t_2/Z) = \chi(t_1 \cdot t_2)$.
  That sign is $-1$ about half the time, in which case exactly one root yields
  inputs. It is $+1$ otherwise — then both roots yield inputs or neither does,
  each about half the time.

By oddness, each input pair $\pm u$ contributes one preimage to the target point
and one to its negation. So the point is reached from $2$ preimages (one per
branch) with probability $\fraction{1}{2} \cdot \fraction{1}{2} = \fraction{1}{4}$,
and from $4$ preimages (two per branch) with probability
$\fraction{1}{2} \cdot \fraction{1}{2} \cdot \fraction{1}{2} = \fraction{1}{8}$;
otherwise it is unreached. The reach probability is
$\fraction{1}{4} + \fraction{1}{8} = \fraction{3}{8}$, and reached points have
$\fraction{8}{3}$ preimages on average.
```

It turns out, for the Pasta curves, that we cannot do much better than this
$\fraction{3}{8}$ coverage by mapping directly from a single field element (or
at least, trying to do so would not lead to a less complicated scheme overall,
given other constraints like the desire for a constant-time group hash).

Particular application protocols might actually be perfectly fine with this
kind of non-uniform mapping. However, it can easily be distinguished from a
uniform one, and so we would have to take account of that non-uniformity in
all of our security arguments. For a clean abstraction we would like a mapping
that cannot be distinguished, when applied to $\mathsf{hash\_to\_field}$
outputs, from a uniform mapping onto the whole group.

We've now established the motivation for using the $H(m) = f(u_0) + f(u_1)$
construction, instead of a mapping from a single field element. The rest of
this page is about why that construction works, specifically why it can
reasonably be modelled as a random oracle.

## Uniformity is not enough

A first guess is that it would suffice for $H$'s outputs to be close to uniform
on $\Group$. We will see from the [regularity](#the-first-ingredient-regularity)
analysis below that this holds. It does not suffice, because $H$ is not a black
box. The function $\mathsf{hash\_to\_field}$ is public: anyone can compute the
intermediate pair $(u_0, u_1)$ and check that $H(m)$ really equals
$f(u_0) + f(u_1)$. A security argument that replaces $H$ by an ideal random
oracle $R$ must survive an adversary that does exactly that. So the question is
not "do $H$'s outputs look uniform?" but "can the *pair* of oracles
$(\mathsf{hash\_to\_field}, H)$ be faked consistently, given only $R$ ?".

## Indifferentiability

Indifferentiability (Maurer–Renner–Holenstein,
[Indifferentiability, Impossibility Results on Reductions, and Applications to the Random Oracle Methodology](https://eprint.iacr.org/2003/161))
makes that question precise. A *simulator* $\Sim$ is given oracle access to the
ideal random oracle $R$, and must answer $\mathsf{hash\_to\_field}$ queries.
A *distinguisher* $\Dist$ talks to two oracles and tries to tell which of two
worlds it is in:

- the **real world** $(\mathsf{hash\_to\_field}, H)$ — the genuine intermediate
  oracle and the genuine construction built on top of it;
- the **ideal world** $(\Sim^R, R)$ — the ideal random oracle $R$ into the
  group, and the simulator faking the intermediate hash consistently with it.

The construction is $(q, \eps)$-**indifferentiable** if some simulator makes
every distinguisher's advantage at most $\eps$ after $q$ queries. The point
of establishing this is the Maurer–Renner–Holenstein composition theorem:
any protocol proven secure with an ideal $R$ in place of the group hash
stays secure with the real $H$ — provided one is content to model
$\mathsf{hash\_to\_field}$ as a random oracle. So indifferentiability is what
lets the rest of the security development treat the group hash as a random
oracle without having to reason about $\mathsf{hash\_to\_field}$ again.

```admonish note title="A heuristic, not an assumption"
Modelling $\mathsf{hash\_to\_field}$ as a random oracle is a *heuristic*, not a
falsifiable hardness assumption. Non-instantiability results (Canetti–Goldreich–Halevi,
[The Random Oracle Methodology, Revisited](https://eprint.iacr.org/1998/011))
show that a scheme can be provably secure in the random-oracle model yet insecure
under every concrete instantiation. So an indifferentiability proof does not
guarantee real-world security on its own; it restricts attention to adversaries
that treat $\mathsf{hash\_to\_field}$ as a black box, which is where analytical
effort is most useful to spend. The [Security Models](security-models.md) page
develops this framing.
```

## The simulator is forced

The consistency check above pins down what the simulator must do. On a query $m$
it learns $Q = R(m)$, a uniform group element, and it must return a pair
$(u_0, u_1)$ with

$$f(u_0) + f(u_1) = Q,$$

because the distinguisher can and will check that equation. Moreover the pair
must *look* like a fresh $\mathsf{hash\_to\_field}$ output, i.e. uniform — so the
simulator must return a preimage of $Q$ that is close enough to uniform under the
two-term sum. Following the proof of Theorem 1 of Brier–Coron–Icart–Madore–Randriam–Tibouchi
([Efficient Indifferentiable Hashing into Ordinary Elliptic Curves](https://eprint.iacr.org/2009/340)),
specialized to this construction, two ingredients make this possible.

### The first ingredient: regularity

For uniform $(u_0, u_1)$, the distribution of $f(u_0) + f(u_1)$ is close to
uniform on $\Group$. CompElliptic's `TwoTermUniformity` proves this from a
Weil bound on the character sums of $f$.

A *character* of $\Group$ is a homomorphism $\psi \typecolon \Group \to \Cmul$
into the nonzero complex numbers: it turns the group operation into ordinary
multiplication, $\psi(P + Q) = \psi(P) \cdot \psi(Q)$, and its values lie on the unit
circle. The *character sum* of $f$ at $\psi$ is

$$S(\psi) = \sum_{u \in \Field} \psi(f(u)),$$

the character added up over all outputs of $f$. The trivial character
$\psi \equiv 1$ gives $S(\psi) = |\Field|$; a *Weil bound* bounds the size
$|S(\psi)|$ of the nontrivial characters, from which such character-sum bounds
follow. The name "Weil bound" is from André Weil's proof of the Riemann hypothesis
for algebraic curves over finite fields
([Sur les courbes algébriques et les variétés qui s'en déduisent](http://denise.vella.chemla.free.fr/Weil-courbes-varietes.pdf), 1948).
A modern presentation of the elliptic-curve case is Kohel–Shparlinski,
[On Exponential Sums and Group Generators for Elliptic Curves over Finite Fields](https://www.i2m.univ-amu.fr/perso/david.kohel/pub/character.pdf), *ANTS-IV*, *LNCS* 1838, 2000.

Character sums measure uniformity because a distribution on $\Group$ is uniform
exactly when all its nontrivial character sums vanish — so small nontrivial
character sums mean close to uniform. That is what lets a Weil bound control
the *regularity distance*

$$\sum_{Q} \left| \frac{\mathsf{pairCount}\, f\, Q}{|\Field|^2} - \frac{1}{|\Group|} \right| \le \eps,$$

where $\mathsf{pairCount}\, f\, Q$ counts the pairs $(u_0, u_1)$ with
$f(u_0) + f(u_1) = Q$ — the size of the *fibre* of $Q$. Dividing by
$|\Field|^2$ turns the count into the probability that the two-term sum lands
on $Q$, so the sum is the $L^1$ distance between that output distribution and the
uniform distribution on $\Group$. The *$L^1$ distance* between two distributions
$p$ and $q$ on a finite set is $\sum_x |p(x) - q(x)|$, the total of the absolute
differences of the probabilities they assign. At the deployed sizes $\eps$ is
about $2^{-116}$.

### The second ingredient: preimage sampling

For each $Q$, the simulator must sample a pair uniformly from the fibre
$\{(u_0, u_1) \mid f(u_0) + f(u_1) = Q\}$. Sampling one coordinate is easy: draw
$u_0$ uniformly. Then the second coordinate must satisfy $f(u_1) = Q - f(u_0)$,
so $u_1$ ranges over the preimages of $Q - f(u_0)$ under the single map $f$.
That single-term fibre has at most a constant number of elements — we saw in
the note above that each point has at most $4$ preimages under $f$, and
CompElliptic's `card_mapToCurve_fibre_le` proves the weaker but sufficient
bound of $10$. That is what makes the sampler efficient, and is where the
simulator's cost analysis will enter (a later milestone).

## The single-query bias, in detail

This is the part the formalization currently establishes, in
`Zcash/Security/GroupHash/Sampler.lean`, and it is the technical heart of the
argument. It compares the two worlds on a *single* fresh query, before worrying
about how queries compose.

### Two per-query laws

On a fresh query, the distinguisher observes a pair in
$\Field \times \Field$ (from which the group element is a fixed
function). Each world draws that pair from a distribution:

- **real**: the pair is uniform on $\Field \times \Field$ — this is
  $\mathsf{hash\_to\_field}$ answering honestly (`PMF.uniformOfFintype`);
- **ideal**: draw a uniform group element $Q$, then draw a pair uniformly from
  the fibre of $Q$ (`idealLaw`, the `bind` of the uniform law on $\Group$
  with the fibre sampler).

### The fibre sampler and its fallback

`fibreSampler f Q` samples a pair uniformly from the fibre of $Q$. One subtlety:
the two-term sum need not be surjective, so some $Q$ have an *empty* fibre, with
no pair to return. On those, the sampler falls back to a uniform pair on
$\Field \times \Field$, which keeps it a genuine distribution. The fallback's
only effect is on the bias, where it is accounted for exactly.

### The bias reduces to the regularity distance

The claim, in each direction, is that the law in each world *overshoots* that
of the other world by at most $\eps$: for every test $w$ valued in $[0, 1]$,
$\sum_x \mu(x)\, w(x) \le \sum_x \nu(x)\, w(x) + \eps$. This one-sided form
(`PMFWeightedBiasLE`) is what the query-composition step needs.

To bound it, regroup the per-pair difference by the group element
$Q = f(u_0) + f(u_1)$. Take a nonempty fibre of $Q$, with
$k = \mathsf{pairCount}\, f\, Q \ge 1$ pairs. Every pair in it looks identical
in both worlds:

- the ideal world puts $\frac{1}{|\Group| \cdot k}$ on each pair — it spreads
  the $\frac{1}{|\Group|}$ that $R$ gives to $Q$ uniformly over the $k$ pairs;
- the real world puts $\frac{1}{|\Field|^2}$ on each pair.

So the absolute difference is one constant across all $k$ pairs of the fibre,
and summed over the fibre it is

$$k \cdot \left| \frac{1}{|\Group| \cdot k} - \frac{1}{|\Field|^2} \right| = \left| \frac{1}{|\Group|} - \frac{k}{|\Field|^2} \right|,$$

a single term of the regularity distance. The $k$ cancels inside the first
fraction. The fibre size enters only as $\mathsf{pairCount}\, f\, Q$ in that
term, which is identical for every nonempty fibre — the ideal-world law is
uniform *within* the fibre whatever its size, so all $k$ pairs share one
probability. Summing over the nonempty fibres gives the part of the regularity
distance with $\mathsf{pairCount}\, f\, Q > 0$.

### Why both directions come out at the same $\eps$

The empty fibres require our attention in one direction only.

When the **real** law overshoots the ideal one, the fallback only *raises* the
ideal law's probabilities, which shrinks $\text{real} - \text{ideal}$. So this
direction is bounded by the nonempty part of the regularity distance alone.

When the **ideal** law overshoots the real one, the fallback contributes a
*fallback mass* $\frac{e}{|\Group|}$, spread over all pairs, where $e$ is the
number of group elements the two-term sum misses — the mass $R$ sends to those
missed elements. That mass is exactly the empty-fibre part of the *same*
regularity distance: an empty fibre has $\mathsf{pairCount}\, f\, Q = 0$, so
its term is $\left| 0 - \frac{1}{|\Group|} \right| = \frac{1}{|\Group|}$, and
there are $e$ of them, totalling $\frac{e}{|\Group|}$. So the nonempty part
and the fallback mass together are the *whole* regularity distance
$\sum_Q \left| \frac{\mathsf{pairCount}\, f\, Q}{|\Field|^2} - \frac{1}{|\Group|} \right| \le \eps$.
The fallback fills in the terms the nonempty part left out, and the bound stays
at $\eps$.

## From one query to many

A single-query bound does not immediately bound a distinguisher that makes many
adaptive queries — later queries may depend on earlier answers. The adaptive
hybrid `runFreshPMF_eventBiasLE` (in `Zcash/Snark/Soundness/Oracle/`) bridges the
gap: it charges the one-squeeze bias once per query node, so a $Q$-query tree
turns a single-query bias $\eps$ into an overall bias of at most $Q \cdot \eps$,
even when the query tree is fully adaptive. Repeated queries to the same point
are first collapsed by `dedup`, so a point asked twice keeps one answer rather
than drawing a fresh one.

## What is proved, and what is modelled

It's important to be precise about the status of each part.

- **Formalized and machine-checked.** The regularity distance
  (`TwoTermUniformity`, conditional on the Weil bound), the single-term fibre
  bound (`card_mapToCurve_fibre_le`), and the single-query bias in both
  directions (`Sampler.lean`).
- **An unformalized mathematical input.** The Weil bound on the character sums of
  $f$ is a well-established but currently unformalized fact. It is not formalized
  because important pieces of the underlying mathematics are not yet present in
  Mathlib — but it is not in doubt. The regularity distance is proved relative to
  it, stated as the named hypothesis `WeilBounded`.
- **A modelling choice, not a theorem.** That $\mathsf{hash\_to\_field}$ behaves
  like a random oracle is a heuristic (see the note above). The
  indifferentiability argument is what makes that heuristic transfer from
  $\mathsf{hash\_to\_field}$ to the group hash $H$; it does not remove it.
- **In progress.** Composing the single-query bias into the full
  distinguisher-advantage bound, and the simulator's cost analysis, are not yet
  formalized.
