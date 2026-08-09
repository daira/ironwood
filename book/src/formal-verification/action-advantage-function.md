# Interpreting Security

> **Bottom line:** within the formal model, every covered computational failure of
> Action knowledge soundness yields a solver for Vesta discrete log. The underlying
> benchmark therefore remains breaking Vesta DLOG, whose best known classical attack has
> a headline expected cost of about $2^{125}$ group operations.

Here “knowledge soundness” means that an accepted proof has a recoverable valid
*witness*: the private data that justifies the proved statement. “Covered” means inside
the theorem's scope: an adversary that stays within the resource budgets below, supplies
a representation for every group element it outputs, and faces Fiat–Shamir challenges
modelled as a random oracle.

## For experts

For a bundle containing $n$ Actions and an adversary $A$ making at most $Q$
random-oracle queries and performing at most $W$ Vesta group operations, the reduction
gives

$$
\Pr[\text{verifier accepts but extraction fails}]
\;\le\;
\operatorname{Adv}_{\mathrm{DLOG}}
  \bigl(Q,\,W+R(n)\bigr)
+ \varepsilon_{\mathrm{stat}}(Q,n).
$$

**$\operatorname{Adv}_{\mathrm{DLOG}}(q,w)$ is the advantage function.** For query
budget $q$ and work budget $w$, it gives the externally supplied upper bound on the
success probability of a Vesta DLOG solver.
$\varepsilon_{\mathrm{stat}}(Q,n)$ is the statistical soundness error term for an
adversary making at most $Q$ oracle queries against a bundle containing $n$ Actions. It
bounds the exceptional cases in which the random challenges prevent extraction. The
reduction also makes a small fixed number of extra oracle reads; the deployed endpoint
absorbs them when it rounds its query budget up to a power of two, so this page writes
$Q$ throughout.

**Direction of the reduction:**

> Action attacker $A$ using $Q$ queries and $W$ group operations
> $\longrightarrow$ reduction adds $R(n)$ group operations
> $\longrightarrow$ Vesta DLOG solver using $Q$ queries and $W+R(n)$ group operations.

The reduction constructs the DLOG solver by running the Action attacker and processing
its output. $R(n)$ is the extra Vesta group work performed by the reduction itself for a
bundle containing $n$ Actions — reduction overhead, not attacker work or a probability
loss.

For the certified consensus profile, the endpoint evaluates the advantage at $2^{126}$
group operations: the $2^{125}$ attacker budget plus the reduction's own work, rounded up
to a power of two. Neither number is a probability; the vertical failure probability is
determined by $\operatorname{Adv}_{\mathrm{DLOG}}+\varepsilon_{\mathrm{stat}}$.

That $2^{125}$ is a coverage parameter — the adversary group-work budget this theorem
covers, not an estimate of anything. It is not the Pasta curves' security design target,
which carries the same value but measures something else: the “headline cost”, meaning
the expectation, of the best known pre-quantum discrete-log attack on the curve. A design
target for the underlying curves and primitives is expected to sit above the achieved
bound for the protocol built on them. [Security Models](security-models.md) develops the
coverage-parameter reading in full.

## In plain language

Outside the statistical soundness error, a covered protocol attack would imply a DLOG
break with the resources shown above. No easier protocol-specific computational term
remains in the bound. The reverse is not claimed: a DLOG solver does not automatically
forge an Action proof.

The advantage function says more than any single “security-bit target” could: for any
query and work budgets, it tells experts exactly where to evaluate their preferred Vesta
DLOG estimate.

## Reading the DLOG curve

Choose an amount of DLOG-solver work on the horizontal axis, trace upward to the orange
curve, and then read the corresponding DLOG-attack success on the vertical axis. The
marked point is the best known attack's headline expected cost, about $2^{125}$ group
operations. The axis runs one bit further, to the $2^{126}$ this page's bound is
evaluated at; that extra bit is accounting, not a better attack.

The graph shows only group work. The oracle-query budget $Q$ remains a separate input in
the equation above.

<figure class="advantage-figure">
<svg class="advantage-chart" viewBox="0 0 840 500" role="img" aria-labelledby="advantage-chart-title advantage-chart-desc">
  <title id="advantage-chart-title">Work versus success for the best known Vesta DLOG attack</title>
  <desc id="advantage-chart-desc">A log-log plot of the idealized Pollard-rho attack-success heuristic. Success rises with group work. The marked point is the best known attack's headline expected cost, near two to the 125 group operations; the shaded strip continues one bit further, to the two to the 126 the bound is evaluated at. This known-attack curve is not a proved upper bound.</desc>
  <rect class="advantage-break-zone" x="765" y="42" width="15" height="390" rx="4" />
  <g class="advantage-grid">
    <line x1="92" y1="42" x2="780" y2="42" />
    <line x1="92" y1="123" x2="780" y2="123" />
    <line x1="92" y1="204" x2="780" y2="204" />
    <line x1="92" y1="285" x2="780" y2="285" />
    <line x1="92" y1="366" x2="780" y2="366" />
    <line x1="92" y1="432" x2="780" y2="432" />
    <line x1="92" y1="42" x2="92" y2="432" />
    <line x1="242" y1="42" x2="242" y2="432" />
    <line x1="391" y1="42" x2="391" y2="432" />
    <line x1="541" y1="42" x2="541" y2="432" />
    <line x1="690" y1="42" x2="690" y2="432" />
    <line x1="780" y1="42" x2="780" y2="432" />
  </g>
  <g class="advantage-axes">
    <line x1="92" y1="42" x2="92" y2="432" />
    <line x1="92" y1="432" x2="780" y2="432" />
  </g>
  <g class="advantage-labels">
    <text x="80" y="46" text-anchor="end">1</text>
    <text x="80" y="127" text-anchor="end">2⁻²⁰</text>
    <text x="80" y="208" text-anchor="end">2⁻⁴⁰</text>
    <text x="80" y="289" text-anchor="end">2⁻⁶⁰</text>
    <text x="80" y="370" text-anchor="end">2⁻⁸⁰</text>
    <text x="80" y="436" text-anchor="end">2⁻⁹⁶</text>
    <text x="92" y="454" text-anchor="middle">2⁸⁰</text>
    <text x="242" y="454" text-anchor="middle">2⁹⁰</text>
    <text x="391" y="454" text-anchor="middle">2¹⁰⁰</text>
    <text x="541" y="454" text-anchor="middle">2¹¹⁰</text>
    <text x="690" y="454" text-anchor="middle">2¹²⁰</text>
    <text x="780" y="454" text-anchor="middle">2¹²⁶</text>
    <text x="436" y="486" text-anchor="middle">DLOG solver group operations</text>
    <text transform="translate(20 237) rotate(-90)" text-anchor="middle">DLOG success probability</text>
  </g>
  <polyline class="advantage-rho" points="92,417 242,336 391,255 481,206 541,174 690,92 735,68 765,52 770,50 780,46" />
  <circle class="advantage-break-point" cx="765" cy="52" r="6" />
  <line class="advantage-break-callout" x1="760" y1="60" x2="706" y2="238" />
  <text class="advantage-break-label" x="700" y="256" text-anchor="end">best known attack</text>
  <text class="advantage-break-label" x="700" y="275" text-anchor="end">≈ 2¹²⁵ (expectation)</text>
</svg>
<figcaption>The orange line is an idealized Pollard-rho reference curve, not a proved upper bound on <code>Adv_DLOG</code>. The marked point is the best known attack's headline expected cost; the shaded strip is the extra bit of accounting — reduction overhead plus rounding — separating it from the 2¹²⁶ this page's bound is evaluated at. Neither is a chosen protocol target.</figcaption>
</figure>

Lean proves the adversary-to-DLOG reduction, its resource transformation, and the
statistical soundness error. The numerical DLOG estimate comes from external
cryptanalysis.
