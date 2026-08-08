# Interpreting Security

> **Bottom line:** within the formal model, every covered computational failure of
> Action knowledge soundness yields a solver for Vesta discrete log. The underlying
> benchmark therefore remains breaking Vesta DLOG, whose best known classical attack
> reaches its break range at roughly $2^{126}$ group operations.

Here “knowledge soundness” means that an accepted proof has a recoverable valid
*witness*: the private data that justifies the proved statement.

## For experts

For a bundle containing $n$ Actions and an adversary $A$ making at most $Q$
random-oracle queries and performing at most $W$ Vesta group operations, the reduction
gives

$$
\Pr[\text{verifier accepts but extraction fails}]
\;\le\;
\operatorname{Adv}_{\mathrm{DLOG}}
  \bigl(Q+22,\,W+R(n)\bigr)
+ \varepsilon_{\mathrm{stat}}(Q,n).
$$

**$\operatorname{Adv}_{\mathrm{DLOG}}(q,w)$ is the advantage function.** For query
budget $q$ and work budget $w$, it gives the externally supplied upper bound on the
success probability of a Vesta DLOG solver.
$\varepsilon_{\mathrm{stat}}(Q,n)$ is the statistical soundness error term for an
adversary making at most $Q$ oracle queries against a bundle containing $n$ Actions. It
bounds the exceptional cases in which the random challenges prevent extraction.

**Direction of the reduction:**

> Action attacker $A$ using $Q$ queries and $W$ group operations
> $\longrightarrow$ reduction adds 22 queries and $R(n)$ group operations
> $\longrightarrow$ Vesta DLOG solver using $Q+22$ queries and $W+R(n)$ group
> operations.

The reduction constructs the DLOG solver by running the Action attacker and processing
its output. The fixed $+22$ is the reduction's extra oracle reads. $R(n)$ is the extra
Vesta group work performed by the reduction itself for a bundle containing $n$ Actions.
Both are reduction overhead, not attacker work or a probability loss.

For the certified consensus profile, $R(n)\le W$, so the DLOG solver uses at most $2W$
group operations. This is the “one-bit loss”: a $2^{125}$ protocol-attacker work budget
maps to a rounded $2^{126}$ DLOG-solver work budget. The graph plots the latter, after
the reduction has added its overhead. Neither number is a probability; the vertical
failure probability is determined by
$\operatorname{Adv}_{\mathrm{DLOG}}+\varepsilon_{\mathrm{stat}}$.

## In plain language

The reduction runs from a protocol attacker to a DLOG solver. Therefore, outside the
statistical soundness error, a covered protocol attack would imply a DLOG break with the
resources shown above. No easier protocol-specific computational term remains in the
bound. The reverse is not claimed: a DLOG solver does not automatically forge an Action
proof.

There is no need to turn this into an arbitrary single “security-bit target.” The full
advantage function says more: for any query and work budgets, it tells experts exactly
where to evaluate their preferred Vesta DLOG estimate.

## Reading the DLOG curve

Choose an amount of DLOG-solver work on the horizontal axis, trace upward to the orange
curve, and then read the corresponding DLOG-attack success on the vertical axis. The
curve reaches the Vesta DLOG break range at roughly $2^{126}$ group operations.
Both axes use base-2 logarithmic scales.

The graph shows only group work. The oracle-query budget $Q$ remains a separate input in
the equation above.

<figure class="advantage-figure">
<svg class="advantage-chart" viewBox="0 0 840 500" role="img" aria-labelledby="advantage-chart-title advantage-chart-desc">
  <title id="advantage-chart-title">Work versus success for the best known Vesta DLOG attack</title>
  <desc id="advantage-chart-desc">A log-log plot of the idealized Pollard-rho attack-success heuristic. Success rises with group work and reaches the discrete-log break range near two to the 126 group operations. This known-attack curve is not a proved upper bound.</desc>
  <rect class="advantage-break-zone" x="750" y="42" width="30" height="390" rx="5" />
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
  <circle class="advantage-break-point" cx="780" cy="46" r="6" />
  <line class="advantage-break-callout" x1="776" y1="51" x2="720" y2="142" />
  <text class="advantage-break-label" x="714" y="160" text-anchor="end">DLOG break range</text>
  <text class="advantage-break-label" x="714" y="179" text-anchor="end">≈ 2¹²⁶ operations</text>
</svg>
<figcaption>The orange line is an idealized Pollard-rho reference curve, not a proved upper bound on <code>Adv_DLOG</code>. The shaded band marks the underlying primitive's break range, not a chosen protocol target.</figcaption>
</figure>

Lean proves the adversary-to-DLOG reduction, its resource transformation, and the
statistical soundness error. The numerical DLOG estimate comes from external
cryptanalysis. See the [Pasta curve design
note](https://z.cash/the-pasta-curves-for-halo-2-and-beyond/).
