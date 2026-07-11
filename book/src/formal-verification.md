# Formal Verification

Ironwood's formal verification is a Lean 4 development (over Mathlib) in this repository:
verifier soundness for the deployed Halo 2 verifier under `Zcash/Snark/`, and the protocol
security-property layers (binding-signature balance, key binding, and the ledger-model
security games) under `Zcash/Security/`. This page documents two development-wide
conventions: how security breaks are represented, and what the development is allowed to
trust.

## Breaks as computed data

The security arguments are reduction-style: a theorem shows that a violation of a protocol
property *exhibits* a concrete break of an underlying primitive — a discrete-log relation, a
hash collision, a commitment-opening collision. Hardness assumptions are consumed only at
the computational layer, against the exhibited break.

Care is needed in how "exhibits" is stated. In a prime-order group, a nontrivial
discrete-log relation between any two elements always *exists*; for any compressing hash,
collisions always *exist* by pigeonhole. So a `Prop` that existentially quantifies over the
break data ("there exist distinct inputs with equal outputs") is simply *true* at every
instantiation of interest. A theorem concluding `property ∨ ∃-break` is then vacuous, and a
hypothesis `¬ ∃-break` is unsatisfiable. Proof irrelevance makes this unrecoverable: even
when a proof constructs the break honestly, a consumer of the statement cannot extract it.

The convention adopted in
[zcash/ironwood#43](https://github.com/zcash/ironwood/issues/43):

* **Break events are structures carrying the breaking data** (the colliding queries, the
  relation coefficients), with `Prop` certificates attached. Examples:
  `RandomOracle.Collision` and `RandomOracle.CollisionUpToSign` (the ±-collision shape produced by
  coordinate-extractor arguments), `Ledger.HashCollision`, `Ledger.NoteCommitBreak`.
* **Reductions are plain computable `def`s** producing them, such as
  `Merkle.collisionOfWrongLeaf` and `noteCommitBreakOfNe`. A structure with data fields
  cannot be inhabited by proof-irrelevant existence, and a plain `def` cannot conjure the
  data from mere existence via choice — the compiler enforces this, so `noncomputable` is
  not permitted for these definitions.
* Efficiency of a reduction is the one property Lean cannot express; it is established by
  inspection. The constructions here are straight-line manipulations of their inputs.
* Predicates over *named* witnesses (for example, a key-binding break of two specific
  witnesses) keep their content as `Prop`s: the breaking pair is bound in the statement
  rather than existentially closed.

## Trust discipline

Following the pattern of CompElliptic's
[trust discipline](https://github.com/daira/CompElliptic#trust-discipline), the development
distinguishes general theorems from concrete, closed computational facts, and holds them to
different trust standards.

**General, quantified theorems** (the soundness statements and security reductions) must
rest only on the standard classical axioms `propext`, `Classical.choice`, and `Quot.sound`.
No `sorry`, no additional axioms, no compiler trust.

**Concrete, closed facts with no free variables** may additionally use `native_decide`
(which discharges a goal by running compiled native code, adding a compiler-trust axiom) and
the kernel's GMP-backed bignum arithmetic. The principal such fact in this repository is the
captured fingerprint match `fingerprint_matches`: a single numeric check that the Lean
verifier's assembled multi-scalar multiplication equals the Rust verifier's on a captured
proof. The CompElliptic dependency applies the same discipline to its concrete
curve-arithmetic facts (cardinalities, primality certificates). Such facts are independently
re-checkable (another implementation, or hand computation, would compute the same result),
so a miscompiled or buggy oracle could in principle be caught by disagreement.

These boundaries are *checked at build time*, not merely documented:

* `Zcash.Snark.Fingerprint.TrustBoundary` pins the fingerprint match: `assert_no_sorry`
  walks the elaborated dependency graph, so a `sorry` hidden in any transitive dependency
  fails the build; and a `#guard_msgs`-pinned `#print axioms` freezes the exact axiom set,
  so a newly introduced axiom fails the build. The pin also documents precisely *which*
  compiler-trust axiom `native_decide` adds — on this toolchain a per-declaration axiom
  (`…_native.native_decide.ax_1_1`), where older Lean versions used the global
  `Lean.ofReduceBool`. Pinning it keeps that claim verified rather than remembered, which
  is the point of the discipline: unpinned claims about the trusted base drift silently as
  toolchains change.
* `Zcash.Security.Ledger.TrustBoundary` pins the break reductions the same way, to `propext`
  and `Quot.sound` only — in particular no `Classical.choice`, connecting to the
  breaks-as-computed-data convention above: the break data cannot have been conjured from
  mere propositional existence.
* CI builds both as part of the default targets, and `fingerprint_matches`'s
  `native_decide` compiles and runs the verifier, so anything `noncomputable` on the
  assembled-verifier path fails the build.

## Glossary

**breaks as computed data** (`Zcash.Security.RandomOracle`, `Zcash/Security/Ledger/`) —
Break events are structures carrying the breaking data, and the reductions producing them
are plain computable `def`s. An ∃-closed break `Prop` is vacuously true at the
instantiations of interest, so the content lives in the data, protected by compiler-checked
computability and pinned axiom sets.

**checked trust boundary** (`Zcash.Snark.Fingerprint.TrustBoundary`,
`Zcash.Security.Ledger.TrustBoundary`) — Build-time pins on what a theorem may rest on:
`assert_no_sorry` over the elaborated dependency graph, plus a `#guard_msgs`-pinned
`#print axioms`. A stray `sorry` or a new axiom fails the build instead of silently widening
the trusted base.

<!-- When formal-verification/glossary.md (zcash/ironwood#38) lands, fold the two entries
above into it as cards, in its grid format:

<section>
<div class="grp">Conventions</div>
<div class="g"><div class="g-head"><span class="term">breaks as computed data</span><span class="anchor">Security.RandomOracle · Security/Ledger</span></div><div class="def">Break events are structures carrying the breaking data (colliding queries, relation coefficients); the reductions producing them are plain computable <code>def</code>s. An ∃-closed break <code>Prop</code> is vacuously true at the instantiations of interest (relations always exist at prime order; compressing hashes always have collisions), so the content lives in the data, protected by compiler-checked computability and pinned axiom sets. See <a href="../formal-verification.html#breaks-as-computed-data">Breaks as computed data</a>.</div></div>
<div class="g"><div class="g-head"><span class="term">checked trust boundary</span><span class="anchor">Fingerprint.TrustBoundary · Ledger.TrustBoundary</span></div><div class="def">Build-time pins on what a theorem may rest on: <code>assert_no_sorry</code> over the elaborated dependency graph plus a <code>#guard_msgs</code>-pinned <code>#print axioms</code>, so a stray <code>sorry</code> or a new axiom fails the build instead of silently widening the trusted base.</div></div>
</section>
-->
