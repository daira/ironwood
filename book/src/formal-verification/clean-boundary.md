# The Clean boundary: architecture rule

Status: agreed by the maintainer (2026-07-24). This note is normative for how
Clean-originated concepts appear in the ironwood codebase; it exists so concurrent
workstreams converge on one structure instead of each growing local bridge plumbing.

## The principle

Ironwood is the host, Clean is a guest. Ironwood has its own first-class vocabulary —
`VerifyingKey`, `Expr`, `Shape`, its satisfaction notions, its polynomial environments —
and the guest must not scatter *its* vocabulary (`Halo2.ConstraintSystem`, `Operations`,
`Gate`, `Expression F Query`, `RichExpression`, …) through the host's rooms.

Everything Clean produces is funneled through **one concept: `TopLevelCircuit`**, which
carries everything downstream needs and is instantiated once per concrete circuit
(`orchardActionTopLevelCircuit`).

`TopLevelCircuit` is deliberately two-sided:

* It is a **Clean-native core concept** (it may well migrate into Clean itself —
  `TopLevelKeygen` already consumes only Clean and could follow). Its Clean-typed
  methods (`constraintSystem`, `operations`, `config`, …) are legitimate and public —
  *for the boundary implementation*.
* Ironwood defines an **ironwood-native interface on top of it**, and that interface is
  the only thing non-boundary ironwood code may consume. Its outputs are ironwood-typed;
  a reader never needs to know Clean exists to use it.

The canonical example of the pattern is

```
TopLevelCircuit.toVerifierKey : TopLevelCircuit → ProofParams → URS G → VerifyingKey …
```

— *the* core Clean concept bridged to a core ironwood concept in one method, with every
Clean internal invisible in the signature.

## The ironwood-native interface (target surface)

On `TopLevelCircuit`, defined ironwood-side in the designated boundary modules:

* `toVerifierKey (pp : ProofParams) (urs : URS G) : VerifyingKey (pp.mergeDerived top) …`
  — keygen, with the derived `Shape` in the return type (no lawfulness side condition).
* Shape/domain data as needed by consumers (`ProofParams.mergeDerived`, domain scalars).
* An `Expr`-typed pinned-constraint-system view (the boundary applies
  `RichExpression.toExpr` internally, exactly as `toVerifierKey` already does for the
  VK's `gates`).
* **A satisfaction contract in ironwood terms** (to be designed with the
  circuit-soundness workstream, which is already converging on it via
  `closesEnvironment*` / `topLevelSoundness`): one theorem shape stating that an
  ironwood-decoded assignment satisfying the circuit's derived key implies
  `top.Statement`. The whole `Soundness` integration cluster is the *implementation*
  behind this theorem, not a public seam.

## The rule (enforceable, greppable)

> Clean identifiers may appear only under `Zcash/Circuits/` and inside the designated
> boundary modules. Every other `Zcash/Snark/` (and `Common/`, `Security/`) signature
> mentions only `TopLevelCircuit` and ironwood types.

Review test: *would a reader of this file need to know Clean exists to understand it?
If yes and it is not a boundary module, it is misplaced.*

## Worked example of the anti-pattern

`Zcash/Common/ExprRich.lean`. `RichExpression` exists precisely because ripping
ironwood's `Expr` out of ironwood for Clean's use would have been rude in the other
direction — the type was deliberately duplicated so the clone stays on the guest's side
of the wall. Installing its conversion (`ofExpr`/`toExpr`/`eval_ofExpr`) in the host's
`Common/` un-quarantines it: it presents a Clean-side clone as a core ironwood concept.
(Contrast `Common/Expr.lean` in the same folder — ironwood's own shared AST — which is
exactly what `Common` is for.) The conversion belongs inside the boundary as private
plumbing; with an `Expr`-typed pinned view on the interface, nothing outside the
boundary mentions `RichExpression` at all.

## Current leak inventory (migration backlog)

1. `Zcash/Bridge/` — dissolves. It is imported *by* Snark modules, so it is not a layer,
   just a junk drawer: pasta domain scalars (`omegaOf`/`deltaFp`/`powFast`) →
   `Snark/Core`; `VerifyingKey.gates_eval_of_gates_eq` → restate as an interface lemma
   (its current hypothesis is spelled in `flatGates`/`substSelectorMap`/`queryWalkInit`
   — maximal leakage); Action keygen instances (`actionCS`, `actionOperations`,
   `actionSelMapDerived`, `actionK`) → superseded by `TopLevelCircuit` methods.
2. `Zcash/Snark/VkCommit/` → rename `Snark/Keygen/` (mirroring Clean's `Halo2/Keygen`,
   same concept on the group side); this is a designated boundary module family.
   `Fast/ParMap` (fully generic) → `Common/`. `Common/ExprRich` → into the boundary.
3. `Snark/Fixtures/SingleAction/{PinnedCsMatch,VkMatch}` — restate over the interface
   (`Certificate.lean` already demonstrates the style: it speaks only `vk`,
   `derivedActionVk`, and `TopLevelCircuit` methods).
4. The `Soundness/` integration seam (`Operation*`, `TopLevel*`, `Resolver*`,
   `CanonicalConstraintModel`, `PolynomialEnvironment`, coherence files, …) — demarcate
   as boundary implementation (e.g. `Soundness/Integration/`), capped by the interface
   satisfaction theorem; Clean types allowed inside, invisible above.
5. Cross-repo: `Circuits/Fixtures/Layout.lean`'s keygen semantics (`V1.copyList`,
   `runAssembly`, fixed contents) → Clean `Halo2/Keygen`; and eventually
   `Circuits/TopLevel{,Keygen}.lean` themselves → Clean core.

Sequencing: items 1–3 are mechanical and ironwood-local; 4 wants co-design with the
circuit-soundness workstream (the satisfaction-contract shape); 5 rides the next Clean
pin cycle. Module renames should land as a dedicated cleanup commit, coordinated, not
mid-workstream.
