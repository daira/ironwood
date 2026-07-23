import Zcash.Circuits.Fixtures.FixtureTypes
import Clean.Halo2.Configure

/-!
# `projectCS` — Halo2-Clean `ConstraintSystem` → `CsFixture`

Projects a Halo2-Clean `ConstraintSystem Fp` (the output of running a chip's `configure`)
into the `CsFixture` shape, so it can be compared for **equality** against a fixture
dumped from the actual Rust circuit (`AddPost.lean`, `actionPost.json`).

Two pieces (design doc `vk-matching-design.md` §3):

* **The first-encounter query-index walk** (halo2 `circuit.rs` `query_{advice,fixed,
  instance}_index`): halo2 assigns each *new* `(column, rotation)` the next query index, in
  the order the query is first *built* inside a gate closure. We reproduce that order by a
  left-to-right traversal of each gate polynomial (matching the order the Rust closure
  constructs its sub-expressions), gate by gate. The walk simultaneously (a) accumulates
  the `{advice,fixed,instance}QueryLayout` lists and (b) rewrites each `Query` atom to its
  index, erasing `Halo2.Expression Fp Query` into the index-based `Expr Fp`.

* **The operator erasure** (`Clean/Halo2/Expression.lean:104-109`): Halo2-Clean's four-node
  `Expression` (`var/const/add/mul`) is lowered to ironwood's `Expr` matching how Rust's
  `std::ops` build `Expression<F>`: `Neg`/`Sub` produce `mul (const (-1)) e ↦ .negated e`,
  `add ↦ .sum`, `mul ↦ .product`, `const ↦ .constant`, and `var ↦ .advice/.fixed/.instance`.
  .scaled` — Rust `expr * field` (`impl Mul<F>`) — DOES arise in the mul chain
  (its lookup, bitshift, incomplete `TWO_INV` and LSB gates use it): it is the `mul e (const c)`
  case, constant on the RIGHT, spelled in ports via the `HMul (Expression F L) F` instance as
  `e * (c : Fp)`. A genuine `Constant * e` product is `mul (const c) e` (constant on the LEFT).

The projection targets the deployed VK's shape (after halo2's `compress_selectors`):
selectors are substituted by their packed-fixed-column replacements *before* the walk
(`substSelectorMap`), so no selector atom survives to the erasure. A stray selector atom
erases to a junk constant; `ProjectSemantics` supplies the selector-freeness that makes
the case unreachable.
-/

namespace Zcash.Circuits.Fixtures

open Halo2
open Zcash.Snark (Expr)

/-- The mutable state of the query walk: the three query layouts accumulated so far, in
first-encounter order. -/
structure QueryState where
  advice : Array (ℕ × ℤ) := #[]
  fixed : Array (ℕ × ℤ) := #[]
  inst : Array (ℕ × ℤ) := #[]

/-- Return the index of `(col, rot)` in `arr`, or `none`. -/
def findQuery (arr : Array (ℕ × ℤ)) (col : ℕ) (rot : ℤ) : Option ℕ :=
  (arr.findIdx? (fun p => p.1 = col ∧ p.2 = rot))

/-- Register `(col, rot)` in the advice layout, returning its index (existing or new). -/
def QueryState.advIdx (s : QueryState) (col : ℕ) (rot : ℤ) : ℕ × QueryState :=
  match findQuery s.advice col rot with
  | some i => (i, s)
  | none => (s.advice.size, { s with advice := s.advice.push (col, rot) })

def QueryState.fixIdx (s : QueryState) (col : ℕ) (rot : ℤ) : ℕ × QueryState :=
  match findQuery s.fixed col rot with
  | some i => (i, s)
  | none => (s.fixed.size, { s with fixed := s.fixed.push (col, rot) })

def QueryState.instIdx (s : QueryState) (col : ℕ) (rot : ℤ) : ℕ × QueryState :=
  match findQuery s.inst col rot with
  | some i => (i, s)
  | none => (s.inst.size, { s with inst := s.inst.push (col, rot) })

/-- Erase one `Expression Fp Query` into an `Expr Fp`, threading the query-walk state.
Traversal order (left operand before right, atom on encounter) is what determines the
query indices, so it must match the order the Rust gate closure *builds* its expression.
The Rust `std::ops` build left-to-right (`a - b` builds `a`, then `b`, then combines), so a
plain left-to-right structural traversal reproduces it. -/
def eraseExpr : Expression Fp Query → QueryState → Expr Fp × QueryState
  | .const c, s => (.constant c, s)
  -- unreachable post-substitution (see the module docstring); junk value keeps the walk total
  | .var (.selector _), s => (.constant 0, s)
  | .var (.advice col rot), s =>
      let (i, s) := s.advIdx col.index rot
      (.advice i, s)
  | .var (.fixed col rot), s =>
      let (i, s) := s.fixIdx col.index rot
      (.fixed i, s)
  | .var (.instance col rot), s =>
      let (i, s) := s.instIdx col.index rot
      (.instance i, s)
  -- Neg/Sub lower to `mul (const (-1)) e`; recognise it as `.negated`. A left constant
  -- otherwise is a genuine `Expression::Constant * e` product (const-on-left is how the
  -- ports spell Rust `Constant(c) * e`).
  | .mul (.const c) e, s =>
      if c = (-1 : Fp) then
        let (e', s) := eraseExpr e s
        (.negated e', s)
      else
        let (e', s) := eraseExpr e s
        (.product (.constant c) e', s)
  -- A RIGHT constant is Rust's `Expression * F` (`impl Mul<F>`), which builds
  -- `Expression::Scaled(e, c)` — NOT a `Product` with a `Constant` node. The Halo2-Clean
  -- `HMul (Expression F L) F` instance (`Expression.lean:266`) spells exactly this as
  -- `mul e (const c)`, and the erasure target is `.scaled` (`Expression.lean:104-109`).
  -- Ports must therefore write field scalings as `e * (c : Fp)` (constant on the right),
  -- matching Rust's `e * F`; a genuine constant product is `(c : Fp) * e` (constant left).
  -- The `mulConstant` marker (`Expression.lean`): Rust's right-constant `Product`
  -- (`e * Expression::Constant(c)`), spelled `e * (const c * const 1)` in ports.
  | .mul e (.mul (.const c) (.const one)), s =>
      if one = (1 : Fp) then
        let (e', s) := eraseExpr e s
        (.product e' (.constant c), s)
      else
        let (e', s) := eraseExpr e s
        let (i', s) := eraseExpr (.mul (.const c) (.const one)) s
        (.product e' i', s)
  | .mul e (.const c), s =>
      let (e', s) := eraseExpr e s
      (.scaled e' c, s)
  | .add a b, s =>
      let (a', s) := eraseExpr a s
      let (b', s) := eraseExpr b s
      (.sum a' b', s)
  | .mul a b, s =>
      let (a', s) := eraseExpr a s
      let (b', s) := eraseExpr b s
      (.product a' b', s)

/-- Erase a list of gate polynomials in order, threading the query walk. -/
def eraseGates : List (Expression Fp Query) → QueryState → List (Expr Fp) × QueryState
  | [], s => ([], s)
  | p :: ps, s =>
      let (e, s) := eraseExpr p s
      let (es, s) := eraseGates ps s
      (e :: es, s)

/-- Flatten a `ConstraintSystem`'s gates to the ordered list of all constraint polynomials
(mirrors halo2 `PinnedGates`' `flat_map(polynomials)`). -/
def flatGates (cs : ConstraintSystem Fp) : List (Expression Fp Query) :=
  cs.gates.flatMap (fun g => g.constraints.map (·.poly))

/-- Erase a whole `LookupArgument` (its input and table expression lists), threading the
query walk. Mirrors `eraseGates` but returns a `LookupFixture`. -/
def eraseLookup (arg : LookupArgument Fp) (s : QueryState) :
    LookupFixture × QueryState :=
  let (inputs, s) := eraseGates arg.inputs s
  let (tables, s) := eraseGates arg.tables s
  ({ inputs, tables }, s)

/-- Erase a list of lookups in registration order, threading the walk. -/
def eraseLookups : List (LookupArgument Fp) → QueryState → List LookupFixture × QueryState
  | [], s => ([], s)
  | a :: as, s =>
      let (l, s) := eraseLookup a s
      let (ls, s) := eraseLookups as s
      (l :: ls, s)

/-! ### The query-registration seed (halo2 `queried_cells`)

**Load-bearing subtlety** (design doc D6): halo2 assigns query indices in the order
`query_advice`/`query_fixed`/`query_instance` are *called* inside each gate/lookup closure —
i.e. the order the queries are *declared*, not the order they appear in the finished
polynomial AST. A gate authored as "declare all queries via `let`, then build polys" (the
standard idiom, and how the ports read) registers in `let` order; but the first poly's AST
may reference those queries in a different order. So a naive first-encounter walk over the
finished polynomials produces the wrong layout *and* the wrong in-gate indices.

We reproduce halo2 faithfully by pre-seeding the walk with each gate's queried cells in
declaration order (halo2's `Gate::queried_cells`, `circuit.rs`). This seed is per-gadget
data supplied by the caller (the fixture test), exactly mirroring what the Rust closure
records. Once seeded, the erasure DFS finds every query already registered and reuses its
index, matching halo2 for both the layout and the gate expressions. Queries not in the seed
(should be none for a faithful seed) are appended in first-encounter order as a fallback. -/

/-- Pre-register a declaration-order list of query atoms into the walk state. -/
def seedQueries : List Query → QueryState → QueryState
  | [], s => s
  | .selector _ :: qs, s => seedQueries qs s
  | .advice col rot :: qs, s => seedQueries qs (s.advIdx col.index rot).2
  | .fixed col rot :: qs, s => seedQueries qs (s.fixIdx col.index rot).2
  | .instance col rot :: qs, s => seedQueries qs (s.instIdx col.index rot).2

/-! ## The projection (selector-compression-map driven)

`compress_selectors` (`circuit.rs:1232-1338`, `compress_selectors.rs`) is a **whole-circuit,
layout-dependent** step (design doc §2.4): which selectors pack into a shared fixed column
is decided by the *exclusion matrix* over the full per-selector activation table (two
selectors may share a column iff never co-enabled on a row, subject to the degree budget),
and each selector's replacement is the root-finding polynomial `q·∏_{i≠root}(i − q)` over
its packed column's fixed query.

**Trust boundary** (task §Lean-side 9): the map's derivation stays RUST-side. The dumper's
harness circuit (`MulDumpCircuit`, `ecc/chip/dump.rs`) runs a REAL mul synthesize through
the floor planner with `Value::unknown()` witnesses — exactly keygen's view (keygen ignores
advice values; the lookup TABLE contents affect only fixed commitments, never the compressed
CS structure, so the table is not loaded) — gathering the TRUE activation table, and
`dump_prepost_acts` runs the real `compress_selectors` on it, emitting `MulSelMap.lean`
(per selector: packed column, combination length, assigned root). Lean applies the map
MECHANICALLY (`substSelectorMap` below) and the resulting CS is checked EQUAL to the dumped
post-compression fixture — any error in the reconstruction conventions (root order, factor
shape, query registration) surfaces as a gate mismatch in that equality. -/

/-- Look up a selector's compression datum by index (`entries` is an association list
keyed by selector index). -/
def SelCompressMap.lookup (map : SelCompressMap) (s : ℕ) : Option SelCompress :=
  (map.entries.find? (fun e => e.1 = s)).map (·.2)

/-- Build the root-finding replacement polynomial `q·∏_{i≠root}((i : Fp) − q)` for a selector,
`q` being the packed column's fixed query (`compress_selectors.rs:184-208`; left-assoc fold,
matching Rust's `expression = expression * (Constant(root) − query)` accumulation). For
`combinationLen = 1` this is the bare `q` (empty product) — the single-selector and
degree-0 (complex/lookup-only selector) cases. -/
def selReplacement (d : SelCompress) : Expression Fp Query :=
  let q : Expression Fp Query := var (.fixed ⟨d.packedCol⟩ 0)
  let factors := (List.range d.combinationLen).filterMap (fun j =>
    let i := j + 1
    if i = d.assignedRoot then none
    else some (((i : Fp) : Expression Fp Query) - q))
  factors.foldl (· * ·) q

/-- Substitute each `Query.selector k` by its root-finding replacement from the map `m`
(`k ↦ SelCompress`). Selectors not in the map are left as-is (should not happen for a
complete map). Rust substitutes in gates AND lookups (`circuit.rs:1321-1335` — lookup
expressions carry the complex selectors). -/
def substSelectorMap (m : ℕ → Option SelCompress) :
    Expression Fp Query → Expression Fp Query
  | .var (.selector s) => match m s.index with
      | some d => selReplacement d
      | none => .var (.selector s)
  | .var q => .var q
  | .const c => .const c
  | .add a b => .add (substSelectorMap m a) (substSelectorMap m b)
  | .mul a b => .mul (substSelectorMap m a) (substSelectorMap m b)

/-- Project the CS with a Rust-dumped selector-compression map: substitute every selector
(in gates and lookups) by its root-finding replacement, grow `numFixedColumns` by the new
packed columns, and run the seeded query walk.

Halo2's query order after compression: the packed columns' fixed queries are registered at
column-ALLOCATION time inside `compress_selectors` (`circuit.rs:1267-1274`, via
`query_fixed_index` in the allocate closure), i.e. all new fixed queries append to the
existing fixed layout in packing order, BEFORE the substituted gates are walked. The
`seed` (built from the dumped fixture's layouts) reproduces this. `numSelectors` is NOT
reset by compression (halo2 keeps the count; the pinned VK doesn't carry it — design doc
§2.3). -/
def projectCS (seed : List Query) (map : SelCompressMap)
    (cs : ConstraintSystem Fp) : CsFixture :=
  let m : ℕ → Option SelCompress := map.lookup
  let polys := (flatGates cs).map (substSelectorMap m)
  let lookups' : List (LookupArgument Fp) := cs.lookups.map (fun a =>
    { inputs := a.inputs.map (substSelectorMap m)
      tables := a.tables.map (substSelectorMap m) })
  -- plain projections (not `let (a, b) := …` matches), so record-field access reduces
  -- structurally without evaluating the walk — `Bridge.VkProjection` relies on this
  let gs := eraseGates polys (seedQueries seed {})
  let lks := eraseLookups lookups' gs.2
  { numAdviceColumns := cs.numAdviceColumns
    numFixedColumns := cs.numFixedColumns + map.newFixedCols
    numInstanceColumns := cs.numInstanceColumns
    numSelectors := cs.numSelectors
    adviceQueryLayout := lks.2.advice.toList
    fixedQueryLayout := lks.2.fixed.toList
    instanceQueryLayout := lks.2.inst.toList
    gates := gs.1
    lookups := lks.1 }

end Zcash.Circuits.Fixtures
