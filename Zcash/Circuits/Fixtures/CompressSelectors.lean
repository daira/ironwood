import Zcash.Circuits.Fixtures.Project

/-!
# `compress_selectors`, ported: deriving the selector-compression map

Derives the `SelCompressMap` from the circuit instead of trusting the Rust dump — the
first half of computing the keygen witnesses circuit-side. The port transcribes halo2's
whole pipeline (`circuit.rs` `compress_selectors` + `compress_selectors.rs` `process`),
whose *exact* greedy order matters: a valid-but-different packing produces different
gate polynomials and fails the capture equality.

* per-selector degrees — the maximal `Expression.degree` of a gate polynomial whose
  simple selector is this one (`selectorMaxDegrees`; complex and gate-less selectors
  stay at `0`);
* the degree budget — `ConstraintSystem::degree()` (`csDegree`): the permutation
  argument's constant `3`, the lookups' `max 4 (2 + input + table)`, the gate degrees
  (Clean's constraint system has no `minimum_degree`, matching Orchard, which never
  sets one);
* the packing (`process`): degree-`0` selectors get their own columns first, in index
  order; the rest combine greedily in index order — a candidate joins if it conflicts
  with no member (never co-enabled on a row) and the combination stays within budget,
  with halo2's short-circuit once the budget is exactly filled.

The activation input is `Layout.activations` over the synthesized operations at their
placement — the placement itself is still layout-fixture data (the floor-planner port
is the second half of this phase). `Zcash.Circuits.Tests.TestSelMapDerivation` checks
the derived map equal to the Rust-dumped `actionSelMap`.
-/

namespace Halo2.Expression

/-- halo2 `Expression::degree`: queries and selectors are degree `1`, constants `0`,
sums take the max, products add. -/
def degree {F L : Type} : Expression F L → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add a b => max a.degree b.degree
  | .mul a b => a.degree + b.degree

/-- halo2 `Expression::extract_simple_selector`, first-found: the simple selector
occurring in the expression, if any (the constraint system enforces at most one). -/
def simpleSelector? {F : Type} : Expression F Query → Option Selector
  | .var (.selector s) => if s.simple then some s else none
  | .var _ => none
  | .const _ => none
  | .add a b => a.simpleSelector? <|> b.simpleSelector?
  | .mul a b => a.simpleSelector? <|> b.simpleSelector?

end Halo2.Expression

namespace Halo2

/-- halo2 `lookup::Argument::required_degree`: `max 4 (2 + input + table)` over the
argument's expression degrees (each at least `1`). -/
def LookupArgument.requiredDegree {F : Type} (l : LookupArgument F) : ℕ :=
  let inputDeg := l.inputs.foldl (fun m e => max m e.degree) 1
  let tableDeg := l.tables.foldl (fun m e => max m e.degree) 1
  max 4 (2 + inputDeg + tableDeg)

end Halo2

namespace Zcash.Circuits.Fixtures

open Halo2

/-- halo2 `compress_selectors::SelectorDescription`: a selector index, its activation
rows, and the maximal degree of a gate involving it. -/
structure SelectorDescription where
  selector : ℕ
  activations : Array Bool
  maxDegree : ℕ

/-- Two selectors conflict if they are enabled on a common row. -/
def SelectorDescription.conflicts (a b : SelectorDescription) : Bool :=
  (a.activations.toList.zip b.activations.toList).any fun (x, y) => x && y

/-- One pass of halo2's inner combination loop: scan the candidates in order, adding
each that conflicts with no member and keeps `max-degree-so-far + len + 1` within the
budget; stop scanning entirely once `d + len` fills the budget (halo2's
short-circuit). Returns the finished combination and the not-added candidates in their
original order. -/
def extendCombination (maxDegree : ℕ) :
    ℕ → List SelectorDescription → List SelectorDescription →
    List SelectorDescription × List SelectorDescription
  | _, comb, [] => (comb, [])
  | d, comb, s :: rest =>
      if d + comb.length = maxDegree then
        (comb, s :: rest)
      else if comb.any (·.conflicts s) then
        let (comb', rem) := extendCombination maxDegree d comb rest
        (comb', s :: rem)
      else
        let nd := max d (s.maxDegree - 1)
        if nd + comb.length + 1 > maxDegree then
          let (comb', rem) := extendCombination maxDegree d comb rest
          (comb', s :: rem)
        else
          extendCombination maxDegree nd (comb ++ [s]) rest

/-- Form combinations by seeding each with the first unassigned selector and extending
greedily (`fuel` bounds the recursion by the selector count; each round consumes at
least the seed). -/
def buildCombinations (maxDegree : ℕ) :
    ℕ → List SelectorDescription → List (List SelectorDescription)
  | 0, _ => []
  | _, [] => []
  | fuel + 1, s :: rest =>
      let (comb, rem) := extendCombination maxDegree (s.maxDegree - 1) [s] rest
      comb :: buildCombinations maxDegree fuel rem

/-- halo2 `compress_selectors::process`, packing only: degree-`0` selectors take their
own columns first (index order, bare-query replacement `len = 1, root = 1`), then the
greedy combinations. Packed-column indices are relative to the first newly allocated
column; entries are in halo2's assignment order. -/
def process (selectors : List SelectorDescription) (maxDegree : ℕ) : SelCompressMap :=
  let deg0 := selectors.filter (·.maxDegree = 0)
  let rest := selectors.filter (·.maxDegree ≠ 0)
  let deg0Entries := deg0.zipIdx.map fun (s, k) =>
    (s.selector, SelCompress.mk k 1 1)
  let combs := buildCombinations maxDegree rest.length rest
  let combEntries := combs.zipIdx.flatMap fun (comb, k) =>
    comb.zipIdx.map fun (s, p) =>
      (s.selector, SelCompress.mk (deg0.length + k) comb.length (p + 1))
  { newFixedCols := deg0.length + combs.length
    entries := deg0Entries ++ combEntries }

/-- Per-selector maximal gate degree (`circuit.rs` `compress_selectors`, the `degrees`
loop): over every gate polynomial, the simple selector it contains — if any — records
the polynomial's degree. -/
def selectorMaxDegrees (cs : ConstraintSystem Fp) : Array ℕ :=
  (flatGates cs).foldl (init := (List.replicate cs.numSelectors 0).toArray)
    fun degs p =>
      match p.simpleSelector? with
      | some s => degs.modify s.index (max · p.degree)
      | none => degs

/-- halo2 `ConstraintSystem::degree`: the max of the permutation argument's constant
`3`, the lookups' required degrees, and the gate degrees (no `minimum_degree` — Clean's
constraint system does not model it and Orchard never sets one). -/
def csDegree (cs : ConstraintSystem Fp) : ℕ :=
  let lookupDeg := cs.lookups.foldl (fun m l => max m l.requiredDegree) 1
  let gateDeg := (flatGates cs).foldl (fun m p => max m p.degree) 0
  max 3 (max lookupDeg gateDeg)

/-- The per-selector activation table from `Layout.activations`' `(selector, absRow)`
pairs, as `numSelectors` rows of `n` booleans. -/
def activationTable (n numSelectors : ℕ) (acts : List (ℕ × ℕ)) : Array (Array Bool) :=
  acts.foldl (init := (List.replicate numSelectors
      ((List.replicate n false).toArray)).toArray)
    fun tbl (sel, row) => tbl.modify sel (·.set! row true)

/-- **Derive the selector-compression map from the circuit**: the constraint system
supplies the degrees and budget, the synthesized activations supply the packing
constraints, and the packed columns append after the existing fixed columns. -/
def deriveSelCompressMap (cs : ConstraintSystem Fp) (n : ℕ) (acts : List (ℕ × ℕ)) :
    SelCompressMap :=
  let tbl := activationTable n cs.numSelectors acts
  let degs := selectorMaxDegrees cs
  let descs := (List.range cs.numSelectors).map fun i =>
    SelectorDescription.mk i tbl[i]! degs[i]!
  let m := process descs (csDegree cs)
  { newFixedCols := m.newFixedCols
    entries := m.entries.map fun (s, sc) =>
      (s, { sc with packedCol := sc.packedCol + cs.numFixedColumns }) }

end Zcash.Circuits.Fixtures
