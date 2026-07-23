import Zcash.Circuits.Fixtures.ProjectSemantics
import Zcash.Circuits.Fixtures.CompressSelectors

/-!
# `PinnedConstraintSystem` — the pinned constraint system, derived from a circuit

halo2's `PinnedConstraintSystem` is the canonical view of the constraint system a
verifying key pins (and hashes into `transcript_repr`): counts, flattened gate
polynomials, query lists, permutation columns, lookups, constants. The Lean record
mirrors every field of the Rust pinned record (`circuit.rs:966-979`).
`PinnedConstraintSystem.derive` computes it from a Clean `ConstraintSystem` and
the `compress_selectors` packing `map` (derived circuit-side, `Bridge/VkProjection.lean`).
The query-registration order needs no input: Clean's configure-time query registration
records it in `cs.{advice,fixed,instance}Queries` (each `Gate` carries its closure's
query atoms in call order; the `Configure` actions register them exactly as Rust's
`query_*_index` does), and the packed columns' fixed queries are appended by the
projection (`queryWalkInit`). `derive` is thus a function of the circuit and the domain
size alone; the recorded orders are certified by the capture-equality theorems
(`Zcash.Snark.Fixtures.SingleAction.PinnedCsMatch`): a wrong `queriedCells` list or
packing produces different layouts or gates and fails the comparison.

The evaluation lemmas (`derive_gates_eval`) carry the projection semantics
(`ProjectSemantics`) to the derived record: each derived gate evaluates to its source
Clean gate expression under the selector-replacement valuation.
-/

namespace Zcash.Circuits.Fixtures

open Halo2
open Snark (Expr)

/-! ## Constraint-system derived scalars

halo2 quantities that are pure functions of the `ConstraintSystem` — computable since
the configure-time query registration records `adviceQueries`. -/

/-- halo2 `ConstraintSystem::blinding_factors` (`circuit.rs:1652-1675`):
`max(3, max per-column advice-query count) + 1 + 1`. The per-column counts are Rust's
`num_advice_queries`, recovered by counting the recorded `adviceQueries`. -/
def _root_.Halo2.ConstraintSystem.blindingFactors (cs : ConstraintSystem Fp) : ℕ :=
  let factors := (List.range cs.numAdviceColumns).foldl
    (fun m c => max m (cs.adviceQueries.countP (fun q => q.1.index = c))) 1
  max 3 factors + 1 + 1

/-- halo2 `ConstraintSystem::minimum_rows` (`circuit.rs:1678-1689`):
blinding factors + l_last + l_0 breathing room + one row. -/
def _root_.Halo2.ConstraintSystem.minimumRows (cs : ConstraintSystem Fp) : ℕ :=
  cs.blindingFactors + 3

/-- The permutation argument's chunk length, `cs.degree() - 2`
(`permutation/verifier.rs:43`). -/
def _root_.Halo2.ConstraintSystem.chunkLen (cs : ConstraintSystem Fp) : ℕ :=
  csDegree cs - 2

/-- The Lean mirror of halo2's `PinnedConstraintSystem` (`circuit.rs:966-979`): column
counts, gate polynomials, query layouts, the permutation argument's columns, lookup
argument expressions, constants columns, and the minimum-degree override — every field
of the Rust pinned record. -/
structure PinnedConstraintSystem where
  numFixedColumns : ℕ
  numAdviceColumns : ℕ
  numInstanceColumns : ℕ
  numSelectors : ℕ
  gates : List (Expr Fp)
  adviceQueryLayout : List (ℕ × ℤ)
  fixedQueryLayout : List (ℕ × ℤ)
  instanceQueryLayout : List (ℕ × ℤ)
  /-- The permutation argument's columns (`permutation::Argument`), in `enable_equality`
  call order — recorded in `cs.permutationColumns`. -/
  permutationColumns : List AnyColumn
  lookupInputExprs : List (List (Expr Fp))
  lookupTableExprs : List (List (Expr Fp))
  constants : List ℕ
  minimumDegree : Option ℕ
deriving DecidableEq, Repr

/-- Derive the pinned CS data from a Clean constraint system and the (circuit-derived)
selector-compression map; the query layouts come from the CS's configure-recorded
queries (see the module docstring). -/
def PinnedConstraintSystem.derive (cs : ConstraintSystem Fp)
    (map : SelCompressMap) : PinnedConstraintSystem :=
  -- single let: the projection (selector substitution + query walk) runs once per
  -- `derive` evaluation, not once per field
  let proj := projectCS map cs
  { numFixedColumns := proj.numFixedColumns
    numAdviceColumns := proj.numAdviceColumns
    numInstanceColumns := proj.numInstanceColumns
    numSelectors := proj.numSelectors
    gates := proj.gates
    adviceQueryLayout := proj.adviceQueryLayout
    fixedQueryLayout := proj.fixedQueryLayout
    instanceQueryLayout := proj.instanceQueryLayout
    permutationColumns := cs.permutationColumns
    lookupInputExprs := proj.lookups.map (·.inputs)
    lookupTableExprs := proj.lookups.map (·.tables)
    -- Clean's constraint system does not model `set_minimum_degree`; Orchard never calls it.
    constants := cs.constants.map (·.index)
    minimumDegree := none }

/-! ## Threading the erasure lemmas through the gate list -/

/-- The gate-list walk only appends: `eraseGates`' output state extends its input. -/
theorem eraseGates_extends (ps : List (Expression Fp Query)) (s : QueryState) :
    ((eraseGates ps s).2).Extends s := by
  induction ps generalizing s with
  | nil => exact QueryState.Extends.refl s
  | cons p ps ih =>
      simp only [eraseGates]
      exact QueryState.Extends.trans (eraseExpr_extends p s) (ih (eraseExpr p s).2)

/-- The walk erases gate lists length-preservingly. -/
theorem eraseGates_length (ps : List (Expression Fp Query)) (s : QueryState) :
    (eraseGates ps s).1.length = ps.length := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => simp only [eraseGates, List.length_cons, ih]

/-- **Erasure preserves evaluation, gate-list form.** Each erased gate evaluates to its
source expression, position by position, when the families interpret a state extending
the walk's output. -/
theorem eraseGates_eval (fE aE iE : ℕ → Fp) (v : Query → Fp)
    (ps : List (Expression Fp Query)) (s sfin : QueryState)
    (hfree : ∀ p ∈ ps, p.selectorFree = true)
    (hext : sfin.Extends (eraseGates ps s).2)
    (hint : Interprets sfin fE aE iE v) :
    ∀ (j : ℕ) (h1 : j < (eraseGates ps s).1.length) (h2 : j < ps.length),
      Expr.eval fE aE iE (eraseGates ps s).1[j] = Expression.eval v ps[j] := by
  induction ps generalizing s with
  | nil => exact fun j _ h2 => absurd h2 (Nat.not_lt_zero j)
  | cons p ps ih =>
      intro j h1 h2
      simp only [eraseGates] at hext h1 ⊢
      cases j with
      | zero =>
          simp only [List.getElem_cons_zero]
          exact eraseExpr_eval fE aE iE v p s sfin
            (hfree p (List.mem_cons_self ..))
            (QueryState.Extends.trans (eraseGates_extends ps (eraseExpr p s).2) hext) hint
      | succ j =>
          simp only [List.getElem_cons_succ]
          exact ih (eraseExpr p s).2
            (fun q hq => hfree q (List.mem_cons_of_mem p hq)) hext
            j (by simpa using h1) (by simpa using h2)

/-! ## Semantics of the derived record -/

/-- The derived gate list, unfolded: the erasure of the compressed flat gates from the
configure-recorded walk state. -/
theorem PinnedConstraintSystem.derive_gates (cs : ConstraintSystem Fp)
    (map : SelCompressMap) :
    (PinnedConstraintSystem.derive cs map).gates
      = (eraseGates ((flatGates cs).map (substSelectorMap map.lookup))
          (queryWalkInit map cs)).1 := by
  simp only [PinnedConstraintSystem.derive, projectCS]

/-- The derived record has one gate polynomial per flattened source gate. -/
theorem PinnedConstraintSystem.derive_gates_length (cs : ConstraintSystem Fp)
    (map : SelCompressMap) :
    (PinnedConstraintSystem.derive cs map).gates.length = (flatGates cs).length := by
  rw [PinnedConstraintSystem.derive_gates, eraseGates_length, List.length_map]

/-- **Each derived gate evaluates to its source gate.** Given selector coverage, the
`j`-th derived gate — at query families interpreting the walk's layout — evaluates to
the `j`-th flattened Clean gate expression under the selector-replacement valuation.
The gate-side link between a verifying key matching the derivation and the Clean
constraint semantics. -/
theorem PinnedConstraintSystem.derive_gates_eval (cs : ConstraintSystem Fp)
    (map : SelCompressMap) (fE aE iE : ℕ → Fp) (v : Query → Fp)
    (hcov : ∀ p ∈ flatGates cs,
      p.selectorsCovered (fun i => (map.lookup i).isSome) = true)
    (hint : Interprets
      (eraseGates ((flatGates cs).map (substSelectorMap map.lookup))
        (queryWalkInit map cs)).2 fE aE iE v)
    (j : ℕ) (hg : j < (PinnedConstraintSystem.derive cs map).gates.length)
    (hp : j < (flatGates cs).length) :
    Expr.eval fE aE iE (PinnedConstraintSystem.derive cs map).gates[j]
      = Expression.eval (substValuation map.lookup v) (flatGates cs)[j] := by
  have hfree : ∀ p ∈ (flatGates cs).map (substSelectorMap map.lookup),
      p.selectorFree = true := by
    intro p hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
    exact (substSelectorMap_selectorFree _ q).trans (hcov q hq)
  rw [List.getElem_of_eq (PinnedConstraintSystem.derive_gates cs map) hg]
  have h := eraseGates_eval fE aE iE v
    ((flatGates cs).map (substSelectorMap map.lookup)) (queryWalkInit map cs) _ hfree
    (QueryState.Extends.refl _) hint j
    ((PinnedConstraintSystem.derive_gates cs map) ▸ hg) (by simpa using hp)
  rw [List.getElem_map, substSelectorMap_eval] at h
  exact h

end Zcash.Circuits.Fixtures
