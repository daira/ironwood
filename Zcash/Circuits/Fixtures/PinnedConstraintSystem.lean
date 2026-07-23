import Zcash.Circuits.Fixtures.ProjectSemantics

/-!
# `PartialPinnedConstraintSystem` — the pinned constraint system, derived from a circuit

halo2's `PinnedConstraintSystem` is the canonical view of the constraint system a
verifying key pins (and hashes into `transcript_repr`): counts, flattened gate
polynomials, query lists, permutation columns, lookups, constants.
`PartialPinnedConstraintSystem` is the sub-record the current capture certifies — the
gate polynomials, the three query layouts, and the lookup argument expressions;
*partial* because the counts (pending a dumper emission) and the permutation columns
and constants (landing with the commitment-matching phase) are not yet compared.
`PartialPinnedConstraintSystem.derive` computes it from a Clean `ConstraintSystem`,
given the two keygen witnesses the Lean side does not yet compute itself:

* `seed` — the query-registration order (halo2 registers queries during `configure`;
  Clean's constraint system does not record declaration order — computing this needs
  the planned `Configure` query-registration refactor);
* `map` — the `compress_selectors` packing (layout-dependent: derives from the
  activation table over the synthesized operations — computing it needs the planned
  floor-planner and `compress_selectors` ports).

Once both are computed, `derive` becomes a function of the `FormalCircuit` alone.
Until then they are explicit inputs, and their correctness is enforced by the
capture-equality theorems (`Zcash.Snark.Fixtures.SingleAction.PinnedCsMatch`): a wrong seed
or packing produces different gates or layouts and fails the comparison.

The evaluation lemmas (`derive_gates_eval`) carry the projection semantics
(`ProjectSemantics`) to the derived record: each derived gate evaluates to its source
Clean gate expression under the selector-replacement valuation.
-/

namespace Zcash.Circuits.Fixtures

open Halo2
open Snark (Expr)

/-- The compared sub-record of halo2's `PinnedConstraintSystem`: gate polynomials,
query layouts, and lookup argument expressions (see the module docstring for the
pending fields). -/
structure PartialPinnedConstraintSystem where
  gates : List (Expr Fp)
  adviceQueryLayout : List (ℕ × ℤ)
  fixedQueryLayout : List (ℕ × ℤ)
  instanceQueryLayout : List (ℕ × ℤ)
  lookupInputExprs : List (List (Expr Fp))
  lookupTableExprs : List (List (Expr Fp))
deriving DecidableEq, Repr

/-- A query-registration seed from per-kind layouts (advice, fixed, instance — the
kinds live in independent index spaces). -/
def csSeed (adviceL fixedL instL : List (ℕ × ℤ)) : List Query :=
  adviceL.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ fixedL.map (fun (c, r) => Query.fixed ⟨c⟩ r)
    ++ instL.map (fun (c, r) => Query.instance ⟨c⟩ r)

/-- Derive the pinned CS data from a Clean constraint system and the two keygen
witnesses (see the module docstring for their status). -/
def PartialPinnedConstraintSystem.derive (cs : ConstraintSystem Fp) (seed : List Query)
    (map : SelCompressMap) : PartialPinnedConstraintSystem where
  gates := (projectCS seed map cs).gates
  adviceQueryLayout := (projectCS seed map cs).adviceQueryLayout
  fixedQueryLayout := (projectCS seed map cs).fixedQueryLayout
  instanceQueryLayout := (projectCS seed map cs).instanceQueryLayout
  lookupInputExprs := (projectCS seed map cs).lookups.map (·.inputs)
  lookupTableExprs := (projectCS seed map cs).lookups.map (·.tables)

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
seeded walk state. -/
theorem PartialPinnedConstraintSystem.derive_gates (cs : ConstraintSystem Fp) (seed : List Query)
    (map : SelCompressMap) :
    (PartialPinnedConstraintSystem.derive cs seed map).gates
      = (eraseGates ((flatGates cs).map (substSelectorMap map.lookup))
          (seedQueries seed {})).1 := by
  simp only [PartialPinnedConstraintSystem.derive, projectCS]

/-- The derived record has one gate polynomial per flattened source gate. -/
theorem PartialPinnedConstraintSystem.derive_gates_length (cs : ConstraintSystem Fp) (seed : List Query)
    (map : SelCompressMap) :
    (PartialPinnedConstraintSystem.derive cs seed map).gates.length = (flatGates cs).length := by
  rw [PartialPinnedConstraintSystem.derive_gates, eraseGates_length, List.length_map]

/-- **Each derived gate evaluates to its source gate.** Given selector coverage, the
`j`-th derived gate — at query families interpreting the walk's layout — evaluates to
the `j`-th flattened Clean gate expression under the selector-replacement valuation.
The gate-side link between a verifying key matching the derivation and the Clean
constraint semantics. -/
theorem PartialPinnedConstraintSystem.derive_gates_eval (cs : ConstraintSystem Fp) (seed : List Query)
    (map : SelCompressMap) (fE aE iE : ℕ → Fp) (v : Query → Fp)
    (hcov : ∀ p ∈ flatGates cs,
      p.selectorsCovered (fun i => (map.lookup i).isSome) = true)
    (hint : Interprets
      (eraseGates ((flatGates cs).map (substSelectorMap map.lookup))
        (seedQueries seed {})).2 fE aE iE v)
    (j : ℕ) (hg : j < (PartialPinnedConstraintSystem.derive cs seed map).gates.length)
    (hp : j < (flatGates cs).length) :
    Expr.eval fE aE iE (PartialPinnedConstraintSystem.derive cs seed map).gates[j]
      = Expression.eval (substValuation map.lookup v) (flatGates cs)[j] := by
  have hfree : ∀ p ∈ (flatGates cs).map (substSelectorMap map.lookup),
      p.selectorFree = true := by
    intro p hp'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
    exact (substSelectorMap_selectorFree _ q).trans (hcov q hq)
  rw [List.getElem_of_eq (PartialPinnedConstraintSystem.derive_gates cs seed map) hg]
  have h := eraseGates_eval fE aE iE v
    ((flatGates cs).map (substSelectorMap map.lookup)) (seedQueries seed {}) _ hfree
    (QueryState.Extends.refl _) hint j
    ((PartialPinnedConstraintSystem.derive_gates cs seed map) ▸ hg) (by simpa using hp)
  rw [List.getElem_map, substSelectorMap_eval] at h
  exact h

end Zcash.Circuits.Fixtures
