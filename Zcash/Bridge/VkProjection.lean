import Clean.Halo2.Keygen
import Zcash.Circuits.Integration.ExprRich
import Zcash.Circuits.Specs.SinsemillaGenerators
import Zcash.Circuits.Action.Circuit
import Zcash.Circuits.Action.RealBases
import Zcash.Snark.Core.Field
import Zcash.Snark.Verifier.Assemble

/-!
# The verifying key's pinned constraint system, on the verifier side

Crosses the Clean-core pinned constraint system (`Clean.Halo2.Keygen`,
`Halo2.PinnedConstraintSystem`) to the verifier's `VerifyingKey` record. The pinned
record carries more than the verifier's runtime `VerifyingKey` (counts, constants), so
the record-level capture equality lives fixture side
(`Zcash.Snark.Fixtures.SingleAction.PinnedCsMatch`), and the verifying key connects
field-wise: `VerifyingKey.gates_eval_of_gates_eq` carries the derived-gate semantics
(`derive_gates_eval`) to any verifying key whose gate list is the derivation mapped
through `RichExpression.toExpr` — exactly the direction in which key generation builds
the key. `actionCS` is the Action instance of the source constraint system.

This module also hosts the DERIVED keygen data of the pinned-CS derivation: the
closed Action circuit's operation stream (`actionOperations`) and the
selector-compression map computed from it end to end (`actionSelMapDerived`) — synthesize
mirror → region shapes → V1 floor-planner placement → selector activations →
`compress_selectors`. Everything here is pure term-level data (no fixture reads); the
Rust-dumped `actionSelMap` survives only as a cross-check in `TestSelMapDerivation`.
-/

namespace Zcash.Snark

open Halo2

/-- **A verifying key whose gate list is a derivation's evaluates like the source
circuit.** The verifier holds `Zcash.Snark.Expr` gates while the derivation produces
`Halo2.RichExpression` gates, so the hypothesis follows keygen's construction direction:
`vk.gates = (.derive cs map).gates.map RichExpression.toExpr`. Given that and selector
coverage, the `j`-th VK gate — at query families interpreting the derivation walk's
layout — evaluates to the `j`-th flattened Clean gate expression under the
selector-replacement valuation. -/
theorem VerifyingKey.gates_eval_of_gates_eq
    {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G)
    (cs : ConstraintSystem Fp) (map : SelCompressMap)
    (hgates : vk.gates =
      (PinnedConstraintSystem.derive cs map).gates.map
        RichExpression.toExpr)
    (fE aE iE : ℕ → Fp) (v : Query → Fp)
    (hcov : ∀ p ∈ flatGates cs,
      p.selectorsCovered (fun i => (map.lookup i).isSome) = true)
    (hint : Interprets
      (eraseGates ((flatGates cs).map (substSelectorMap map.lookup))
        (queryWalkInit map cs)).2 fE aE iE v)
    (j : ℕ) (hg : j < vk.gates.length) (hp : j < (flatGates cs).length) :
    Expr.eval fE aE iE vk.gates[j]
      = Expression.eval (substValuation map.lookup v) (flatGates cs)[j] := by
  have hg' : j < (PinnedConstraintSystem.derive cs map).gates.length := by
    rw [hgates, List.length_map] at hg
    exact hg
  have key := PinnedConstraintSystem.derive_gates_eval cs map fE aE iE v hcov hint j hg' hp
  rw [List.getElem_of_eq hgates hg, List.getElem_map,
    RichExpression.eval_toExpr]
  exact key

end Zcash.Snark

namespace Zcash.Bridge

open Halo2
open Circuits.Specs.Sinsemilla (orchardGenerators)
open Snark (Fp)

open Circuits.Action.Circuit in
/-- The ported Action circuit's constraint system (`configure` is version-independent:
post-NU 6.2 and 6.3 share it). -/
def actionCS : ConstraintSystem Fp :=
  (configure orchardGenerators {}).2

open Circuits.Action.Circuit in
/-- The Action circuit's config — the `.1` of the same `configure` run as `actionCS`. -/
def actionConfig : Config :=
  (configure orchardGenerators {}).1

open Circuits.Action (orchardActionCircuit) in
/-- The closed ironwood Action circuit's operation stream at the real certified bases.
Key generation does not evaluate witness programs, so the fixed hint-backed programs
affect assigned expressions but not the circuit's layout. This is the object the layout
tests mirror as
`TestVkLayoutAction.aProgram` (its placements, copies, σ and fixed contents are pinned
against the Rust dump there and in `TestFloorPlanner`). -/
def actionOperations : Operations Fp :=
  (orchardActionCircuit.synthesize actionConfig ()).operations

/-- The selector-compression map, DERIVED end to end from the ported circuit: V1
floor-planner placements (`FloorPlanner.V1.starts`, the legacy-pdqsort port) → selector
activations (`Layout.activations`) → the `compress_selectors` port
(`deriveSelCompressMap`). `n` is the evaluation-domain size (`2^k`; the Action circuit
has `k = 11`) — a parameter of the activation table, not a fixture artifact.
Cross-checked EQUAL to the Rust-dumped `actionSelMap` in `TestSelMapDerivation`; used as
the derivation witness of `actionPinnedCs` (`PinnedCsMatch`). -/
def actionSelMapDerived (n : ℕ) : SelCompressMap :=
  deriveSelCompressMap actionCS n
    (activations (FloorPlanner.V1.starts actionOperations)
      (indexedRegions actionOperations 0).1)

/-! ## The domain exponent `k`, derived

Rust does not compute `k` — orchard pins `const K: u32 = 11` (`circuit.rs:76`) and
keygen *asserts* the circuit fits (`Halo2.minimalK`, the minimal `k` for which every
assignment row lies in `usable_rows = 0..n − (blinding_factors + 1)` and
`n ≥ cs.minimum_rows()`, `keygen.rs`). It equals the pinned constant today (Action:
regions end at row 1779, tables are 1024 rows, blinding 5 → `2^10` fails, `2^11` fits)
and moves exactly when Rust's assert would force the constant to move. -/

/-- The Action circuit's derived domain exponent (= orchard's `K = 11`; the equality is
`#guard`ed in `TestSelMapDerivation`). -/
def actionK : ℕ := minimalK actionCS actionOperations

/-! ## The permutation argument's verifier view -/

/-- The permutation columns chunked for the verifier (`permutation/verifier.rs:43-47`:
`columns.chunks(chunk_len)` with global position indices), in the `ColumnRef`
QUERY-INDEX space the verifier resolves evals with (`ColumnRef.resolve`): each column's
cur-rotation query index in the post-compression layouts. -/
def permutationChunksOf (map : SelCompressMap) (cs : ConstraintSystem Fp) :
    List (List (Snark.ColumnRef × ℕ)) :=
  let proj := projectCS map cs
  let ref : AnyColumn → Snark.ColumnRef := fun c =>
    match c.kind with
    | .advice => .advice (proj.adviceQueryLayout.findIdx (· = (c.index, 0)))
    | .fixed => .fixed (proj.fixedQueryLayout.findIdx (· = (c.index, 0)))
    | .instance => .instance (proj.instanceQueryLayout.findIdx (· = (c.index, 0)))
  ((cs.permutationColumns.map ref).zipIdx).toChunks cs.chunkLen

end Zcash.Bridge
