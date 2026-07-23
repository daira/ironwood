import Zcash.Circuits.Fixtures.PinnedConstraintSystem
import Zcash.Circuits.Fixtures.CompressSelectors
import Zcash.Circuits.Fixtures.FloorPlanner
import Zcash.Circuits.Specs.SinsemillaGenerators
import Zcash.Circuits.Action.Circuit
import Zcash.Circuits.Action.RealBases
import Zcash.Snark.Core.Field
import Zcash.Snark.Verifier.Assemble

/-!
# The verifying key's pinned constraint system, on the verifier side

Crosses `Zcash.Circuits.Fixtures.PartialPinnedConstraintSystem` to the verifier's
`VerifyingKey` record. The pinned record carries more than the verifier's runtime
`VerifyingKey` (counts, constants), so the record-level capture equality lives fixture
side (`Zcash.Snark.Fixtures.SingleAction.PinnedCsMatch`), and the verifying key
connects field-wise: `VerifyingKey.gates_eval_of_gates_eq` carries the derived-gate
semantics (`derive_gates_eval`) to any verifying key whose gate list equals a
derivation's — the gate-side input to the Clean-constraints transport. `actionCS` is
the Action instance of the source constraint system.

This module also hosts the DERIVED keygen witnesses of the pinned-CS derivation: the
Action circuit's keygen-view operation stream (`actionOperations`) and the
selector-compression map computed from it end to end (`actionSelMapDerived`) — synthesize
mirror → region shapes → V1 floor-planner placement → selector activations →
`compress_selectors`. Everything here is pure term-level data (no fixture reads); the
Rust-dumped `actionSelMap` survives only as a cross-check in `TestSelMapDerivation`.
-/

namespace Zcash.Snark

open Halo2
open Circuits.Fixtures

/-- **A verifying key whose gate list is a derivation's evaluates like the source
circuit.** Given `vk.gates = (.derive cs seed map).gates` and selector coverage, the
`j`-th VK gate — at query families interpreting the derivation walk's layout —
evaluates to the `j`-th flattened Clean gate expression under the selector-replacement
valuation. -/
theorem VerifyingKey.gates_eval_of_gates_eq
    {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G)
    (cs : ConstraintSystem Fp) (seed : List Query) (map : SelCompressMap)
    (hgates : vk.gates = (PartialPinnedConstraintSystem.derive cs seed map).gates)
    (fE aE iE : ℕ → Fp) (v : Query → Fp)
    (hcov : ∀ p ∈ flatGates cs,
      p.selectorsCovered (fun i => (map.lookup i).isSome) = true)
    (hint : Interprets
      (eraseGates ((flatGates cs).map (substSelectorMap map.lookup))
        (seedQueries seed {})).2 fE aE iE v)
    (j : ℕ) (hg : j < vk.gates.length) (hp : j < (flatGates cs).length) :
    Expr.eval fE aE iE vk.gates[j]
      = Expression.eval (substValuation map.lookup v) (flatGates cs)[j] := by
  rw [List.getElem_of_eq hgates hg]
  exact PartialPinnedConstraintSystem.derive_gates_eval cs seed map fE aE iE v hcov
    hint j (hgates ▸ hg) hp

end Zcash.Snark

namespace Zcash.Bridge

open Halo2
open Circuits.Fixtures
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

open Circuits.Action.Circuit in
/-- Keygen-view witnesses: every program `Value::unknown()`-shaped. Keygen synthesizes
`without_witnesses()` (`plonk/keygen.rs`) and never evaluates witness programs, so
`actionOperations` — and everything derived from it — is witness-independent; these are
the canonical unknown-shaped programs (the same set as the layout tests'
`TestVkLayoutAction.aW`). -/
def keygenWitnesses : Witnesses Fp :=
  let unk : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp) := pure (.const 0)
  let unkPoint : Witgen.MOver Fp (AssignedCell Fp) (Circuits.Point (FExpr Fp)) :=
    pure { x := .const 0, y := .const 0 }
  let unkNat : Witgen.MOver Fp (AssignedCell Fp) (NExpr Fp) := pure (.const 0)
  { psiOld := unk, rhoOld := unk, nk := unk, vOld := unk, vNew := unk, psiNew := unk,
    magnitude := unk, sign := unk,
    cmOld := unkPoint, gdOld := unkPoint, akP := unkPoint, pkDOld := unkPoint,
    gdNew := unkPoint, pkdNew := unkPoint,
    rcv := unkNat, alpha := unkNat, rivk := unkNat,
    rcmOld := unkNat, rcmNew := unkNat,
    merkleSib := fun _ => .native fun _ => #v[(0 : Fp)],
    merkleSwap := fun _ _ => false }

open Circuits.Action (orchardBases) in
/-- The ironwood (post-NU 6.3) Action circuit's keygen-view operation stream, at the
real certified bases — the object the layout tests mirror as
`TestVkLayoutAction.aProgram` (its placements, copies, σ and fixed contents are pinned
against the Rust dump there and in `TestFloorPlanner`). -/
def actionOperations : Operations Fp :=
  (Circuits.Action.Circuit.synthesize orchardGenerators orchardBases keygenWitnesses
    actionConfig).operations

/-- The selector-compression map, DERIVED end to end from the ported circuit: V1
floor-planner placements (`FloorPlanner.V1.starts`, the legacy-pdqsort port) → selector
activations (`Layout.activations`) → the `compress_selectors` port
(`deriveSelCompressMap`). `n` is the evaluation-domain size (`2^k`; the Action circuit
has `k = 11`) — a parameter of the activation table, not a fixture artifact.
Cross-checked EQUAL to the Rust-dumped `actionSelMap` in `TestSelMapDerivation`; used as
the derivation witness of `actionPinnedCs` (`PinnedCsMatch`). -/
def actionSelMapDerived (n : ℕ) : SelCompressMap :=
  deriveSelCompressMap actionCS n
    (Layout.activations (FloorPlanner.V1.starts actionOperations)
      (Layout.indexedRegions actionOperations 0).1)

end Zcash.Bridge
