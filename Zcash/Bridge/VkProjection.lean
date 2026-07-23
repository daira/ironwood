import Zcash.Circuits.Fixtures.PinnedConstraintSystem
import Zcash.Circuits.Fixtures.ActionSelMap
import Zcash.Circuits.Specs.SinsemillaGenerators
import Zcash.Circuits.Action.Circuit
import Zcash.Snark.Core.Field
import Zcash.Snark.Verifier.Assemble

/-!
# The verifying key's pinned constraint system, on the verifier side

Crosses `Zcash.Circuits.Fixtures.PartialPinnedConstraintSystem` to the verifier's
`VerifyingKey` record: `VerifyingKey.pinnedCs` reads the pinned sub-record off a
verifying key, and `VerifyingKey.gates_eval_of_pinnedCs_eq` carries the derived-gate
semantics (`derive_gates_eval`) to any verifying key whose pinned CS equals a
derivation — the gate-side input to the Clean-constraints transport. `actionCS` is the
Action instance of the source constraint system; the capture equality lives in
`Zcash.Snark.Fixtures.SingleAction.PinnedCsMatch`/`VkMatch`.
-/

namespace Zcash.Snark

open Halo2
open Circuits.Fixtures

/-- The pinned-CS sub-record of a verifying key: gates, query layouts, and the
flattened lookup expression lists. -/
def VerifyingKey.pinnedCs {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) : PartialPinnedConstraintSystem where
  gates := vk.gates
  adviceQueryLayout := vk.adviceQueryLayout
  fixedQueryLayout := vk.fixedQueryLayout
  instanceQueryLayout := vk.instanceQueryLayout
  lookupInputExprs := List.ofFn vk.lookupInputExprs
  lookupTableExprs := List.ofFn vk.lookupTableExprs

/-- **A verifying key whose pinned CS is a derivation evaluates like the source
circuit.** Given `vk.pinnedCs = .derive cs seed map` and selector coverage, the `j`-th
VK gate — at query families interpreting the derivation walk's layout — evaluates to
the `j`-th flattened Clean gate expression under the selector-replacement valuation. -/
theorem VerifyingKey.gates_eval_of_pinnedCs_eq
    {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G)
    (cs : ConstraintSystem Fp) (seed : List Query) (map : SelCompressMap)
    (heq : vk.pinnedCs = PartialPinnedConstraintSystem.derive cs seed map)
    (fE aE iE : ℕ → Fp) (v : Query → Fp)
    (hcov : ∀ p ∈ flatGates cs,
      p.selectorsCovered (fun i => (map.lookup i).isSome) = true)
    (hint : Interprets
      (eraseGates ((flatGates cs).map (substSelectorMap map.lookup))
        (seedQueries seed {})).2 fE aE iE v)
    (j : ℕ) (hg : j < vk.gates.length) (hp : j < (flatGates cs).length) :
    Expr.eval fE aE iE vk.gates[j]
      = Expression.eval (substValuation map.lookup v) (flatGates cs)[j] := by
  have hgates : vk.gates = (PartialPinnedConstraintSystem.derive cs seed map).gates :=
    congrArg PartialPinnedConstraintSystem.gates heq
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

end Zcash.Bridge
