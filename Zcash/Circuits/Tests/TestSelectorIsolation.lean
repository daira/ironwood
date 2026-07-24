import Zcash.Circuits.Fixtures.Json

/-!
# Selector isolation: mechanizing the gate-evaluation zeroing assumption

Clean's gate semantics evaluates a gate's polynomials under the valuation
`own selector ↦ 1, every other selector ↦ 0` (`Clean/Halo2/Operations.lean`,
`.enableGate`). That is faithful to real halo2 exactly when no gate polynomial
references a *foreign* selector: a real gate `q_own · (A + q_foreign · B)` on a row
where `q_foreign = 1` constrains `A + B = 0`, while the zeroing model would assert the
stronger `A = 0` — a satisfying real witness the model rejects, breaking the transfer
of the soundness theorem to the deployed circuit.

Until now that assumption rested on a manual survey
(`Clean/Halo2/halo2-selector-survey.md`). This test mechanizes it against the
constraint system dumped from the actual Rust circuit:

* **Pre-compression** (`actionPre.json`): every gate polynomial references at most ONE
  distinct selector index. Own-selector occurrences are harmless anywhere in the
  polynomial (own = 1 under both semantics); with only one distinct selector present —
  the gate's own, by the `TestVkMatchAction` projected-CS equality — no foreign
  selector can occur.
* **Post-compression** (`actionPost.json`): no selector atom survives anywhere (gates
  or lookups) — `compress_selectors` substituted every one by a fixed-column
  root-finding polynomial, so the pre-compression check above covers the only form in
  which selectors ever appear.

Lookup *input* expressions are deliberately exempt from the pre-compression bound:
halo2's complex-selector arithmetic legitimately combines several selectors in one
lookup input (e.g. `q_lookup · (q_running · … + (1 − q_running) · …)`), and Clean
models lookup inputs with the selectors in scope rather than zeroed.
-/

namespace Zcash.Circuits.Fixtures.Test.SelectorIsolation

open Fixtures Fixtures.Json

/-- The distinct selector indices referenced by a gate polynomial. -/
def selectorIndices : Expr Fp → List ℕ
  | .selector i => [i]
  | .negated e => selectorIndices e
  | .scaled e _ => selectorIndices e
  | .sum a b => (selectorIndices a ++ selectorIndices b).eraseDups
  | .product a b => (selectorIndices a ++ selectorIndices b).eraseDups
  | .constant _ | .fixed _ | .advice _ | .instance _ => []

/-- At most one distinct selector — the gate's own — appears in the polynomial. -/
def selectorIsolated (e : Expr Fp) : Bool :=
  (selectorIndices e).length ≤ 1

/-- No selector atom at all (the post-compression invariant). -/
def selectorFree (e : Expr Fp) : Bool :=
  (selectorIndices e).isEmpty

#eval show IO Unit from do
  let actionPre ← loadCsFixture "Zcash/Circuits/Fixtures/actionPre.json" 0x31656840fdb3156d
  let actionPost ← loadCsFixture "Zcash/Circuits/Fixtures/actionPost.json" 0xdb884f3c3174a41b
  runChecks [
    ("actionPre: every gate polynomial references at most its own selector",
      actionPre.gates.all selectorIsolated),
    ("actionPost: no selector atom survives compression (gates)",
      actionPost.gates.all selectorFree),
    ("actionPost: no selector atom survives compression (lookups)",
      actionPost.lookups.all fun l =>
        l.inputs.all selectorFree && l.tables.all selectorFree)]

end Zcash.Circuits.Fixtures.Test.SelectorIsolation
