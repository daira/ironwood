import Clean.Halo2.Keygen
import Zcash.Common.ExprRich
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
(`derive_gates_eval`) to any verifying key whose gate list equals a derivation's (through
the `Expr`/`RichExpression` boundary conversion `RichExpression.ofExpr`) — the gate-side
input to the Clean-constraints transport. `actionCS` is the Action instance of the source
constraint system.

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
`Halo2.RichExpression` gates, so the hypothesis relates them through the boundary
conversion (`RichExpression.ofExpr`): `(.derive cs map).gates = vk.gates.map ofExpr`. Given
that and selector coverage, the `j`-th VK gate — at query families interpreting the
derivation walk's layout — evaluates to the `j`-th flattened Clean gate expression under
the selector-replacement valuation. The evaluation transports across the boundary because
`ofExpr` preserves evaluation (`RichExpression.eval_ofExpr`). -/
theorem VerifyingKey.gates_eval_of_gates_eq
    {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G)
    (cs : ConstraintSystem Fp) (map : SelCompressMap)
    (hgates : (PinnedConstraintSystem.derive cs map).gates
      = vk.gates.map RichExpression.ofExpr)
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
    rw [hgates, List.length_map]; exact hg
  have key := PinnedConstraintSystem.derive_gates_eval cs map fE aE iE v hcov hint j hg' hp
  rw [List.getElem_of_eq hgates hg', List.getElem_map,
    RichExpression.eval_ofExpr] at key
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

/-! ## Domain scalars -/

/-- Binary exponentiation (`Monoid.npow`'s default recursion is linear — unusable for
exponents of order `p/2^k`). -/
def powFast (b : Fp) (n : ℕ) : Fp :=
  if n = 0 then 1
  else
    let r := powFast (b * b) (n / 2)
    if n % 2 = 1 then b * r else r
  decreasing_by omega

/-- Binary exponentiation agrees with the field's ordinary natural power. -/
theorem powFast_eq_pow (b : Fp) (n : ℕ) :
    powFast b n = b ^ n := by
  induction n using Nat.strong_induction_on generalizing b with
  | h n ih =>
      rw [powFast]
      by_cases hn : n = 0
      · simp [hn]
      · rw [if_neg hn]
        have hhalf : n / 2 < n := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hn) (by norm_num)
        rw [ih (n / 2) hhalf]
        by_cases hodd : n % 2 = 1
        · rw [if_pos hodd]
          have hn_split : n = 2 * (n / 2) + 1 := by omega
          calc
            b * (b * b) ^ (n / 2) =
                b * (b ^ 2) ^ (n / 2) := by rw [pow_two]
            _ = b ^ (2 * (n / 2) + 1) := by
              rw [pow_add, pow_mul, pow_one]
              ring
            _ = b ^ n := congrArg (b ^ ·) hn_split.symm
        · have heven : n % 2 = 0 := by omega
          rw [if_neg hodd]
          have hn_split : n = 2 * (n / 2) := by omega
          calc
            (b * b) ^ (n / 2) = (b ^ 2) ^ (n / 2) := by rw [pow_two]
            _ = b ^ (2 * (n / 2)) := by rw [pow_mul]
            _ = b ^ n := congrArg (b ^ ·) hn_split.symm

/-- The size-`2^k` domain's root of unity: pasta `Fp::GENERATOR = 5`,
`ROOT_OF_UNITY = 5^((p−1)/2^32)`, and `EvaluationDomain::new` squares it down `32 − k`
times — so `omega = 5^((p−1)/2^k)`. Certified against the captured VK in `VkMatch`. -/
def omegaOf (k : ℕ) : Fp :=
  powFast 5 ((Snark.scalarFieldOrder - 1) / 2 ^ k)

/--
The executable generator spelling of every supported `omegaOf` agrees with powers of
CompElliptic's certified Pasta root. This is the sole native-tier bridge in the domain
facts below; `omegaOf` itself remains pure data and does not infect assignment
definitions with the certificate's native axiom.
-/
private theorem omegaOf_eq_certifiedRootPow :
    ∀ k : Fin 33,
      omegaOf k =
        powFast CompElliptic.Fields.Pasta.pallasBase.rootOfUnity
          (2 ^ (32 - (k : ℕ))) := by
  native_decide

/-- `omegaOf k` is a primitive size-`2^k` domain root for every supported exponent. -/
theorem omegaOf_isPrimitiveRoot (k : ℕ) (hk : k ≤ 32) :
    IsPrimitiveRoot (omegaOf k) (2 ^ k) := by
  have hroot :
      IsPrimitiveRoot
        CompElliptic.Fields.Pasta.pallasBase.rootOfUnity (2 ^ 32) :=
    IsPrimitiveRoot.iff_orderOf.mpr
      CompElliptic.Fields.Pasta.pallasBase.valid.rootOfUnity_order
  rw [omegaOf_eq_certifiedRootPow ⟨k, Nat.lt_succ_of_le hk⟩, powFast_eq_pow]
  apply IsPrimitiveRoot.pow (by positivity) hroot
  rw [← pow_add, Nat.sub_add_cancel hk]

/-- Every point `omegaOf k ^ row` lies in the size-`2^k` evaluation domain. -/
theorem omegaOf_domain (k row : ℕ) (hk : k ≤ 32) :
    (omegaOf k ^ row) ^ (2 ^ k) = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]
  rw [(omegaOf_isPrimitiveRoot k hk).pow_eq_one, one_pow]

/-- Distinct row indices below `2^k` name distinct evaluation-domain points. -/
theorem omegaOf_powers_injective (k : ℕ) (hk : k ≤ 32) :
    Function.Injective fun row : Fin (2 ^ k) => omegaOf k ^ (row : ℕ) := by
  intro left right heq
  apply Fin.ext
  exact (omegaOf_isPrimitiveRoot k hk).pow_inj left.isLt right.isLt heq

/-- The supported evaluation-domain size is nonzero when cast into `Fp`. -/
theorem domainSize_cast_ne_zero (k : ℕ) (hk : k ≤ 32) :
    ((2 ^ k : ℕ) : Fp) ≠ 0 := by
  intro hzero
  have hdiv : Snark.scalarFieldOrder ∣ 2 ^ k :=
    (ZMod.natCast_eq_zero_iff (2 ^ k) Snark.scalarFieldOrder).mp hzero
  apply Nat.not_dvd_of_pos_of_lt (by positivity) _ hdiv
  calc
    2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hk
    _ < Snark.scalarFieldOrder := by
      norm_num [Snark.scalarFieldOrder,
        CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

/-- pasta `Fp::DELTA = GENERATOR^(2^S) = 5^(2^32)`. -/
def deltaFp : Fp := powFast 5 (2 ^ 32)

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
