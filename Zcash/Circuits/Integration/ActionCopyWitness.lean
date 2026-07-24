import Zcash.Circuits.Integration.ActionEncoding
import Zcash.Circuits.Integration.CopyListMembership

/-!
# The Action copy-replay witness

The concrete copy adapter: Action's permutation cells, the endpoint encoding (cells
through the placement, instance endpoints at absolute rows, constants at their
allocated constants-column cells), the cell valuation (the environment read of the
cell's permutation column), and the witness constructor feeding
`CopyReplayWitness.ofPairValues` with kind-dispatched pair facts — non-constant copies
through the keygen copy list and the σ-semantics value transport, constant copies
through the allocation zip and the constants-column reads.
-/

namespace Zcash.Snark

open Halo2 Halo2.Layout Zcash.Circuits Zcash.Circuits.Action
open Keygen

/-- Action's permutation columns, in verifying-key order. -/
def actionPermCols : List ColRef :=
  permColsOf orchardActionTopLevelCircuit.constraintSystem

/-- The permutation-column count (15 for the deployed Action circuit). -/
def actionNumPermCols : ℕ := actionPermCols.length

/-- The evaluation-domain size at the derived exponent. -/
def actionDomainSize : ℕ := 2 ^ orchardActionTopLevelCircuit.domainExponent

/-- The V1 constants allocation of the Action operation stream. -/
def actionConsts : List (ℕ × ℕ × ℕ) :=
  constantsOf orchardActionTopLevelCircuit.constraintSystem
    (orchardActionTopLevelCircuit.operations 0)

/-- The keygen copy list of the Action operation stream. -/
def actionCopyRaw : List (ℕ × ℕ × ℕ × ℕ) :=
  Halo2.Layout.V1.copyList actionPermCols
    orchardActionTopLevelCircuit.regionStarts
    (orchardActionTopLevelCircuit.operations 0) actionConsts

theorem actionNumPermCols_pos : 0 < actionNumPermCols := by
  native_decide

theorem actionDomainSize_pos : 0 < actionDomainSize :=
  Nat.two_pow_pos _

/-- A raw coordinate pair as a typed Action permutation cell (`mod` totalization —
the identity on every in-range coordinate, and every declared coordinate is). -/
def mkActionCell (p : ℕ × ℕ) : FlatCell actionNumPermCols actionDomainSize :=
  (⟨p.1 % actionNumPermCols, Nat.mod_lt _ actionNumPermCols_pos⟩,
    ⟨p.2 % actionDomainSize, Nat.mod_lt _ actionDomainSize_pos⟩)

/-- The Action endpoint encoding: region cells through the placement, instance
endpoints at their absolute rows, constants at their first allocated
constants-column cell. -/
def actionCopyEncode : CopyEndpoint Fp → FlatCell actionNumPermCols actionDomainSize
  | .cell c => mkActionCell
      (resolveCell actionPermCols orchardActionTopLevelCircuit.regionStarts c)
  | .instance col row => mkActionCell (permIndex actionPermCols col.toAny, row)
  | .constant v => mkActionCell
      (match actionConsts.find? (fun e => e.1 = v.val) with
        | some e => (permIndex actionPermCols (ColRef.toAny (.fixed e.2.1)), e.2.2)
        | none => (0, 0))

/-- The Action cell valuation: the environment read of the cell's permutation column
at the cell's absolute row. -/
def actionCopyValue (env : Environment Fp)
    (fc : FlatCell actionNumPermCols actionDomainSize) : Fp :=
  env.get (ColRef.toAny (actionPermCols.getD (fc.1 : ℕ) (.advice 0)))
    (((fc.2 : ℕ) : ℕ) : ℤ)

/-- **The Action copy-replay witness.** Kind-dispatched from three leaf families over
the concrete data: value agreement along each decoded keygen copy (the σ-semantics
transport), value agreement of each declared constant copy (two constants-column
reads), and the declared-endpoint read equations (resolution coordinates). -/
noncomputable def actionCopyReplayWitness
    (env : Environment Fp) {Bad : Prop}
    (hbounds : ∀ t ∈ actionCopyRaw, t.1 < actionNumPermCols ∧
      t.2.1 < actionDomainSize ∧ t.2.2.1 < actionNumPermCols ∧
      t.2.2.2 < actionDomainSize)
    (hpairval : ∀ pr ∈ decodeCopies actionNumPermCols actionDomainSize
        actionCopyRaw hbounds,
      actionCopyValue env pr.1 = actionCopyValue env pr.2 ∨ Bad)
    (hconstval : ∀ copy ∈ operationDeclaredCopies
        (orchardActionTopLevelCircuit.operations 0),
      ∀ c v, copy = (.cell c, .constant v) →
        actionCopyValue env (actionCopyEncode (.cell c)) =
          actionCopyValue env (actionCopyEncode (.constant v)) ∨ Bad)
    (hlink : ∀ copy ∈ operationDeclaredCopies
        (orchardActionTopLevelCircuit.operations 0),
      ∀ tuple, resolveDeclared actionPermCols
          orchardActionTopLevelCircuit.regionStarts copy = some tuple →
        (replayKeygenPermutation (decodeCopies actionNumPermCols actionDomainSize
            actionCopyRaw hbounds)).SameCycle
          (actionCopyEncode copy.1) (actionCopyEncode copy.2))
    (hshape : ∀ copy ∈ operationDeclaredCopies
        (orchardActionTopLevelCircuit.operations 0),
      (∃ tuple, resolveDeclared actionPermCols
          orchardActionTopLevelCircuit.regionStarts copy = some tuple) ∨
        ∃ c v, copy = (.cell c, .constant v))
    (hread : ∀ copy ∈ operationDeclaredCopies
        (orchardActionTopLevelCircuit.operations 0),
      copy.1.eval orchardActionTopLevelCircuit.placement env =
          actionCopyValue env (actionCopyEncode copy.1) ∧
        copy.2.eval orchardActionTopLevelCircuit.placement env =
          actionCopyValue env (actionCopyEncode copy.2)) :
    CopyReplayWitness orchardActionTopLevelCircuit.placement env
      (orchardActionTopLevelCircuit.operations 0)
      (FlatCell actionNumPermCols actionDomainSize) Bad :=
  Zcash.Snark.Layout.Asm.CopyReplayWitness.ofPairValues actionCopyEncode (actionCopyValue env)
    (by
      intro pr hpr
      rw [encodeDeclaredCopies, List.mem_map] at hpr
      obtain ⟨copy, hcopy, rfl⟩ := hpr
      rcases hshape copy hcopy with ⟨tuple, hres⟩ | ⟨c, v, hcv⟩
      · exact Zcash.Snark.Layout.Asm.value_eq_or_bad_of_replay_sameCycle (actionCopyValue env) _
          hpairval (hlink copy hcopy tuple hres)
      · subst hcv
        exact hconstval _ hcopy c v rfl)
    hread

end Zcash.Snark
