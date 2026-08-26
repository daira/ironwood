import Zcash.Common.Satisfying
import Zcash.Security.Ledger.SinsemillaDLR
import Zcash.Snark.Soundness.Action.StraightLineTerminal

/-!
# The bundle-level Action-to-ledger bridge

Lift the per-Action data bridge across an accepted bundle.  Each extracted member
witness (`TopLevelSemanticWitness`) is a satisfying witness of the circuit-facing
`ActionSpec` (`Zcash.Common.Satisfying`), and `actionSpecToLedgerData` refines it to
the member's ledger data —the full extracted witness together with its refined
ledger action— or the computed discrete-log relation of its first Sinsemilla
escape.  The bundle traversal returns every member's data or the first escape
(`finForallOrRelationWitness`): knowledge soundness composed at the reduction layer,
with everything carried as data.
-/

namespace Zcash.Security.Ledger.ActionBundleBridge

open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Common
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Bridge
open Zcash.Snark
open Zcash.Snark.ActionTerminal

variable {MSG SIG : Type*}

/-- An extracted bundle member as a satisfying witness of the circuit-facing
`ActionSpec`: the private witness transported across the circuit boundary, with its
specification proof. -/
def memberSatisfying {input : PublicInputs Fp}
    (w : TopLevelSemanticWitness actionCircuit input) :
    Satisfying ActionSpec input where
  w := actionCircuit_privateWitness_eq ▸ w.w
  satisfied := by
    rw [actionCircuit_spec_iff]
    simp only [eqRec_eq_cast, cast_cast, cast_eq]
    exact w.satisfied

/-- The ledger data of one accepted bundle member. -/
structure MemberLedgerData
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    (input : PublicInputs Fp) where
  /-- The member's extracted private witness — the chain's genuinely free value,
  carried in full. -/
  wit : PrivateWitness
  /-- The member's refined ledger action. -/
  success : ActionLedgerSuccess spendAuthVerify bindingVerify (combine input wit)

/-- Refine one extracted bundle member to its ledger data, or the computed
discrete-log relation of its first Sinsemilla escape. -/
def memberLedgerData
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    {input : PublicInputs Fp}
    (w : TopLevelSemanticWitness actionCircuit input) :
    MemberLedgerData spendAuthVerify bindingVerify input ⊕' ActionDLBreak :=
  let sat := memberSatisfying w
  bindOrRelationWitness
    (actionSpecToLedgerData spendAuthVerify bindingVerify input sat.w sat.satisfied)
    fun success => { wit := sat.w, success := success }

/-- Refine every member of an accepted bundle, or return the first member's computed
escape relation. -/
def bundleLedgerData
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    {numProofs : ℕ} {inputs : Fin numProofs → PublicInputs Fp}
    (witness : ActionBundleWitness inputs) :
    (∀ i, MemberLedgerData spendAuthVerify bindingVerify (inputs i)) ⊕' ActionDLBreak :=
  finForallOrRelationWitness fun i =>
    memberLedgerData spendAuthVerify bindingVerify (witness i)

end Zcash.Security.Ledger.ActionBundleBridge
