import Zcash.Security.Ledger.ActionBundleBridge
import Zcash.Security.Ledger.OrchardIntegrityExperiment
import Zcash.Snark.Capstones.Action

/-!
# The Orchard extraction experiment

Compose the ledger games with the Action circuit's knowledge extractor.

The `_idealizedks` experiments quantify over witness-annotated adversaries: every
action of the output chain carries the witness for the Action statement. This module
builds that annotated adversary from a proof-emitting one. The composed adversary
presents, per chain position and bundle size, the Fiat–Shamir family that produces its
proofs; the sample space adds the generator table and one transcript per slot and
size; and the annotations are computed by the composed ledger extractor
(`actionLedgerOutcome`) from the sampled runs.

Two facts shape the composition. First, consensus validity is public: structural
validity, type checks on public data, and verification of the proofs and signatures.
Nothing in it speaks about openings of commitments or extracted witnesses. Second,
the annotations cannot be a function of the public chain: the commitments are
perfectly hiding, so which opening a chain "contains" is well-defined only relative
to a prover execution. The constructed adversary's annotations are therefore a
function of its coins —which include the sampled runs— and that is the only shape a
sound composition can take.

The bundle size is selected adaptively. The deployed verifier absorbs the verifying
key digest, every instance commitment, and every advice commitment before squeezing
its first challenge, so the pre-challenge transcript determines the bundle size and
distinct sizes never share a squeeze input. Sampling an independent transcript per
slot and size is therefore a sound finite presentation of one random oracle, and the
ledger machine may select each position's size after seeing the runs. The cost is
that the knowledge-soundness terms of the composed bound sum over the slot-size
pairs — a factor `k * maxActions` — and each per-size family carries its own query
budget where a real adversary's attempts share one.
-/

open scoped ENNReal

namespace Zcash.Security.Ledger.OrchardExtractionExperiment

open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Common Zcash.Security.BindingSignature Zcash.Security.RedDSA Zcash.Snark
open Zcash.Common.LabeledOracleComp
open Zcash.Security.Concrete
open Zcash.Security.Ledger.ActionBundleBridge
open Zcash.Security.Ledger.Bridge
open Zcash.Security.Ledger.Model
open Zcash.Security.Ledger.Pool
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Capstone (adaptiveStatement_pairCount_lt)
open Zcash.Snark.Keygen (actionProofParamsFor)

/-- The transaction-level data the ledger machine supplies for one chain position: the
selected bundle size and the declared transaction fields. The action instances and
witnesses are not requested — they come from the selected slot's extracted ledger
data. -/
structure TxRequest (MSG : Type) (maxActions : ℕ) where
  /-- The selected bundle size: the transaction carries `size + 1` actions. -/
  size : Fin maxActions
  /-- The spend-authorization signature of each action. -/
  sigs : Fin (size.1 + 1) → RedDSA.Sig Fq PallasGroup
  /-- The declared net value leaving the pool. -/
  vBalance : ℤ
  /-- The sighash the transaction's signatures are over. -/
  sighash : MSG
  /-- The binding signature. -/
  bindingSig : RedDSA.Sig Fq PallasGroup

/-- **The proof-emitting balance adversary model, as a type.** Per chain position
`t < k` and bundle size, a Fiat–Shamir family produces the proofs; the ledger machine
`B` sees the whole sampled runs component and the presented bases, and requests one
transaction per position. The witness annotations are not part of this model — the
composition computes them by extraction. -/
structure ExtractionBalanceAdversary (MSG : Type) [Fintype MSG] [DecidableEq MSG]
    [Inhabited MSG]
    (spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop)
    {T : Type} [DecidableEq T] (query : AugmentedIndex actionCircuit.n → T)
    (k maxActions : ℕ) : Type 1 where
  /-- The adversary's coin space. -/
  ι : Type
  /-- The coin distribution. -/
  coins : PMF ι
  /-- Per slot and bundle size, the family producing that proof. -/
  families : Fin k → (n : Fin maxActions) →
    ComputedAdaptiveActionStatementFSFamily (actionProofParamsFor (n.1 + 1))
  /-- The ledger machine: from the coins, the sampled runs, and the presented bases,
  request one transaction per chain position, with its announced binding
  representation. -/
  B : ι → (table : ↥(Set.range query) → VestaG) →
    (Os : ∀ p : Fin k × Fin maxActions, (families p.1 p.2).Coins) →
    (Fin 2 → PallasGroup) →
    LabeledOracleComp (OrchardQuery MSG) Fq (fun _ => QueryRep Fq 2)
      (List (TxRequest MSG maxActions × QueryRep Fq 2))
  /-- The challenge-oracle query budget. -/
  qH : ℕ

namespace ExtractionBalanceAdversary

variable {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
  {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
  {T : Type} [DecidableEq T] {query : AugmentedIndex actionCircuit.n → T}
  {k maxActions : ℕ}
  (H_bind : PallasGroup → PallasGroup → MSG → Fq)
  (A : ExtractionBalanceAdversary MSG spendAuthVerify query k maxActions)

/-- The deployed annotated transaction type the assembled chain carries. -/
abbrev AnnotatedTx :=
  Tx (KeyBinding.Pool.Witness Fq PallasGroup Fp) Fq PallasGroup Fp Fp Fp Pool.Encoding
    MSG (RedDSA.Sig Fq PallasGroup)
    (primitives spendAuthVerify (redPallasBindingVerify H_bind)).depth

/-- The runs component of the composed sample: the generator table, and one
Fiat–Shamir transcript per slot and size. -/
abbrev Runs :=
  (↥(Set.range query) → VestaG) ×
    ∀ p : Fin k × Fin maxActions, (A.families p.1 p.2).Coins

/-- Assemble one transaction at one chain position: extract the selected slot's ledger
data and zip it with the requested signatures. Returns nothing exactly when the
composed extractor does. -/
def assembleTx (r : Runs A) (t : Fin k) (req : TxRequest MSG maxActions) :
    Option (AnnotatedTx (spendAuthVerify := spendAuthVerify) H_bind) :=
  match actionLedgerExtractor (A.families t req.size)
      (adaptiveStatement_pairCount_lt (req.size.1 + 1) (A.families t req.size))
      spendAuthVerify (redPallasBindingVerify H_bind)
      (orchardGeneratorROBasis query r.1) (r.2 (t, req.size)) with
  | none => none
  | some members =>
      some { actions := (List.finRange (req.size.1 + 1)).map fun i =>
               { inst := (members i).success.inst
                 w := (members i).success.w
                 sig := req.sigs i }
             vBalance := req.vBalance
             sighash := req.sighash
             bindingSig := req.bindingSig }

/-- Assemble the annotated chain: process the requests at successive chain positions,
and stop at the first position whose extraction fails. The samples cut short here are
exactly the samples that the extraction-failure arm of the composed experiment
covers. -/
def assembleChain (r : Runs A) :
    ℕ → List (TxRequest MSG maxActions × QueryRep Fq 2) →
      List (AnnotatedTx (spendAuthVerify := spendAuthVerify) H_bind × QueryRep Fq 2)
  | _, [] => []
  | t, (req, rep) :: rest =>
      if ht : t < k then
        match assembleTx H_bind A r ⟨t, ht⟩ req with
        | none => []
        | some tx => (tx, rep) :: assembleChain r (t + 1) rest
      else []

/-- The constructed annotated adversary's machine: run the ledger machine on the
sampled runs and annotate its output by extraction. -/
def toLA (x : A.ι × Runs A) (b : Fin 2 → PallasGroup) :
    LabeledOracleComp (OrchardQuery MSG) Fq (fun _ => QueryRep Fq 2)
      (List (AnnotatedTx (spendAuthVerify := spendAuthVerify) H_bind ×
        QueryRep Fq 2)) :=
  (A.B x.1 x.2.1 x.2.2 b).bind fun out =>
    .pure (assembleChain H_bind A x.2 0 out)

/-- The law of the runs component: a uniform generator table, and independent uniform
transcripts. -/
noncomputable def runsLaw : PMF (Runs A) :=
  independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype (∀ p : Fin k × Fin maxActions, (A.families p.1 p.2).Coins))

/-- **The composed adversary as an idealized annotated adversary.**  Its coins are the
ledger machine's coins together with the sampled runs, and the annotations are computed
by the composed extractor — a function of those coins, as the module doc explains they
must be. The query-bound and algebraicity obligations are supplied for the assembled
machine. -/
noncomputable def toIdealizedKS
    (hqb : ∀ j b, (toLA H_bind A j b).QueryBound A.qH)
    (halg : ∀ j, AlgebraicAtBindingPoints 2 pallasGen 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
      (toLA H_bind A j)) :
    IdealizedKSBalanceAdversary MSG spendAuthVerify H_bind where
  ι := A.ι × Runs A
  coins := independentProductPMF A.coins (runsLaw A)
  LA := toLA H_bind A
  qH := A.qH
  queryBound := hqb
  algebraic := halg

/-- The extraction-failure event of one slot and size, over that run's own sample: the
run accepts, and the composed extractor returns nothing. -/
def runExtractionFailure (t : Fin k) (n : Fin maxActions) :
    Set ((↥(Set.range query) → VestaG) × (A.families t n).Coins) :=
  {p | (A.families t n).accepts (orchardGeneratorROBasis query p.1) p.2 ∧
    actionLedgerExtractor (A.families t n)
      (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n))
      spendAuthVerify (redPallasBindingVerify H_bind)
      (orchardGeneratorROBasis query p.1) p.2 = none}

/-- Collapse the runs sample to one slot and size: the table, and that run's
transcript. -/
def runsAt (t : Fin k) (n : Fin maxActions) :
    Runs A → (↥(Set.range query) → VestaG) × (A.families t n).Coins :=
  Prod.map id (fun Os => Os (t, n))

/-- The law of a collapsed runs sample is the knowledge endpoints' own law: the
generator table with that one run's uniform transcript. -/
theorem runsLaw_map_runsAt (t : Fin k) (n : Fin maxActions) :
    (runsLaw A).map (runsAt A t n) =
      independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype ((A.families t n).Coins)) := by
  rw [runsAt, runsLaw, independentProductPMF_map_prodMap, PMF.map_id,
    uniformOfFintype_pi_map_eval]
  rfl

end ExtractionBalanceAdversary

end Zcash.Security.Ledger.OrchardExtractionExperiment
