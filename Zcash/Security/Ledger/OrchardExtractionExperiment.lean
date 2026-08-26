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
budget where a real adversary's attempts share one. Removing the factor is tracked
as #214.
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

/-- The law of one run: the generator table with that run's uniform transcript. This
is the knowledge endpoints' own sample law, so per-run hypotheses stated over it are
the endpoints' conclusions verbatim. -/
noncomputable def runLawAt (t : Fin k) (n : Fin maxActions) :
    PMF ((↥(Set.range query) → VestaG) × (A.families t n).Coins) :=
  independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype ((A.families t n).Coins))

/-- One run's knowledge-failure event, pulled back to the generator table: the run
accepts and the witness projection returns nothing. -/
def runKnowledgeFailure (t : Fin k) (n : Fin maxActions) :
    Set ((↥(Set.range query) → VestaG) × (A.families t n).Coins) :=
  (fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
    (A.families t n).adaptiveStatementKnowledgeFailureEvent
      (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n))

/-- The event that one run accepts and a member of its extracted bundle escapes the
bridge, over that run's own sample. -/
def runEscape (t : Fin k) (n : Fin maxActions) :
    Set ((↥(Set.range query) → VestaG) × (A.families t n).Coins) :=
  {p | (A.families t n).accepts (orchardGeneratorROBasis query p.1) p.2 ∧
    (actionLedgerEscapeFinder (A.families t n)
      (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n))
      spendAuthVerify (redPallasBindingVerify H_bind)
      (orchardGeneratorROBasis query p.1) p.2).isSome}

/-- One run's extraction failure decomposes into that run's knowledge-failure event
and its computed ledger escape (`actionLedgerExtractor_eq_none_iff`). -/
theorem runExtractionFailure_subset (t : Fin k) (n : Fin maxActions) :
    runExtractionFailure H_bind A t n ⊆
      runKnowledgeFailure A t n ∪ runEscape H_bind A t n := by
  rintro p ⟨hacc, hnone⟩
  rcases (actionLedgerExtractor_eq_none_iff (A.families t n)
      (adaptiveStatement_pairCount_lt (n.1 + 1) (A.families t n))
      spendAuthVerify (redPallasBindingVerify H_bind)
      (orchardGeneratorROBasis query p.1) p.2).mp hnone with h | h
  · exact Or.inl ⟨hacc, h⟩
  · exact Or.inr ⟨hacc, h⟩

/-- An event that reads only the generator table and one run's transcript has the same
measure under the composed experiment as under that run's own law. -/
theorem experiment_measure_runsAt
    (hqb : ∀ j b, (toLA H_bind A j b).QueryBound A.qH)
    (halg : ∀ j, AlgebraicAtBindingPoints 2 pallasGen 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id (toLA H_bind A j))
    (t : Fin k) (n : Fin maxActions)
    (E : Set ((↥(Set.range query) → VestaG) × (A.families t n).Coins)) :
    (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        ((fun x : (A.ι × Runs A) × ((OrchardQuery MSG → Fq) × (Fin 2 → Fq)) =>
          runsAt A t n x.1.2) ⁻¹' E) =
      (runLawAt A t n).toOuterMeasure E := by
  have hfst : (toIdealizedKS H_bind A hqb halg).experiment.map Prod.fst =
      independentProductPMF A.coins (runsLaw A) :=
    challengeExperiment_map_fst 2 _
  have hsnd : (independentProductPMF A.coins (runsLaw A)).map Prod.snd = runsLaw A :=
    independentProductPMF_map_snd _ _
  have hmap : (toIdealizedKS H_bind A hqb halg).experiment.map
      (fun x : (A.ι × Runs A) × ((OrchardQuery MSG → Fq) × (Fin 2 → Fq)) =>
        runsAt A t n x.1.2) = runLawAt A t n := by
    have h1a : ((toIdealizedKS H_bind A hqb halg).experiment.map Prod.fst).map
        Prod.snd =
        (toIdealizedKS H_bind A hqb halg).experiment.map (Prod.snd ∘ Prod.fst) :=
      PMF.map_comp _ _ _
    have h1b : ((toIdealizedKS H_bind A hqb halg).experiment.map
          (Prod.snd ∘ Prod.fst)).map (runsAt A t n) =
        (toIdealizedKS H_bind A hqb halg).experiment.map
          ((runsAt A t n) ∘ (Prod.snd ∘ Prod.fst)) :=
      PMF.map_comp _ _ _
    have h1 : (toIdealizedKS H_bind A hqb halg).experiment.map
        (fun x : (A.ι × Runs A) × ((OrchardQuery MSG → Fq) × (Fin 2 → Fq)) =>
          runsAt A t n x.1.2) =
        (((toIdealizedKS H_bind A hqb halg).experiment.map Prod.fst).map Prod.snd).map
          (runsAt A t n) := by
      rw [h1a, h1b]
      rfl
    rw [h1, hfst, hsnd, runsLaw_map_runsAt]
    rfl
  calc (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        ((fun x : (A.ι × Runs A) × ((OrchardQuery MSG → Fq) × (Fin 2 → Fq)) =>
          runsAt A t n x.1.2) ⁻¹' E)
      = ((toIdealizedKS H_bind A hqb halg).experiment.map
          (fun x : (A.ι × Runs A) × ((OrchardQuery MSG → Fq) × (Fin 2 → Fq)) =>
            runsAt A t n x.1.2)).toOuterMeasure E :=
        (PMF.toOuterMeasure_map_apply _ _ _).symm
    _ = (runLawAt A t n).toOuterMeasure E := by rw [hmap]

/-- The extraction-failure arm of the composed experiment: some run among the sampled
slot-size pairs accepts and its composed extractor returns nothing. -/
def extractionFailureEvent :
    Set ((A.ι × Runs A) × ((OrchardQuery MSG → Fq) × (Fin 2 → Fq))) :=
  ⋃ q : Fin k × Fin maxActions,
    (fun x => runsAt A q.1 q.2 x.1.2) ⁻¹' runExtractionFailure H_bind A q.1 q.2

/-- The extraction-failure arm costs one knowledge-soundness bound and one escape
bound per slot-size pair: the factor `k * maxActions` counts the extraction targets
this model hands the adversary. Removing the factor —composing with the SNARK
argument at the reduction layer instead of consuming its endpoint— is tracked as
#214. -/
theorem extractionFailureEvent_measure_le
    (hqb : ∀ j b, (toLA H_bind A j b).QueryBound A.qH)
    (halg : ∀ j, AlgebraicAtBindingPoints 2 pallasGen 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id (toLA H_bind A j))
    {ε_ks ε_escape : ℝ≥0∞}
    (hks : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt A t n).toOuterMeasure (runKnowledgeFailure A t n) ≤ ε_ks)
    (hescape : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt A t n).toOuterMeasure (runEscape H_bind A t n) ≤ ε_escape) :
    (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        (extractionFailureEvent H_bind A) ≤
      (k * maxActions : ℕ) * (ε_ks + ε_escape) := by
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  have hslot : ∀ q : Fin k × Fin maxActions,
      (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        ((fun x => runsAt A q.1 q.2 x.1.2) ⁻¹'
          runExtractionFailure H_bind A q.1 q.2) ≤ ε_ks + ε_escape := by
    intro q
    refine le_trans
      (le_of_eq (experiment_measure_runsAt H_bind A hqb halg q.1 q.2 _)) ?_
    refine le_trans (MeasureTheory.measure_mono
      (runExtractionFailure_subset H_bind A q.1 q.2)) ?_
    refine le_trans (MeasureTheory.measure_union_le _ _) ?_
    exact add_le_add (hks q.1 q.2) (hescape q.1 q.2)
  refine le_trans (ENNReal.tsum_le_tsum hslot) (le_of_eq ?_)
  calc ∑' _q : Fin k × Fin maxActions, (ε_ks + ε_escape)
      = (Fintype.card (Fin k × Fin maxActions) : ℝ≥0∞) * (ε_ks + ε_escape) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((k * maxActions : ℕ) : ℝ≥0∞) * (ε_ks + ε_escape) := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

end ExtractionBalanceAdversary

section Endpoints

open ExtractionBalanceAdversary

variable {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
  {spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop}
  {T : Type} [DecidableEq T] {query : AugmentedIndex actionCircuit.n → T}
  {k maxActions : ℕ}
  (H_bind : PallasGroup → PallasGroup → MSG → Fq)
  (A : ExtractionBalanceAdversary MSG spendAuthVerify query k maxActions)

/-- **Balance integrity for the proof-emitting adversary, at deployed Orchard.**
Except with probability at most the bound, every run among the sampled slot-size pairs
that the verifier accepts yields extracted ledger data, and the annotated chain
assembled from that data —whenever it validates at the sampled primitives— satisfies
balance integrity at every prefix below `k`.

The event's validity conjunct is consensus validity together with the assembled
annotations. Consensus validity itself is public and says nothing about openings; the
annotations are computed by the composed extractor from the sampled runs (module doc).
The composed statement is for the reprogrammed basis: the extracted witnesses open the
value commitments at the deployed bases, and the sampled bases stand for those under
the reference-string idealization recorded at
`IdealizedKSBalanceAdversary.violationEvent`.

`hks` is stated so that `orchard_action_adaptiveStatement_knowledge_error_bound`
applies to it verbatim, one application per slot-size pair; `hescape` names each
pair's Sinsemilla-escape bound. The remaining hypotheses and the second summand are
the KS-idealized integrity endpoint's, applied at the constructed adversary. -/
theorem orchardBalanceIntegrityExtraction_measure_le
    (hqb : ∀ j b, (toLA H_bind A j b).QueryBound A.qH)
    (halg : ∀ j, AlgebraicAtBindingPoints 2 pallasGen 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id (toLA H_bind A j))
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {ε_ks ε_escape ε_sinsemilladlr ε_dl : ℝ≥0∞}
    (hks : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt A t n).toOuterMeasure (runKnowledgeFailure A t n) ≤ ε_ks)
    (hescape : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt A t n).toOuterMeasure (runEscape H_bind A t n) ≤ ε_escape)
    (hsin : (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
      ((toIdealizedKS H_bind A hqb halg).sinsemillaRelationEvent issuance maxActions k)
      ≤ ε_sinsemilladlr)
    (hdl : ∀ j, TextbookDLWithCoinsAdvantageLE pallasGen
      ((toIdealizedKS H_bind A hqb halg).conservationFinder k j) ε_dl) :
    (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A hqb halg).violationEvent issuance maxActions
            (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) k)) ≤
      (k * maxActions : ℕ) * (ε_ks + ε_escape) +
        (ε_sinsemilladlr + (ε_dl + ((A.qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card Fq)) := by
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (extractionFailureEvent_measure_le H_bind A hqb halg hks hescape)
    (orchardBalanceIntegrity_measure_le_idealizedks (toIdealizedKS H_bind A hqb halg)
      issuance maxActions hmax k hsin hdl)

/-- **Balance conservation for the proof-emitting adversary, at deployed Orchard.**
As the integrity endpoint (`orchardBalanceIntegrityExtraction_measure_le`), covering
the conservation violation alone; the second summand is the KS-idealized conservation
endpoint's bound. -/
theorem orchardBalanceConservationExtraction_measure_le
    (hqb : ∀ j b, (toLA H_bind A j b).QueryBound A.qH)
    (halg : ∀ j, AlgebraicAtBindingPoints 2 pallasGen 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id (toLA H_bind A j))
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {ε_ks ε_escape ε_dl : ℝ≥0∞}
    (hks : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt A t n).toOuterMeasure (runKnowledgeFailure A t n) ≤ ε_ks)
    (hescape : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt A t n).toOuterMeasure (runEscape H_bind A t n) ≤ ε_escape)
    (hdl : ∀ j, TextbookDLWithCoinsAdvantageLE pallasGen
      ((toIdealizedKS H_bind A hqb halg).conservationFinder k j) ε_dl) :
    (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A hqb halg).violationEvent issuance maxActions
            (fun P => balanceConservationViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) k)) ≤
      (k * maxActions : ℕ) * (ε_ks + ε_escape) +
        (ε_dl + ((A.qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card Fq) := by
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (extractionFailureEvent_measure_le H_bind A hqb halg hks hescape)
    (orchardBalanceConservation_measure_le_idealizedks (toIdealizedKS H_bind A hqb halg)
      issuance maxActions hmax k hdl)

/-- **Shielded balance cap for the proof-emitting adversary, at deployed Orchard.**
As the conservation endpoint, for the shielded pool exceeding the minted issuance at
some prefix below `k`. -/
theorem orchardShieldedBalanceCapExtraction_measure_le
    (hqb : ∀ j b, (toLA H_bind A j b).QueryBound A.qH)
    (halg : ∀ j, AlgebraicAtBindingPoints 2 pallasGen 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id (toLA H_bind A j))
    (issuance : ℕ → ℕ) (hmax : maxActions < 2 ^ 16)
    {ε_ks ε_escape ε_dl : ℝ≥0∞}
    (hks : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt A t n).toOuterMeasure (runKnowledgeFailure A t n) ≤ ε_ks)
    (hescape : ∀ (t : Fin k) (n : Fin maxActions),
      (runLawAt A t n).toOuterMeasure (runEscape H_bind A t n) ≤ ε_escape)
    (hdl : ∀ j, TextbookDLWithCoinsAdvantageLE pallasGen
      ((toIdealizedKS H_bind A hqb halg).conservationFinder k j) ε_dl) :
    (toIdealizedKS H_bind A hqb halg).experiment.toOuterMeasure
        (extractionFailureEvent H_bind A ∪
          (toIdealizedKS H_bind A hqb halg).violationEvent issuance maxActions
            (fun P => shieldedBalanceCapViolationBefore (P := P) (kv := keyBinding)
              (issuance := issuance) (maxActions := maxActions) k)) ≤
      (k * maxActions : ℕ) * (ε_ks + ε_escape) +
        (ε_dl + ((A.qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card Fq) := by
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (extractionFailureEvent_measure_le H_bind A hqb halg hks hescape)
    (orchardShieldedBalanceCap_measure_le_idealizedks (toIdealizedKS H_bind A hqb halg)
      issuance maxActions hmax k hdl)

end Endpoints

end Zcash.Security.Ledger.OrchardExtractionExperiment
