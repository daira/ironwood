import Zcash.Security.Ledger.IntegrityExperiment
import Zcash.Security.Ledger.OrchardCapstone

/-!
# The Orchard integrity experiment: the non-negativity arms collapse to one Sinsemilla DLR

The abstract integrity experiment (`balanceIntegrityBefore_measure_le_experiment`) bounds a
balance-integrity violation by `ε_nonneg + conservation` over the challenge-oracle sample space,
taking the union of the three Balance-subset arms (merkle, note-commitment, key-binding) as one
named bound `ε_nonneg`. This module discharges `ε_nonneg` at the Orchard instantiation: all three
arms collapse onto the single advantage of computing a nontrivial discrete-log relation among the
fixed Sinsemilla bases, exactly as `orchardBalanceIntegrity_measure_le` does at the deployed
capstone layer, but now over the challenge experiment's sample space.

The enabler is that `kappaPrimitivesAt` is a record update of the deployed primitives touching only
`valueCommit` and `bindingVerify`, and the three non-negativity arms read only the note-commitment,
key-binding, and Merkle structure — which the sampling leaves fixed. So at the sampled primitives a
Balance-subset break is the same data as at the deployed primitives, and the Orchard reducers
(`relationOfKeyBindingBreak`, `relationOfNoteCommitBreak`, `relationOfMerkleCollision`) apply
unchanged. The reductions are deterministic and need no value/binding-side hypotheses, so this
discharge is independent of the conservation side, which the abstract experiment still handles
through its coin-consuming finders.
-/

-- The Orchard reducers carry Sinsemilla chunk exponents beyond the default threshold, as in
-- `MerkleDLR`; raise it so the relation terms elaborate without an unevaluated-power warning.
set_option exponentiation.threshold 600

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Common Zcash.Security.BindingSignature Zcash.Security.RedDSA Zcash.Snark
open Zcash.Common.LabeledOracleComp
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Pool
open Zcash.Security.Ledger.Model
open scoped ENNReal

universe u

variable {MSG SIG : Type*}
  (verify bverify : PallasGroup → MSG → SIG → Prop)
  (issuance : ℕ → ℕ) (maxActions : ℕ)
variable {Q : Type u} [Fintype Q] [DecidableEq Q] [Inhabited Q]
variable (m : ℕ) (gen : PallasGroup) (v_idx r_idx : Fin m)
  (queryOf : PallasGroup → PallasGroup → MSG → Q)
  (toSig : SIG → RedDSA.Sig Fq PallasGroup)

/-- A note-commitment break at the sampled primitives is one at the deployed primitives. The break
constrains only `noteCommit`, `extract`, and `valueBound`, and `kappaPrimitivesAt` — a record update
touching only `valueCommit` and `bindingVerify` — leaves those three fields equal to the deployed
ones, so every field transports by definitional equality. (`NoteCommitBreak` is indexed by the whole
primitives record, which the sampling does change, so the two break types are not definitionally
equal; rebuilding field-by-field is what carries the break across.) -/
def noteCommitBreakOfKappa (O : Q → Fq) (s : Fin m → Fq)
    (nb : NoteCommitBreak (kappaPrimitivesAt m gen v_idx r_idx queryOf
      (primitives verify bverify) toSig O s)) :
    NoteCommitBreak (primitives verify bverify) :=
  ⟨nb.rcm₁, nb.n₁, nb.rcm₂, nb.n₂, nb.cm₁, nb.cm₂, nb.ne, nb.open₁, nb.open₂, nb.extract_eq,
    nb.v₁_lt, nb.v₂_lt⟩

/-- **The Orchard Balance-subset reduction at the sampled bases.** As
`orchardBalanceSubsetOrRelation`, but at `kappaPrimitivesAt`'s primitives — the deployed Orchard
primitives with the value and binding fields replaced by the sampled slots. Those replaced fields
are not read by any Balance-subset arm, so the reduction routes each break through the same Orchard
reducer and lands in the same `OrchardBalanceRelation`. -/
def kappaOrchardBalanceSubsetOrRelation (O : Q → Fq) (s : Fin m → Fq)
    {ledger : Ledger _ Fq PallasGroup Fp Fp Fp Encoding MSG SIG _}
    (hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf
        (primitives verify bverify) toSig O s) keyBinding issuance maxActions ledger) (i : ℕ) :
    (nonZeroSpends ledger (i + 1) ≤ ↑(positionedOutputs ledger i)) ⊕' OrchardBalanceRelation :=
  match balanceSubsetOrBreak hval i with
  | .inl hsub => .inl hsub
  | .inr (.keyBinding _ _ h) => .inr (.keyBinding (relationOfKeyBindingBreak h))
  | .inr (.noteCommit nb) => .inr (.noteCommit (relationOfNoteCommitBreak verify bverify
      (noteCommitBreakOfKappa verify bverify m gen v_idx r_idx queryOf toSig O s nb)))
  | .inr (.merkle c) => .inr (.merkle (relationOfMerkleCollision c.2))

omit [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- A Balance-subset break at the sampled primitives computes an Orchard Sinsemilla relation: the
total reduction cannot return the containment when handed a break, so it returns a relation. -/
theorem kappaOrchardBalanceSubsetOrRelation_inr_of_break (O : Q → Fq) (s : Fin m → Fq)
    {ledger : Ledger _ Fq PallasGroup Fp Fp Fp Encoding MSG SIG _}
    (hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf
        (primitives verify bverify) toSig O s) keyBinding issuance maxActions ledger) (i : ℕ)
    {b : BalanceBreak (kappaPrimitivesAt m gen v_idx r_idx queryOf
        (primitives verify bverify) toSig O s) keyBinding}
    (hb : balanceSubsetOrBreak hval i = .inr b) :
    ∃ rel, kappaOrchardBalanceSubsetOrRelation verify bverify issuance maxActions m gen v_idx r_idx
      queryOf toSig O s hval i = .inr rel := by
  unfold kappaOrchardBalanceSubsetOrRelation
  rw [hb]
  cases b <;> exact ⟨_, rfl⟩

variable {ι : Type u}
  (LA : ι → (Fin m → PallasGroup) → LabeledOracleComp Q Fq (fun _ => QueryRep Fq m)
    (List (Tx (KeyBinding.Pool.Witness Fq PallasGroup Fp) Fq PallasGroup Fp Fp Fp Encoding MSG SIG
      (primitives verify bverify).depth × QueryRep Fq m)))

/-- **The sampled Orchard Sinsemilla-relation event.** The samples on which the output ledger is
valid at the sampled primitives and its data computes a nontrivial discrete-log relation among the
fixed Sinsemilla bases at some step `i < k`. This is the challenge-experiment analogue of the
deployed capstone's `orchardRelationEventUpTo`; the single advantage `ε_sinsemilladlr` is a bound on
this one event. -/
def sampledOrchardRelationEventUpTo (k : ℕ) :
    Set (ι × ((Q → Fq) × (Fin m → Fq))) :=
  setOf fun x =>
    ∃ hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf
        (primitives verify bverify) toSig x.2.1 x.2.2) keyBinding issuance maxActions
        (((LA x.1 (scalarBasis gen x.2.2)).run x.2.1).map Prod.fst),
      ∃ i, i < k ∧ ∃ rel, kappaOrchardBalanceSubsetOrRelation verify bverify issuance maxActions
        m gen v_idx r_idx queryOf toSig x.2.1 x.2.2 hval i = .inr rel

omit [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- **The three sampled non-negativity arms collapse onto the Sinsemilla-relation event.** Every
sample on which the reduction lands in the merkle, note-commitment, or key-binding arm computes a
nontrivial discrete-log relation among the fixed Sinsemilla bases: the arm's break is routed through
its deterministic Orchard reducer (`kappaOrchardBalanceSubsetOrRelation`). This is what discharges
the abstract experiment's combined `ε_nonneg` by the single `ε_sinsemilladlr` at the Orchard
instantiation. -/
theorem sampledBalanceSubsetArms_subset_orchardRelation (k : ℕ) :
    sampledLedgerEvent m gen v_idx r_idx queryOf (primitives verify bverify) toSig LA
        (fun P => balanceSubsetBreakEventUpTo (P := P) (kv := keyBinding) (issuance := issuance)
            (maxActions := maxActions) k .merkle
          ∪ balanceSubsetBreakEventUpTo (P := P) (kv := keyBinding) (issuance := issuance)
            (maxActions := maxActions) k .noteCommit
          ∪ balanceSubsetBreakEventUpTo (P := P) (kv := keyBinding) (issuance := issuance)
            (maxActions := maxActions) k .keyBinding)
      ⊆ sampledOrchardRelationEventUpTo verify bverify issuance maxActions m gen v_idx r_idx
          queryOf toSig LA k := by
  rintro x ⟨hval, harm⟩
  refine ⟨hval, ?_⟩
  obtain ⟨i, hik, b, hb⟩ : ∃ i, i < k ∧ ∃ b, balanceSubsetOrBreak hval i = .inr b := by
    rcases harm with (⟨i, hik, b, hb, -⟩ | ⟨i, hik, b, hb, -⟩) | ⟨i, hik, b, hb, -⟩ <;>
      exact ⟨i, hik, b, hb⟩
  exact ⟨i, hik, kappaOrchardBalanceSubsetOrRelation_inr_of_break verify bverify issuance
    maxActions m gen v_idx r_idx queryOf toSig x.2.1 x.2.2 hval i hb⟩

/-- **The Orchard integrity experiment.** Over the adversary's coins, the challenge table, and the
basis logs, the probability that the output Orchard ledger is valid and violates balance integrity
at some prefix `i < k` is at most
`ε_sinsemilladlr + ((ε_rel + 1/|F|) + ((qH+2)/|F| + ε_κ))`. This is the abstract integrity
experiment with the non-negativity side discharged at the Orchard instantiation: the three
Balance-subset arms collapse onto the single advantage `ε_sinsemilladlr` of computing a nontrivial
Sinsemilla discrete-log relation (`sampledBalanceSubsetArms_subset_orchardRelation`), replacing the
abstract `ε_nonneg` with one term and no factor of three. The conservation side is unchanged — the
two coin-consuming finders of the conservation experiment, whose Orchard discharge is separate. -/
theorem orchardBalanceIntegrityBefore_measure_le_experiment (p : PMF ι)
    (hne_idx : v_idx ≠ r_idx)
    {qH : ℕ} (hQ : ∀ j b, (LA j b).QueryBound qH)
    (halgLabel : ∀ (j : ι) (O : Q → Fq) (s : Fin m → Fq) (q : Q) (ℓ : QueryRep Fq m),
      (LA j (scalarBasis gen s)).findLabel O q = some ℓ →
      ∀ p ∈ (LA j (scalarBasis gen s)).run O,
        queryOf (toSig p.1.bindingSig).R
            (bvkAt m v_idx r_idx (primitives verify bverify) (scalarBasis gen s) p.1)
            p.1.sighash = q →
          (toSig p.1.bindingSig).R = representationEval (scalarBasis gen s) ℓ.commitment
          ∧ bvkAt m v_idx r_idx (primitives verify bverify) (scalarBasis gen s) p.1
            = representationEval (scalarBasis gen s) ℓ.key)
    (halgOut : ∀ (j : ι) (O : Q → Fq) (s : Fin m → Fq),
      ∀ p ∈ (LA j (scalarBasis gen s)).run O,
        (toSig p.1.bindingSig).R = representationEval (scalarBasis gen s) p.2.commitment
        ∧ bvkAt m v_idx r_idx (primitives verify bverify) (scalarBasis gen s) p.1
          = representationEval (scalarBasis gen s) p.2.key)
    (hr : (maxActions + 1) * (primitives verify bverify).valueBound
      ≤ CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD) (k : ℕ)
    {ε_sinsemilladlr ε_rel ε_κ : ℝ≥0∞}
    (hsin : (challengeExperiment m p).toOuterMeasure
      (sampledOrchardRelationEventUpTo verify bverify issuance maxActions m gen v_idx r_idx queryOf
        toSig LA k) ≤ ε_sinsemilladlr)
    (hdlRel : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen
      (fun b O => valueRelFinder m v_idx r_idx queryOf (primitives verify bverify) toSig hne_idx k
        (LA j) O b) ε_rel)
    (hdlκ : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen
      (fun b O => relFinder m r_idx
        (kappaComposite m v_idx r_idx queryOf (primitives verify bverify) toSig k (LA j)) O b) ε_κ) :
    (challengeExperiment m p).toOuterMeasure
        (sampledLedgerEvent m gen v_idx r_idx queryOf (primitives verify bverify) toSig LA
          (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding) (issuance := issuance)
            (maxActions := maxActions) k))
      ≤ ε_sinsemilladlr
        + ((ε_rel + 1 / Fintype.card Fq)
          + (((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card Fq + ε_κ)) :=
  balanceIntegrityBefore_measure_le_experiment m gen v_idx r_idx queryOf (primitives verify bverify)
    toSig p hne_idx hQ halgLabel halgOut hr k
    (le_trans (MeasureTheory.measure_mono
      (sampledBalanceSubsetArms_subset_orchardRelation verify bverify issuance maxActions m gen
        v_idx r_idx queryOf toSig LA k)) hsin)
    hdlRel hdlκ

end Zcash.Security.Ledger.Bridge
