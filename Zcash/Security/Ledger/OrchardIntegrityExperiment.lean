import Zcash.Security.Ledger.IntegrityExperiment
import Zcash.Security.Ledger.OrchardCapstone
import Zcash.Security.BindingSignature.Orchard

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
through its combined coin-consuming finder.
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
  (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
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
      (primitives spendAuthVerify bindingVerify) toSig O s)) :
    NoteCommitBreak (primitives spendAuthVerify bindingVerify) :=
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
        (primitives spendAuthVerify bindingVerify) toSig O s) keyBinding issuance maxActions ledger) (i : ℕ) :
    (nonZeroSpends ledger (i + 1) ≤ ↑(positionedOutputs ledger i)) ⊕' OrchardBalanceRelation :=
  match balanceSubsetOrBreak hval i with
  | .inl hsub => .inl hsub
  | .inr (.keyBinding _ _ h) => .inr (.keyBinding (relationOfKeyBindingBreak h))
  | .inr (.noteCommit nb) => .inr (.noteCommit (relationOfNoteCommitBreak spendAuthVerify bindingVerify
      (noteCommitBreakOfKappa spendAuthVerify bindingVerify m gen v_idx r_idx queryOf toSig O s nb)))
  | .inr (.merkle c) => .inr (.merkle (relationOfMerkleCollision c.2))

omit [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- A Balance-subset break at the sampled primitives computes an Orchard Sinsemilla relation: the
total reduction cannot return the containment when handed a break, so it returns a relation. -/
theorem kappaOrchardBalanceSubsetOrRelation_inr_of_break (O : Q → Fq) (s : Fin m → Fq)
    {ledger : Ledger _ Fq PallasGroup Fp Fp Fp Encoding MSG SIG _}
    (hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf
        (primitives spendAuthVerify bindingVerify) toSig O s) keyBinding issuance maxActions ledger) (i : ℕ)
    {b : BalanceBreak (kappaPrimitivesAt m gen v_idx r_idx queryOf
        (primitives spendAuthVerify bindingVerify) toSig O s) keyBinding}
    (hb : balanceSubsetOrBreak hval i = .inr b) :
    ∃ rel, kappaOrchardBalanceSubsetOrRelation spendAuthVerify bindingVerify issuance maxActions m gen v_idx r_idx
      queryOf toSig O s hval i = .inr rel := by
  unfold kappaOrchardBalanceSubsetOrRelation
  rw [hb]
  cases b <;> exact ⟨_, rfl⟩

variable {ι : Type u}
  (LA : ι → (Fin m → PallasGroup) → LabeledOracleComp Q Fq (fun _ => QueryRep Fq m)
    (List (Tx (KeyBinding.Pool.Witness Fq PallasGroup Fp) Fq PallasGroup Fp Fp Fp Encoding MSG SIG
      (primitives spendAuthVerify bindingVerify).depth × QueryRep Fq m)))

/-- **The sampled Orchard Sinsemilla-relation event.** The samples on which the output ledger is
valid at the sampled primitives and its data computes a nontrivial discrete-log relation among the
fixed Sinsemilla bases at some step `i < k`. This is the challenge-experiment analogue of the
deployed capstone's `orchardRelationEventUpTo`; the single advantage `ε_sinsemilladlr` is a bound on
this one event. -/
def sampledOrchardRelationEventUpTo (k : ℕ) :
    Set (ι × ((Q → Fq) × (Fin m → Fq))) :=
  setOf fun x =>
    ∃ hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf
        (primitives spendAuthVerify bindingVerify) toSig x.2.1 x.2.2) keyBinding issuance maxActions
        (((LA x.1 (scalarBasis gen x.2.2)).run x.2.1).map Prod.fst),
      ∃ i, i < k ∧ ∃ rel, kappaOrchardBalanceSubsetOrRelation spendAuthVerify bindingVerify issuance maxActions
        m gen v_idx r_idx queryOf toSig x.2.1 x.2.2 hval i = .inr rel

omit [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- **The three sampled non-negativity arms collapse onto the Sinsemilla-relation event.** Every
sample on which the reduction lands in the merkle, note-commitment, or key-binding arm computes a
nontrivial discrete-log relation among the fixed Sinsemilla bases: the arm's break is routed through
its deterministic Orchard reducer (`kappaOrchardBalanceSubsetOrRelation`). This is what discharges
the abstract experiment's combined `ε_nonneg` by the single `ε_sinsemilladlr` at the Orchard
instantiation. -/
theorem sampledBalanceSubsetArms_subset_orchardRelation (k : ℕ) :
    sampledLedgerEvent m gen v_idx r_idx queryOf (primitives spendAuthVerify bindingVerify) toSig LA
        (fun P => balanceSubsetBreakEventUpTo (P := P) (kv := keyBinding) (issuance := issuance)
            (maxActions := maxActions) k .merkle
          ∪ balanceSubsetBreakEventUpTo (P := P) (kv := keyBinding) (issuance := issuance)
            (maxActions := maxActions) k .noteCommit
          ∪ balanceSubsetBreakEventUpTo (P := P) (kv := keyBinding) (issuance := issuance)
            (maxActions := maxActions) k .keyBinding)
      ⊆ sampledOrchardRelationEventUpTo spendAuthVerify bindingVerify issuance maxActions m gen v_idx r_idx
          queryOf toSig LA k := by
  rintro x ⟨hval, harm⟩
  refine ⟨hval, ?_⟩
  obtain ⟨i, hik, b, hb⟩ : ∃ i, i < k ∧ ∃ b, balanceSubsetOrBreak hval i = .inr b := by
    rcases harm with (⟨i, hik, b, hb, -⟩ | ⟨i, hik, b, hb, -⟩) | ⟨i, hik, b, hb, -⟩ <;>
      exact ⟨i, hik, b, hb⟩
  exact ⟨i, hik, kappaOrchardBalanceSubsetOrRelation_inr_of_break spendAuthVerify bindingVerify issuance
    maxActions m gen v_idx r_idx queryOf toSig x.2.1 x.2.2 hval i hb⟩

/-- **The Orchard integrity experiment.** Over the adversary's coins, the challenge table, and the
basis logs, the probability that the output Orchard ledger is valid and violates balance integrity
at some prefix `i < k` is at most `ε_sinsemilladlr + (ε_dl + (qH+2)/#F)`. This is the abstract
integrity experiment with the non-negativity side discharged at the Orchard instantiation: the
three Balance-subset arms collapse onto the single advantage `ε_sinsemilladlr` of computing a
nontrivial Sinsemilla discrete-log relation (`sampledBalanceSubsetArms_subset_orchardRelation`),
replacing the abstract `ε_nonneg` with one term and no factor of three. The conservation side is
the abstract experiment's combined coin-consuming finder, so the whole bound carries one
discrete-log advantage per side: `ε_sinsemilladlr` among the fixed Sinsemilla bases, `ε_dl` at the
sampled value-commitment bases. -/
theorem orchardBalanceIntegrityBefore_measure_le_experiment (p : PMF ι)
    (hne_idx : v_idx ≠ r_idx)
    {qH : ℕ} (hQ : ∀ j b, (LA j b).QueryBound qH)
    (halg : ∀ j : ι, AlgebraicAtBindingPoints m gen v_idx r_idx queryOf
      (primitives spendAuthVerify bindingVerify) toSig (LA j))
    (hr : maxActions * ((primitives spendAuthVerify bindingVerify).valueBound - 1)
        + (primitives spendAuthVerify bindingVerify).vBalanceBound
      < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD) (k : ℕ)
    {ε_sinsemilladlr ε_dl : ℝ≥0∞}
    (hsin : (challengeExperiment m p).toOuterMeasure
      (sampledOrchardRelationEventUpTo spendAuthVerify bindingVerify issuance maxActions m gen v_idx r_idx queryOf
        toSig LA k) ≤ ε_sinsemilladlr)
    (hdl : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen (fun b O =>
      conservationRelFinder m v_idx r_idx queryOf (primitives spendAuthVerify bindingVerify) toSig hne_idx k
        (LA j) O b) ε_dl) :
    (challengeExperiment m p).toOuterMeasure
        (sampledLedgerEvent m gen v_idx r_idx queryOf (primitives spendAuthVerify bindingVerify) toSig LA
          (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding) (issuance := issuance)
            (maxActions := maxActions) k))
      ≤ ε_sinsemilladlr + (ε_dl + ((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card Fq) :=
  balanceIntegrityBefore_measure_le_experiment m gen v_idx r_idx queryOf (primitives spendAuthVerify bindingVerify)
    toSig p hne_idx hQ halg hr k
    (le_trans (MeasureTheory.measure_mono
      (sampledBalanceSubsetArms_subset_orchardRelation spendAuthVerify bindingVerify issuance maxActions m gen
        v_idx r_idx queryOf toSig LA k)) hsin)
    hdl

end Zcash.Security.Ledger.Bridge

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Common Zcash.Security.BindingSignature Zcash.Security.RedDSA
open Zcash.Common.LabeledOracleComp
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Pool
open Zcash.Security.Ledger.Model
open scoped ENNReal

universe v

/-- The deployed challenge-query type: the literal triple the challenge hash consumes — the
signature's nonce `R`, the binding verification key `bvk`, and the sighash. Finite because
the Pallas group's affine representation is a computable finite enumeration. -/
abbrev OrchardQuery (MSG : Type v) : Type v := PallasGroup × PallasGroup × MSG

/-- The deployed challenge-query encoding: the identity triple. `queryOf`'s intended
injectivity (collisions only shrink the covered adversary class) is discharged here with no
collisions at all (`orchardQueryOf_injective`). -/
def orchardQueryOf {MSG : Type v} (R bvk : PallasGroup) (msg : MSG) : OrchardQuery MSG :=
  (R, bvk, msg)

/-- The identity triple is injective, so distinct binding-signature points query distinct
challenges. -/
theorem orchardQueryOf_injective {MSG : Type v} {R R' bvk bvk' : PallasGroup} {m m' : MSG}
    (h : orchardQueryOf R bvk m = orchardQueryOf R' bvk' m') :
    R = R' ∧ bvk = bvk' ∧ m = m' := by
  simpa [orchardQueryOf, Prod.ext_iff] using h

/-- The deployed discrete-log base: the standard Pallas generator. -/
def pallasGen : PallasGroup := ⟨CompElliptic.Curves.Pasta.Pallas.Gpt⟩

/-- The deployed discrete-log base is not the identity, so the textbook game at it is a
hardness claim rather than the degenerate zero-base game. -/
theorem pallasGen_ne_zero : pallasGen ≠ 0 := by decide

/-- **The Orchard integrity experiment at the deployed parameters.** The experiment's
apparatus is pinned at its deployed choices: two presented bases standing for the
value-commitment pair (slots `0` and `1`), the standard Pallas generator as the discrete-log
base, the challenge query as the literal `(R, bvk, sighash)` triple, signatures decoded as
themselves, and binding verification as actual RedPallas at ℛ^Orchard
(`redPallasBindingVerify`) — Balance uses its extractability, not its unforgeability. Only
the challenge hash `H_bind`, the sighash algorithm, and the spend-authorization predicate
are left unspecified.

Every remaining hypothesis is a resource parameter, a documented idealization, or justified
by consensus rules. The query budget `qH` is the adversary's oracle resource, priced in the
bound. Algebraicity at the binding points is the model restriction documented at
`AlgebraicAtBindingPoints`. The action cap `maxActions < 2^16` is the dedicated consensus
rule on the action count —`nActionsOrchard` and `nActionsIronwood` are each less than `2^16`
(§7.1.2, <https://zips.z.cash/protocol/protocol.pdf#txnconsensus>), so the result applies to
either Orchard-protocol pool— and `orchard_ledger_no_overflow` turns it into no-overflow
against the Pallas scalar order. The two advantages are named bounds for exhibited machines —the
Sinsemilla discrete-log relation for non-negativity, the combined finder's textbook discrete
log for conservation— not hardness premisses. The idealizations:

* the experiment models the RedPallas binding challenge hash as a random oracle: the sampled
  binding verification is the Schnorr equation with its challenge read off the uniform
  table, in place of `H_bind`;
* validity is at the sampled value and binding bases, and the reference-string heuristic
  carries the presented random bases to the deployed `𝒱^Orchard`, `ℛ^Orchard`;
* byte encodings are elided, as at the RedDSA abstraction boundary;
* nothing is assumed of the sighash algorithm or of the spend-authorization predicate
  `spendAuthVerify`, which stays universally quantified — Balance does not need the sighash to
  commit to the transaction effects; Spendability and Spend authority do. -/
theorem orchardBalanceIntegrityBefore_measure_le_experiment_deployed
    {MSG : Type} [Fintype MSG] [DecidableEq MSG] [Inhabited MSG]
    (spendAuthVerify : PallasGroup → MSG → RedDSA.Sig Fq PallasGroup → Prop)
    (H_bind : PallasGroup → PallasGroup → MSG → Fq)
    (issuance : ℕ → ℕ) (maxActions : ℕ)
    {ι : Type} (p : PMF ι)
    (LA : ι → (Fin 2 → PallasGroup) → LabeledOracleComp (OrchardQuery MSG) Fq
      (fun _ => QueryRep Fq 2)
      (List (Tx (KeyBinding.Pool.Witness Fq PallasGroup Fp) Fq PallasGroup Fp Fp Fp Encoding
        MSG (RedDSA.Sig Fq PallasGroup)
        (primitives spendAuthVerify (redPallasBindingVerify H_bind)).depth × QueryRep Fq 2)))
    {qH : ℕ} (hQ : ∀ j b, (LA j b).QueryBound qH)
    (halg : ∀ j : ι, AlgebraicAtBindingPoints 2 pallasGen 0 1 orchardQueryOf
      (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id (LA j))
    (hmax : maxActions < 2^16) (k : ℕ) {ε_sinsemilladlr ε_dl : ℝ≥0∞}
    (hsin : (challengeExperiment 2 p).toOuterMeasure
      (sampledOrchardRelationEventUpTo spendAuthVerify (redPallasBindingVerify H_bind) issuance
        maxActions 2 pallasGen 0 1 orchardQueryOf id LA k) ≤ ε_sinsemilladlr)
    (hdl : ∀ j : ι, TextbookDLWithCoinsAdvantageLE pallasGen (fun b O =>
      conservationRelFinder 2 0 1 orchardQueryOf
        (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id
        (by decide) k (LA j) O b) ε_dl) :
    (challengeExperiment 2 p).toOuterMeasure
        (sampledLedgerEvent 2 pallasGen 0 1 orchardQueryOf
          (primitives spendAuthVerify (redPallasBindingVerify H_bind)) id LA
          (fun P => balanceIntegrityViolationBefore (P := P) (kv := keyBinding)
            (issuance := issuance) (maxActions := maxActions) k))
      ≤ ε_sinsemilladlr + (ε_dl + ((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card Fq) :=
  orchardBalanceIntegrityBefore_measure_le_experiment spendAuthVerify (redPallasBindingVerify H_bind)
    issuance maxActions 2 pallasGen 0 1 orchardQueryOf id LA p (by decide) hQ halg
    (orchard_ledger_no_overflow hmax) k hsin hdl

end Zcash.Security.Ledger.Bridge
