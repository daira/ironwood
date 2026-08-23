import Zcash.Common.Oracle.LabeledOracleComp
import Zcash.Security.Ledger.ConservationExperiment
import Zcash.Security.Ledger.Capstone

/-!
# The integrity experiment: the non-negativity and conservation arms in one sample space

The `BalanceIntegrity` capstone bounds an integrity violation by
`εm + εnc + εkb + ε_conservation`, over an abstract `PMF (ValidAnnotated …)`, with each arm's
bound a named hypothesis (`balanceIntegrity_measure_le`). A violation is the shielded pool
going negative, or the pools failing to sum to the minted issuance, at some prefix `i < k`.
This module places that composition in the challenge-oracle model, over the *same* sample
space as the conservation experiment: the adversary's coins, the challenge table, and the
logs of the `m` presented bases.

The reduction layer is what lets the two sides share one sample space. The conservation side
runs on the sampled value and binding bases (`kappaPrimitivesAt`) and is discharged by the two
computable finders of the conservation experiment (the relation finder at `ε_rel + 1/|F|`, the
knowledge-error finder at `(qH+2)/|F| + ε_κ`). The non-negativity side's three arms (merkle,
note-commitment, key-binding) are deterministic reductions to breaks among primitives that
`kappaPrimitivesAt` leaves fixed, so they do not add a sample-space dimension: each is a named
bound `εm`/`εnc`/`εkb` on its Balance-subset arm event over this same space. At the Orchard
instantiation those three collapse to the single Sinsemilla discrete-log-relation advantage.

The composition is the capstone layer's own containment
(`balanceIntegrityViolationBefore_subset`): at each sample a violation lands in one of the
three non-negativity arms or in the transaction-balance premiss arm, and the latter splits into
the conservation relation and extraction-failure arms
(`txBalanceBreakEvent_fallible_subset`). A single union bound over the five shared arm events
gives `(εm + εnc + εkb) + ((ε_rel + 1/|F|) + ((qH+2)/|F| + ε_κ))`, with no factor of `k`.

Two abstractions keep the statements readable: `challengeExperiment` is the sample distribution,
and `sampledLedgerEvent` lifts a per-primitives ledger event to the samples on which the output
ledger is valid at the sampled primitives and lands in it.
-/

namespace Zcash.Security.Ledger.Model

open Zcash.Common Zcash.Security.BindingSignature Zcash.Security.RedDSA Zcash.Snark
open Zcash.Common.LabeledOracleComp
open scoped ENNReal

universe u

variable {r : ℕ} [Fact (Nat.Prime r)]
variable {G : Type*} [AddCommGroup G] [Module (ZMod r) G] [DecidableEq G]
  [NoZeroSMulDivisors (ZMod r) G]
variable {Q : Type u} [Fintype Q] [DecidableEq Q] [Inhabited Q]
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}
  [DecidableEq RHO] [DecidableEq PSI] [DecidableEq MHASH] [DecidableEq MENC] [DecidableEq NK]
variable (m : ℕ)

variable (gen : G) (v_idx r_idx : Fin m) (queryOf : G → G → MSG → Q)
  (P₀ : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG)
  (toSig : SIG → RedDSA.Sig (ZMod r) G)
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- **The integrity experiment.** Over the adversary's coins, the challenge table, and the
basis logs, the probability that the output ledger is valid and violates balance integrity at
some prefix `i < k`, at the sampled primitives, is at most
`(εm + εnc + εkb) + ((ε_rel + 1/|F|) + ((qH+2)/|F| + ε_κ))`. A violation is the shielded pool
going negative, or the pools failing to sum to the minted issuance. The three non-negativity
arms are named bounds over this same space. The two conservation arms are the coin-consuming
finders. -/
theorem balanceIntegrityBefore_measure_le_experiment {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    (hne_idx : v_idx ≠ r_idx)
    {qH : ℕ} (hQ : ∀ j b, (LA j b).QueryBound qH)
    (halgLabel : ∀ (j : ι) (O : Q → ZMod r) (s : Fin m → ZMod r) (q : Q)
      (ℓ : QueryRep (ZMod r) m),
      (LA j (scalarBasis gen s)).findLabel O q = some ℓ →
      ∀ p ∈ (LA j (scalarBasis gen s)).run O,
        queryOf (toSig p.1.bindingSig).R (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1)
            p.1.sighash = q →
          (toSig p.1.bindingSig).R = representationEval (scalarBasis gen s) ℓ.commitment
          ∧ bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1
            = representationEval (scalarBasis gen s) ℓ.key)
    (halgOut : ∀ (j : ι) (O : Q → ZMod r) (s : Fin m → ZMod r),
      ∀ p ∈ (LA j (scalarBasis gen s)).run O,
        (toSig p.1.bindingSig).R = representationEval (scalarBasis gen s) p.2.commitment
        ∧ bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1
          = representationEval (scalarBasis gen s) p.2.key)
    (hr : (maxActions + 1) * P₀.valueBound ≤ r) (k : ℕ) {εm εnc εkb ε_rel ε_κ : ℝ≥0∞}
    (hm : (challengeExperiment m p).toOuterMeasure
        (sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (fun P => balanceSubsetBreakEventUpTo (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k .merkle)) ≤ εm)
    (hnc : (challengeExperiment m p).toOuterMeasure
        (sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (fun P => balanceSubsetBreakEventUpTo (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k .noteCommit)) ≤ εnc)
    (hkb : (challengeExperiment m p).toOuterMeasure
        (sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (fun P => balanceSubsetBreakEventUpTo (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k .keyBinding)) ≤ εkb)
    (hdlRel : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen
      (fun b O => valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) O b) ε_rel)
    (hdlκ : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen
      (fun b O => relFinder m r_idx
        (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j)) O b) ε_κ) :
    (challengeExperiment m p).toOuterMeasure
        (sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (fun P => balanceIntegrityViolationBefore (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k))
      ≤ (εm + εnc + εkb)
        + ((ε_rel + 1 / Fintype.card (ZMod r))
          + (((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) + ε_κ)) := by
  have hcons := balanceConservationBefore_measure_le_experiment m gen v_idx r_idx queryOf P₀
    toSig (kv := kv) (issuance := issuance) (maxActions := maxActions)
    p hne_idx hQ halgLabel halgOut hr k hdlRel hdlκ
  refine le_trans (MeasureTheory.measure_mono
    (sampledLedgerEvent_mono m gen v_idx r_idx queryOf P₀ toSig LA
      fun P => balanceIntegrityViolationBefore_subset_conservation
        (P := P) (kv := kv) (issuance := issuance) (maxActions := maxActions) k)) ?_
  simp only [sampledLedgerEvent_union]
  exact le_trans (toOuterMeasure_le_add₂ _ Set.Subset.rfl)
    (add_le_add
      (le_trans (toOuterMeasure_le_add₃ _ Set.Subset.rfl) (add_le_add (add_le_add hm hnc) hkb))
      hcons)

end Zcash.Security.Ledger.Model
