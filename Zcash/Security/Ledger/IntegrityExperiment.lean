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
runs on the sampled value and binding bases (`kappaPrimitivesAt`) and is discharged wholesale by
the conservation experiment (its two computable finders — the relation finder at `ε_rel + 1/|F|`,
the knowledge-error finder at `(qH+2)/|F| + ε_κ`). The non-negativity side's three arms (merkle,
note-commitment, key-binding) are deterministic reductions to breaks among primitives that
`kappaPrimitivesAt` leaves fixed, so they do not add a sample-space dimension: the experiment
takes their union as one named bound `ε_nonneg` over this same space. At the Orchard instantiation
that collapses to the single Sinsemilla discrete-log-relation advantage.

The composition is the capstone layer's own per-primitives containment
(`balanceIntegrityViolationBefore_subset_conservation`): at each sample a violation lands in one
of the three non-negativity arms or in the conservation violation itself. That set-level
containment lifts to the sample space through the `sampledLedgerEvent` join-homomorphism
(`sampledBalanceIntegrity_subset`, which is monotone and preserves unions), and a union bound
over the two lifted events gives `ε_nonneg + ((ε_rel + 1/|F|) + ((qH+2)/|F| + ε_κ))`, with no
factor of `k`.

Two abstractions keep the statements readable: `challengeExperiment` is the sample distribution,
and `sampledLedgerEvent` lifts a per-primitives ledger event to the samples on which the output
ledger is valid at the sampled primitives and lands in it — a monotone join-homomorphism, which
is what makes the containment lift in one step.
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

omit [Fintype Q] [DecidableEq Q] [Inhabited Q] in
/-- **The challenge-experiment integrity containment.** The samples on which the output ledger
is valid and violates balance integrity are contained in the lift of the union of the three
non-negativity arms — merkle, note-commitment, key-binding — together with the lifted
conservation violation. This is the capstone layer's per-primitives
`balanceIntegrityViolationBefore_subset_conservation` lifted through the `sampledLedgerEvent`
join-homomorphism (`sampledLedgerEvent_mono` then `sampledLedgerEvent_union`). -/
theorem sampledBalanceIntegrity_subset {ι : Type u}
    (LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (k : ℕ) :
    sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
        (fun P => balanceIntegrityViolationBefore (P := P) (kv := kv) (issuance := issuance)
          (maxActions := maxActions) k)
      ⊆ sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (fun P => balanceSubsetBreakEventUpTo (P := P) (kv := kv) (issuance := issuance)
              (maxActions := maxActions) k .merkle
            ∪ balanceSubsetBreakEventUpTo (P := P) (kv := kv) (issuance := issuance)
              (maxActions := maxActions) k .noteCommit
            ∪ balanceSubsetBreakEventUpTo (P := P) (kv := kv) (issuance := issuance)
              (maxActions := maxActions) k .keyBinding)
        ∪ sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (fun P => balanceConservationViolationBefore (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k) :=
  (sampledLedgerEvent_mono m gen v_idx r_idx queryOf P₀ toSig LA
    fun P => balanceIntegrityViolationBefore_subset_conservation (P := P) (kv := kv)
      (issuance := issuance) (maxActions := maxActions) k).trans
    (sampledLedgerEvent_union m gen v_idx r_idx queryOf P₀ toSig LA
      _
      (fun P => balanceConservationViolationBefore (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) k)).le

/-- **The integrity experiment.** Over the adversary's coins, the challenge table, and the
basis logs, the probability that the output ledger is valid and violates balance integrity at
some prefix `i < k`, at the sampled primitives, is at most
`ε_nonneg + ((ε_rel + 1/|F|) + ((qH+2)/|F| + ε_κ))`. A violation is the shielded pool going
negative, or the pools failing to sum to the minted issuance. The non-negativity side is one
named bound on the combined arm event over this same space; the two conservation arms are the
coin-consuming finders. -/
theorem balanceIntegrityBefore_measure_le_experiment {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    (hne_idx : v_idx ≠ r_idx)
    {qH : ℕ} (hQ : ∀ j b, (LA j b).QueryBound qH)
    (halg : ∀ j : ι, AlgebraicAtBindingPoints m gen v_idx r_idx queryOf P₀ toSig (LA j))
    (hr : (maxActions + 1) * P₀.valueBound ≤ r) (k : ℕ) {ε_nonneg ε_rel ε_κ : ℝ≥0∞}
    (hnn : (challengeExperiment m p).toOuterMeasure
        (sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (fun P => balanceSubsetBreakEventUpTo (P := P) (kv := kv) (issuance := issuance)
              (maxActions := maxActions) k .merkle
            ∪ balanceSubsetBreakEventUpTo (P := P) (kv := kv) (issuance := issuance)
              (maxActions := maxActions) k .noteCommit
            ∪ balanceSubsetBreakEventUpTo (P := P) (kv := kv) (issuance := issuance)
              (maxActions := maxActions) k .keyBinding)) ≤ ε_nonneg)
    (hdlRel : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen
      (fun b O => valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) O b) ε_rel)
    (hdlκ : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen
      (fun b O => relFinder m r_idx
        (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j)) O b) ε_κ) :
    (challengeExperiment m p).toOuterMeasure
        (sampledLedgerEvent m gen v_idx r_idx queryOf P₀ toSig LA
          (fun P => balanceIntegrityViolationBefore (P := P) (kv := kv) (issuance := issuance)
            (maxActions := maxActions) k))
      ≤ ε_nonneg
        + ((ε_rel + 1 / Fintype.card (ZMod r))
          + (((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) + ε_κ)) := by
  have hcons := balanceConservationBefore_measure_le_experiment m gen v_idx r_idx queryOf P₀
    toSig (kv := kv) (issuance := issuance) (maxActions := maxActions)
    p hne_idx hQ halg hr k hdlRel hdlκ
  exact le_trans
    (toOuterMeasure_le_add₂ _
      (sampledBalanceIntegrity_subset m gen v_idx r_idx queryOf P₀ toSig LA k))
    (add_le_add hnn hcons)

end Zcash.Security.Ledger.Model
