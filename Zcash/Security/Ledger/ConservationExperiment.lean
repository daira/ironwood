import Zcash.Common.Oracle.LabeledOracleComp
import Zcash.Security.Ledger.ValueRelationArm

/-!
# The conservation experiment: both arms in one sample space

The capstones bound the conservation and cap violations by `εdlr + κ`, over an abstract
`PMF (ValidAnnotated …)` with the two arms' bounds as named hypotheses. This module
instantiates that composition in the challenge-oracle model, in one experiment: over the
adversary's coins, the challenge table, and the logs of the `m` presented bases, the
probability that the output ledger is valid *and* violates conservation (or the cap) at some
prefix `i < k` is at most `(ε_rel + 1/|F|) + ((qH+2)/|F| + ε_κ)`.

The composition is the capstone layer's own: at each sample, a violation lands in the
transaction-balance premiss's relation arm or its extraction-failure arm
(`balanceConservationViolationBefore_subset_fallible`), and each arm's measure is the bound
already proved for it — the relation arm at `ε_rel + 1/|F|`
(`balanceConservationBefore_valueRelationArm_measure_le`) and the extraction-failure arm at
`(qH+2)/|F| + ε_κ` (`balanceConservationBefore_extractFailArm_measure_le_of_coins`, the
coins form proved here). Both discrete-log hypotheses are single bounds for coin-consuming
finders (`TextbookDLWithCoinsAdvantageLE` at `ρ` := the challenge table), quantified only
over the adversary's coins: no supremum over challenge tables remains anywhere in the
experiment.
-/

namespace Zcash.Security.Ledger.Model

open Zcash.Common Zcash.Security.BindingSignature Zcash.Security.RedDSA Zcash.Snark
open Zcash.Common.LabeledOracleComp
open scoped ENNReal

universe u

variable {r : ℕ} [Fact (Nat.Prime r)]
variable {G : Type*} [AddCommGroup G] [Module (ZMod r) G] [DecidableEq G]
variable {Q : Type u} [Fintype Q] [DecidableEq Q] [Inhabited Q]
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}
variable (m : ℕ)

variable (gen : G) (v_idx r_idx : Fin m) (queryOf : G → G → MSG → Q)
  (P₀ : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG)
  (toSig : SIG → RedDSA.Sig (ZMod r) G)
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- **The all-prefixes extraction-failure arm, with a single randomized reduction.** As
`balanceConservationBefore_extractFailArm_measure_le`, with the per-table DL hypothesis
replaced by one bound for the coin-consuming relation finder, per adversary coin. -/
theorem balanceConservationBefore_extractFailArm_measure_le_of_coins {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
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
    (hr : (maxActions + 1) * P₀.valueBound ≤ r) (k : ℕ) {ε : ℝ≥0∞}
    (hdl : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen
      (fun b O => relFinder m r_idx
        (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j)) O b) ε) :
    ((p.bind fun j =>
        (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).map (Prod.mk j))).toOuterMeasure
        (setOf fun (x : ι × ((Q → ZMod r) × (Fin m → ZMod r))) =>
          ∃ hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
              kv issuance maxActions
              (((LA x.1 (scalarBasis gen x.2.2)).run x.2.1).map Prod.fst),
            ∃ i, i < k ∧ ∃ e, balanceConservationOrBreak (issuance := issuance)
                (fun tx htx => (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
                  |>.premissOrBreakFallible
                    (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
                    hval hr
                    (kappaExtractor m gen r_idx queryOf P₀ k (LA x.1) x.2.1 x.2.2)
                    tx htx) i
              = .inr (.inr e))
      ≤ ((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) + ε := by
  refine Zcash.Security.KeyBinding.toOuterMeasure_bind_le _ _ _ fun j => ?_
  rw [PMF.toOuterMeasure_map_apply]
  refine le_trans (le_trans (MeasureTheory.measure_mono ?hsub)
    (kappaEvent_measure_le_of_coins m gen r_idx
      (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j))
      (fun s => kappaComposite_queryBound m v_idx r_idx queryOf P₀ toSig (hQ j _))
      (hdl j))) (le_of_eq ?heq)
  case heq =>
    rw [add_comm ε, ← add_assoc, ENNReal.div_add_div_same]
    norm_cast
  rintro ⟨O, s⟩ ⟨hval, i, hik, e, heq⟩
  dsimp only at hval heq
  exact extractFail_mem_kappaEvent m gen v_idx r_idx queryOf P₀ toSig
    (halgLabel j) (halgOut j) hr (le_of_lt hik) hval heq

/-- **The conservation experiment.** Over the adversary's coins, the challenge table, and the
basis logs, the probability that the output ledger is valid and violates balance conservation
at some prefix `i < k` — the capstone's `balanceConservationViolationBefore`, at the sampled
primitives — is at most `(ε_rel + 1/|F|) + ((qH+2)/|F| + ε_κ)`. The two discrete-log
hypotheses are single bounds for the coin-consuming finders, per adversary coin. -/
theorem balanceConservationBefore_measure_le_experiment {ι : Type u} (p : PMF ι)
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
    (hr : (maxActions + 1) * P₀.valueBound ≤ r) (k : ℕ) {ε_rel ε_κ : ℝ≥0∞}
    (hdlRel : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen
      (fun b O => valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) O b) ε_rel)
    (hdlκ : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen
      (fun b O => relFinder m r_idx
        (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j)) O b) ε_κ) :
    ((p.bind fun j =>
        (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).map (Prod.mk j))).toOuterMeasure
        (setOf fun (x : ι × ((Q → ZMod r) × (Fin m → ZMod r))) =>
          ∃ hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
              kv issuance maxActions
              (((LA x.1 (scalarBasis gen x.2.2)).run x.2.1).map Prod.fst),
            (⟨_, hval⟩ : ValidAnnotated (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig
                x.2.1 x.2.2) kv issuance maxActions)
              ∈ balanceConservationViolationBefore (P := kappaPrimitivesAt m gen v_idx r_idx
                  queryOf P₀ toSig x.2.1 x.2.2) (kv := kv) (issuance := issuance)
                  (maxActions := maxActions) k)
      ≤ (ε_rel + 1 / Fintype.card (ZMod r))
        + (((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) + ε_κ) := by
  have hrel := balanceConservationBefore_valueRelationArm_measure_le m gen v_idx r_idx
    queryOf P₀ toSig (kv := kv) (issuance := issuance) (maxActions := maxActions)
    p hne_idx hr k hdlRel
  have hκ := balanceConservationBefore_extractFailArm_measure_le_of_coins m gen v_idx r_idx
    queryOf P₀ toSig (kv := kv) (issuance := issuance) p hQ halgLabel halgOut hr k hdlκ
  refine le_trans (MeasureTheory.measure_mono ?_)
    (le_trans (MeasureTheory.measure_union_le _ _) (add_le_add hrel hκ))
  rintro ⟨j, O, s⟩ ⟨hval, hviol⟩
  rcases balanceConservationViolationBefore_subset_fallible
      (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig O s)
      (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig O s) hr
      (kappaExtractor m gen r_idx queryOf P₀ k (LA j) O s) k hviol
    with ⟨i, hik, w, hw⟩ | ⟨i, hik, e, he⟩
  · exact Or.inl ⟨hval, i, hik, w, hw⟩
  · exact Or.inr ⟨hval, i, hik, e, he⟩

/-- **The cap experiment.** As `balanceConservationBefore_measure_le_experiment`, for the
shielded pool exceeding the minted issuance at some prefix `i < k`. -/
theorem shieldedBalanceCapBefore_measure_le_experiment {ι : Type u} (p : PMF ι)
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
    (hr : (maxActions + 1) * P₀.valueBound ≤ r) (k : ℕ) {ε_rel ε_κ : ℝ≥0∞}
    (hdlRel : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen
      (fun b O => valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) O b) ε_rel)
    (hdlκ : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen
      (fun b O => relFinder m r_idx
        (kappaComposite m v_idx r_idx queryOf P₀ toSig k (LA j)) O b) ε_κ) :
    ((p.bind fun j =>
        (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).map (Prod.mk j))).toOuterMeasure
        (setOf fun (x : ι × ((Q → ZMod r) × (Fin m → ZMod r))) =>
          ∃ hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
              kv issuance maxActions
              (((LA x.1 (scalarBasis gen x.2.2)).run x.2.1).map Prod.fst),
            (⟨_, hval⟩ : ValidAnnotated (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig
                x.2.1 x.2.2) kv issuance maxActions)
              ∈ shieldedBalanceCapViolationBefore (P := kappaPrimitivesAt m gen v_idx r_idx
                  queryOf P₀ toSig x.2.1 x.2.2) (kv := kv) (issuance := issuance)
                  (maxActions := maxActions) k)
      ≤ (ε_rel + 1 / Fintype.card (ZMod r))
        + (((qH + 2 : ℕ) : ℝ≥0∞) / Fintype.card (ZMod r) + ε_κ) := by
  have hrel := balanceConservationBefore_valueRelationArm_measure_le m gen v_idx r_idx
    queryOf P₀ toSig (kv := kv) (issuance := issuance) (maxActions := maxActions)
    p hne_idx hr k hdlRel
  have hκ := balanceConservationBefore_extractFailArm_measure_le_of_coins m gen v_idx r_idx
    queryOf P₀ toSig (kv := kv) (issuance := issuance) p hQ halgLabel halgOut hr k hdlκ
  refine le_trans (MeasureTheory.measure_mono ?_)
    (le_trans (MeasureTheory.measure_union_le _ _) (add_le_add hrel hκ))
  rintro ⟨j, O, s⟩ ⟨hval, hviol⟩
  rcases shieldedBalanceCapViolationBefore_subset_fallible
      (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig O s)
      (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig O s) hr
      (kappaExtractor m gen r_idx queryOf P₀ k (LA j) O s) k hviol
    with ⟨i, hik, w, hw⟩ | ⟨i, hik, e, he⟩
  · exact Or.inl ⟨hval, i, hik, w, hw⟩
  · exact Or.inr ⟨hval, i, hik, e, he⟩

end Zcash.Security.Ledger.Model
