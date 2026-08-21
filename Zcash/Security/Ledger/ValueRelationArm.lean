import Mathlib.Tactic.Ring
import Zcash.Common.Oracle.LabeledOracleComp
import Zcash.Security.Ledger.ExtractionKappaArm
import Zcash.Security.BindingSignature.DiscreteLog
import Zcash.Common.RelationProbabilityCoins

/-!
# The conservation relation arm, discharged in the oracle model

A transaction's binding verification key reads two ways. Linearly in the witnessed bundle it is
`bvk = A • 𝒱 + B • ℛ`, with `A` the integer value imbalance and `B` the net commitment randomness
(`bindingVK_decomp`). When the extractor pins the binding key it is `bvk = bsk • ℛ`. On a
transaction that does not balance, so `A ≠ 0`, the two readings subtract to

    A • 𝒱 + (B − bsk) • ℛ = 0,

a nontrivial `(𝒱, ℛ)` relation. This module prices the samples where that happens.

For any labeled ledger adversary, the probability that the output ledger is valid *and* the
conservation reduction computes such a relation is at most `ε_DL + 1/|F|`
(`relationWithCoins_prob_le_of_textbookDL`). No query budget appears: the arm's witness is
oracle-free data, so there is no bad-challenge accounting. This is the easier sibling of the
extraction-failure arm in `Ledger/ExtractionKappaArm.lean`, over the same experiment, and it
discharges the `εdlr` the capstone layer leaves named.

## The reduction

The relation branch fires at the prefix's first imbalanced transaction, where the extractor pins
its binding key (`ValueRelationSelection`, computed from the reduction hypothesis as in the
extraction-failure arm). The finder (`valueRelFinder`) replays the adversary at the presented
basis, selects that transaction (`failTxOfAnn`), recomputes the extractor's value from the run's
own data, and rebuilds the relation behind three decidable guards: `A ≠ 0`, the no-overflow bound
`|A| < r`, and the binding-key equation. All three are decidable, so the finder needs no validity
proof; on a sample in the event they pass, because validity supplies the same facts the reduction
derived. The relation is placed in the generic AGM witness type at the two value-commitment slots
of the presented basis (`toAlgebraicRelationWitnessAt`), which is where the distinctness
hypothesis `v_idx ≠ r_idx` is consumed.

The discrete-log premiss is the coins form: the reduction samples the challenge table as its own
coins (`TextbookDLWithCoinsAdvantageLE` at `ρ := Q → F`), so one bound for one randomized finder
replaces a supremum over challenge tables.
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

section Identification

variable {P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}
variable {ledger : Ledger KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}

/-- The relation arm's selection, identified with the searched list's first imbalanced
transaction: `find?` selects `tx`, and the extractor pins its binding key. Computed data, in
the breaks-as-computed-data style. -/
structure ValueRelationSelection {S : ValueShape P} (B : BindingSigShape P S)
    (E : RedDSA.Extractor (ZMod r) G MSG)
    (L : List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth)) where
  tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth
  find : L.find? (fun tx => decide (txNetValue tx ≠ tx.vBalance)) = some tx
  extract_eq : tx.bvk P = E (tx.bvk P) tx.sighash (B.toSig tx.bindingSig) • S.Rbase

/-- The premiss fold's relation arm breaks at the first transaction of the list failing the
net-value equation, with the extractor pinning its key; the selection is computed from the
fold hypothesis. -/
def allConservedOrBreak_valueRelation
    (hval : ValidLedger P kv issuance maxActions ledger)
    (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG)
    (L : List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth))
    (hL : ∀ tx ∈ L, tx ∈ ledger)
    {w : BindingSignature.NontrivialRelation (F := ZMod r) S.Vbase S.Rbase}
    (h : allConservedOrBreak (fun tx htx => S.premissOrBreakFallible B hval hr E tx htx) L hL
        = .inr (.inl w)) :
    ValueRelationSelection B E L := by
  induction L with
  | nil => simp [allConservedOrBreak] at h
  | cons tx t ih =>
      rw [allConservedOrBreak] at h
      by_cases heq : txNetValue tx = tx.vBalance
      · rw [ValueShape.premissOrBreakFallible] at h
        rw [dif_pos heq] at h
        simp only at h
        split at h
        next b hb =>
          simp only [PSum.inr.injEq] at h
          subst h
          obtain ⟨tx', hfind, hex⟩ := ih _ hb
          refine ⟨tx', ?_, hex⟩
          rw [List.find?_cons_of_neg (by simp [heq]), hfind]
        next hall => exact absurd h (by simp)
      · rw [ValueShape.premissOrBreakFallible] at h
        rw [dif_neg heq] at h
        by_cases hex : tx.bvk P
            = E (tx.bvk P) tx.sighash (B.toSig tx.bindingSig) • S.Rbase
        · exact ⟨tx, List.find?_cons_of_pos (by simp [heq]), hex⟩
        · rw [dif_neg hex] at h
          exact absurd h (by simp)

/-- The conservation reduction's relation arm at prefix `i` breaks at the prefix's first
imbalanced transaction, with the extractor pinning its key; the selection is computed from
the reduction hypothesis. -/
def balanceConservationOrBreak_valueRelation
    (hval : ValidLedger P kv issuance maxActions ledger)
    (S : ValueShape P) (B : BindingSigShape P S)
    (hr : (maxActions + 1) * P.valueBound ≤ r)
    (E : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ)
    {w : BindingSignature.NontrivialRelation (F := ZMod r) S.Vbase S.Rbase}
    (h : balanceConservationOrBreak (issuance := issuance)
        (fun tx htx => S.premissOrBreakFallible B hval hr E tx htx) i = .inr (.inl w)) :
    ValueRelationSelection B E (ledger.take i) := by
  rw [balanceConservationOrBreak] at h
  split at h
  next b hb =>
    simp only [PSum.inr.injEq] at h
    subst h
    exact allConservedOrBreak_valueRelation hval S B hr E _ _ hb
  next hall => exact absurd h (by simp)

end Identification

section ArmBound

variable (gen : G) (v_idx r_idx : Fin m) (queryOf : G → G → MSG → Q)
  (P₀ : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG)
  (toSig : SIG → RedDSA.Sig (ZMod r) G)
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- The relation finder for the conservation relation arm: replay the labeled adversary at
the presented basis, select the prefix's first imbalanced transaction, recompute the
extractor's value from the run's own data, and rebuild the reduction's relation behind
decidable guards — the integer imbalance, the no-overflow bound, and the binding-key
equation. Computable, and free of any validity hypothesis: on an event sample the guards
pass because validity supplies the same facts the reduction derived. -/
def valueRelFinder (hne_idx : v_idx ≠ r_idx) (i : ℕ)
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m)))
    (O : Q → ZMod r) (b : Fin m → G) :
    Option (AlgebraicRelationWitness (F := ZMod r) b) :=
  match failTxOfAnn m P₀ ((LA b).run O) i with
  | none => none
  | some p =>
      letI tx := p.1
      letI bsk :=
        match (LA b).findLabel O
            (queryOf (toSig tx.bindingSig).R (bvkAt m v_idx r_idx P₀ b tx) tx.sighash) with
        | some ℓ => ℓ.key r_idx
        | none => p.2.key r_idx
      -- the three hypotheses of `ofBundleIntImbalance`, all decidable: the imbalance
      -- `A = ∑ bundle values − vBalance` is nonzero, `|A| < r` so it survives reduction
      -- mod `r`, and the extractor's `bsk` really opens `bvk` at the `ℛ` slot.
      if h : (((txBundle tx).map Prod.fst).sum
            - (([] : List (ℤ × ZMod r)).map Prod.fst).sum - tx.vBalance ≠ 0)
          ∧ ((((txBundle tx).map Prod.fst).sum
            - (([] : List (ℤ × ZMod r)).map Prod.fst).sum - tx.vBalance).natAbs < r)
          ∧ bindingVK (b v_idx) (b r_idx) (castBundle (txBundle tx)) (castBundle [])
              (tx.vBalance : ZMod r) = bsk • b r_idx then
        some ((NontrivialRelation.ofBundleIntImbalance (b v_idx) (b r_idx) (txBundle tx) []
            tx.vBalance bsk h.1 h.2.1 h.2.2).toAlgebraicRelationWitnessAt b v_idx r_idx
          hne_idx rfl rfl)
      else none

omit [Fintype Q] [Inhabited Q] in
/-- On a relation-arm sample the finder returns a relation, for the finder at any prefix `k`
at least the failing prefix: the arm breaks at the first imbalanced transaction of its
prefix, which is the same transaction for every prefix containing it. -/
theorem valueRelation_finder_isSome
    {LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    (hne_idx : v_idx ≠ r_idx)
    (hr : (maxActions + 1) * P₀.valueBound ≤ r) {i k : ℕ} (hik : i ≤ k)
    {O : Q → ZMod r} {s : Fin m → ZMod r}
    (hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig O s) kv issuance
      maxActions (((LA (scalarBasis gen s)).run O).map Prod.fst))
    {w : BindingSignature.NontrivialRelation (F := ZMod r)
      (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig O s).Vbase
      (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig O s).Rbase}
    (heq : balanceConservationOrBreak (issuance := issuance)
        (fun tx htx => (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig O s)
          |>.premissOrBreakFallible (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig O s)
            hval hr (kappaExtractor m gen r_idx queryOf P₀ k LA O s) tx htx) i
      = .inr (.inl w)) :
    (valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k LA O (scalarBasis gen s)).isSome
      := by
  obtain ⟨tx, hfind, hex⟩ :=
    balanceConservationOrBreak_valueRelation hval _ _ hr
      (kappaExtractor m gen r_idx queryOf P₀ k LA O s) i heq
  have hex' : bvkAt m v_idx r_idx P₀ (scalarBasis gen s) tx
      = kappaExtractor m gen r_idx queryOf P₀ k LA O s
          (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) tx) tx.sighash
          (toSig tx.bindingSig) • (s r_idx • gen) := hex
  obtain ⟨pr, hpr, hfst⟩ : ∃ pr,
      failTxOfAnn m P₀ ((LA (scalarBasis gen s)).run O) i = some pr ∧ pr.1 = tx := by
    rw [← List.map_take, List.find?_map] at hfind
    obtain ⟨pr, hpr, hfst⟩ := Option.map_eq_some_iff.mp hfind
    exact ⟨pr, hpr, hfst⟩
  obtain ⟨rep, rfl⟩ : ∃ rep, pr = (tx, rep) := ⟨pr.2, by rw [← hfst, Prod.mk.eta]⟩
  have hfindAnnK : failTxOfAnn m P₀ ((LA (scalarBasis gen s)).run O) k = some (tx, rep) :=
    find?_take_eq_some_of_le hik hpr
  have hmem : (tx, rep) ∈ (LA (scalarBasis gen s)).run O :=
    (List.take_sublist k _).subset (List.mem_of_find?_eq_some hfindAnnK)
  have htx : tx ∈ ((LA (scalarBasis gen s)).run O).map Prod.fst :=
    List.mem_map_of_mem hmem
  -- the finder's recomputed extractor value is the extractor's
  have hbsk : kappaExtractor m gen r_idx queryOf P₀ k LA O s
        (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) tx) tx.sighash (toSig tx.bindingSig)
      = (match (LA (scalarBasis gen s)).findLabel O
            (queryOf (toSig tx.bindingSig).R
              (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) tx) tx.sighash) with
        | some ℓ => ℓ.key r_idx
        | none => rep.key r_idx) := by
    unfold kappaExtractor
    cases (LA (scalarBasis gen s)).findLabel O
        (queryOf (toSig tx.bindingSig).R (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) tx)
          tx.sighash) <;>
      simp [hfindAnnK]
    rfl
  -- decide the three guards from validity and the selection
  have heqtx : txNetValue tx ≠ tx.vBalance := by
    have := List.find?_some hfind
    simpa using this
  have hc1 : ((txBundle tx).map Prod.fst).sum
      - (([] : List (ℤ × ZMod r)).map Prod.fst).sum - tx.vBalance ≠ 0 := by
    simp only [List.map_nil, List.sum_nil, sub_zero, txBundle_fst_sum]
    exact sub_ne_zero.mpr heqtx
  have hc2 : (((txBundle tx).map Prod.fst).sum
      - (([] : List (ℤ × ZMod r)).map Prod.fst).sum - tx.vBalance).natAbs < r := by
    simp only [List.map_nil, List.sum_nil, sub_zero, txBundle_fst_sum]
    have h1 := txNetValue_natAbs_le (P := kappaPrimitivesAt m gen v_idx r_idx queryOf P₀
      toSig O s) (kv := kv) (hval.satisfied tx htx)
    have h2 := hval.vbalance_bound tx htx
    have hb : tx.actions.length * (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀
          toSig O s).valueBound
        ≤ maxActions * (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig O s).valueBound :=
      Nat.mul_le_mul_right _ (hval.action_bound tx htx)
    calc (txNetValue tx - tx.vBalance).natAbs
        ≤ (txNetValue tx).natAbs + tx.vBalance.natAbs := Int.natAbs_sub_le _ _
      _ < maxActions * (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig O
            s).valueBound
          + (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig O s).valueBound :=
          Nat.add_lt_add_of_le_of_lt (le_trans h1 hb) h2
      _ = (maxActions + 1) * (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig O
            s).valueBound := by ring
      _ ≤ r := hr
  have hc3 : bindingVK (scalarBasis gen s v_idx) (scalarBasis gen s r_idx)
      (castBundle (txBundle tx)) (castBundle []) (tx.vBalance : ZMod r)
      = (match (LA (scalarBasis gen s)).findLabel O
            (queryOf (toSig tx.bindingSig).R
              (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) tx) tx.sighash) with
        | some ℓ => ℓ.key r_idx
        | none => rep.key r_idx) • scalarBasis gen s r_idx := by
    have hb := bvk_eq (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig O s)
      (hval.satisfied tx htx)
    rw [← hbsk]
    exact hb.symm.trans hex'
  unfold valueRelFinder
  rw [hfindAnnK]
  dsimp only
  rw [dif_pos ⟨hc1, hc2, hc3⟩]
  rfl

omit [Inhabited Q] in
/-- **The conservation relation arm, discharged.** For any labeled ledger adversary in the
challenge-oracle model, the probability that its output ledger is valid and the conservation
reduction at prefix `i`, with the effective-representation extractor, computes a nontrivial
relation is at most `ε + 1/|F|`: the finder replaying the adversary rebuilds the relation, and
the tight Jaeger–Tessaro accounting applies. The DL hypothesis is a single bound for the
coin-consuming finder — the reduction samples the challenge table as its own coins — so no
supremum over tables appears. No query budget appears — the arm's witness
is oracle-free data. Validity of the output ledger is a conjunct of the measured event, as in
the extraction-failure arm. Kept as a named single-prefix result; the conservation experiment
consumes the all-prefixes form below. -/
theorem balanceConservation_valueRelationArm_measure_le {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    (hne_idx : v_idx ≠ r_idx)
    (hr : (maxActions + 1) * P₀.valueBound ≤ r) (i : ℕ) {ε : ℝ≥0∞}
    (hdl : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen
      (fun b O => valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx i (LA j) O b) ε) :
    ((p.bind fun j =>
        (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).map (Prod.mk j))).toOuterMeasure
        (setOf fun (x : ι × ((Q → ZMod r) × (Fin m → ZMod r))) =>
          ∃ hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
              kv issuance maxActions
              (((LA x.1 (scalarBasis gen x.2.2)).run x.2.1).map Prod.fst),
            ∃ w, balanceConservationOrBreak (issuance := issuance)
                (fun tx htx => (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
                  |>.premissOrBreakFallible
                    (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
                    hval hr
                    (kappaExtractor m gen r_idx queryOf P₀ i (LA x.1) x.2.1 x.2.2)
                    tx htx) i
              = .inr (.inl w))
      ≤ ε + 1 / Fintype.card (ZMod r) := by
  haveI : Nonempty (Fin m) := ⟨r_idx⟩
  refine Zcash.Security.KeyBinding.toOuterMeasure_bind_le _ _ _ fun j => ?_
  rw [PMF.toOuterMeasure_map_apply]
  refine le_trans (MeasureTheory.measure_mono ?_)
    (le_trans (le_of_eq (toOuterMeasure_swap_relSetWithCoins gen
        (fun b O => valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx i (LA j) O b)))
      (relationWithCoins_prob_le_of_textbookDL gen _ (hdl j)))
  rintro ⟨O, s⟩ ⟨hval, w, heq⟩
  exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    valueRelation_finder_isSome m gen v_idx r_idx queryOf P₀ toSig hne_idx hr le_rfl hval heq⟩)

omit [Inhabited Q] in
/-- **The all-prefixes conservation relation arm, discharged with no factor of `k`.** As
`balanceConservation_valueRelationArm_measure_le`, over the event that the reduction computes
a relation at *some* prefix `i < k`: every such prefix breaks at the ledger's first
imbalanced transaction — the same transaction for every prefix containing it — so the one
prefix-`k` finder covers them all and the bound is unchanged. -/
theorem balanceConservationBefore_valueRelationArm_measure_le {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    (hne_idx : v_idx ≠ r_idx)
    (hr : (maxActions + 1) * P₀.valueBound ≤ r) (k : ℕ) {ε : ℝ≥0∞}
    (hdl : ∀ j : ι, TextbookDLWithCoinsAdvantageLE gen
      (fun b O => valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) O b) ε) :
    ((p.bind fun j =>
        (PMF.uniformOfFintype ((Q → ZMod r) × (Fin m → ZMod r))).map (Prod.mk j))).toOuterMeasure
        (setOf fun (x : ι × ((Q → ZMod r) × (Fin m → ZMod r))) =>
          ∃ hval : ValidLedger (kappaPrimitivesAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
              kv issuance maxActions
              (((LA x.1 (scalarBasis gen x.2.2)).run x.2.1).map Prod.fst),
            ∃ i, i < k ∧ ∃ w, balanceConservationOrBreak (issuance := issuance)
                (fun tx htx => (kappaShapeAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
                  |>.premissOrBreakFallible
                    (kappaBindingAt m gen v_idx r_idx queryOf P₀ toSig x.2.1 x.2.2)
                    hval hr
                    (kappaExtractor m gen r_idx queryOf P₀ k (LA x.1) x.2.1 x.2.2)
                    tx htx) i
              = .inr (.inl w))
      ≤ ε + 1 / Fintype.card (ZMod r) := by
  haveI : Nonempty (Fin m) := ⟨r_idx⟩
  refine Zcash.Security.KeyBinding.toOuterMeasure_bind_le _ _ _ fun j => ?_
  rw [PMF.toOuterMeasure_map_apply]
  refine le_trans (MeasureTheory.measure_mono ?_)
    (le_trans (le_of_eq (toOuterMeasure_swap_relSetWithCoins gen
        (fun b O => valueRelFinder m v_idx r_idx queryOf P₀ toSig hne_idx k (LA j) O b)))
      (relationWithCoins_prob_le_of_textbookDL gen _ (hdl j)))
  rintro ⟨O, s⟩ ⟨hval, i, hik, w, heq⟩
  exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    valueRelation_finder_isSome m gen v_idx r_idx queryOf P₀ toSig hne_idx hr
      (le_of_lt hik) hval heq⟩)

end ArmBound

end Zcash.Security.Ledger.Model
