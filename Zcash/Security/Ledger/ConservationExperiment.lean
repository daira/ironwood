import Zcash.Common.Oracle.LabeledOracleComp
import Zcash.Security.Ledger.ValueRelationArm

/-!
# The conservation experiment: both arms in one sample space

An unbalanced transaction whose binding signature verifies costs the adversary one of two
things: the `(𝒱, ℛ)` relation the imbalance computes (`Ledger/ValueRelationArm.lean`), or a
verifying signature whose key the extractor misses (`Ledger/ExtractionKappaArm.lean`). The
capstones bound conservation and cap violations by `εdlr + κ`, one named ε per arm, over an
abstract `PMF (ValidAnnotated …)`. Those two ε's were priced in separate experiments, so nothing
tied them to one adversary facing one sampling.

This module runs both arms in one experiment: over the adversary's coins, the challenge table,
and the logs of the `m` presented bases, the probability that the output ledger is valid *and*
violates conservation (or the cap) at some prefix `i < k` is at most

    (ε_rel + 1/|F|) + ((q_H + 2)/|F| + ε_κ).

The composition is the capstone layer's own: at each sample a violation lands in the
transaction-balance premiss's relation arm or its extraction-failure arm
(`balanceConservationViolationBefore_subset_fallible`), and each arm's measure is the bound
already proved for it (`balanceConservationBefore_valueRelationArm_measure_le` and
`balanceConservationBefore_extractFailArm_measure_le_of_coins`, the coins form proved here).

Both discrete-log premisses are the coins form (`TextbookDLWithCoinsAdvantageLE` at `ρ` := the
challenge table), quantified only over the adversary's coins: no supremum over challenge tables
remains anywhere in the experiment.

## The algebraic-adversary assumption

`AlgebraicAtBindingPoints` is an assumption about the adversary, the online AGM's algebraic
restriction, and not something proved of one.

It constrains only the two points the extraction reduction reads, rather than every group
element the run produces, so it admits more adversaries than a fully algebraic restriction does
and the theorems assuming it are correspondingly stronger. The labels never reach the oracle,
which answers the query point alone, so they hand the adversary nothing and return nothing to
it: they are the argument's bookkeeping (`LabeledOracleComp`).

Each half earns its place. The extractor recovers `bsk` by reading the `ℛ`-slot coefficient off
the announced key, so a false announcement would extract nothing. And a query's one bad
challenge is computed from the representation in effect at that query point, so the
representation has to be pinned before the oracle answers, which is what the query-time half
supplies.
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

/-- **The adversary is algebraic at the binding-signature points.** For each transaction it
outputs, and at each challenge query it makes, the adversary announces how it built two group
elements out of the presented basis: the binding signature's nonce `R`, and the transaction's
binding verification key `bvk`. An announcement is a `QueryRep` pair of coefficient vectors, and
nothing in the type makes one true. This is the assumption that each one is: it evaluates
(`representationEval`) to the point it names.

Why the reduction needs it, and why only these two points, is the module docstring's assumption
section. Consumed by `extractFail_mem_kappaEvent`. -/
structure AlgebraicAtBindingPoints
    (LA : (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))) :
    Prop where
  /-- At query time: the label recorded at a challenge query represents the querying
  transaction's nonce and binding key. The half that pins the query's one bad challenge before
  the oracle answers. -/
  atLabel : ∀ (O : Q → ZMod r) (s : Fin m → ZMod r) (q : Q) (ℓ : QueryRep (ZMod r) m),
    (LA (scalarBasis gen s)).findLabel O q = some ℓ →
    ∀ p ∈ (LA (scalarBasis gen s)).run O,
      queryOf (toSig p.1.bindingSig).R (bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1)
          p.1.sighash = q →
        (toSig p.1.bindingSig).R = representationEval (scalarBasis gen s) ℓ.commitment
        ∧ bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1
          = representationEval (scalarBasis gen s) ℓ.key
  /-- At output time: each transaction's announced representation represents its own nonce and
  binding key. The half the extractor falls back on when the run never queried that point. -/
  atOutput : ∀ (O : Q → ZMod r) (s : Fin m → ZMod r),
    ∀ p ∈ (LA (scalarBasis gen s)).run O,
      (toSig p.1.bindingSig).R = representationEval (scalarBasis gen s) p.2.commitment
      ∧ bvkAt m v_idx r_idx P₀ (scalarBasis gen s) p.1
        = representationEval (scalarBasis gen s) p.2.key

/-- **The all-prefixes extraction-failure arm, with a single randomized reduction.** As
`balanceConservationBefore_extractFailArm_measure_le`, with the per-table DL hypothesis
replaced by one bound for the coin-consuming relation finder, per adversary coin. -/
theorem balanceConservationBefore_extractFailArm_measure_le_of_coins {ι : Type u} (p : PMF ι)
    {LA : ι → (Fin m → G) → LabeledOracleComp Q (ZMod r) (fun _ => QueryRep (ZMod r) m)
      (List (Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P₀.depth × QueryRep (ZMod r) m))}
    {qH : ℕ} (hQ : ∀ j b, (LA j b).QueryBound qH)
    (halg : ∀ j : ι, AlgebraicAtBindingPoints m gen v_idx r_idx queryOf P₀ toSig (LA j))
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
    (halg j).atLabel (halg j).atOutput hr (le_of_lt hik) hval heq

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
    (halg : ∀ j : ι, AlgebraicAtBindingPoints m gen v_idx r_idx queryOf P₀ toSig (LA j))
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
    queryOf P₀ toSig (kv := kv) (issuance := issuance) p hQ halg hr k hdlκ
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
    (halg : ∀ j : ι, AlgebraicAtBindingPoints m gen v_idx r_idx queryOf P₀ toSig (LA j))
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
    queryOf P₀ toSig (kv := kv) (issuance := issuance) p hQ halg hr k hdlκ
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
