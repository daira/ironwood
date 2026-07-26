import Zcash.Snark.Soundness.Forking.PinnedSqueeze

/-!
# Additive pricing for prefix-indexed root events

The fourth-root adaptive-coupling loss is unnecessary when extraction failure exposes a bad root
at a particular squeeze.  Such a root set is determined by the transcript prefix before that
squeeze and has a direct Schwartz--Zippel measure bound.  `xEscAtPoint_measure_le` prices one
adaptive squeeze at `(Q + 1) * epsilon`; this file packages a finite union of such events and sums
their budgets.
-/

namespace Zcash.Snark

open scoped ENNReal
open Classical

variable {T F P : Type*} [Fintype F] [Nonempty F]

/-- One bad-root set indexed by the transcript prefix before its squeeze.

Indexing by `point (A.run O)` makes the causal boundary part of the data model.  There is no
caller-supplied equality comparing two hindsight-dependent final outputs. -/
structure PinnedRootEvent [DecidableEq T] (A : OracleComp T F P) where
  point : P -> T
  badAt : T -> Set F
  budget : ENNReal
  measure_le : forall t,
    (PMF.uniformOfFintype F).toOuterMeasure (badAt t) <= budget

namespace PinnedRootEvent

/-- The run's own squeeze answer lands in this bad-root set. -/
def Landing [DecidableEq T] {A : OracleComp T F P} (event : PinnedRootEvent A)
    (O : T -> F) : Prop :=
  O (event.point (A.run O)) ∈ event.badAt (event.point (A.run O))

/-- One pinned root event costs its direct root-set budget, with only the standard query loss. -/
theorem landing_measure_le [Fintype T] [DecidableEq T]
    {A : OracleComp T F P} (event : PinnedRootEvent A) {Q : Nat}
    (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T -> F)).toOuterMeasure {O : T -> F | event.Landing O}
      <= (Q + 1 : Nat) * event.budget := by
  exact xEscAtPoint_measure_le A event.point event.badAt event.measure_le hQ

end PinnedRootEvent

/-- A finite collection of independently priced root events. -/
structure PinnedRootFamily [DecidableEq T] (A : OracleComp T F P) (n : Nat) where
  event : Fin n -> PinnedRootEvent A

namespace PinnedRootFamily

/-- At least one root event occurs on the run. -/
def Landing [DecidableEq T] {A : OracleComp T F P} {n : Nat}
    (family : PinnedRootFamily A n) (O : T -> F) : Prop :=
  ∃ i : Fin n, (family.event i).Landing O

/-- A finite union of pinned root events is additive: no product threshold and no fourth root. -/
theorem landing_measure_le [Fintype T] [DecidableEq T]
    {A : OracleComp T F P} {n : Nat} (family : PinnedRootFamily A n) {Q : Nat}
    (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T -> F)).toOuterMeasure {O : T -> F | family.Landing O}
      <= (Q + 1 : Nat) * ∑ i : Fin n, (family.event i).budget := by
  have hsub : {O : T -> F | family.Landing O} <=
      ⋃ i : Fin n, {O : T -> F | (family.event i).Landing O} := by
    intro O hO
    obtain ⟨i, hi⟩ := hO
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    (∑ i : Fin n, (PMF.uniformOfFintype (T -> F)).toOuterMeasure
        {O : T -> F | (family.event i).Landing O})
        <= ∑ i : Fin n, (Q + 1 : Nat) * (family.event i).budget :=
      Finset.sum_le_sum fun i _ => (family.event i).landing_measure_le hQ
    _ = (Q + 1 : Nat) * ∑ i : Fin n, (family.event i).budget := by
      rw [Finset.mul_sum]

end PinnedRootFamily

end Zcash.Snark
