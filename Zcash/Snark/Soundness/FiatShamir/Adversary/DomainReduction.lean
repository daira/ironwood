import Zcash.Snark.Soundness.FiatShamir.Adversary.Adaptive

/-!
# Reduce an unbounded oracle domain to finite support

A bounded-query adversary reaches finitely many oracle points; split them into deployed transcripts
and finite junk support.
-/

namespace Zcash.Snark

open scoped ENNReal
open Zcash.Common

section GamePoints

variable {T F α : Type*} [DecidableEq T] [Fintype F]

/-- Extend a subdomain assignment to a full table with a fixed junk value. -/
def extendOn (S : Finset T) (assign : {t // t ∈ S} → F) (f₀ : F) : T → F :=
  fun t => if h : t ∈ S then assign ⟨t, h⟩ else f₀

/-- The finite set of game points of a machine's attainable outputs: attainable outputs are runs
over the finitely many reach-set assignments. -/
def gamePoints {n : ℕ} (A : OracleComp T F α) (pts : α → Fin n → T)
    (f₀ : F) : Finset T :=
  Finset.univ.biUnion fun assign : {t // t ∈ A.reachSet} → F =>
    Finset.univ.image fun j : Fin n => pts (A.run (extendOn A.reachSet assign f₀)) j

/-- Every run's game points land in the finite game-point set: the run agrees with the run over
its own reach-set assignment. -/
theorem pts_run_mem_gamePoints {n : ℕ} (A : OracleComp T F α) (pts : α → Fin n → T)
    (f₀ : F) (O : T → F) (j : Fin n) :
    pts (A.run O) j ∈ gamePoints A pts f₀ := by
  have hagree : ∀ t ∈ A.reachSet, O t = extendOn A.reachSet (fun t' => O t'.1) f₀ t := by
    intro t ht
    rw [extendOn, dif_pos ht]
  rw [show A.run O = A.run (extendOn A.reachSet (fun t' => O t'.1) f₀) from
    OracleComp.run_congr_reachSet A hagree]
  exact Finset.mem_biUnion.mpr ⟨fun t' => O t'.1, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩

end GamePoints

section Reduction

variable {T F P : Type*} [DecidableEq T] [Fintype F] [Nonempty F]

/-- Restrict an adversary to a finite set containing every reachable query and attainable game
point, preserving its query bound and outcome. -/
theorem finite_domain_restriction {m k : ℕ} (hm : 0 < m)
    (A : OracleComp T F P) {Q : ℕ} (hQ : A.QueryBound Q)
    (accept : P → (Fin m → F) → (Fin k → F) → Prop)
    (prefixesPre : P → Fin m → T) (prefixes : P → Fin k → T) :
    ∃ (S : Finset T) (A₀ : OracleComp {t // t ∈ S} F P)
      (preS : P → Fin m → {t // t ∈ S}) (ptsS : P → Fin k → {t // t ∈ S}),
      A₀.QueryBound Q ∧
      ∀ O : T → F,
        fsWinsFull A accept prefixesPre prefixes O
          ↔ fsWinsFull A₀ accept preS ptsS (fun t => O t.1) := by
  obtain ⟨f₀⟩ := ‹Nonempty F›
  set S : Finset T := A.reachSet ∪ gamePoints A prefixesPre f₀ ∪ gamePoints A prefixes f₀
    with hSdef
  have hreach : A.reachSet ⊆ S := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hpreS : ∀ (O : T → F) (i : Fin m), prefixesPre (A.run O) i ∈ S := fun O i =>
    Finset.mem_union_left _ (Finset.mem_union_right _
      (pts_run_mem_gamePoints A prefixesPre f₀ O i))
  have hptsS : ∀ (O : T → F) (j : Fin k), prefixes (A.run O) j ∈ S := fun O j =>
    Finset.mem_union_right _ (pts_run_mem_gamePoints A prefixes f₀ O j)
  have hd : prefixesPre (A.run (fun _ => f₀)) ⟨0, hm⟩ ∈ S := hpreS (fun _ => f₀) ⟨0, hm⟩
  set d : {t // t ∈ S} := ⟨prefixesPre (A.run (fun _ => f₀)) ⟨0, hm⟩, hd⟩ with hddef
  refine ⟨S, A.restrictTo S hreach,
    (fun p i => if h : prefixesPre p i ∈ S then ⟨prefixesPre p i, h⟩ else d),
    (fun p j => if h : prefixes p j ∈ S then ⟨prefixes p j, h⟩ else d),
    OracleComp.queryBound_restrictTo S hQ hreach, ?_⟩
  intro O
  have hrun : (A.restrictTo S hreach).run (fun t => O t.1) = A.run O :=
    OracleComp.run_restrictTo S A hreach (fun t => O t.1) O (fun t ht => rfl)
  rw [fsWinsFull, fsWinsFull, hrun]
  have h1 : (fun i => (fun t : {t // t ∈ S} => O t.1)
        ((fun p i => if h : prefixesPre p i ∈ S then
          (⟨prefixesPre p i, h⟩ : {t // t ∈ S}) else d) (A.run O) i))
      = fun i => O (prefixesPre (A.run O) i) := by
    funext i
    beta_reduce
    rw [dif_pos (hpreS O i)]
  have h2 : (fun j => (fun t : {t // t ∈ S} => O t.1)
        ((fun p j => if h : prefixes p j ∈ S then
          (⟨prefixes p j, h⟩ : {t // t ∈ S}) else d) (A.run O) j))
      = fun j => O (prefixes (A.run O) j) := by
    funext j
    beta_reduce
    rw [dif_pos (hptsS O j)]
  rw [h1, h2]

/-- Adding independent junk coordinates to a finite game preserves its win probability. -/
theorem fsWinsFull_mapDomain_measure_eq {T₀ J : Type*} [Fintype T₀] [DecidableEq T₀]
    [Fintype J] [DecidableEq J] {m k : ℕ}
    (A : OracleComp T₀ F P) (accept : P → (Fin m → F) → (Fin k → F) → Prop)
    (prefixesPre : P → Fin m → T₀) (prefixes : P → Fin k → T₀) :
    (PMF.uniformOfFintype ((T₀ ⊕ J) → F)).toOuterMeasure
        {O' : (T₀ ⊕ J) → F | fsWinsFull (A.mapDomain Sum.inl) accept
          (fun p i => Sum.inl (prefixesPre p i)) (fun p j => Sum.inl (prefixes p j)) O'}
      = (PMF.uniformOfFintype (T₀ → F)).toOuterMeasure
          {O : T₀ → F | fsWinsFull A accept prefixesPre prefixes O} := by
  have hset : {O' : (T₀ ⊕ J) → F | fsWinsFull (A.mapDomain Sum.inl) accept
        (fun p i => Sum.inl (prefixesPre p i)) (fun p j => Sum.inl (prefixes p j)) O'}
      = (fun O' : (T₀ ⊕ J) → F => O' ∘ Sum.inl) ⁻¹'
          {O : T₀ → F | fsWinsFull A accept prefixesPre prefixes O} := by
    ext O'
    simp only [Set.mem_preimage, Set.mem_setOf_eq, fsWinsFull, OracleComp.run_mapDomain]
    exact Iff.rfl
  rw [hset, ← PMF.toOuterMeasure_map_apply,
    uniformOfFintype_map_precomp_injective Sum.inl Sum.inl_injective]

omit [Fintype F] [Nonempty F] in
/-- Split and original machines have the same outcome on agreeing tables when all game points lie
in the designated component. -/
theorem fsWinsFull_splitDomain {T T_D : Type*} [DecidableEq T] [Fintype F]
    {m k : ℕ} (ι : T_D → T) (ρ : T → Option T_D) (S : Finset T)
    (hρ₂ : ∀ t tD, ρ t = some tD → t = ι tD)
    (A : OracleComp T F P) (h : A.reachSet ⊆ S)
    (accept : P → (Fin m → F) → (Fin k → F) → Prop)
    (preD : P → Fin m → T_D) (ptsD : P → Fin k → T_D)
    (O' : (T_D ⊕ {t // t ∈ S}) → F) (Ofull : T → F)
    (hD : ∀ tD, Ofull (ι tD) = O' (Sum.inl tD))
    (hJ : ∀ (t : T) (ht : t ∈ S), ρ t = none → Ofull t = O' (Sum.inr ⟨t, ht⟩)) :
    fsWinsFull A accept (fun p i => ι (preD p i)) (fun p j => ι (ptsD p j)) Ofull
      ↔ fsWinsFull (A.splitDomain ι ρ S h) accept
          (fun p i => Sum.inl (preD p i)) (fun p j => Sum.inl (ptsD p j)) O' := by
  rw [fsWinsFull, fsWinsFull,
    OracleComp.run_splitDomain ι ρ S hρ₂ A h O' Ofull hD hJ]
  have h1 : (fun i => O' (Sum.inl (preD (A.run Ofull) i)))
      = fun i => Ofull (ι (preD (A.run Ofull) i)) := by
    funext i
    exact (hD (preD (A.run Ofull) i)).symm
  have h2 : (fun j => O' (Sum.inl (ptsD (A.run Ofull) j)))
      = fun j => Ofull (ι (ptsD (A.run Ofull) j)) := by
    funext j
    exact (hD (ptsD (A.run Ofull) j)).symm
  rw [h1, h2]

/-- A bound for all `Q`-query machines on the designated finite domain also bounds a `Q`-query
machine on an arbitrary domain. -/
theorem fsWinsFull_unbounded_measure_le {T T_D : Type*} [DecidableEq T]
    [Fintype T_D] [DecidableEq T_D] {m k : ℕ}
    (ι : T_D → T) (ρ : T → Option T_D)
    (A : OracleComp T F P) {Q : ℕ} (hQ : A.QueryBound Q)
    (accept : P → (Fin m → F) → (Fin k → F) → Prop)
    (preD : P → Fin m → T_D) (ptsD : P → Fin k → T_D) {β : ℝ≥0∞}
    (hβ : ∀ A₀ : OracleComp T_D F P, A₀.QueryBound Q →
      (PMF.uniformOfFintype (T_D → F)).toOuterMeasure
        {O : T_D → F | fsWinsFull A₀ accept preD ptsD O} ≤ β) :
    (PMF.uniformOfFintype ((T_D ⊕ {t // t ∈ A.reachSet}) → F)).toOuterMeasure
      {O' : (T_D ⊕ {t // t ∈ A.reachSet}) → F |
        fsWinsFull (A.splitDomain ι ρ A.reachSet (Finset.Subset.refl _)) accept
          (fun p i => Sum.inl (preD p i)) (fun p j => Sum.inl (ptsD p j)) O'} ≤ β :=
  fsWinsFull_restrictSum_le _ accept preD ptsD (fun j =>
    hβ _ (OracleComp.queryBound_restrictSum
      (OracleComp.queryBound_splitDomain ι ρ A.reachSet hQ (Finset.Subset.refl _)) j))

end Reduction

section DeployedRetraction

variable {F G : Type*}

/-- The deployed partial retraction: an arbitrary transcript retracts to the bounded domain
exactly when its length is within the bound. -/
def truncateTranscript (L : ℕ) (t : List (TranscriptElt F G)) :
    Option (BTranscript F G L) :=
  if h : t.length ≤ L then some ⟨t, h⟩ else none

end DeployedRetraction

end Zcash.Snark
