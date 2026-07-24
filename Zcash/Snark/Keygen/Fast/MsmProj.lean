/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Snark.Keygen.Fast.Msm
import Zcash.Snark.Keygen.Fast.Projective

/-!
# The windowed Pippenger MSM run entirely in projective coordinates

`Fast/Msm.lean` proves a windowed Pippenger accelerator (`pippenger`, `pippengerFast`) equal to the
naive multi-scalar multiplication over any `AddCommMonoid`.  Instantiated at the Vesta affine group
`G = SWPoint Vesta.curve`, every one of its group additions — bucket insertions, the suffix-sum
accumulation, and the Horner doublings — is an *affine* point add, each paying a field inversion.

`Fast/Projective.lean` provides the complete Renes–Costello–Batina projective addition `padd` on
`PVes`, with the homomorphism `toAffine_padd : Valid P → Valid Q → toAffine (padd P Q) = toAffine P +
toAffine Q`, closure `valid_padd`, and the leaf bridges `ofAffine`/`toAffine` (`valid_ofAffine`,
`toAffine_ofAffine`, `valid_pid`, `toAffine_pid`), plus the fast scalar multiplication
`pnsmulFast`/`pnsmulFast_spec`.

This module runs the **entire Pippenger interior in projective coordinates** — one `toAffine` (one
inversion) per whole MSM instead of one per add — with a proven equality back to the affine
accelerator.  `PVes` is not a lawful monoid on the nose (associativity only holds after `toAffine`),
so we do not re-run the Pippenger equality proof; instead we mirror each fold of `Fast/Msm.lean`
(`bucketOf`, `accStep`, `hornerList`, `windowValue`, `pippenger`) with a `padd`/`pid`/`pnsmulFast`
version and prove — by carrying `Valid` through every intermediate — that it commutes with
`toAffine`.  Composing with `Fast.Msm.pippenger_eq_msm` lands
`pippengerProj_eq : pippengerProj c terms = pippenger c terms`.

Concretely everything is specialized to the Vesta group `G` (the projective bridge is
Vesta-specific).

## Transport skeleton

* `psum_spec`          — a `foldr padd pid` sum transports to `(·.map toAffine).sum` (`bucketOf`).
* `pbucketOf_spec`     — the per-bucket projective sum matches `Fast.Msm.bucketOf` after `toAffine`.
* `foldr_paccStep_spec`— the projective suffix-sum accumulator matches `Fast.Msm.accStep`.
* `pwindowValue_spec`  — one window value transports to `Fast.Msm.windowValue`.
* `phornerList_spec`   — the projective Horner fold (doublings via `pnsmulFast`) transports to
  `Fast.Msm.hornerList`, using `pnsmulFast_spec` for each `2^c`-fold doubling.
-/

open Zcash.Snark
open Zcash.Snark.Keygen.Fast
open Zcash.Snark.Keygen.Fast.Projective
open Zcash.Snark.Keygen.Fast.Projective.PVes
open CompElliptic
open CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Curves.Pasta

namespace Zcash.Snark.Keygen.Fast.MsmProj

/-- The Vesta affine group carries a default point, needed to instantiate the `Fast.Msm` wrapper
(`commitLagrangeSpec`, `commitLagrangeFastWith_eq`) whose section fixes `[Inhabited G]`. -/
local instance : Inhabited Projective.G := ⟨0⟩

/-! ## Projective bucket sum (`foldr padd pid`), mirroring `Fast.Msm.bucketOf` -/

/-- The `padd`-fold sum of a list of projective points, from the projective identity `pid`. -/
def psum (L : List PVes) : PVes := L.foldr padd pid

theorem psum_cons (a : PVes) (xs : List PVes) : psum (a :: xs) = padd a (psum xs) := rfl

/-- A projective `padd`-sum of valid points is valid, and `toAffine` carries it to the affine sum. -/
theorem psum_spec (L : List PVes) (h : ∀ P ∈ L, Valid P) :
    Valid (psum L) ∧ toAffine (psum L) = (L.map toAffine).sum := by
  induction L with
  | nil => exact ⟨valid_pid, by simp [psum, toAffine_pid]⟩
  | cons a xs ih =>
    have ha : Valid a := h a (by simp)
    have hxs : ∀ P ∈ xs, Valid P := fun P hP => h P (by simp [hP])
    obtain ⟨hvxs, hxseq⟩ := ih hxs
    rw [psum_cons]
    exact ⟨valid_padd ha hvxs, by rw [toAffine_padd ha hvxs, hxseq, List.map_cons, List.sum_cons]⟩

/-- The projective bucket-`b` sum: `padd`-fold the points whose digit tag is `b`. -/
def pbucketOf (dp : List (ℕ × PVes)) (b : ℕ) : PVes :=
  psum (dp.filterMap fun p => if p.1 = b then some p.2 else none)

/-- The projective bucket sum is valid and matches `Fast.Msm.bucketOf` of the `toAffine`-mapped
digit-tagged list. -/
theorem pbucketOf_spec (dp : List (ℕ × PVes)) (b : ℕ) (h : ∀ p ∈ dp, Valid p.2) :
    Valid (pbucketOf dp b)
      ∧ toAffine (pbucketOf dp b)
        = Msm.bucketOf (dp.map fun t => (t.1, toAffine t.2)) b := by
  have hval : ∀ P ∈ dp.filterMap (fun p => if p.1 = b then some p.2 else none), Valid P := by
    intro P hP
    rw [List.mem_filterMap] at hP
    obtain ⟨q, hq, hqeq⟩ := hP
    by_cases hc : q.1 = b
    · rw [if_pos hc, Option.some.injEq] at hqeq; rw [← hqeq]; exact h q hq
    · rw [if_neg hc] at hqeq; exact absurd hqeq (by simp)
  obtain ⟨hv, heq⟩ := psum_spec _ hval
  refine ⟨hv, ?_⟩
  rw [pbucketOf, heq, Msm.bucketOf, List.filterMap_map, List.map_filterMap]
  refine congrArg List.sum (congrArg (dp.filterMap ·) ?_)
  funext p
  by_cases hc : p.1 = b <;> simp [hc, Function.comp]

/-! ## Projective suffix-sum accumulator, mirroring `Fast.Msm.accStep` -/

/-- One step of the projective suffix-sum accumulator: carry `(running, total)`, `padd` the next
bucket into `running`, then `padd` `running` into `total`. -/
def paccStep (a : PVes) (p : PVes × PVes) : PVes × PVes :=
  (padd p.1 a, padd p.2 (padd p.1 a))

/-- Folding `paccStep` over valid points keeps both accumulator components valid, and `toAffine`
carries the whole fold (componentwise) to the affine `Fast.Msm.accStep` fold. -/
theorem foldr_paccStep_spec (L : List PVes) (h : ∀ P ∈ L, Valid P) :
    Valid (L.foldr paccStep (pid, pid)).1 ∧ Valid (L.foldr paccStep (pid, pid)).2
      ∧ (toAffine (L.foldr paccStep (pid, pid)).1, toAffine (L.foldr paccStep (pid, pid)).2)
        = List.foldr Msm.accStep ((0 : Projective.G), (0 : Projective.G)) (L.map toAffine) := by
  induction L with
  | nil => exact ⟨valid_pid, valid_pid, by simp [toAffine_pid]⟩
  | cons a xs ih =>
    have ha : Valid a := h a (by simp)
    have hxs : ∀ P ∈ xs, Valid P := fun P hP => h P (by simp [hP])
    obtain ⟨hv1, hv2, heq⟩ := ih hxs
    have hstep : (a :: xs).foldr paccStep (pid, pid) = paccStep a (xs.foldr paccStep (pid, pid)) :=
      rfl
    rw [hstep]
    have hv1' : Valid (padd (xs.foldr paccStep (pid, pid)).1 a) := valid_padd hv1 ha
    refine ⟨hv1', valid_padd hv2 hv1', ?_⟩
    rw [List.map_cons, List.foldr_cons, ← heq, Msm.accStep]
    simp only [paccStep, toAffine_padd hv1 ha, toAffine_padd hv2 hv1']

/-! ## Projective window value, mirroring `Fast.Msm.windowValue` -/

/-- The digit-tagged projective term list for window `i`. -/
def pdpOf (base i : ℕ) (pterms : List (ℕ × PVes)) : List (ℕ × PVes) :=
  pterms.map fun t => (Msm.digit base i t.1, t.2)

/-- The projective window value: build the `base − 1` projective buckets, then run the projective
suffix-sum accumulation. -/
def pwindowValue (base i : ℕ) (pterms : List (ℕ × PVes)) : PVes :=
  (List.foldr paccStep (pid, pid)
    ((List.range (base - 1)).map fun k => pbucketOf (pdpOf base i pterms) (k + 1))).2

/-- The projective window value is valid and matches `Fast.Msm.windowValue` of the `toAffine`-mapped
terms. -/
theorem pwindowValue_spec (base i : ℕ) (pterms : List (ℕ × PVes))
    (h : ∀ p ∈ pterms, Valid p.2) :
    Valid (pwindowValue base i pterms)
      ∧ toAffine (pwindowValue base i pterms)
        = Msm.windowValue base i (pterms.map fun t => (t.1, toAffine t.2)) := by
  have hdp : ∀ p ∈ pdpOf base i pterms, Valid p.2 := by
    intro p hp
    rw [pdpOf, List.mem_map] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact h t ht
  simp only [pwindowValue]
  set buckets := (List.range (base - 1)).map fun k => pbucketOf (pdpOf base i pterms) (k + 1)
    with hbuck
  have hbval : ∀ P ∈ buckets, Valid P := by
    intro P hP
    rw [hbuck, List.mem_map] at hP
    obtain ⟨k, _, rfl⟩ := hP
    exact (pbucketOf_spec _ _ hdp).1
  obtain ⟨_, hv2, heq⟩ := foldr_paccStep_spec buckets hbval
  refine ⟨hv2, ?_⟩
  have hmap : buckets.map toAffine
      = (List.range (base - 1)).map fun k =>
          Msm.bucketOf (Msm.dpOf base i (pterms.map fun t => (t.1, toAffine t.2))) (k + 1) := by
    rw [hbuck, List.map_map]
    apply List.map_congr_left
    intro k _
    rw [Function.comp_apply, (pbucketOf_spec _ _ hdp).2]
    congr 1
    simp only [pdpOf, Msm.dpOf, List.map_map, Function.comp_def]
  rw [Msm.windowValue, ← hmap, ← heq]

/-! ## Projective Horner fold, mirroring `Fast.Msm.hornerList` -/

/-- Horner across windows in projective coordinates: each `base •` doubling is the fast binary
scalar multiplication `pnsmulFast base`, and the window value is folded in with `padd`. -/
def phornerList (base : ℕ) (vals : List PVes) : PVes :=
  List.foldr (fun v acc => padd (pnsmulFast base acc) v) pid vals

/-- The projective Horner fold is valid and matches `Fast.Msm.hornerList` of the `toAffine`-mapped
window values; each `2^c`-fold doubling transports via `pnsmulFast_spec`. -/
theorem phornerList_spec (base : ℕ) (vals : List PVes) (h : ∀ P ∈ vals, Valid P) :
    Valid (phornerList base vals)
      ∧ toAffine (phornerList base vals) = Msm.hornerList base (vals.map toAffine) := by
  induction vals with
  | nil => exact ⟨valid_pid, by simp [phornerList, Msm.hornerList, toAffine_pid]⟩
  | cons v xs ih =>
    have hv : Valid v := h v (by simp)
    have hxs : ∀ P ∈ xs, Valid P := fun P hP => h P (by simp [hP])
    obtain ⟨hvacc, heq⟩ := ih hxs
    have hstep : phornerList base (v :: xs)
        = padd (pnsmulFast base (phornerList base xs)) v := rfl
    rw [hstep]
    refine ⟨valid_padd (pnsmulFast_spec hvacc base).1 hv, ?_⟩
    rw [toAffine_padd (pnsmulFast_spec hvacc base).1 hv, (pnsmulFast_spec hvacc base).2, heq,
      List.map_cons]
    simp only [Msm.hornerList, List.foldr_cons]

/-! ## The projective Pippenger MSM and its equality to the affine accelerator -/

/-- **Windowed Pippenger MSM run in projective coordinates.**  Each affine point is lifted via
`ofAffine`; the same windowed algorithm (digits, buckets, suffix-sum, Horner doublings) runs over
`PVes` with `padd`/`pnsmulFast`; a single `toAffine` (one field inversion) is taken at the end.
Proven equal to the affine `Fast.Msm.pippenger` (`pippengerProj_eq`). -/
def pippengerProj (c : ℕ) (terms : List (ℕ × Projective.G)) : Projective.G :=
  toAffine (phornerList (2 ^ c)
    ((List.range (Msm.numWindows c terms)).map fun i =>
      pwindowValue (2 ^ c) i (terms.map fun t => (t.1, ofAffine t.2))))

/-- **The projective Pippenger equals the affine Pippenger.**  Lifting by `ofAffine` and reading back
by `toAffine` is the identity on terms (`toAffine_ofAffine`); each window and the Horner fold commute
with `toAffine` (`pwindowValue_spec`, `phornerList_spec`), so the whole projective interior collapses
to the affine `Fast.Msm.pippenger`. -/
theorem pippengerProj_eq (c : ℕ) (terms : List (ℕ × Projective.G)) :
    pippengerProj c terms = Msm.pippenger c terms := by
  rw [pippengerProj]
  set pterms := terms.map (fun t => (t.1, ofAffine t.2)) with hpterms
  set windows := (List.range (Msm.numWindows c terms)).map fun i => pwindowValue (2 ^ c) i pterms
    with hwin
  have hval : ∀ p ∈ pterms, Valid p.2 := by
    intro p hp
    rw [hpterms, List.mem_map] at hp
    obtain ⟨t, _, rfl⟩ := hp
    exact valid_ofAffine t.2
  have hf : pterms.map (fun t => (t.1, toAffine t.2)) = terms := by
    rw [hpterms, List.map_map]
    conv_rhs => rw [← List.map_id terms]
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, toAffine_ofAffine, id_eq]
  have hwval : ∀ P ∈ windows, Valid P := by
    intro P hP
    rw [hwin, List.mem_map] at hP
    obtain ⟨i, _, rfl⟩ := hP
    exact (pwindowValue_spec (2 ^ c) i pterms hval).1
  rw [(phornerList_spec (2 ^ c) windows hwval).2, Msm.pippenger]
  congr 1
  rw [hwin, List.map_map]
  apply List.map_congr_left
  intro i _
  rw [Function.comp_apply, (pwindowValue_spec (2 ^ c) i pterms hval).2, hf]

/-- **The projective Pippenger equals the naive MSM.**  End-to-end correctness for `c ≥ 1`. -/
theorem pippengerProj_eq_msm (c : ℕ) (hc : 0 < c) (terms : List (ℕ × Projective.G)) :
    pippengerProj c terms = (terms.map fun t => t.1 • t.2).sum := by
  rw [pippengerProj_eq, Msm.pippenger_eq_msm c hc]

/-! ## The `commit_lagrange` wrapper -/

/-- The fast `commit_lagrange` run in projective coordinates: projective windowed Pippenger over the
`(coeffᵢ.val, basisᵢ)` terms (single final inversion), plus the blind.  The terms are zipped
identically to `Fast.Msm.commitLagrangeFastWith` so the wrapper equality reuses `zip_terms_eq`. -/
def commitLagrangeProjWith (c : ℕ) (blind : Projective.G) (basis : List Projective.G)
    (coeffs : List Fp) : Projective.G :=
  pippengerProj c
    ((coeffs.zip (basis ++ List.replicate (coeffs.length - basis.length) 0)).map
      fun t => (t.1.val, t.2)) + blind

/-- **The projective commitment equals the naive `commit_lagrange` spec**
(`Fast.Msm.commitLagrangeSpec`, verbatim from `Keygen.commitLagrangeWith`). -/
theorem commitLagrangeProjWith_eq (c : ℕ) (hc : 0 < c)
    (blind : Projective.G) (basis : List Projective.G) (coeffs : List Fp) :
    commitLagrangeProjWith c blind basis coeffs = Msm.commitLagrangeSpec blind basis coeffs := by
  unfold commitLagrangeProjWith Msm.commitLagrangeSpec
  rw [pippengerProj_eq, Msm.zip_terms_eq, Msm.pippenger_eq_msm c hc, List.map_map]
  rfl

end Zcash.Snark.Keygen.Fast.MsmProj
