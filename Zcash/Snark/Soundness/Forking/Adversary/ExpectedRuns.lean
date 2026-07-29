import Zcash.Snark.Soundness.Forking.Adversary.Recursive

/-!
# Expected extractor runs under fork spread

Under optional fork spread, `E[runs] ≤ (6·|F|/(σ₀−1))^k`; `.runs` counts adversary calls.
The separate unconditional AFK analysis is completed in `ExpectedRunsPoly`.
-/

namespace Zcash.Snark

section RankCounting

variable {F : Type*} [DecidableEq F] {n : ℕ}

/-- The number of members of `A` sampled strictly before `x` by the order `e`. For `x ∈ A` this is
`x`'s zero-based rank within `A`. -/
def scanRank (e : Fin n ≃ F) (A : Finset F) (x : F) : ℕ :=
  (A.filter (fun a => e.symm a < e.symm x)).card

omit [DecidableEq F] in
/-- Ranks are strictly monotone along the sampling order. -/
theorem scanRank_lt_of_lt (e : Fin n ≃ F) (A : Finset F) {x y : F}
    (hx : x ∈ A) (hxy : e.symm x < e.symm y) : scanRank e A x < scanRank e A y := by
  apply Finset.card_lt_card
  constructor
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, lt_trans ha.2 hxy⟩
  · intro hsub
    have hxmem : x ∈ A.filter (fun a => e.symm a < e.symm y) :=
      Finset.mem_filter.mpr ⟨hx, hxy⟩
    have := hsub hxmem
    rw [Finset.mem_filter] at this
    exact absurd this.2 (lt_irrefl _)

omit [DecidableEq F] in
/-- At most `j` members of `A` have rank below `j`: ranks are injective on `A`. -/
theorem card_filter_scanRank_lt_le (e : Fin n ≃ F) (A : Finset F) (j : ℕ) :
    (A.filter (fun x => scanRank e A x < j)).card ≤ j := by
  have hinj : Set.InjOn (scanRank e A) (A.filter (fun x => scanRank e A x < j)) := by
    intro x hx y hy hxy
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    rcases lt_trichotomy (e.symm x) (e.symm y) with h | h | h
    · exact absurd hxy (Nat.ne_of_lt (scanRank_lt_of_lt e A hx.1 h))
    · exact e.symm.injective h
    · exact absurd hxy.symm (Nat.ne_of_lt (scanRank_lt_of_lt e A hy.1 h))
  calc (A.filter (fun x => scanRank e A x < j)).card
      = ((A.filter (fun x => scanRank e A x < j)).image (scanRank e A)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range j).card := by
        apply Finset.card_le_card
        intro r hr
        rw [Finset.mem_image] at hr
        obtain ⟨x, hx, rfl⟩ := hr
        rw [Finset.mem_filter] at hx
        exact Finset.mem_range.mpr hx.2
    _ = j := Finset.card_range j

/-- A finite set is closed under swapping two of its members. -/
theorem image_swap_of_mem {A : Finset F} {x y : F} (hx : x ∈ A) (hy : y ∈ A) :
    A.image (Equiv.swap x y) = A := by
  ext a
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rcases eq_or_ne b x with rfl | hbx
    · rwa [Equiv.swap_apply_left]
    rcases eq_or_ne b y with rfl | hby
    · rwa [Equiv.swap_apply_right]
    · rwa [Equiv.swap_apply_of_ne_of_ne hbx hby]
  · intro ha
    refine ⟨Equiv.swap x y a, ?_, Equiv.swap_apply_self x y a⟩
    rcases eq_or_ne a x with rfl | hax
    · rw [Equiv.swap_apply_left]; exact hy
    rcases eq_or_ne a y with rfl | hay
    · rw [Equiv.swap_apply_right]; exact hx
    · rw [Equiv.swap_apply_of_ne_of_ne hax hay]; exact ha

/-- Swapping two members of `A` swaps their ranks: composing the order with `Equiv.swap x y`
carries the rank of `x` to the rank of `y`. -/
theorem scanRank_trans_swap (e : Fin n ≃ F) (A : Finset F) {x y : F}
    (hx : x ∈ A) (hy : y ∈ A) :
    scanRank (e.trans (Equiv.swap x y)) A x = scanRank e A y := by
  have hsymm : ∀ a : F, (e.trans (Equiv.swap x y)).symm a = e.symm (Equiv.swap x y a) := by
    intro a
    rw [Equiv.symm_trans_apply, Equiv.symm_swap]
  unfold scanRank
  have h1 : A.filter (fun a => (e.trans (Equiv.swap x y)).symm a
        < (e.trans (Equiv.swap x y)).symm x)
      = A.filter (fun a => e.symm (Equiv.swap x y a) < e.symm y) := by
    apply Finset.filter_congr
    intro a _
    rw [hsymm a, hsymm x, Equiv.swap_apply_left]
  rw [h1]
  calc (A.filter (fun a => e.symm (Equiv.swap x y a) < e.symm y)).card
      = ((A.filter (fun a => e.symm (Equiv.swap x y a) < e.symm y)).image
          (Equiv.swap x y)).card :=
        (Finset.card_image_of_injective _ (Equiv.injective _)).symm
    _ = ((A.image (Equiv.swap x y)).filter (fun b => e.symm b < e.symm y)).card := by
        rw [Finset.filter_image]
    _ = (A.filter (fun b => e.symm b < e.symm y)).card := by
        rw [image_swap_of_mem hx hy]

variable [Fintype F]

/-- Two members of `A` are low-rank in equally many orders: composing with the swap is a bijection
of the order space exchanging the two events. -/
theorem card_orders_scanRank_lt_congr (A : Finset F) {x y : F} (hx : x ∈ A) (hy : y ∈ A)
    (j : ℕ) :
    (Finset.univ.filter (fun e : Fin n ≃ F => scanRank e A x < j)).card
      = (Finset.univ.filter (fun e : Fin n ≃ F => scanRank e A y < j)).card := by
  have himg : (Finset.univ.filter (fun e : Fin n ≃ F => scanRank e A x < j)).image
      (fun e => e.trans (Equiv.swap x y))
      = Finset.univ.filter (fun e : Fin n ≃ F => scanRank e A y < j) := by
    ext e'
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨e, he, rfl⟩
      rw [show Equiv.swap x y = Equiv.swap y x from Equiv.swap_comm x y]
      rwa [scanRank_trans_swap e A hy hx]
    · intro he'
      refine ⟨e'.trans (Equiv.swap x y), ?_, ?_⟩
      · rwa [scanRank_trans_swap e' A hx hy]
      · ext i
        simp [Equiv.swap_apply_self]
  rw [← himg]
  refine (Finset.card_image_of_injective _ ?_).symm
  intro e₁ e₂ h
  ext i
  have := congrArg (fun e : Fin n ≃ F => Equiv.swap x y (e i)) h
  simpa [Equiv.swap_apply_self] using this

/-- A member of `A` has rank below `j` in at most a `j/|A|` fraction of sampling orders. -/
theorem card_scanRank_lt_mul_le (A : Finset F) {x : F} (hx : x ∈ A) (j : ℕ) :
    A.card * (Finset.univ.filter (fun e : Fin n ≃ F => scanRank e A x < j)).card
      ≤ j * Fintype.card (Fin n ≃ F) := by
  have hdouble : A.card *
      (Finset.univ.filter (fun e : Fin n ≃ F => scanRank e A x < j)).card
      = ∑ y ∈ A, (Finset.univ.filter (fun e : Fin n ≃ F => scanRank e A y < j)).card := by
    rw [Finset.sum_congr rfl (fun y hy => card_orders_scanRank_lt_congr A hy hx j),
      Finset.sum_const, smul_eq_mul]
  rw [hdouble]
  have hswap : ∑ y ∈ A, (Finset.univ.filter (fun e : Fin n ≃ F => scanRank e A y < j)).card
      = ∑ e : Fin n ≃ F, (A.filter (fun y => scanRank e A y < j)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  calc ∑ e : Fin n ≃ F, (A.filter (fun y => scanRank e A y < j)).card
      ≤ ∑ _e : Fin n ≃ F, j := Finset.sum_le_sum (fun e _ => card_filter_scanRank_lt_le e A j)
    _ = j * Fintype.card (Fin n ≃ F) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

end RankCounting

section Marginalization

/-- Summing a function of one coordinate of a finite function space marginalizes: every value of
the coordinate appears in `|β|^(|α|−1)` assignments. -/
theorem sum_eval_pi {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (a : α) (g : β → ℕ) :
    ∑ f : α → β, g (f a) = Fintype.card β ^ (Fintype.card α - 1) * ∑ b : β, g b := by
  rw [← Equiv.sum_comp (Equiv.piSplitAt a (fun _ : α => β)).symm (fun f => g (f a))]
  have happ : ∀ p : β × ({a' // a' ≠ a} → β),
      ((Equiv.piSplitAt a (fun _ : α => β)).symm p) a = p.1 := by
    intro p
    simp [Equiv.piSplitAt_symm_apply]
  simp only [happ]
  rw [Fintype.sum_prod_type_right]
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  rw [Fintype.card_fun, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

end Marginalization

section PaidScan

variable {F α : Type*} [Zero F] [DecidableEq F]

/-- Candidates paid by a scan: failures followed by its first success, if any. -/
def paidList (attempt : F → RecursiveForkAttempt α) (seen : List F) : List F → List F
  | [] => []
  | u :: us =>
      if u = 0 ∨ u ∈ seen then paidList attempt seen us
      else
        match (attempt u).output with
        | some _ => [u]
        | none => u :: paidList attempt seen us

/-- The scanner's run count is the sum of the paid candidates' run counts. -/
theorem nextForkChallenge_runs_eq (attempt : F → RecursiveForkAttempt α) (seen : List F) :
    (l : List F) →
    (nextForkChallenge attempt seen l).runs
      = ((paidList attempt seen l).map (fun u => (attempt u).runs)).sum
  | [] => rfl
  | u :: us => by
      simp only [nextForkChallenge, paidList]
      split
      · exact nextForkChallenge_runs_eq attempt seen us
      · cases hu : (attempt u).output with
        | some result => simp
        | none =>
            simp only [RecursiveForkAttempt.addRuns, List.map_cons, List.sum_cons]
            rw [nextForkChallenge_runs_eq attempt seen us, Nat.add_comm]

/-- The paid candidates form a sublist of the scanned order. -/
theorem paidList_sublist (attempt : F → RecursiveForkAttempt α) (seen : List F) :
    (l : List F) → List.Sublist (paidList attempt seen l) l
  | [] => List.Sublist.refl []
  | u :: us => by
      simp only [paidList]
      split
      · exact (paidList_sublist attempt seen us).cons u
      · cases hu : (attempt u).output with
        | some result => exact (List.nil_sublist us).cons_cons u
        | none => exact (paidList_sublist attempt seen us).cons_cons u

/-- Every paid candidate is eligible, and every eligible candidate strictly before it in the
scanned order failed. -/
theorem mem_paidList (attempt : F → RecursiveForkAttempt α) (seen : List F) :
    (l : List F) → ∀ u ∈ paidList attempt seen l,
      u ≠ 0 ∧ u ∉ seen ∧ ∃ l₁ l₂, l = l₁ ++ u :: l₂ ∧
        ∀ v ∈ l₁, v ≠ 0 → v ∉ seen → (attempt v).output = none
  | [] => by intro u hu; simp [paidList] at hu
  | v :: vs => by
      intro u hu
      simp only [paidList] at hu
      split at hu
      · rename_i hskip
        obtain ⟨h0, hseen, l₁, l₂, rfl, hfail⟩ := mem_paidList attempt seen vs u hu
        refine ⟨h0, hseen, v :: l₁, l₂, rfl, ?_⟩
        intro w hw hw0 hwseen
        rcases List.mem_cons.mp hw with rfl | hw
        · exact absurd hskip (by simp [hw0, hwseen])
        · exact hfail w hw hw0 hwseen
      · rename_i hfresh
        cases hv : (attempt v).output with
        | some result =>
            rw [hv] at hu
            simp only [List.mem_singleton] at hu
            subst u
            exact ⟨fun h => hfresh (Or.inl h), fun h => hfresh (Or.inr h), [], vs, rfl,
              by intro w hw; simp at hw⟩
        | none =>
            rw [hv] at hu
            rcases List.mem_cons.mp hu with rfl | hu
            · exact ⟨fun h => hfresh (Or.inl h), fun h => hfresh (Or.inr h), [], vs, rfl,
                by intro w hw; simp at hw⟩
            · obtain ⟨h0, hseen, l₁, l₂, rfl, hfail⟩ := mem_paidList attempt seen vs u hu
              refine ⟨h0, hseen, v :: l₁, l₂, rfl, ?_⟩
              intro w hw hw0 hwseen
              rcases List.mem_cons.mp hw with rfl | hw
              · exact hv
              · exact hfail w hw hw0 hwseen

/-- A successful scan splits its order at the selected challenge, with every eligible challenge
before it failing. -/
theorem nextForkChallenge_output_decompose (attempt : F → RecursiveForkAttempt α)
    (seen : List F) :
    (l : List F) → ∀ {u₂ : F} {c₂ : α} {rest seen' : List F},
    (nextForkChallenge attempt seen l).output = some ((u₂, c₂), (rest, seen')) →
    ∃ l₁, l = l₁ ++ u₂ :: rest ∧
      ∀ v ∈ l₁, v ≠ 0 → v ∉ seen → (attempt v).output = none
  | [] => by intro hout; simp [nextForkChallenge] at hout
  | v :: vs => by
      intro hout
      simp only [nextForkChallenge] at hout
      split at hout
      · rename_i hskip
        obtain ⟨l₁, rfl, hfail⟩ := nextForkChallenge_output_decompose attempt seen vs hout
        refine ⟨v :: l₁, rfl, ?_⟩
        intro w hw hw0 hwseen
        rcases List.mem_cons.mp hw with rfl | hw
        · exact absurd hskip (by simp [hw0, hwseen])
        · exact hfail w hw hw0 hwseen
      · rename_i hfresh
        cases hv : (attempt v).output with
        | some result =>
            rw [hv] at hout
            simp only [Option.some.injEq, Prod.mk.injEq] at hout
            obtain ⟨⟨rfl, -⟩, rfl, -⟩ := hout
            exact ⟨[], rfl, by intro w hw; simp at hw⟩
        | none =>
            rw [hv] at hout
            simp only [RecursiveForkAttempt.addRuns] at hout
            obtain ⟨l₁, rfl, hfail⟩ := nextForkChallenge_output_decompose attempt seen vs hout
            refine ⟨v :: l₁, rfl, ?_⟩
            intro w hw hw0 hwseen
            rcases List.mem_cons.mp hw with rfl | hw
            · exact hv
            · exact hfail w hw hw0 hwseen

end PaidScan

section Positions

variable {F : Type*}

/-- In the list enumeration of a sampling order, the elements before `u` are exactly those the
order samples before `u`. -/
theorem mem_left_of_ofFn_decompose {n : ℕ} (order : Fin n ≃ F) {l₁ l₂ : List F} {u : F}
    (hdec : List.ofFn order = l₁ ++ u :: l₂) (v : F) :
    v ∈ l₁ ↔ order.symm v < order.symm u := by
  have hlen : l₁.length + (l₂.length + 1) = n := by
    have := congrArg List.length hdec
    simp only [List.length_ofFn, List.length_append, List.length_cons] at this
    omega
  have hidx : l₁.length < n := by omega
  have hu : order ⟨l₁.length, hidx⟩ = u := by
    have h1 : (List.ofFn order)[l₁.length]? = some (order ⟨l₁.length, hidx⟩) := by
      rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hidx)]
      rw [List.getElem_ofFn]
    rw [hdec, List.getElem?_append_right (le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at h1
    exact h1.symm
  have husymm : order.symm u = ⟨l₁.length, hidx⟩ := by
    rw [← hu, Equiv.symm_apply_apply]
  constructor
  · intro hv
    obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hv
    have hin : i < n := by omega
    have h1 : (List.ofFn order)[i]? = some v := by
      rw [hdec, List.getElem?_append_left (by exact hi), List.getElem?_eq_getElem hi]
      exact congrArg some hiv
    rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hin),
      List.getElem_ofFn, Option.some.injEq] at h1
    rw [← h1, Equiv.symm_apply_apply, husymm]
    exact hi
  · intro hv
    rw [husymm] at hv
    have hvn : (order.symm v : ℕ) < l₁.length := hv
    have h1 : (List.ofFn order)[(order.symm v : ℕ)]? = some v := by
      rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact (order.symm v).isLt),
        List.getElem_ofFn]
      simp
    rw [hdec, List.getElem?_append_left hvn] at h1
    exact List.mem_of_getElem? h1

end Positions

section SumHelper

/-- A nodup list of paid candidates inside a filter set is dominated by the filter sum. -/
theorem sum_map_le_sum_filter {F : Type*} [DecidableEq F] [Fintype F] {p : List F}
    (hnd : p.Nodup) (cond : F → Prop) [DecidablePred cond] (hsub : ∀ u ∈ p, cond u)
    (f : F → ℕ) :
    (p.map f).sum ≤ ∑ u ∈ Finset.univ.filter cond, f u := by
  rw [← List.sum_toFinset _ hnd]
  apply Finset.sum_le_sum_of_subset
  intro u hu
  rw [List.mem_toFinset] at hu
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hsub u hu⟩

end SumHelper

section ScanRankBound

variable {F : Type*} [Zero F] [DecidableEq F] [Fintype F]

/-- A scan pays only candidates preceded by fewer than two good challenges. -/
theorem nextForkChallenge_runs_le_rank_sum {α : Type*}
    (attempt : F → RecursiveForkAttempt α) (order : Fin (Fintype.card F) ≃ F)
    (M : Finset F) (hM : ∀ v ∈ M, v ≠ 0 ∧ (attempt v).output.isSome)
    (seen : List F) (l₀ l' : List F) (hdec : List.ofFn (⇑order) = l₀ ++ l')
    (hMseen : ∀ v ∈ M, v ∈ seen → v ∈ l₀)
    (hMl₀ : (M.filter (· ∈ l₀)).card ≤ 1) :
    (nextForkChallenge attempt seen l').runs
      ≤ ∑ u ∈ Finset.univ.filter (fun u : F => scanRank order (insert u M) u < 2),
          (attempt u).runs := by
  rw [nextForkChallenge_runs_eq]
  have hndl : (List.ofFn (⇑order)).Nodup := List.nodup_ofFn.mpr order.injective
  rw [hdec] at hndl
  obtain ⟨hndl₀, hndl', hdisj⟩ := List.nodup_append.mp hndl
  apply sum_map_le_sum_filter (List.Nodup.sublist (paidList_sublist attempt seen l') hndl')
  intro u hu
  obtain ⟨hu0, huseen, r₁, r₂, hdec', hfail⟩ := mem_paidList attempt seen l' u hu
  have hfull : List.ofFn (⇑order) = (l₀ ++ r₁) ++ u :: r₂ := by
    rw [hdec, hdec', List.append_assoc]
  have hins : (insert u M).filter (fun a => order.symm a < order.symm u)
      = M.filter (fun a => order.symm a < order.symm u) := by
    rw [Finset.filter_insert, if_neg (lt_irrefl _)]
  show ((insert u M).filter (fun a => order.symm a < order.symm u)).card < 2
  rw [hins]
  have hsub : M.filter (fun a => order.symm a < order.symm u) ⊆ M.filter (· ∈ l₀) := by
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨hv.1, ?_⟩
    have hbefore : v ∈ l₀ ++ r₁ := (mem_left_of_ofFn_decompose order hfull v).mpr hv.2
    rcases List.mem_append.mp hbefore with hvl | hvr
    · exact hvl
    · exfalso
      obtain ⟨hv0, hvsome⟩ := hM v hv.1
      by_cases hvseen : v ∈ seen
      · have hvl0 := hMseen v hv.1 hvseen
        have hvl' : v ∈ l' := by
          rw [hdec']
          exact List.mem_append.mpr (Or.inl hvr)
        exact absurd rfl (hdisj v hvl0 v hvl')
      · have hnone := hfail v hvr hv0 hvseen
        rw [hnone] at hvsome
        simp at hvsome
  calc (M.filter (fun a => order.symm a < order.symm u)).card
      ≤ (M.filter (· ∈ l₀)).card := Finset.card_le_card hsub
    _ ≤ 1 := hMl₀
    _ < 2 := by omega

end ScanRankBound

section NodeBound

variable {T F G P ι : Type*} [DecidableEq T] [Field F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [Fintype ι]

variable (basis : ι → G) (k : ℕ) (A : OracleComp T F P) (prefixes : P → Fin k → T)
  (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
  (final : P → F × F) (win : (T → F) → P → Prop) (decideWin : ∀ O p, Decidable (win O p))

/-- Rerun the adversary with round `m` reprogrammed, rejecting changed trunks before recursion. -/
def scanCandidate {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k) (O : T → F)
    (childC : F → RecursiveForkCoins F d) (u : F) :
    RecursiveForkAttempt (AlgebraicDForkCert (F := F) basis d) :=
  let j : Fin k := ⟨m, by omega⟩
  let t : T := prefixes (A.run O) j
  let O' := Function.update O t u
  let p' := A.run O'
  if prefixes p' j = t then
    recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin
      (m + 1) (by omega) O' p' (childC u)
  else { output := none, runs := 1 }

/-- The node's good set: nonzero challenges whose reprogrammed candidate returns a certificate. -/
noncomputable def goodChallenges [Fintype F] {d : ℕ} (m : ℕ) (hmk : m + (d + 1) = k)
    (O : T → F) (childC : F → RecursiveForkCoins F d) : Finset F :=
  Finset.univ.filter (fun u : F => u ≠ 0 ∧
    (scanCandidate basis k A prefixes rounds final win decideWin m hmk O childC u).output.isSome)

/-- One extractor node pays the abort unit, its first branch, and at most twice its low-rank
candidates. -/
theorem recursiveAlgebraicForkFrom_node_runs_le [Fintype F] {d m : ℕ}
    (hmk : m + (d + 1) = k) (O : T → F) (p : P) (order : Fin (Fintype.card F) ≃ F)
    (childC : F → RecursiveForkCoins F d) :
    (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin m hmk O p
        (.node (List.ofFn (⇑order)) childC)).runs
      ≤ 1
        + (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin (m + 1)
            (by omega) O p (childC (O (prefixes (A.run O) ⟨m, by omega⟩)))).runs
        + 2 * ∑ u ∈ Finset.univ.filter (fun u : F =>
              scanRank order (insert u ((goodChallenges basis k A prefixes rounds final win
                decideWin m hmk O childC).erase (O (prefixes (A.run O) ⟨m, by omega⟩)))) u < 2),
            (scanCandidate basis k A prefixes rounds final win decideWin m hmk O childC u).runs := by
  have hm : m < k := by omega
  have htail : m + 1 + d = k := by omega
  set u₁ : F := O (prefixes (A.run O) ⟨m, hm⟩) with hu₁def
  set M : Finset F := (goodChallenges basis k A prefixes rounds final win decideWin
    m hmk O childC).erase u₁ with hMdef
  set S : ℕ := ∑ u ∈ Finset.univ.filter (fun u : F => scanRank order (insert u M) u < 2),
    (scanCandidate basis k A prefixes rounds final win decideWin m hmk O childC u).runs
    with hSdef
  have hMgood : ∀ v ∈ M, v ≠ 0 ∧
      (scanCandidate basis k A prefixes rounds final win decideWin m hmk O childC v).output.isSome := by
    intro v hv
    have hv' := Finset.mem_of_mem_erase hv
    rw [goodChallenges, Finset.mem_filter] at hv'
    exact hv'.2
  show (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin m hmk O p
      (.node (List.ofFn (⇑order)) childC)).runs
      ≤ 1 + (recursiveAlgebraicForkFrom basis k A prefixes rounds final win decideWin (m + 1)
          htail O p (childC u₁)).runs + 2 * S
  simp only [recursiveAlgebraicForkFrom]
  split
  · -- the current challenge is zero: unit cost
    simp only
    exact le_trans (Nat.le_add_right 1 _) (Nat.le_add_right _ _)
  · rename_i hu₁0
    split
    · -- first branch failed: only its cost is paid
      simp only
      exact le_trans (Nat.le_add_left _ 1) (Nat.le_add_right _ _)
    · rename_i c₁ hfirst
      -- the two scans each pay only rank-< 2 candidates
      have hscan₂ : (nextForkChallenge
          (fun u => scanCandidate basis k A prefixes rounds final win decideWin m hmk O childC u)
          [u₁] (List.ofFn (⇑order))).runs ≤ S := by
        rw [hSdef]
        apply nextForkChallenge_runs_le_rank_sum _ order M hMgood [u₁] [] _
          (by rw [List.nil_append])
        · intro v hv hvseen
          rw [List.mem_singleton] at hvseen
          exact absurd (hvseen ▸ hv) (Finset.notMem_erase u₁ _)
        · simp
      split
      · -- second scan failed
        rename_i hsecond
        simp only
        refine le_trans (Nat.add_le_add (Nat.le_add_left _ 1) ?_) (le_of_eq rfl)
        calc (nextForkChallenge _ [u₁] (List.ofFn (⇑order))).runs
            ≤ S := hscan₂
          _ ≤ 2 * S := Nat.le_mul_of_pos_left S (by omega)
      · rename_i u₂ c₂ rest seen hsecond
        have hfresh := nextForkChallenge_output_fresh _ [u₁] hsecond
        obtain ⟨l₁, hdecomp, hfailL⟩ := nextForkChallenge_output_decompose _ [u₁] _ hsecond
        have hscan₃ : (nextForkChallenge
            (fun u => scanCandidate basis k A prefixes rounds final win decideWin m hmk O childC u)
            seen rest).runs ≤ S := by
          rw [hSdef]
          apply nextForkChallenge_runs_le_rank_sum _ order M hMgood seen (l₁ ++ [u₂]) rest
            (by rw [hdecomp, List.append_assoc, List.singleton_append])
          · intro v hv hvseen
            rw [hfresh.2.2, List.mem_cons, List.mem_singleton] at hvseen
            rcases hvseen with h | h
            · rw [h]
              exact List.mem_append.mpr (Or.inr (List.mem_singleton_self u₂))
            · exact absurd (h ▸ hv) (Finset.notMem_erase u₁ _)
          · have hsub : M.filter (· ∈ l₁ ++ [u₂]) ⊆ {u₂} := by
              intro v hv
              rw [Finset.mem_filter] at hv
              rcases List.mem_append.mp hv.2 with hvl | hvu
              · exfalso
                obtain ⟨hv0, hvsome⟩ := hMgood v hv.1
                have hvne₁ : v ∉ ([u₁] : List F) := by
                  rw [List.mem_singleton]
                  intro h
                  exact absurd (h ▸ hv.1) (Finset.notMem_erase u₁ _)
                have hnone : (scanCandidate basis k A prefixes rounds final win decideWin
                    m hmk O childC v).output = none := hfailL v hvl hv0 hvne₁
                rw [hnone] at hvsome
                simp at hvsome
              · rw [List.mem_singleton] at hvu
                rw [Finset.mem_singleton]
                exact hvu
            calc (M.filter (· ∈ l₁ ++ [u₂])).card
                ≤ ({u₂} : Finset F).card := Finset.card_le_card hsub
              _ = 1 := Finset.card_singleton u₂
        split
        · -- third scan failed
          simp only
          refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.le_add_left _ 1) hscan₂)
            hscan₃) ?_
          rw [Nat.add_assoc, ← Nat.two_mul]
        · -- full extraction
          simp only
          refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.le_add_left _ 1) hscan₂)
            hscan₃) ?_
          rw [Nat.add_assoc, ← Nat.two_mul]


end NodeBound

section SpreadTheorem

variable {T F G P ι : Type*} [DecidableEq T] [Field F] [DecidableEq F] [Fintype F]
  [AddCommGroup G] [Module F G] [Fintype ι]

variable (basis : ι → G) (k : ℕ) (A : OracleComp T F P) (prefixes : P → Fin k → T)
  (rounds : P → Fin k → AlgebraicPoint (F := F) basis × AlgebraicPoint (F := F) basis)
  (final : P → F × F) (win : (T → F) → P → Prop) (decideWin : ∀ O p, Decidable (win O p))





end SpreadTheorem

end Zcash.Snark
