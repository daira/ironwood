import Mathlib.Tactic
import Zcash.Snark.Fingerprint.SchwartzZippel
import Zcash.Snark.Fingerprint.Rational.Rep

/-!
# The quantified random match: ε for a competing coefficient family

The generic half of the quantified match's ε theorem. The representation walk
(`Fingerprint/Rational/`) delivers, per capture family, a `RationalCoeffFamily`: polynomial
numerators over enumerated challenge-only denominators for every coefficient position of the
assembled MSM, agreeing with `assemble?`'s output on the good event. This module prices what
that buys:

* `card_exists_eval_zero_le` — a list of nonzero polynomials vanishes somewhere on at most the
  sum of its Schwartz–Zippel prices (union bound over the list).
* `goodEvent_compl_card_le` — the good event's complement costs at most
  `Σ totalDegree (denFactors vk) / p` (`denFactors_totalDegree_sum_le` turns this into the
  literal `(n + 1 + |lagrangeRotations| + |queryRotations| + k) / p`).
* `competing_coefficient_family_agreement_le` — **the ε theorem**: any competing numerator
  family of total degree ≤ `D` over the same denominators that differs from Lean's anywhere
  agrees with the assembled MSM at a uniformly random point with probability at most
  `(D + Σ totalDegree (denFactors vk)) / p`, `p = scalarFieldOrder ≈ 2²⁵⁴`. Either the point
  falls off the good event, or the agreement at the differing coordinate makes the nonzero
  difference polynomial vanish — Schwartz–Zippel.

Statements are conditioned on `assemble? = some m` throughout — never the total `assemble`,
whose zero-MSM fallback evaluates to the accept value (`Verifier/Assemble.lean`).

The comparison is positional over `MsmCoord`: on the good event the multiopen grouping is a
fixed combinatorial object, so Lean's coordinate frame is point-independent, and a family is
compared coordinate-by-coordinate. `MsmMatch`'s `List.Perm` on the `other` terms exists to
absorb append-order between two concrete assemblies; between *families* sharing base markers,
a permutation is a fixed re-indexing of `MsmCoord` and changes neither degrees nor ε
(precompose the competing family). A competing family over *different* denominators from the
same factor closure reduces to this statement by cross-multiplication at degree
`≤ D + Dden` — the denominators are challenge-only and event-nonvanishing on both sides.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm scalarFieldOrder)
open MvPolynomial Finset Fintype

/-- Union bound over a list of nonzero polynomials: the fraction of the sample space on which
some element vanishes is at most the sum of the elements' Schwartz–Zippel prices. -/
theorem card_exists_eval_zero_le {σ : Type*} [Fintype σ] [DecidableEq σ]
    (l : List (MvPolynomial σ Fp)) (hl : ∀ φ ∈ l, φ ≠ 0) :
    (#{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ φ ∈ l, eval f φ = 0} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card σ
      ≤ (((l.map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder := by
  classical
  induction l with
  | nil => simp
  | cons φ t ih =>
    have hφ0 : φ ≠ 0 := hl φ List.mem_cons_self
    have ht := ih fun ψ hψ => hl ψ (List.mem_cons_of_mem _ hψ)
    have hsub : {f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ φ :: t, eval f ψ = 0}
        ⊆ {f ∈ piFinset fun _ : σ => (univ : Finset Fp) | eval f φ = 0}
          ∪ {f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ t, eval f ψ = 0} := by
      intro f hf
      simp only [Finset.mem_filter, List.mem_cons, Finset.mem_union] at hf ⊢
      obtain ⟨hmem, ψ, hψ | hψ, hzero⟩ := hf
      · exact Or.inl ⟨hmem, hψ ▸ hzero⟩
      · exact Or.inr ⟨hmem, ψ, hψ, hzero⟩
    have hcard : #{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ φ :: t, eval f ψ = 0}
        ≤ #{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | eval f φ = 0}
          + #{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ t, eval f ψ = 0} :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have hφSZ := fingerprint_schwartz_zippel_index hφ0
    calc (#{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ φ :: t, eval f ψ = 0} : ℚ≥0)
          / (scalarFieldOrder : ℚ≥0) ^ Fintype.card σ
        ≤ ((#{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | eval f φ = 0}
            + #{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ t, eval f ψ = 0} : ℕ) : ℚ≥0)
              / (scalarFieldOrder : ℚ≥0) ^ Fintype.card σ := by
          gcongr
      _ = (#{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | eval f φ = 0} : ℚ≥0)
              / (scalarFieldOrder : ℚ≥0) ^ Fintype.card σ
            + (#{f ∈ piFinset fun _ : σ => (univ : Finset Fp) | ∃ ψ ∈ t, eval f ψ = 0} : ℚ≥0)
              / (scalarFieldOrder : ℚ≥0) ^ Fintype.card σ := by
          push_cast
          rw [add_div]
      _ ≤ (φ.totalDegree : ℚ≥0) / scalarFieldOrder
            + (((t.map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder :=
          add_le_add hφSZ ht
      _ = ((((φ :: t).map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder := by
          simp only [List.map_cons, List.sum_cons]
          push_cast
          rw [add_div]

/-- The good event's complement, priced: the fraction of the sample space off the good event is
at most the summed Schwartz–Zippel price of the enumerated denominator factors
(`denFactors_totalDegree_sum_le` bounds the sum by
`n + 1 + |lagrangeRotations| + |queryRotations| + k`). -/
theorem goodEvent_compl_card_le {shape : Shape} {G : Type*} (vk : VerifyingKey shape Fp G)
    (hn : 0 < vk.n) :
    (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | ¬ GoodEvent vk f} : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape)
      ≤ ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder := by
  classical
  have hcongr : {f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | ¬ GoodEvent vk f}
      = {f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
          ∃ φ ∈ denFactors vk, eval f φ = 0} := by
    refine Finset.filter_congr fun f _ => ?_
    simp [GoodEvent]
  rw [hcongr]
  exact card_exists_eval_zero_le _ (denFactors_ne_zero vk hn)

/-- A rational representation of the assembled MSM's whole coefficient family on the good
event: per coefficient position, a polynomial numerator over a denominator from the enumerated
factor closure, with uniform degree bounds, agreeing with `assemble?`'s output — which the
`represents` field also pins to `some` with a fixed `other` length. The representation walk
(`Fingerprint/Rational/`) constructs a term of this structure per capture family; the ε theorem
consumes one. -/
structure RationalCoeffFamily {shape : Shape} {G : Type*} [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape Fp G) (ic : Fin shape.numProofs → ℕ → G)
    (base : ProofString shape Fp G) (L D Dden : ℕ) where
  num : MsmCoord shape.k L → MvPolynomial (ScalarSlot shape) Fp
  den : MsmCoord shape.k L → MvPolynomial (ScalarSlot shape) Fp
  den_mem : ∀ c, den c ∈ Submonoid.closure {φ | φ ∈ denFactors vk}
  num_totalDegree_le : ∀ c, (num c).totalDegree ≤ D
  den_totalDegree_le : ∀ c, (den c).totalDegree ≤ Dden
  represents : ∀ pt : Point shape, GoodEvent vk pt →
    ∃ m : Msm shape.k Fp G,
      assemble? vk ic (Point.toProofString pt base) (Point.toChallenges pt) = some m
        ∧ m.other.length = L
        ∧ ∀ c : MsmCoord shape.k L, m.coeffAt c * eval pt (den c) = eval pt (num c)

open Classical in
/-- **The ε theorem, generic form.** Any competing numerator family of total degree ≤ `D` over
the same denominators that differs from Lean's at some coordinate agrees with the assembled MSM
at a uniformly random sample-space point with probability at most
`(D + Σ totalDegree (denFactors vk)) / p`: either the point falls off the good event (the
second summand, `goodEvent_compl_card_le`), or agreement at the differing coordinate makes the
nonzero difference polynomial vanish (the first summand, Schwartz–Zippel). Conditioned on
`assemble? = some m` — the total `assemble`'s zero fallback evaluates to the accept value and
must not appear here. -/
theorem competing_coefficient_family_agreement_le {shape : Shape} {G : Type*}
    [DecidableEq G] [Inhabited G]
    {vk : VerifyingKey shape Fp G} {ic : Fin shape.numProofs → ℕ → G}
    {base : ProofString shape Fp G} {L D Dden : ℕ}
    (fam : RationalCoeffFamily vk ic base L D Dden) (hn : 0 < vk.n)
    (num' : MsmCoord shape.k L → MvPolynomial (ScalarSlot shape) Fp)
    (hdeg' : ∀ c, (num' c).totalDegree ≤ D)
    (c₀ : MsmCoord shape.k L) (hne : num' c₀ ≠ fam.num c₀) :
    (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString f base) (Point.toChallenges f) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L, m.coeffAt c * eval f (fam.den c) = eval f (num' c)}
        : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape)
      ≤ ((D : ℚ≥0) + (((denFactors vk).map totalDegree).sum : ℕ))
          / scalarFieldOrder := by
  set d : MvPolynomial (ScalarSlot shape) Fp := fam.num c₀ - num' c₀ with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hddeg : d.totalDegree ≤ D :=
    le_trans (totalDegree_sub _ _) (max_le (fam.num_totalDegree_le c₀) (hdeg' c₀))
  have hsub : {f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString f base) (Point.toChallenges f) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L, m.coeffAt c * eval f (fam.den c) = eval f (num' c)}
      ⊆ {f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | ¬ GoodEvent vk f}
        ∪ {f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | eval f d = 0} := by
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_union] at hf ⊢
    obtain ⟨hmem, m, hm, _, hagree⟩ := hf
    by_cases hgood : GoodEvent vk f
    · refine Or.inr ⟨hmem, ?_⟩
      obtain ⟨m', hm', _, hrep⟩ := fam.represents f hgood
      have hmm : m = m' := Option.some.inj (hm ▸ hm')
      have h1 := hrep c₀
      have h2 := hagree c₀
      rw [hmm] at h2
      rw [hd, map_sub, sub_eq_zero, ← h1, ← h2]
    · exact Or.inl ⟨hmem, hgood⟩
  have hcard := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hbad := goodEvent_compl_card_le vk hn
  have hzero := fingerprint_schwartz_zippel_index hd0
  calc (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) |
        ∃ m : Msm shape.k Fp G,
          assemble? vk ic (Point.toProofString f base) (Point.toChallenges f) = some m
            ∧ m.other.length = L
            ∧ ∀ c : MsmCoord shape.k L, m.coeffAt c * eval f (fam.den c) = eval f (num' c)}
        : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape)
      ≤ ((#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | ¬ GoodEvent vk f}
          + #{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | eval f d = 0}
          : ℕ) : ℚ≥0)
          / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape) := by
        gcongr
    _ = (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | ¬ GoodEvent vk f}
          : ℚ≥0) / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape)
        + (#{f ∈ piFinset fun _ : ScalarSlot shape => (univ : Finset Fp) | eval f d = 0}
          : ℚ≥0) / (scalarFieldOrder : ℚ≥0) ^ Fintype.card (ScalarSlot shape) := by
        push_cast
        rw [add_div]
    _ ≤ ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder
        + (d.totalDegree : ℚ≥0) / scalarFieldOrder := add_le_add hbad hzero
    _ ≤ ((((denFactors vk).map totalDegree).sum : ℕ) : ℚ≥0) / scalarFieldOrder
        + (D : ℚ≥0) / scalarFieldOrder := by
        gcongr
    _ = ((D : ℚ≥0) + (((denFactors vk).map totalDegree).sum : ℕ)) / scalarFieldOrder := by
        rw [add_comm, add_div]

end Zcash.Snark
