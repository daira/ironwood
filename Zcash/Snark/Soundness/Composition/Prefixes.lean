import Zcash.Snark.Soundness.Composition.Assembly

/-!
# The concrete multiopen prefixes for the composition ladder

The ladder endpoint (`Soundness.Composition.Assembly`) needs to know where the four multiopen
challenges live in the transcript. This module pins them: the four squeeze points `x₁,x₂,x₃,x₄`,
with the ladder's reads at those points being exactly the multiopen challenges the verifier uses
(`multiopenPrefixReads_eq`).

## The ladder decode at these prefixes

The decode's *chain* half is discharged outright, following `fullDecodeDeployed`
(`Forking.Adversary.Algebraic`): `multiopenLevelOf` reads the level off the prefix length (the four
lengths are distinct, `multiopenLen_lt`), and `multiopenChainAt` truncates to the earlier length,
landing on the earlier squeeze point.

Its *state* half is not a free choice: `stateAt` must return `accept p` at every level, `0`
included, so it must recover the accept event from the `x₁`-level prefix alone.
`exists_multiopenStateAt_iff` proves this is exactly the level-0 factorisation

  `multiopenPrefixes … p 0 = multiopenPrefixes … q 0 → accept p = accept q`,

and `multiopenPeelDecode_of_factors` builds the decode from it, feeding the concrete ladder
endpoint.

`memberBadEvent` (`Soundness.Composition.Residual`) does **not** satisfy the factorisation: it reads
`ch.x3` and the point-set commitments, absorbed at squeeze positions `7` and `8` — after `x₁` is
answered at `5` — so a prover steering its post-`x₁` commitments moves the accept event while the
level-0 prefix stands still. Closing the composition therefore needs a decode whose escape sets may
read the table off their own point; `Forking.AdaptiveCoupling` builds exactly that (`updEsc`, blind
by overwriting), with the concrete conditional-continuation weights still to come.

## Scheduled for deletion

`exists_multiopenStateAt_iff`, `multiopenPeelDecode_of_factors`, and the endpoint
`snarkExtraction_prob_le_of_generatorRO_textbookDL_multiopen` are tied to the current `PeelDecode`
interface and go when the adaptive coupling replaces it. They are retained until then because the
iff is what *proves* the redesign necessary. The chain half is not on that list: it is transcript
geometry, independent of the accept event, and the adaptive coupling needs it unchanged.
-/

namespace Zcash.Snark

open ComputedAlgebraicFSFamily
open scoped ENNReal

variable {shape : Shape}

/-- The four multiopen squeeze positions (`x₁,x₂,x₃,x₄`) among the eleven pre-IPA points
`θ β γ y x x₁ x₂ x₃ x₄ ξ z`. -/
def multiopenIdx (j : Fin 4) : Fin 11 := ⟨5 + j.val, by omega⟩

/-- The four multiopen squeeze positions (`x₁,x₂,x₃,x₄` = `chRecord` / `ν`-indices `5,6,7,8`)
of an algebraic output, packaged as the ladder's `prefixes`. -/
def multiopenPrefixes (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (p : AlgebraicWfProof basis (family.vk basis)) : Fin 4 →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) :=
  fun j => algebraicFullPrefixesPre family.init p (multiopenIdx j)

/-- On any oracle table `O`, the ladder's four prefix reads at `multiopenPrefixes` are exactly the
four multiopen challenge fields (`x₁,x₂,x₃,x₄`) of the challenge record `chRecord` squeezed from `O`
at the algebraic output's own pre-IPA squeeze points — the value the family's acceptance test
(`algebraicTableAcceptZ`) uses. This is the definitional tie the ladder's `hcont` "lands" half needs:
`prefixReads = (ch.x1, ch.x2, ch.x3, ch.x4)` for the honest challenge record. -/
theorem multiopenPrefixReads_eq (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (χ : Fin shape.k → Fp) :
    PeelDecode.prefixReads (multiopenPrefixes family basis) (family.adversary basis) O
      = (let ν := fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) i)
         ((chRecord ν χ).x1, (chRecord ν χ).x2, (chRecord ν χ).x3, (chRecord ν χ).x4)) := by
  rfl

/-! ## The chain half of the ladder decode

`levelOf` and `chainAt` at the four multiopen squeeze points, and their three coherence laws. This
mirrors `fullDecodeDeployed`'s `chainPre` (`Soundness.Forking.Adversary.Algebraic`): all bookkeeping,
no probabilistic content. -/

/-- The four multiopen squeeze positions have strictly increasing pre-IPA lengths: `x₁` sits at
`l₅`, and the transcript then absorbs one element before `x₂`, two before `x₃`, and the point-set
commitments before `x₄`. -/
theorem multiopenLen_lt (shape : Shape) (n₀ : ℕ) {i j : Fin 4} (h : (i : ℕ) < (j : ℕ)) :
    preIpaLen shape n₀ (multiopenIdx i) < preIpaLen shape n₀ (multiopenIdx j) := by
  have key : ∀ (a b : ℕ) (ha : a < 4) (hb : b < 4), a < b →
      preIpaLen shape n₀ (multiopenIdx ⟨a, ha⟩)
        < preIpaLen shape n₀ (multiopenIdx ⟨b, hb⟩) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;> simp [multiopenIdx, preIpaLen] <;> omega
  exact key i.val j.val i.isLt j.isLt h

/-- The non-strict form of `multiopenLen_lt`. -/
theorem multiopenLen_le (shape : Shape) (n₀ : ℕ) {i j : Fin 4} (h : (i : ℕ) ≤ (j : ℕ)) :
    preIpaLen shape n₀ (multiopenIdx i) ≤ preIpaLen shape n₀ (multiopenIdx j) := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact le_of_lt (multiopenLen_lt shape n₀ hlt)
  · exact le_of_eq (by rw [show i = j from Fin.ext heq])

/-- The multiopen prefix at level `j` has the pre-IPA length of its squeeze position — the
shape-determined length of a well-formed proof's `j`-th multiopen squeeze point. -/
theorem multiopenPrefixes_length (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (p : AlgebraicWfProof basis (family.vk basis)) (j : Fin 4) :
    (multiopenPrefixes family basis p j).val.length
      = preIpaLen shape family.init.length (multiopenIdx j) := by
  show (preIpaSqueezePoints family.init p.proof.1 (multiopenIdx j)).length = _
  exact preIpaSqueezePoints_length_eq family.init p.proof.1 p.proof.2 (multiopenIdx j)

/-- The ladder's chain at a transcript point: truncate to the earlier multiopen squeeze length.
`List.take` at a fixed position, exactly `fullDecodeDeployed`'s `chainPre`. -/
def multiopenChainAt (family : ComputedAlgebraicFSFamily shape)
    (t : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (i : Fin 4) : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) :=
  ⟨t.val.take (preIpaLen shape family.init.length (multiopenIdx i)), by
    rw [List.length_take]
    exact le_trans (min_le_right _ _) t.prop⟩

/-- On an output's own multiopen prefixes, the chain returns the earlier prefixes — at every level
`i ≤ j`, not only `i < j` (the diagonal is the identity, which the `stateAt` construction below
uses). The eleven squeeze points are prefixes of the pre-IPA transcript, hence of one another. -/
theorem multiopenChainAt_prefixes (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (p : AlgebraicWfProof basis (family.vk basis)) (j i : Fin 4) (hij : (i : ℕ) ≤ (j : ℕ)) :
    multiopenChainAt family (multiopenPrefixes family basis p j) i
      = multiopenPrefixes family basis p i := by
  apply Subtype.ext
  show (preIpaSqueezePoints family.init p.proof.1 (multiopenIdx j)).take
      (preIpaLen shape family.init.length (multiopenIdx i))
    = preIpaSqueezePoints family.init p.proof.1 (multiopenIdx i)
  have hlen : (preIpaSqueezePoints family.init p.proof.1 (multiopenIdx i)).length
      ≤ (preIpaSqueezePoints family.init p.proof.1 (multiopenIdx j)).length := by
    rw [preIpaSqueezePoints_length_eq family.init p.proof.1 p.proof.2,
      preIpaSqueezePoints_length_eq family.init p.proof.1 p.proof.2]
    exact multiopenLen_le shape family.init.length hij
  have hsub := List.prefix_of_prefix_length_le
    (preIpaSqueezePoints_prefix family.init p.proof.1 (multiopenIdx i))
    (preIpaSqueezePoints_prefix family.init p.proof.1 (multiopenIdx j)) hlen
  have h := List.prefix_iff_eq_take.mp hsub
  rw [preIpaSqueezePoints_length_eq family.init p.proof.1 p.proof.2] at h
  exact h.symm

/-- The ladder's level at a transcript point: read off the prefix length. The four multiopen
squeeze lengths are distinct (`multiopenLen_lt`), so a genuine squeeze point is classified
correctly; everything else — including the level-0 point, whose length carries no later
information — falls to level `0`, where `chainAt_ne` is vacuous. -/
def multiopenLevelOf (family : ComputedAlgebraicFSFamily shape)
    (t : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k)) : ℕ :=
  if t.val.length = preIpaLen shape family.init.length (multiopenIdx 1) then 1
  else if t.val.length = preIpaLen shape family.init.length (multiopenIdx 2) then 2
  else if t.val.length = preIpaLen shape family.init.length (multiopenIdx 3) then 3
  else 0

/-- On an output's own multiopen prefixes, the decoded level is the prefix's level. -/
theorem multiopenLevelOf_prefixes (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (p : AlgebraicWfProof basis (family.vk basis)) (j : Fin 4) :
    multiopenLevelOf family (multiopenPrefixes family basis p j) = (j : ℕ) := by
  have h01 := multiopenLen_lt shape family.init.length (i := 0) (j := 1) (by decide)
  have h02 := multiopenLen_lt shape family.init.length (i := 0) (j := 2) (by decide)
  have h03 := multiopenLen_lt shape family.init.length (i := 0) (j := 3) (by decide)
  have h12 := multiopenLen_lt shape family.init.length (i := 1) (j := 2) (by decide)
  have h13 := multiopenLen_lt shape family.init.length (i := 1) (j := 3) (by decide)
  have h23 := multiopenLen_lt shape family.init.length (i := 2) (j := 3) (by decide)
  have hb := j.isLt
  have hj : (j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 2 ∨ (j : ℕ) = 3 := by omega
  rcases hj with h | h | h | h
  · obtain rfl : j = 0 := Fin.ext h
    simp only [multiopenLevelOf, multiopenPrefixes_length]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rfl
  · obtain rfl : j = 1 := Fin.ext h
    simp only [multiopenLevelOf, multiopenPrefixes_length]
    simp
  · obtain rfl : j = 2 := Fin.ext h
    simp only [multiopenLevelOf, multiopenPrefixes_length]
    rw [if_neg (by omega)]
    simp
  · obtain rfl : j = 3 := Fin.ext h
    simp only [multiopenLevelOf, multiopenPrefixes_length]
    rw [if_neg (by omega), if_neg (by omega)]
    simp

/-- Chain points before a transcript point's level differ from it: the level pins the point's
length, and the chain strictly truncates it. -/
theorem multiopenChainAt_ne (family : ComputedAlgebraicFSFamily shape)
    (t : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (i : Fin 4) (hi : (i : ℕ) < multiopenLevelOf family t) :
    multiopenChainAt family t i ≠ t := by
  have h01 := multiopenLen_lt shape family.init.length (i := 0) (j := 1) (by decide)
  have h02 := multiopenLen_lt shape family.init.length (i := 0) (j := 2) (by decide)
  have h03 := multiopenLen_lt shape family.init.length (i := 0) (j := 3) (by decide)
  have h12 := multiopenLen_lt shape family.init.length (i := 1) (j := 2) (by decide)
  have h13 := multiopenLen_lt shape family.init.length (i := 1) (j := 3) (by decide)
  have h23 := multiopenLen_lt shape family.init.length (i := 2) (j := 3) (by decide)
  intro hEq
  have hlen : (t.val.take (preIpaLen shape family.init.length (multiopenIdx i))).length
      = t.val.length := congrArg (fun x : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) => x.val.length) hEq
  rw [List.length_take] at hlen
  have hb := i.isLt
  simp only [multiopenLevelOf] at hi
  split_ifs at hi with c1 c2 c3
  · obtain rfl : i = 0 := Fin.ext (by omega)
    omega
  · have hcase : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
    rcases hcase with h | h
    · obtain rfl : i = 0 := Fin.ext h; omega
    · obtain rfl : i = 1 := Fin.ext h; omega
  · have hcase : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by omega
    rcases hcase with h | h | h
    · obtain rfl : i = 0 := Fin.ext h; omega
    · obtain rfl : i = 1 := Fin.ext h; omega
    · obtain rfl : i = 2 := Fin.ext h; omega
  · omega

/-! ## The state half, and the ladder endpoint

`stateAt` must equal `accept p` at all four of `p`'s squeeze points, level `0` included. Since the
level-0 point is the shortest of the four, this is exactly a factorisation of `accept` through it. -/

/-- **`stateAt` exists exactly when the accept event factors through the level-0 squeeze prefix.**
Forward: two outputs sharing their `x₁`-level prefix get the same decoded state, hence the same
accept event. Backward: the level-0 chain point of any squeeze prefix is that prefix's own level-0
prefix (`multiopenChainAt_prefixes` at `i = 0`), so choosing an output with the observed level-0
prefix and reading its accept event is well defined by the factorisation. This isolates the whole
decode-side content of the composition ladder in one condition. -/
theorem exists_multiopenStateAt_iff (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (accept : AlgebraicWfProof basis (family.vk basis) → Set (Fp × Fp × Fp × Fp)) :
    (∃ stateAt : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
        Set (Fp × Fp × Fp × Fp),
      ∀ p (j : Fin 4), stateAt (multiopenPrefixes family basis p j) = accept p)
      ↔ ∀ p q, multiopenPrefixes family basis p 0 = multiopenPrefixes family basis q 0 →
          accept p = accept q := by
  classical
  constructor
  · rintro ⟨stateAt, hstate⟩ p q hpq
    rw [← hstate p 0, ← hstate q 0, hpq]
  · intro hfac
    refine ⟨fun t => if h : ∃ p, multiopenPrefixes family basis p 0
        = multiopenChainAt family t 0 then accept h.choose else ∅, ?_⟩
    intro p j
    have hchain : multiopenChainAt family (multiopenPrefixes family basis p j) 0
        = multiopenPrefixes family basis p 0 :=
      multiopenChainAt_prefixes family basis p j 0 (Nat.zero_le _)
    have hex : ∃ q, multiopenPrefixes family basis q 0
        = multiopenChainAt family (multiopenPrefixes family basis p j) 0 := ⟨p, hchain.symm⟩
    show (if h : ∃ q, multiopenPrefixes family basis q 0
        = multiopenChainAt family (multiopenPrefixes family basis p j) 0
      then accept h.choose else ∅) = accept p
    rw [dif_pos hex]
    exact hfac _ _ (hex.choose_spec.trans hchain)

open Classical in
/-- **The ladder decode at the multiopen prefixes.** The chain half is discharged above; the state
half is supplied by the level-0 factorisation of the accept event. -/
noncomputable def multiopenPeelDecode_of_factors (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    {accept : AlgebraicWfProof basis (family.vk basis) → Set (Fp × Fp × Fp × Fp)}
    (hfac : ∀ p q, multiopenPrefixes family basis p 0 = multiopenPrefixes family basis q 0 →
      accept p = accept q) :
    PeelDecode (BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
      Fp accept (multiopenPrefixes family basis) :=
  { stateAt := ((exists_multiopenStateAt_iff family basis accept).mpr hfac).choose
    levelOf := multiopenLevelOf family
    chainAt := multiopenChainAt family
    stateAt_prefixes := ((exists_multiopenStateAt_iff family basis accept).mpr hfac).choose_spec
    levelOf_prefixes := multiopenLevelOf_prefixes family basis
    chainAt_prefixes := fun p j i hij =>
      multiopenChainAt_prefixes family basis p j i (le_of_lt hij)
    chainAt_ne := multiopenChainAt_ne family }

open ComputedAlgebraicFSFamily in
/-- **The ladder endpoint at the concrete multiopen prefixes.**
`snarkExtraction_prob_le_of_generatorRO_textbookDL_ladder` (`Soundness.Composition.Assembly`) with
`prefixes := multiopenPrefixes` and its `PeelDecode` supplied by
`multiopenPeelDecode_of_factors`: the knowledge-error probability is at most the clean-opening
bound plus the adaptive-coupling term `(Q+4)·τ`, and the decode input has collapsed from a whole
`PeelDecode` to the single level-0 factorisation `hfac`. The landing input `hcont` is unchanged (its
`prefixReads` side is `multiopenPrefixReads_eq`, the honest challenge tuple). -/
theorem snarkExtraction_prob_le_of_generatorRO_textbookDL_multiopen {shape : Shape}
    {T' : Type*} [DecidableEq T'] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T') (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (accept : ∀ basis, AlgebraicWfProof basis (family.vk basis) → Set (Fp × Fp × Fp × Fp))
    (hfac : ∀ basis p q, multiopenPrefixes family basis p 0 = multiopenPrefixes family basis q 0 →
      accept basis p = accept basis q)
    {τ s : ℝ≥0∞} (hsτ : s ≤ τ * (τ * (τ * τ)))
    (hcont : ∀ basis, {coins : family.Coins |
        family.hasCleanOpening basis coins ∧ ¬ extracted basis coins} ⊆
      {coins : family.Coins |
        PeelDecode.prefixReads (multiopenPrefixes family basis) (family.adversary basis) coins.1 ∈
          accept basis ((family.adversary basis).run coins.1) ∧
        (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (accept basis ((family.adversary basis).run coins.1)) ≤ s}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkExtractionFailureEvent extracted)
      ≤ ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound)
        + (family.Q + 4 : ℕ) * τ :=
  snarkExtraction_prob_le_of_generatorRO_textbookDL_ladder B hB query hquery family hDL extracted
    (multiopenPrefixes family) accept
    (fun basis => multiopenPeelDecode_of_factors family basis (hfac basis)) hsτ hcont

end Zcash.Snark
