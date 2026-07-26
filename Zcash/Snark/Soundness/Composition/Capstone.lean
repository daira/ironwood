import Zcash.Snark.Soundness.Composition.Adaptive
import Zcash.Snark.Soundness.Composition.ActionBudget
import Zcash.Snark.Soundness.VestaBudget

/-!
# The composite knowledge-error bound

One probability statement carrying every term: the recursive extraction's query loss and `z = 0`
slice, the DL advantage, the adaptive multiopen loss `(Q+4)·τ` with its resampled-joint budget
capped by the consensus-maximum action budget, and the good-challenge loss `(Q+1)·ε` for the
constraint squeeze. The failure event is deployed acceptance without the joint success — the
extraction *and* the good squeeze — so the bound reads directly over deployed acceptance.
-/

namespace Zcash.Snark

open scoped ENNReal
open Classical
open ComputedAlgebraicFSFamily

variable {shape : Shape}

open ComputedAlgebraicFSFamily in
/-- **The good-squeeze failure, priced through the one-level squeeze.** If failing `goodX` lands
the coins in "the run's own squeeze answer is bad" (`hcontX`), the squeeze point and bad set are
pinned under resampling, and every output's bad set has measure at most `ε`, then the `goodX`
failure costs at most `(Q+1)·ε` — marginalising the fork tape and integrating over the
generator-RO setup. -/
theorem badX_le_via_squeeze {T' : Type*} [DecidableEq T']
    (query : AugmentedIndex (2 ^ shape.k) → T')
    (family : ComputedAlgebraicFSFamily shape)
    (goodX : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (xpt : ∀ basis, AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (bad : ∀ basis, AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) → Set Fp)
    (hstab : ∀ basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp),
      xpt basis ((family.adversary basis).run
          (Function.update O (xpt basis ((family.adversary basis).run O)) v))
        = xpt basis ((family.adversary basis).run O))
    (hpin : ∀ basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp),
      bad basis ((family.adversary basis).run
          (Function.update O (xpt basis ((family.adversary basis).run O)) v))
        = bad basis ((family.adversary basis).run O))
    {ε : ℝ≥0∞}
    (hbad : ∀ basis (p : AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis)),
      (PMF.uniformOfFintype Fp).toOuterMeasure (bad basis p) ≤ ε)
    (hcontX : ∀ basis, {coins : family.Coins | ¬ goodX basis coins} ⊆
      {coins : family.Coins |
        coins.1 (xpt basis ((family.adversary basis).run coins.1))
          ∈ bad basis ((family.adversary basis).run coins.1)}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          {q : (AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins | ¬ goodX q.1 q.2})
      ≤ (family.Q + 1 : ℕ) * ε := by
  have hset : (fun p : (↥(Set.range query) → VestaG) × family.Coins =>
        (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        {q : (AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins | ¬ goodX q.1 q.2}
      = {x : (↥(Set.range query) → VestaG) × family.Coins | x.2 ∈
          (fun setup => {coins : family.Coins |
            ¬ goodX (orchardGeneratorROBasis query setup) coins}) x.1} := by
    ext p; simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [hset]
  refine independentProductPMF_fiber_bound (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)
    (fun setup => {coins : family.Coins |
      ¬ goodX (orchardGeneratorROBasis query setup) coins}) ?_
  intro setup
  refine le_trans (MeasureTheory.measure_mono
    (hcontX (orchardGeneratorROBasis query setup))) ?_
  refine uniformOfFintype_prod_fiber_bound
    (fun _ : RecursiveForkTape Fp shape.k =>
      {O | O (xpt (orchardGeneratorROBasis query setup)
          ((family.adversary (orchardGeneratorROBasis query setup)).run O))
        ∈ bad (orchardGeneratorROBasis query setup)
          ((family.adversary (orchardGeneratorROBasis query setup)).run O)})
    (fun _ => ?_)
  exact xEsc_measure_le (family.adversary (orchardGeneratorROBasis query setup))
    (xpt (orchardGeneratorROBasis query setup)) (bad (orchardGeneratorROBasis query setup))
    (hstab (orchardGeneratorROBasis query setup))
    (hpin (orchardGeneratorROBasis query setup))
    (hbad (orchardGeneratorROBasis query setup))
    (family.queryBound (orchardGeneratorROBasis query setup))

open ComputedAlgebraicFSFamily in
/-- **The composite knowledge-error bound.** Deployed acceptance without the joint success —
extraction *and* good squeeze — has probability at most

  `(Q+k)·3/|Fp| + (Q+1)/|Fp| + |basis|·ε_DL + (Q+4)·τ + (Q+1)·ε_x`

for any per-level threshold `τ` with the resampled-joint budget `s ≤ τ⁴`. The recursive
extraction, DL, adaptive multiopen, and good-challenge terms in one statement; the
action-dependent budget enters through `s` (`deployed_member_threshold_le_actionBudget`,
`actionBudget_le_consensusMax`). -/
theorem snarkExtraction_prob_le_composite {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T') (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (extracted goodX : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (accept : ∀ basis, AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) → Set (Fp × Fp × Fp × Fp))
    (hS : ∀ basis, ResampleStable (family.adversary basis) (multiopenPrefixes family basis)
      (multiopenLevelOf family))
    {τ s : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτtop : τ ≠ ⊤) (hsτ : s ≤ τ * (τ * (τ * τ)))
    (hcont : ∀ basis, {coins : family.Coins |
        family.hasCleanOpening basis coins ∧ ¬ extracted basis coins} ⊆
      {coins : family.Coins |
        contLeaf (family.adversary basis) (accept basis) (multiopenPrefixes family basis)
          coins.1 ∧
        contJoint (family.adversary basis) (accept basis) (multiopenPrefixes family basis)
          coins.1 ≤ s})
    (xpt : ∀ basis, AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (bad : ∀ basis, AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) → Set Fp)
    (hstab : ∀ basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp),
      xpt basis ((family.adversary basis).run
          (Function.update O (xpt basis ((family.adversary basis).run O)) v))
        = xpt basis ((family.adversary basis).run O))
    (hpin : ∀ basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp),
      bad basis ((family.adversary basis).run
          (Function.update O (xpt basis ((family.adversary basis).run O)) v))
        = bad basis ((family.adversary basis).run O))
    {εx : ℝ≥0∞}
    (hbad : ∀ basis (p : AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis)),
      (PMF.uniformOfFintype Fp).toOuterMeasure (bad basis p) ≤ εx)
    (hcontX : ∀ basis, {coins : family.Coins | ¬ goodX basis coins} ⊆
      {coins : family.Coins |
        coins.1 (xpt basis ((family.adversary basis).run coins.1))
          ∈ bad basis ((family.adversary basis).run coins.1)}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkExtractionFailureEvent
            (fun basis coins => extracted basis coins ∧ goodX basis coins))
      ≤ ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound)
        + (family.Q + 4 : ℕ) * τ
        + (family.Q + 1 : ℕ) * εx := by
  -- split the joint failure into the extraction failure and the squeeze failure
  have hsplit : family.snarkExtractionFailureEvent
      (fun basis coins => extracted basis coins ∧ goodX basis coins)
      ⊆ family.snarkExtractionFailureEvent extracted
        ∪ {q : (AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins | ¬ goodX q.1 q.2} := by
    rintro ⟨basis, coins⟩ ⟨hacc, hnex⟩
    by_cases hg : goodX basis coins
    · exact Or.inl ⟨hacc, fun he => hnex ⟨he, hg⟩⟩
    · exact Or.inr hg
  refine le_trans ((independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)).toOuterMeasure.mono
      (Set.preimage_mono hsplit)) ?_
  refine le_trans (le_of_eq (congrArg
    (fun S => (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure S) Set.preimage_union)) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (snarkExtraction_prob_le_of_generatorRO_textbookDL_adaptive B hB query hquery family hDL
      extracted accept hS hτ0 hτtop hsτ hcont)
    (badX_le_via_squeeze query family goodX xpt bad hstab hpin hbad hcontX)

open ComputedAlgebraicFSFamily in
/-- `badX_le_via_squeeze` with the bad set *factored through the squeeze point*: `bad` is any
function of the point alone, so the pinning hypothesis disappears — resampling preserves the
point (`hstab`), hence the set. This is the shape the concrete constraint bad set takes: the
committed polynomials are read off the pre-`x` transcript, which *is* the squeeze point. -/
theorem badX_le_via_squeeze_factored {T' : Type*} [DecidableEq T']
    (query : AugmentedIndex (2 ^ shape.k) → T')
    (family : ComputedAlgebraicFSFamily shape)
    (goodX : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (xpt : ∀ basis, AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (badF : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Set Fp)
    (hstab : ∀ basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp),
      xpt basis ((family.adversary basis).run
          (Function.update O (xpt basis ((family.adversary basis).run O)) v))
        = xpt basis ((family.adversary basis).run O))
    {ε : ℝ≥0∞}
    (hbad : ∀ basis t, (PMF.uniformOfFintype Fp).toOuterMeasure (badF basis t) ≤ ε)
    (hcontX : ∀ basis, {coins : family.Coins | ¬ goodX basis coins} ⊆
      {coins : family.Coins |
        coins.1 (xpt basis ((family.adversary basis).run coins.1))
          ∈ badF basis (xpt basis ((family.adversary basis).run coins.1))}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          {q : (AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins | ¬ goodX q.1 q.2})
      ≤ (family.Q + 1 : ℕ) * ε :=
  badX_le_via_squeeze query family goodX xpt
    (fun basis p => badF basis (xpt basis p))
    hstab
    (fun basis O v => congrArg (badF basis) (hstab basis O v))
    (fun basis p => hbad basis (xpt basis p))
    hcontX

/-! ### The prefixed squeeze: a bad set reading the point and the earlier answers

The concrete constraint bad set reads the pre-`x` commitments (contents of the `x` squeeze
point) *and* the earlier challenges `θ, β, γ, y` — table answers at the earlier squeeze points,
which the point alone does not carry. The squeeze below takes the bad set as a function of the
point and those four answers; its pinning is derived: the earlier points are the `x` point's own
prefixes at strictly smaller shape-determined lengths, so resampling the `x` answer moves
neither them nor their answers. -/

/-- Pre-`x` squeeze lengths sit strictly below the `x` point's: every squeeze appends at least
its challenge marker. -/
theorem preIpaLen_lt_x (shape : Shape) (n₀ : ℕ) {i : Fin 11} (hi : (i : ℕ) < 4) :
    preIpaLen shape n₀ i < preIpaLen shape n₀ 4 := by
  have hcase : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 := by omega
  rcases hcase with h | h | h | h
  · obtain rfl : i = ⟨0, by norm_num⟩ := Fin.ext h
    simp [preIpaLen] <;> omega
  · obtain rfl : i = ⟨1, by norm_num⟩ := Fin.ext h
    simp [preIpaLen] <;> omega
  · obtain rfl : i = ⟨2, by norm_num⟩ := Fin.ext h
    simp [preIpaLen] <;> omega
  · obtain rfl : i = ⟨3, by norm_num⟩ := Fin.ext h
    simp [preIpaLen] <;> omega

/-- Equal `x` squeeze points pin every earlier squeeze point: the pre-`x` points are the `x`
point's own prefixes at shape-determined lengths. -/
theorem algebraicFullPrefixesPre_eq_of_x_eq {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (p q : AlgebraicWfProof basis vk instanceCommitment)
    (h : algebraicFullPrefixesPre init p 4 = algebraicFullPrefixesPre init q 4)
    {i : Fin 11} (hi : (i : ℕ) < 4) :
    algebraicFullPrefixesPre init p i = algebraicFullPrefixesPre init q i := by
  apply Subtype.ext
  have hval : preIpaSqueezePoints init p.proof.1 4 = preIpaSqueezePoints init q.proof.1 4 :=
    congrArg Subtype.val h
  have hpre_p := List.prefix_of_prefix_length_le
    (preIpaSqueezePoints_prefix init p.proof.1 i)
    (preIpaSqueezePoints_prefix init p.proof.1 4)
    (by rw [preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2,
        preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2]
        exact le_of_lt (preIpaLen_lt_x shape init.length hi))
  have hpre_q := List.prefix_of_prefix_length_le
    (preIpaSqueezePoints_prefix init q.proof.1 i)
    (preIpaSqueezePoints_prefix init q.proof.1 4)
    (by rw [preIpaSqueezePoints_length_eq init q.proof.1 q.proof.2,
        preIpaSqueezePoints_length_eq init q.proof.1 q.proof.2]
        exact le_of_lt (preIpaLen_lt_x shape init.length hi))
  show preIpaSqueezePoints init p.proof.1 i = preIpaSqueezePoints init q.proof.1 i
  rw [List.prefix_iff_eq_take.mp hpre_p, List.prefix_iff_eq_take.mp hpre_q,
    preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2,
    preIpaSqueezePoints_length_eq init q.proof.1 q.proof.2, hval]

/-- A pre-`x` squeeze point differs from the `x` point: the lengths do. -/
theorem algebraicFullPrefixesPre_ne_x {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (p : AlgebraicWfProof basis vk instanceCommitment) {i : Fin 11} (hi : (i : ℕ) < 4) :
    algebraicFullPrefixesPre init p i ≠ algebraicFullPrefixesPre init p 4 := by
  intro hEq
  have hlen : (preIpaSqueezePoints init p.proof.1 i).length
      = (preIpaSqueezePoints init p.proof.1 4).length :=
    congrArg (fun t : List (TranscriptElt Fp VestaG) => t.length) (congrArg Subtype.val hEq)
  rw [preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2,
    preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2] at hlen
  exact absurd hlen (Nat.ne_of_lt (preIpaLen_lt_x shape init.length hi))

open ComputedAlgebraicFSFamily in
/-- **The prefixed squeeze bound.** The bad set reads the `x` squeeze point and the four earlier
answers; the only stability input is the point's own (`hstab`) — the earlier points are its
prefixes (`algebraicFullPrefixesPre_eq_of_x_eq`) and their answers are off the resampled point
(`algebraicFullPrefixesPre_ne_x`), so the table-reading pinning is derived. -/
theorem badX_le_via_squeeze_prefixed {T' : Type*} [DecidableEq T']
    (query : AugmentedIndex (2 ^ shape.k) → T')
    (family : ComputedAlgebraicFSFamily shape)
    (goodX : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (badF : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 4 → Fp) → Set Fp)
    (hstab : ∀ basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp),
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 4) v)) 4
        = algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4)
    {ε : ℝ≥0∞}
    (hbad : ∀ basis t ν, (PMF.uniformOfFintype Fp).toOuterMeasure (badF basis t ν) ≤ ε)
    (hcontX : ∀ basis, {coins : family.Coins | ¬ goodX basis coins} ⊆
      {coins : family.Coins |
        coins.1 (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run coins.1) 4)
          ∈ badF basis (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins.1) 4)
            (fun i : Fin 4 => coins.1 (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins.1) (i.castLE (by omega))))}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          {q : (AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins | ¬ goodX q.1 q.2})
      ≤ (family.Q + 1 : ℕ) * ε := by
  have hset : (fun p : (↥(Set.range query) → VestaG) × family.Coins =>
        (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        {q : (AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins | ¬ goodX q.1 q.2}
      = {x : (↥(Set.range query) → VestaG) × family.Coins | x.2 ∈
          (fun setup => {coins : family.Coins |
            ¬ goodX (orchardGeneratorROBasis query setup) coins}) x.1} := by
    ext p; simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [hset]
  refine independentProductPMF_fiber_bound (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)
    (fun setup => {coins : family.Coins |
      ¬ goodX (orchardGeneratorROBasis query setup) coins}) ?_
  intro setup
  set basis' := orchardGeneratorROBasis query setup with hbasis'
  refine le_trans (MeasureTheory.measure_mono (hcontX basis')) ?_
  refine uniformOfFintype_prod_fiber_bound
    (fun _ : RecursiveForkTape Fp shape.k =>
      {O | O (algebraicFullPrefixesPre family.init ((family.adversary basis').run O) 4)
        ∈ badF basis' (algebraicFullPrefixesPre family.init
            ((family.adversary basis').run O) 4)
          (fun i : Fin 4 => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis').run O) (i.castLE (by omega))))})
    (fun _ => ?_)
  refine xEscTable_measure_le (family.adversary basis')
    (fun p => algebraicFullPrefixesPre family.init p 4)
    (fun p O => badF basis' (algebraicFullPrefixesPre family.init p 4)
      (fun i : Fin 4 => O (algebraicFullPrefixesPre family.init p (i.castLE (by omega)))))
    ?_ (fun p O => hbad basis' _ _) (family.queryBound basis')
  intro O v
  have hx := hstab basis' O v
  show badF basis' (algebraicFullPrefixesPre family.init ((family.adversary basis').run
        (Function.update O (algebraicFullPrefixesPre family.init
          ((family.adversary basis').run O) 4) v)) 4)
      (fun i : Fin 4 => (Function.update O (algebraicFullPrefixesPre family.init
          ((family.adversary basis').run O) 4) v)
        (algebraicFullPrefixesPre family.init ((family.adversary basis').run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis').run O) 4) v)) (i.castLE (by omega))))
    = badF basis' (algebraicFullPrefixesPre family.init ((family.adversary basis').run O) 4)
      (fun i : Fin 4 => O (algebraicFullPrefixesPre family.init
        ((family.adversary basis').run O) (i.castLE (by omega))))
  rw [hx]
  congr 1
  funext i
  rw [algebraicFullPrefixesPre_eq_of_x_eq family.init _ _ hx
      (show ((i.castLE (by omega) : Fin 11) : ℕ) < 4 from i.isLt),
    Function.update_of_ne
      (algebraicFullPrefixesPre_ne_x family.init _
        (show ((i.castLE (by omega) : Fin 11) : ℕ) < 4 from i.isLt))]

open Polynomial in
/-- **The good-challenge lemmas, consumed.** The composite's squeeze bad set instantiated at a
constraint difference: `hgood_failure_priced` supplies the `ε_x` measure bound in the
`PMF.uniformOfFintype` form the composite reads, and any answer off the set satisfies the
supplied terminal's `hxgood` receiver verbatim (`hgood_of_good_challenge`). -/
theorem szBadSet_quotient_measure_le (numerator hq : Polynomial Fp) (n : ℕ) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        ↑(szBadSet (numerator - hq * (X ^ n - 1)))
      ≤ ((max numerator.natDegree (hq.natDegree + n) : ℕ) : ℝ≥0∞)
        / (Fintype.card Fp : ℝ≥0∞) := by
  have h := hgood_failure_priced numerator hq n
  rw [uniformChallenge] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext x
  simp only [Finset.mem_coe, mem_szBadSet, Set.mem_setOf_eq, Classical.not_imp, not_not,
    sub_ne_zero]

open ComputedAlgebraicFSFamily in
/-- **The deployed knowledge-error capstone at the constraint predicate.** The composite bound
with the success event fixed to the constraint conclusion: deployed acceptance where neither the
constraint-encoded statement `S` nor a binding `HasNontrivialRelation` is delivered alongside a
good squeeze has probability at most

  `(Q+k)·3/|Fp| + (Q+1)/|Fp| + |basis|·ε_DL + (Q+4)·τ + (Q+1)·ε_x`,

with the resampled-joint budget `s` capped by the consensus-maximum action budget
(`deployed_member_threshold_le_actionBudget` + `actionBudget_le_consensusMax` discharge the
per-run thresholds against it). The named inputs are the standing structural surfaces: the
adversary's resample stability, the containment of extraction failure into the joint-budget
event, and the squeeze pinning with its containment. -/
theorem orchard_deployed_knowledge_error {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T') (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (S : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (goodX : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (accept : ∀ basis, AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) → Set (Fp × Fp × Fp × Fp))
    (hS : ∀ basis, ResampleStable (family.adversary basis) (multiopenPrefixes family basis)
      (multiopenLevelOf family))
    {τ s : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτtop : τ ≠ ⊤) (hsτ : s ≤ τ * (τ * (τ * τ)))
    (hcont : ∀ basis, {coins : family.Coins |
        family.hasCleanOpening basis coins ∧ ¬ (S basis coins ∨
          HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
            (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)} ⊆
      {coins : family.Coins |
        contLeaf (family.adversary basis) (accept basis) (multiopenPrefixes family basis)
          coins.1 ∧
        contJoint (family.adversary basis) (accept basis) (multiopenPrefixes family basis)
          coins.1 ≤ s})
    (xpt : ∀ basis, AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (bad : ∀ basis, AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) → Set Fp)
    (hstab : ∀ basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp),
      xpt basis ((family.adversary basis).run
          (Function.update O (xpt basis ((family.adversary basis).run O)) v))
        = xpt basis ((family.adversary basis).run O))
    (hpin : ∀ basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp),
      bad basis ((family.adversary basis).run
          (Function.update O (xpt basis ((family.adversary basis).run O)) v))
        = bad basis ((family.adversary basis).run O))
    {εx : ℝ≥0∞}
    (hbad : ∀ basis (p : AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis)),
      (PMF.uniformOfFintype Fp).toOuterMeasure (bad basis p) ≤ εx)
    (hcontX : ∀ basis, {coins : family.Coins | ¬ goodX basis coins} ⊆
      {coins : family.Coins |
        coins.1 (xpt basis ((family.adversary basis).run coins.1))
          ∈ bad basis ((family.adversary basis).run coins.1)}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkExtractionFailureEvent
            (fun basis coins => (S basis coins ∨
              HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
                (ursOfAugmentedBasis shape.k basis).u
                (ursOfAugmentedBasis shape.k basis).w) ∧ goodX basis coins))
      ≤ ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound)
        + (family.Q + 4 : ℕ) * τ
        + (family.Q + 1 : ℕ) * εx :=
  snarkExtraction_prob_le_composite B hB query hquery family hDL
    (fun basis coins => S basis coins ∨
      HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)
    goodX accept hS hτ0 hτtop hsτ hcont xpt bad hstab hpin hbad hcontX

open ComputedAlgebraicFSFamily in
/-- `orchard_deployed_knowledge_error` with the squeeze bad set factored through the point: the
set is a function of the pre-`x` transcript alone, so the pinning input disappears — resampling
preserves the point, hence the set. -/
theorem orchard_deployed_knowledge_error_factored {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T') (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (S : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (goodX : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (accept : ∀ basis, AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) → Set (Fp × Fp × Fp × Fp))
    (hS : ∀ basis, ResampleStable (family.adversary basis) (multiopenPrefixes family basis)
      (multiopenLevelOf family))
    {τ s : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτtop : τ ≠ ⊤) (hsτ : s ≤ τ * (τ * (τ * τ)))
    (hcont : ∀ basis, {coins : family.Coins |
        family.hasCleanOpening basis coins ∧ ¬ (S basis coins ∨
          HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
            (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)} ⊆
      {coins : family.Coins |
        contLeaf (family.adversary basis) (accept basis) (multiopenPrefixes family basis)
          coins.1 ∧
        contJoint (family.adversary basis) (accept basis) (multiopenPrefixes family basis)
          coins.1 ≤ s})
    (xpt : ∀ basis, AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (badF : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Set Fp)
    (hstab : ∀ basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp),
      xpt basis ((family.adversary basis).run
          (Function.update O (xpt basis ((family.adversary basis).run O)) v))
        = xpt basis ((family.adversary basis).run O))
    {εx : ℝ≥0∞}
    (hbad : ∀ basis t, (PMF.uniformOfFintype Fp).toOuterMeasure (badF basis t) ≤ εx)
    (hcontX : ∀ basis, {coins : family.Coins | ¬ goodX basis coins} ⊆
      {coins : family.Coins |
        coins.1 (xpt basis ((family.adversary basis).run coins.1))
          ∈ badF basis (xpt basis ((family.adversary basis).run coins.1))}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkExtractionFailureEvent
            (fun basis coins => (S basis coins ∨
              HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
                (ursOfAugmentedBasis shape.k basis).u
                (ursOfAugmentedBasis shape.k basis).w) ∧ goodX basis coins))
      ≤ ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound)
        + (family.Q + 4 : ℕ) * τ
        + (family.Q + 1 : ℕ) * εx :=
  orchard_deployed_knowledge_error B hB query hquery family hDL S goodX accept hS
    hτ0 hτtop hsτ hcont xpt (fun basis p => badF basis (xpt basis p)) hstab
    (fun basis O v => congrArg (badF basis) (hstab basis O v))
    (fun basis p => hbad basis (xpt basis p)) hcontX

open ComputedAlgebraicFSFamily in
/-- **The deployed knowledge-error capstone at the prefixed squeeze.** As
`orchard_deployed_knowledge_error_factored`, with the bad set reading the `x` squeeze point and
the four earlier challenge answers — the concrete constraint set's full data. The squeeze arm is
`badX_le_via_squeeze_prefixed`; the only squeeze-side stability input is the point's own. -/
theorem orchard_deployed_knowledge_error_prefixed {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T') (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (S : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (goodX : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (accept : ∀ basis, AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) → Set (Fp × Fp × Fp × Fp))
    (hS : ∀ basis, ResampleStable (family.adversary basis) (multiopenPrefixes family basis)
      (multiopenLevelOf family))
    {τ s : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτtop : τ ≠ ⊤) (hsτ : s ≤ τ * (τ * (τ * τ)))
    (hcont : ∀ basis, {coins : family.Coins |
        family.hasCleanOpening basis coins ∧ ¬ (S basis coins ∨
          HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
            (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)} ⊆
      {coins : family.Coins |
        contLeaf (family.adversary basis) (accept basis) (multiopenPrefixes family basis)
          coins.1 ∧
        contJoint (family.adversary basis) (accept basis) (multiopenPrefixes family basis)
          coins.1 ≤ s})
    (badF : (AugmentedIndex (2 ^ shape.k) → VestaG) →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin 4 → Fp) → Set Fp)
    (hstab : ∀ basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp),
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 4) v)) 4
        = algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4)
    {εx : ℝ≥0∞}
    (hbad : ∀ basis t ν, (PMF.uniformOfFintype Fp).toOuterMeasure (badF basis t ν) ≤ εx)
    (hcontX : ∀ basis, {coins : family.Coins | ¬ goodX basis coins} ⊆
      {coins : family.Coins |
        coins.1 (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run coins.1) 4)
          ∈ badF basis (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins.1) 4)
            (fun i : Fin 4 => coins.1 (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins.1) (i.castLE (by omega))))}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkExtractionFailureEvent
            (fun basis coins => (S basis coins ∨
              HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
                (ursOfAugmentedBasis shape.k basis).u
                (ursOfAugmentedBasis shape.k basis).w) ∧ goodX basis coins))
      ≤ ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound)
        + (family.Q + 4 : ℕ) * τ
        + (family.Q + 1 : ℕ) * εx := by
  have hsplit : family.snarkExtractionFailureEvent
      (fun basis coins => (S basis coins ∨
        HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).u
          (ursOfAugmentedBasis shape.k basis).w) ∧ goodX basis coins)
      ⊆ family.snarkExtractionFailureEvent (fun basis coins => S basis coins ∨
          HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
            (ursOfAugmentedBasis shape.k basis).u
            (ursOfAugmentedBasis shape.k basis).w)
        ∪ {q : (AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins | ¬ goodX q.1 q.2} := by
    rintro ⟨basis, coins⟩ ⟨hacc, hnex⟩
    by_cases hg : goodX basis coins
    · exact Or.inl ⟨hacc, fun he => hnex ⟨he, hg⟩⟩
    · exact Or.inr hg
  refine le_trans ((independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)).toOuterMeasure.mono
      (Set.preimage_mono hsplit)) ?_
  refine le_trans (le_of_eq (congrArg
    (fun S => (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure S) Set.preimage_union)) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (snarkExtraction_prob_le_of_generatorRO_textbookDL_adaptive B hB query hquery family hDL
      _ accept hS hτ0 hτtop hsτ hcont)
    (badX_le_via_squeeze_prefixed query family goodX badF hstab hbad hcontX)

end Zcash.Snark
