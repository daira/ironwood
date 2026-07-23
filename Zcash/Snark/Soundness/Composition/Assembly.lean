import Zcash.Snark.Soundness.Composition.Residual
import Zcash.Snark.Soundness.Composition.Decomposition
import Zcash.Snark.Soundness.Forking.AdaptiveCoupling

/-!
# Assembling the unconditional knowledge-error bound from the adaptive coupling

The decomposed bound leaves `clean-opening bound + μ(cleanButNotExtracted)`. This module bounds the
residual through the adaptive coupling (`PeelDecode.landsBelow_measure_le`), which carries the
ladder's `(Q+4)·τ` query loss — the honest random-oracle model supplies no exact pushforward, since
the accept set depends on the table. `independentProductPMF_fiber_bound` integrates the per-basis
ladder bound over the (non-uniform) generator-RO setup, reducing the residual to two concrete
inputs: a `PeelDecode` for the family's four multiopen prefixes, and the honest-completeness
containment `hcont`.
-/

open scoped ENNReal
open Classical

namespace Zcash.Snark

/-- **Fiber bound for a general independent product.** If every first-factor fiber of the second
factor has outer measure at most `β`, the product event `{x | x.2 ∈ S x.1}` does too. This
generalises `uniformOfFintype_prod_fiber_bound` (`Forking.Probability`) to an *arbitrary*
first-factor PMF `p` — needed because the generator-RO setup measure is not uniform. Proof: the
independent product is `p.bind (q.map ∘ Prod.mk)`, so its outer measure is
`∑' a, p a · μ_q (S a) ≤ ∑' a, p a · β = β` by `PMF.tsum_coe`. -/
theorem independentProductPMF_fiber_bound {A B : Type*} (p : PMF A) (q : PMF B)
    (S : A → Set B) {β : ℝ≥0∞} (hS : ∀ a, q.toOuterMeasure (S a) ≤ β) :
    (independentProductPMF p q).toOuterMeasure {x : A × B | x.2 ∈ S x.1} ≤ β := by
  rw [independentProductPMF, PMF.toOuterMeasure_bind_apply]
  calc ∑' a, p a * (q.map (Prod.mk a)).toOuterMeasure {x : A × B | x.2 ∈ S x.1}
      = ∑' a, p a * q.toOuterMeasure (S a) := by
        refine tsum_congr fun a => ?_
        have hpre : (Prod.mk a) ⁻¹' {x : A × B | x.2 ∈ S x.1} = S a := by
          ext b; simp only [Set.mem_preimage, Set.mem_setOf_eq]
        rw [PMF.toOuterMeasure_map_apply, hpre]
    _ ≤ ∑' a, p a * β := ENNReal.tsum_le_tsum fun a => mul_le_mul_left' (hS a) _
    _ = (∑' a, p a) * β := by rw [ENNReal.tsum_mul_right]
    _ = β := by rw [PMF.tsum_coe, one_mul]

open ComputedAlgebraicFSFamily in
/-- **The clean-but-not-extracted residual, bounded by the adaptive coupling.** Given a
`PeelDecode` for the family's four multiopen prefixes (`D`) and the containment `hcont` (on the
residual, the four challenge reads land in the per-output joint accept event, of measure below
`s`), the residual measure is at most `(Q + 4)·τ` for any `τ` with `s ≤ τ⁴` — the ladder's
query-loss coupling, integrated over the generator-RO setup by
`independentProductPMF_fiber_bound`. -/
theorem residual_le_via_ladder {shape : Shape}
    {T' : Type*} [DecidableEq T']
    (query : AugmentedIndex (2 ^ shape.k) → T')
    (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (prefixes : ∀ basis, AlgebraicWfProof basis (family.vk basis) → Fin 4 →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (accept : ∀ basis, AlgebraicWfProof basis (family.vk basis) → Set (Fp × Fp × Fp × Fp))
    (D : ∀ basis, PeelDecode
        (BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
        Fp (accept basis) (prefixes basis))
    {τ s : ℝ≥0∞} (hsτ : s ≤ τ * (τ * (τ * τ)))
    (hcont : ∀ basis, {coins : family.Coins |
        family.hasCleanOpening basis coins ∧ ¬ extracted basis coins} ⊆
      {coins : family.Coins |
        PeelDecode.prefixReads (prefixes basis) (family.adversary basis) coins.1 ∈
          accept basis ((family.adversary basis).run coins.1) ∧
        (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (accept basis ((family.adversary basis).run coins.1)) ≤ s}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.cleanButNotExtracted extracted)
      ≤ (family.Q + 4 : ℕ) * τ := by
  -- reshape the residual preimage as a fiber set over the setup factor
  have hset : (fun p : (↥(Set.range query) → VestaG) × family.Coins =>
        (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        family.cleanButNotExtracted extracted
      = {x : (↥(Set.range query) → VestaG) × family.Coins | x.2 ∈
          (fun setup => {coins : family.Coins |
            family.hasCleanOpening (orchardGeneratorROBasis query setup) coins ∧
            ¬ extracted (orchardGeneratorROBasis query setup) coins}) x.1} := by
    ext p; simp only [Set.mem_preimage, cleanButNotExtracted, Set.mem_setOf_eq]
  rw [hset]
  refine independentProductPMF_fiber_bound (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)
    (fun setup => {coins : family.Coins |
      family.hasCleanOpening (orchardGeneratorROBasis query setup) coins ∧
      ¬ extracted (orchardGeneratorROBasis query setup) coins}) ?_
  intro setup
  -- per basis: the clean-but-not-extracted fiber measure over `Coins` is at most `(Q+4)·τ`
  refine le_trans (MeasureTheory.measure_mono (hcont (orchardGeneratorROBasis query setup))) ?_
  -- marginalise the recursive-fork tape (the landing event reads only the oracle table `coins.1`)
  refine uniformOfFintype_prod_fiber_bound
    (fun _ : RecursiveForkTape Fp shape.k =>
      {O | PeelDecode.prefixReads (prefixes (orchardGeneratorROBasis query setup))
          (family.adversary (orchardGeneratorROBasis query setup)) O ∈
        accept (orchardGeneratorROBasis query setup)
          ((family.adversary (orchardGeneratorROBasis query setup)).run O) ∧
        (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (accept (orchardGeneratorROBasis query setup)
            ((family.adversary (orchardGeneratorROBasis query setup)).run O)) ≤ s})
    (fun _ => ?_)
  -- per basis: the ladder bound
  exact (D (orchardGeneratorROBasis query setup)).landsBelow_measure_le
    (family.queryBound (orchardGeneratorROBasis query setup)) hsτ

open ComputedAlgebraicFSFamily in
/-- **The knowledge-error bound, unconditional up to the adaptive coupling inputs.** Deployed
acceptance without SNARK extraction has probability at most the clean-opening bound
`(Q+k)·3/|Fp| + (Q+1)/|Fp| + |basis|·ε` plus `(Q+4)·τ`, for any `τ` with `s ≤ τ⁴`. No `hExtract`
and no exact pushforward; the two inputs are the decode `D` and the containment `hcont`
(via `deployed_member_budget`), both non-circular. -/
theorem snarkExtraction_prob_le_of_generatorRO_textbookDL_ladder {shape : Shape}
    {T' : Type*} [DecidableEq T'] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T') (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (prefixes : ∀ basis, AlgebraicWfProof basis (family.vk basis) → Fin 4 →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (accept : ∀ basis, AlgebraicWfProof basis (family.vk basis) → Set (Fp × Fp × Fp × Fp))
    (D : ∀ basis, PeelDecode
        (BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
        Fp (accept basis) (prefixes basis))
    {τ s : ℝ≥0∞} (hsτ : s ≤ τ * (τ * (τ * τ)))
    (hcont : ∀ basis, {coins : family.Coins |
        family.hasCleanOpening basis coins ∧ ¬ extracted basis coins} ⊆
      {coins : family.Coins |
        PeelDecode.prefixReads (prefixes basis) (family.adversary basis) coins.1 ∈
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
        + (family.Q + 4 : ℕ) * τ := by
  refine le_trans
    (snarkExtraction_prob_le_of_generatorRO_textbookDL_decomposed B hB query hquery family hDL
      extracted) ?_
  refine add_le_add le_rfl ?_
  exact residual_le_via_ladder query family extracted prefixes accept D hsτ hcont

end Zcash.Snark
