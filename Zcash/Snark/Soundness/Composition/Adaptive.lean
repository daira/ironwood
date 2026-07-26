import Zcash.Snark.Soundness.Composition.Prefixes
import Zcash.Snark.Soundness.Forking.Continuation

/-!
# The adaptive residual: the ladder endpoint at the continuation weights

`residual_le_via_ladder` (`Composition.Assembly`) priced the clean-but-not-extracted residual at
`(Q+4)·τ` through a `PeelDecode` — which the multiopen accept events cannot supply: the accept
event is not determined by the level-0 prefix. This module re-prices it through the
conditional-continuation
ladder (`Forking.Continuation`): no `stateAt`, the accept event free to read the whole table, and
the top gate derived from the resampled-joint threshold.

The structural input is `ResampleStable` for the family's adversary at the multiopen squeeze
points. Its level half is transcript geometry, discharged here (`multiopenLevelOf_prefixes`); its
resample-stability half — the machine's prefixes through level `j` survive overwriting the `j`-th
squeeze answer — is the machine's read discipline, a named hypothesis dischargeable for concrete
adversaries (the Fiat–Shamir wrapper reads only its squeeze points, in transcript order).
-/

namespace Zcash.Snark

open scoped ENNReal
open Classical
open ComputedAlgebraicFSFamily

variable {shape : Shape}

/-- The multiopen `ResampleStable`, from its resample-stability half: the level half is
`multiopenLevelOf_prefixes`. -/
theorem multiopenResampleStable (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (hupd : ∀ (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
      (j : Fin 4) (v : Fp) (i : Fin 4), (i : ℕ) ≤ (j : ℕ) →
      multiopenPrefixes family basis ((family.adversary basis).run
          (Function.update O (multiopenPrefixes family basis
            ((family.adversary basis).run O) j) v)) i
        = multiopenPrefixes family basis ((family.adversary basis).run O) i) :
    ResampleStable (family.adversary basis) (multiopenPrefixes family basis)
      (multiopenLevelOf family) where
  level_prefixes := fun O j =>
    multiopenLevelOf_prefixes family basis ((family.adversary basis).run O) j
  prefix_update := hupd

open ComputedAlgebraicFSFamily in
/-- **The clean-but-not-extracted residual, bounded by the continuation ladder.** As
`residual_le_via_ladder`, with the fixed-set decode replaced by the conditional-continuation
weights: the containment `hcont` lands the residual in "the run accepts and its resampled joint
sits inside the `τ⁴` budget", and the ladder prices that at `(Q+4)·τ` per basis. -/
theorem residual_le_via_continuation {T' : Type*} [DecidableEq T']
    (query : AugmentedIndex (2 ^ shape.k) → T')
    (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (accept : ∀ basis, AlgebraicWfProof basis (family.vk basis)
      (family.instanceCommitment basis) → Set (Fp × Fp × Fp × Fp))
    (hS : ∀ basis, ResampleStable (family.adversary basis) (multiopenPrefixes family basis)
      (multiopenLevelOf family))
    {τ s : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτtop : τ ≠ ⊤) (hsτ : s ≤ τ * (τ * (τ * τ)))
    (hcont : ∀ basis, {coins : family.Coins |
        family.hasCleanOpening basis coins ∧ ¬ extracted basis coins} ⊆
      {coins : family.Coins |
        contLeaf (family.adversary basis) (accept basis) (multiopenPrefixes family basis)
          coins.1 ∧
        contJoint (family.adversary basis) (accept basis) (multiopenPrefixes family basis)
          coins.1 ≤ s}) :
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
  -- per basis: land in the ladder's event, marginalising the recursive-fork tape
  refine le_trans (MeasureTheory.measure_mono (hcont (orchardGeneratorROBasis query setup))) ?_
  refine uniformOfFintype_prod_fiber_bound
    (fun _ : RecursiveForkTape Fp shape.k =>
      {O | contLeaf (family.adversary (orchardGeneratorROBasis query setup))
          (accept (orchardGeneratorROBasis query setup))
          (multiopenPrefixes family (orchardGeneratorROBasis query setup)) O ∧
        contJoint (family.adversary (orchardGeneratorROBasis query setup))
          (accept (orchardGeneratorROBasis query setup))
          (multiopenPrefixes family (orchardGeneratorROBasis query setup)) O ≤ s})
    (fun _ => ?_)
  -- per basis: the continuation-ladder bound
  exact (hS (orchardGeneratorROBasis query setup)).contLand_measure_le
    (family.queryBound (orchardGeneratorROBasis query setup)) hτ0 hτtop hsτ

open ComputedAlgebraicFSFamily in
/-- **The knowledge-error bound through the continuation ladder.** Deployed acceptance without
SNARK extraction has probability at most the clean-opening bound plus `(Q+4)·τ`, for any `τ` with
`s ≤ τ⁴` — the adaptive replacement for the retired fixed-set multiopen endpoint, with no
level-0 factorisation: the
inputs are the resample-stability of the adversary's squeeze points and the containment into the
resampled-joint budget event. -/
theorem snarkExtraction_prob_le_of_generatorRO_textbookDL_adaptive {T' : Type*}
    [DecidableEq T'] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T') (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (accept : ∀ basis, AlgebraicWfProof basis (family.vk basis)
      (family.instanceCommitment basis) → Set (Fp × Fp × Fp × Fp))
    (hS : ∀ basis, ResampleStable (family.adversary basis) (multiopenPrefixes family basis)
      (multiopenLevelOf family))
    {τ s : ℝ≥0∞} (hτ0 : τ ≠ 0) (hτtop : τ ≠ ⊤) (hsτ : s ≤ τ * (τ * (τ * τ)))
    (hcont : ∀ basis, {coins : family.Coins |
        family.hasCleanOpening basis coins ∧ ¬ extracted basis coins} ⊆
      {coins : family.Coins |
        contLeaf (family.adversary basis) (accept basis) (multiopenPrefixes family basis)
          coins.1 ∧
        contJoint (family.adversary basis) (accept basis) (multiopenPrefixes family basis)
          coins.1 ≤ s}) :
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
  exact residual_le_via_continuation query family extracted accept hS hτ0 hτtop hsτ hcont

end Zcash.Snark
