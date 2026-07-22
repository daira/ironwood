import Zcash.Snark.Soundness.Compose67Unconditional
import Zcash.Snark.Soundness.Multiopen.BudgetedExtraction

/-!
# The forking reduction closing the #67 residual

`Compose67Unconditional.snarkExtraction_prob_le_of_generatorRO_textbookDL_decomposed` bounds the
SNARK-extraction failure by the `#56` clean-opening bound **plus** the clean-but-not-extracted
residual `μ(cleanButNotExtracted)`. This module closes that residual to the multiopen knowledge
error, isolating exactly the two standard, **non-circular** facts the forking argument needs:

* **(a) the coupling** — a *distributional* statement: the four fresh multiopen challenges,
  extracted from the coins by reading/reprogramming the random oracle at the sealed multiopen
  prefixes, are jointly uniform (a `PMF.map` equality onto `uniformOfFintype`, the exact shape of the
  proven `Soundness.Forking.Rewind.roChallenges_ipaRound_uniform`, and the explicit form of the
  random-oracle-uniformity convention every `hprob`/`hJ` floor already carries —
  `Soundness.Forking.Oracle`);
* **(b) the containment** — a *structural* statement: on the clean-but-not-extracted residual the
  extracted challenge tuple lands in the per-base accept event whose measure is below the threshold
  (this bundles the deployed→opened accept decomposition, `openedX*Accept_of_deployedAccepts`, with
  the budget `Soundness.Multiopen.BudgetedExtraction.deployed_member_budget`: extraction fails only
  when the joint accept measure is `≤ Σtᵢ`).

Neither mentions `extracted`'s measure or the conclusion — (a) is about the challenge distribution,
(b) is a set containment. The reduction proper (this file's `residual_le_of_coupling_containment`
and its `fibered_accept_below_threshold_le` engine) is *proven*: given (a) and (b) the residual is
`≤ Σtᵢ` by the fibered single-slot counting bound
(`Soundness.Forking.Probability.uniformOfFintype_accept_below_threshold_le`, lifted over the base by
`uniformOfFintype_prod_fiber_bound_right`) transported along the coupling's pushforward. Composing
with the decomposition gives the unconditional single-number bound
`(Q+k)·3/|Fp| + (Q+1)/|Fp| + |basis|·ε + t`.

The residual base-dependence (the accept set varies with the coins prefix) is why a single
pushforward does not suffice and the *fibered* form is needed: per base the challenge is uniform and
the accept set is fixed, so the single-slot bound applies fiberwise and integrates. What this module
does **not** discharge is (a) and (b) themselves for the concrete family: (a) is the genuine
probabilistic modeling step (an adaptive multiopen rewind tree, not a composition of existing
lemmas — confirmed by the forking/oracle audit that `reprogramX*` are pointwise-only), and (b) is
the protocol-decomposition of a family clean opening into the four canonical-run accept events.
They are the honest remaining premises; everything between them and the single number is proven here.
-/

namespace Zcash.Snark

open scoped ENNReal

/-- **The fibered single-slot counting bound.** For a per-base accept family `acc : A → B → Prop`
over a uniform product `A × B`, the event "the second coordinate accepts at the first *and* that
base's accept measure is below `t`" has measure `≤ t`. Per base `a`, this is the single-slot bound
`uniformOfFintype_accept_below_threshold_le (acc a) t`; `uniformOfFintype_prod_fiber_bound_right`
lifts the uniform fiber bound to the product. This is the engine that lets the base-dependent accept
set (fixed once the base is read) still be controlled by one threshold. -/
theorem fibered_accept_below_threshold_le {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] [DecidableEq B] (acc : A → B → Prop)
    [∀ a, DecidablePred (acc a)] (t : ℝ≥0∞) :
    (PMF.uniformOfFintype (A × B)).toOuterMeasure
        {x : A × B | acc x.1 x.2 ∧
          (PMF.uniformOfFintype B).toOuterMeasure (Finset.univ.filter (acc x.1)) ≤ t}
      ≤ t := by
  have h := uniformOfFintype_prod_fiber_bound_right
    (S := fun a => {b : B | acc a b ∧
      (PMF.uniformOfFintype B).toOuterMeasure (Finset.univ.filter (acc a)) ≤ t})
    (fun a => uniformOfFintype_accept_below_threshold_le (acc a) t)
  convert h using 2

/-- **The residual bound from the coupling and containment.** If the coins measure pushes forward
under the base-and-challenge extraction `f` to the uniform product measure (**coupling (a)**), and
the residual `R` is contained in the preimage of the accept-below-threshold event (**containment
(b)**), then `μ(R) ≤ t`. Proof: monotonicity along (b), the pushforward identity
`PMF.toOuterMeasure_map_apply`, the coupling (a), and the fibered counting bound. Both hypotheses are
non-circular: (a) is distributional (a `map` equality), (b) is a set containment — neither refers to
`μ(R)` or the conclusion. -/
theorem residual_le_of_coupling_containment {Ω A B : Type*}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] [DecidableEq B]
    (μ : PMF Ω) (f : Ω → A × B) (acc : A → B → Prop) [∀ a, DecidablePred (acc a)]
    (t : ℝ≥0∞) (R : Set Ω)
    (hcouple : μ.map f = PMF.uniformOfFintype (A × B))
    (hcont : R ⊆ f ⁻¹' {x : A × B | acc x.1 x.2 ∧
        (PMF.uniformOfFintype B).toOuterMeasure (Finset.univ.filter (acc x.1)) ≤ t}) :
    μ.toOuterMeasure R ≤ t := by
  set AccSet : Set (A × B) := {x : A × B | acc x.1 x.2 ∧
    (PMF.uniformOfFintype B).toOuterMeasure (Finset.univ.filter (acc x.1)) ≤ t} with hAcc
  calc μ.toOuterMeasure R
      ≤ μ.toOuterMeasure (f ⁻¹' AccSet) := μ.toOuterMeasure.mono hcont
    _ = (μ.map f).toOuterMeasure AccSet := (PMF.toOuterMeasure_map_apply f μ AccSet).symm
    _ = (PMF.uniformOfFintype (A × B)).toOuterMeasure AccSet := by rw [hcouple]
    _ ≤ t := fibered_accept_below_threshold_le acc t

set_option maxHeartbeats 1000000 in
open ComputedAlgebraicFSFamily in
/-- **#67: the unconditional single-number knowledge-error bound, modulo the forking coupling.**
`snarkExtraction_prob_le_of_generatorRO_textbookDL_decomposed` with the clean-but-not-extracted
residual closed to the threshold `t` by the forking reduction. The two hypotheses are the isolated
standard facts:

* `hcouple` — **(a)** the challenge-uniformity coupling: the coins measure pushes forward under the
  base-and-challenge extraction `f : Ω → A × (Fp⁴)` to the uniform product. `A` is the base space
  (the per-coins deployed instance data the multiopen accept event depends on); the `Fp⁴` factor is
  the four fresh multiopen challenges.
* `hcont` — **(b)** the accept containment: on the clean-but-not-extracted residual, `f` lands in the
  accept-below-threshold event for the per-base accept family `acc` (instantiated at
  `w ∈ memberJointAccept` and `t := Σtᵢ` by `deployed_member_budget`).

Instantiating `t` with the multiopen knowledge error
`((deployedSetQueries…−1)/|Fp|) + ((deployedX4PairCount…−1)/|Fp| + (…allPts…)/|Fp| +
deployedX4PairCount/|Fp|)` gives the single-number bound
`(Q+k)·3/|Fp| + (Q+1)/|Fp| + |basis|·ε + Σtᵢ`. This is the honest close: everything is proven except
`hcouple` (the random-oracle modeling step, an adaptive multiopen rewind tree) and `hcont` (the
family-clean-opening decomposition), both non-circular and both the standard forking-lemma inputs. -/
theorem snarkExtraction_prob_le_of_generatorRO_textbookDL_unconditional {shape : Shape}
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T) (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    {A : Type*} [Fintype A] [Nonempty A]
    (f : (↥(Set.range query) → VestaG) × family.Coins → A × (Fp × Fp × Fp × Fp))
    (acc : A → (Fp × Fp × Fp × Fp) → Prop) [∀ a, DecidablePred (acc a)]
    (t : ℝ≥0∞)
    (hcouple : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).map f
        = PMF.uniformOfFintype (A × (Fp × Fp × Fp × Fp)))
    (hcont : ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.cleanButNotExtracted extracted)
        ⊆ f ⁻¹' {x : A × (Fp × Fp × Fp × Fp) | acc x.1 x.2 ∧
          (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
            (Finset.univ.filter (acc x.1)) ≤ t}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkExtractionFailureEvent extracted)
      ≤ ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound)
        + t := by
  refine le_trans
    (snarkExtraction_prob_le_of_generatorRO_textbookDL_decomposed B hB query hquery family hDL
      extracted) ?_
  refine add_le_add le_rfl ?_
  exact residual_le_of_coupling_containment
    (independentProductPMF (orchardGeneratorROSetup query) (PMF.uniformOfFintype family.Coins))
    f acc t _ hcouple hcont

/-! ## The budget half of the containment is a theorem

The containment premise `hcont` of `snarkExtraction_..._unconditional` bundles two facts about the
residual: **(b)** the honest challenge tuple lands in `memberJointAccept` (the structural
accept-decomposition), and **(c)** the joint accept measure at that base is within the knowledge
error `Σtᵢ`. Fact **(c)** is *not* a premise — it is `deployed_member_budget` read as a
contrapositive: when the decoded member columns do **not** all take their claimed evaluations (i.e.
extraction fails, off the `(g,U,W)`-relation branch), the joint accept measure is at most the
budget. Isolating it here leaves only the coupling **(a)** and the pure structural containment
**(b)** as the standing non-circular premises of the forking argument. -/
theorem memberJointAccept_measure_le_of_not_extraction {G : Type*} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW}
    (i : ℕ) (hi : i < deployedX4PairCount vk ps ch)
    (md : OpenedMemberDecode urs hk vk ps ch pbatch i hi)
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (havoid : ∀ (ξv ζv χv : Fp),
      OpenedX3Accept urs hk vk
        ((canonicalX2Run urs hk vk ((canonicalX1Run urs hk vk ps ch ξv).spliced ps)
            ((canonicalX1Run urs hk vk ps ch ξv).challenges ch ξv) (b₂f ξv) ζv).spliced
          ((canonicalX1Run urs hk vk ps ch ξv).spliced ps))
        ((canonicalX2Run urs hk vk ((canonicalX1Run urs hk vk ps ch ξv).spliced ps)
            ((canonicalX1Run urs hk vk ps ch ξv).challenges ch ξv) (b₂f ξv) ζv).challenges
          ((canonicalX1Run urs hk vk ps ch ξv).challenges ch ξv) ζv)
        (evalVector urs.k χv) χv →
      ∀ k', χv ∉ deployedSetPts vk ((canonicalX1Run urs hk vk ps ch ξv).spliced ps)
        ((canonicalX1Run urs hk vk ps ch ξv).challenges ch ξv) k')
    (hnex : ¬ ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries vk ps ch)).points.getD i []).length)
        (m₀ : Fin (deployedSetQueries vk ps ch i).length),
        (coeffsToPoly (md.cols m₀)).eval
            (((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [])[idx])
          = ((deployedSetQueries vk ps ch i).getD (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w) :
    (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
        (memberJointAccept urs hk vk ps ch b₂f)
      ≤ (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk ps ch).card
              + (deployedAllPts vk ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk ps ch : ℝ≥0∞) / Fintype.card Fp) :=
  (deployed_member_budget urs hk vk ps ch i hi md b₂f havoid).resolve_right hnex

end Zcash.Snark
