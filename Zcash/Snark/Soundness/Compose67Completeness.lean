import Zcash.Snark.Soundness.Compose67Forking
import Zcash.Snark.Soundness.Compose67

/-!
# The honest-completeness containment for the #67 ladder (`hcont`)

The ladder endpoint `snarkExtraction_prob_le_of_generatorRO_textbookDL_ladder`
(`Soundness.Compose67Assembly`) is unconditional modulo two concrete non-circular inputs: the family
`PeelDecode` (`D`) and the honest-completeness containment (`hcont`). This module discharges the
measure side of `hcont` outright and reduces its landing side to a single sharp, non-circular
*honest-completeness supply* hypothesis.

Two facts assembled here from `Compose67Forking`:

* **`memberBadEvent_measure_le`** — the priced bad event has measure at most the sum of its three
  worst-case thresholds, *unconditionally* (no acceptance, no coupling). Each of the three parts is
  self-pricing: the joint-accept part is either empty or `memberJointAccept` itself (whose measure
  the part's own guard bounds); the `x₄`/`x₁` floor-failure parts are the single-slot below-threshold
  events (`uniformOfFintype_accept_below_threshold_le`) read through the fourth/first coordinate
  cylinders. This is the `μ(accept) ≤ s` half of `hcont` for `accept := memberBadEvent`.

* **`memberBadEvent_containment_of_supply`** — the landing half: on the clean-but-not-extracted
  residual, the honest challenge tuple lands in `memberBadEvent` — *given the single-transcript
  supply* (deployed acceptance and a Fiat–Shamir tree at the honest IPA base `evalVector urs.k ch.x3`
  produced by the clean opening). This is `honest_tuple_mem_memberBadEvent` (already proven — the
  batch and member decode are produced or priced, nothing assumed) packaged with the supply as an
  explicit premise.

The one remaining input, `HonestCompletenessSupply`, is the standard AGM-completeness bridge: a
family clean opening yields deployed acceptance and a Fiat–Shamir tree at the honest base. It is
non-circular (it mentions neither `extracted` nor any measure) and is the sole residual on the
landing side of `#67`. -/

namespace Zcash.Snark

open Polynomial
open scoped ENNReal
open Classical

/-- Named `Inhabited VestaG` matching the algebraic family's value, so the VestaG-instance lemmas
below do not shadow it with an auto-named copy (which tangles `whnf` on `multiopenCommitment`). -/
local instance vestaInhabitedCompletenessZ8 : Inhabited VestaG := ⟨0⟩

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- The three worst-case thresholds of `memberBadEvent` at point set `i`, summed: the joint-accept
budget, the `x₄` pair-count floor, and the `x₁` member-count floor. This is the `s` bounding
`μ(memberBadEvent … i)`. -/
noncomputable def memberBadBudget [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (urs : URS G) (i : ℕ) : ℝ≥0∞ :=
  (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
      + (((deployedX4PairCount vk ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + ((max (2 ^ urs.k) (deployedAllPts vk ps ch).card
            + (deployedAllPts vk ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (deployedX4PairCount vk ps ch : ℝ≥0∞) / Fintype.card Fp)
    + (deployedX4PairCount vk ps ch : ℝ≥0∞) / Fintype.card Fp
    + (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp

/-- **The priced bad event has measure at most its three-threshold budget — unconditionally.** No
acceptance and no coupling: each of the three parts of `memberBadEvent` is self-pricing. This is the
`μ(accept) ≤ s` half of the ladder's `hcont` for `accept := memberBadEvent`. -/
theorem memberBadEvent_measure_le [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (i : ℕ) :
    (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure (memberBadEvent urs hk vk ps ch i)
      ≤ memberBadBudget vk ps ch urs i := by
  set thr : ℝ≥0∞ :=
    (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
      + (((deployedX4PairCount vk ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + ((max (2 ^ urs.k) (deployedAllPts vk ps ch).card
            + (deployedAllPts vk ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (deployedX4PairCount vk ps ch : ℝ≥0∞) / Fintype.card Fp) with hthr
  set thr4 : ℝ≥0∞ := (deployedX4PairCount vk ps ch : ℝ≥0∞) / Fintype.card Fp with hthr4
  set thr1 : ℝ≥0∞ :=
    (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp with hthr1
  -- part 1: the joint-accept part, either `memberJointAccept` (guard holds) or empty
  set S : Set (Fp × Fp × Fp × Fp) :=
    memberJointAccept urs hk vk ps ch (fun _ => evalVector urs.k ch.x3) with hS
  have hpart1 : (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
      {w : Fp × Fp × Fp × Fp | w ∈ S ∧
        (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure S ≤ thr} ≤ thr := by
    by_cases hc : (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure S ≤ thr
    · have hset : {w : Fp × Fp × Fp × Fp | w ∈ S ∧
          (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure S ≤ thr} = S :=
        Set.ext fun w => ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩
      rw [hset]; exact hc
    · have hset : {w : Fp × Fp × Fp × Fp | w ∈ S ∧
          (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure S ≤ thr} = (∅ : Set _) :=
        Set.ext fun w => ⟨fun h => absurd h.2 hc, fun h => h.elim⟩
      rw [hset]; simp
  -- part 2: the `x₄` floor-failure part, read through the fourth-coordinate cylinder
  have hpart2 : (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
      {w : Fp × Fp × Fp × Fp | OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3) w.2.2.2 ∧
        (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3))) ≤ thr4} ≤ thr4 := by
    by_cases hc : (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
        (OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3))) ≤ thr4
    · have hset : {w : Fp × Fp × Fp × Fp |
          OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3) w.2.2.2 ∧
          (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3))) ≤ thr4}
          = {w : Fp × Fp × Fp × Fp | w.2.2.2 ∈
              {χ : Fp | OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3) χ}} :=
        Set.ext fun w => ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩
      rw [hset, uniformOfFintype_x4_cylinder, uniformOfFintype_toOuterMeasure_setOf_filter]
      exact hc
    · have hset : {w : Fp × Fp × Fp × Fp |
          OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3) w.2.2.2 ∧
          (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3))) ≤ thr4} = (∅ : Set _) :=
        Set.ext fun w => ⟨fun h => absurd h.2 hc, fun h => h.elim⟩
      rw [hset]; simp
  -- part 3: the `x₁` floor-failure part, read through the first-coordinate cylinder
  have hpart3 : (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
      {w : Fp × Fp × Fp × Fp | OpenedX1Accept urs hk vk ps ch w.1 ∧
        (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX1Accept urs hk vk ps ch)) ≤ thr1} ≤ thr1 := by
    by_cases hc : (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
        (OpenedX1Accept urs hk vk ps ch)) ≤ thr1
    · have hset : {w : Fp × Fp × Fp × Fp | OpenedX1Accept urs hk vk ps ch w.1 ∧
          (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk ps ch)) ≤ thr1}
          = {w : Fp × Fp × Fp × Fp | w.1 ∈ {χ : Fp | OpenedX1Accept urs hk vk ps ch χ}} :=
        Set.ext fun w => ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩
      rw [hset, uniformOfFintype_fst_cylinder (α := Fp) (β := Fp × Fp × Fp),
        uniformOfFintype_toOuterMeasure_setOf_filter]
      exact hc
    · have hset : {w : Fp × Fp × Fp × Fp | OpenedX1Accept urs hk vk ps ch w.1 ∧
          (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk ps ch)) ≤ thr1} = (∅ : Set _) :=
        Set.ext fun w => ⟨fun h => absurd h.2 hc, fun h => h.elim⟩
      rw [hset]; simp
  -- union bound over the three parts
  rw [memberBadEvent, memberBadBudget]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (le_trans (MeasureTheory.measure_union_le _ _) ?_) hpart3
  exact add_le_add hpart1 hpart2

/-- **The honest-completeness supply.** A clean opening at base `(ps, ch)` yields the
single-transcript ingredients `honest_tuple_mem_memberBadEvent` consumes: a nonzero blinding `z`, a
Fiat–Shamir tree at the honest IPA base `evalVector urs.k ch.x3`, and deployed acceptance. This is
the standard AGM-completeness bridge (a clean opening corresponds to an accepting deployed
transcript); it is non-circular — it mentions neither `extracted` nor any measure. -/
def HonestCompletenessSupply [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : Prop :=
  ∃ (z blind : Fp), z ≠ 0 ∧
    Nonempty (FiatShamirTree urs hk vk ps ch (evalVector urs.k ch.x3) z blind) ∧
    DeployedAccepts urs hk vk ps ch

/-- **The landing half of `hcont`, from the supply.** On a base admitting the honest-completeness
supply and off the `(g, U, W)`-relation branch, if extraction fails at point set `i` (`hnex`: no
produced batch's member decode binds all columns and no nontrivial relation is at hand), the honest
challenge tuple lands in `memberBadEvent`. This is `honest_tuple_mem_memberBadEvent` with the
single-transcript ingredients supplied by `HonestCompletenessSupply` rather than assumed piecemeal —
so the only standing input on the landing side of `hcont` is the AGM-completeness bridge. -/
theorem memberBadEvent_of_supply [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hsupply : HonestCompletenessSupply urs hk vk ps ch)
    (i : ℕ) (hi : i < deployedX4PairCount vk ps ch)
    (hlen : 0 < (deployedSetQueries vk ps ch i).length)
    (havoid : ∀ (ξv ζv χv : Fp),
      OpenedX3Accept urs hk vk
        ((canonicalX2Run urs hk vk ((canonicalX1Run urs hk vk ps ch ξv).spliced ps)
            ((canonicalX1Run urs hk vk ps ch ξv).challenges ch ξv)
            (evalVector urs.k ch.x3) ζv).spliced
          ((canonicalX1Run urs hk vk ps ch ξv).spliced ps))
        ((canonicalX2Run urs hk vk ((canonicalX1Run urs hk vk ps ch ξv).spliced ps)
            ((canonicalX1Run urs hk vk ps ch ξv).challenges ch ξv)
            (evalVector urs.k ch.x3) ζv).challenges
          ((canonicalX1Run urs hk vk ps ch ξv).challenges ch ξv) ζv)
        (evalVector urs.k χv) χv →
      ∀ k', χv ∉ deployedSetPts vk ((canonicalX1Run urs hk vk ps ch ξv).spliced ps)
        ((canonicalX1Run urs hk vk ps ch ξv).challenges ch ξv) k')
    (hnex : ∀ (a₀ : Fin (2 ^ urs.k) → Fp) (pU pW : Fp)
      (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW)
      (md : OpenedMemberDecode urs hk vk ps ch pbatch i hi),
      ¬ ∀ (idx : Fin ((constructIntermediateSets
            (assembleQueries vk ps ch)).points.getD i []).length)
          (m₀ : Fin (deployedSetQueries vk ps ch i).length),
          (coeffsToPoly (md.cols m₀)).eval
              (((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [])[idx])
            = ((deployedSetQueries vk ps ch i).getD (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
          ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w) :
    (ch.x1, ch.x2, ch.x3, ch.x4) ∈ memberBadEvent urs hk vk ps ch i := by
  obtain ⟨z, blind, hz, ⟨hFS⟩, hacc⟩ := hsupply
  exact honest_tuple_mem_memberBadEvent urs hk vk ps ch hnrel hz hFS hacc i hi hlen havoid hnex

/-- **The supply from a forked transcript and deployed acceptance.** `FiatShamirTree` is the function
type `DeployedIpaVerifierEq → ForkedTranscript`, so a nonempty forked transcript at the honest IPA
base `evalVector urs.k ch.x3` gives a nonempty Fiat–Shamir tree (the constant function). With a
nonzero blinding `z` and deployed acceptance, this is exactly `HonestCompletenessSupply` — reducing
the supply to its two primitives (a forked transcript and `DeployedAccepts`). -/
theorem honestCompletenessSupply_of_forkedTranscript [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {z blind : Fp} (hz : z ≠ 0)
    (hft : Nonempty (ForkedTranscript urs hk vk ps ch (evalVector urs.k ch.x3) z blind))
    (hacc : DeployedAccepts urs hk vk ps ch) :
    HonestCompletenessSupply urs hk vk ps ch :=
  let ⟨ft⟩ := hft
  ⟨z, blind, hz, ⟨fun _ => ft⟩, hacc⟩

set_option maxHeartbeats 1000000 in
/-- **The honest-base forked transcript from a family instance's clean opening.** The instance's
`Opening` gives an `IpaRelation` at `commit aMulti`; `ipaRelation_deployed_of_instance` re-expresses
it (under the honest value shift `hshift`) at the de-blinded deployed commitment
`deployedCommitment − multiU•u − multiBlind•w`, opening to `multiopenValue` at the honest IPA base
`evalVector shape.k (ν 7)`. `ForkedTranscript.nonempty_of_opening` turns that blinded opening into a
forked transcript. The three distinct nonzero fold challenges `u₁,u₂,u₃` are the standard
IPA-soundness field facts (`|Fp|` is a large prime), taken as explicit hypotheses. -/
theorem forkedTranscript_nonempty_of_instanceOpening {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG} (p : AlgebraicWfProof basis vk) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening)
    (hshift : (ν 10)⁻¹ * (p.multiU ν + ν 9 * p.sU)
        - ν 9 * innerProduct p.s (evalVector shape.k (ν 7)) = 0)
    (u₁ u₂ u₃ : Fp) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0) (blind : Fp) :
    Nonempty (ForkedTranscript (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0)) (evalVector shape.k (ν 7)) (ν 10) blind) := by
  obtain ⟨hcommit, hval⟩ := ipaRelation_deployed_of_instance p ν cert hz hvalid hshift o
  refine ForkedTranscript.nonempty_of_opening (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
    (chRecord ν (fun _ => 0)) u₁ u₂ u₃ h12 h13 h23 hu₁ hu₂ hu₃ o.1 (p.multiU ν) (p.multiBlind ν)
    ?_ ?_
  · rw [commit_eq_commitGen] at hcommit
    rw [hcommit]; abel
  · rw [← hval]; simp only [commitGen, innerProduct, smul_eq_mul]

set_option maxHeartbeats 1000000 in
/-- **The honest-completeness supply from a family instance's clean opening.** Combining the forked
transcript from the opening (`forkedTranscript_nonempty_of_instanceOpening`) with deployed acceptance
via `honestCompletenessSupply_of_forkedTranscript`. This discharges the *tree-construction* side of
the honest-completeness bridge outright; the standing inputs are the honest value shift `hshift`, the
IPA fold-challenge field facts, and `DeployedAccepts` — the latter being the AGM-completeness fact
that a family clean opening's transcript is deployed-accepted (`erase p` at `chRecord ν`). -/
theorem honestCompletenessSupply_of_instanceOpening {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG} (p : AlgebraicWfProof basis vk) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening)
    (hshift : (ν 10)⁻¹ * (p.multiU ν + ν 9 * p.sU)
        - ν 9 * innerProduct p.s (evalVector shape.k (ν 7)) = 0)
    (u₁ u₂ u₃ : Fp) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (hacc : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0))) :
    HonestCompletenessSupply (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0)) :=
  honestCompletenessSupply_of_forkedTranscript (ursOfAugmentedBasis shape.k basis) rfl vk
    p.proof.1 (chRecord ν (fun _ => 0)) hz
    (forkedTranscript_nonempty_of_instanceOpening p ν cert hz hvalid o hshift
      u₁ u₂ u₃ h12 h13 h23 hu₁ hu₂ hu₃ 0)
    hacc

end Zcash.Snark
