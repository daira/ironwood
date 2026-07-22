import Zcash.Snark.Soundness.Composition.Residual
import Zcash.Snark.Soundness.Composition.Bridge

/-!
# The honest-completeness containment for the composition ladder (`hcont`)

The ladder endpoint (`Soundness.Composition.Assembly`) is unconditional modulo two inputs: the family
`PeelDecode` and the containment `hcont`. This module discharges `hcont`'s measure side outright
and reduces its landing side to one non-circular hypothesis:

* `memberBadEvent_measure_le` — the priced bad event has measure at most the sum of its three
  worst-case thresholds, unconditionally: each part is self-pricing (the joint-accept part by its
  own guard, the `x₄`/`x₁` floor-failure parts by the single-slot bound through coordinate
  cylinders).
* `memberBadEvent_of_supply` — on the clean-but-not-extracted residual the honest challenge tuple
  lands in `memberBadEvent`, given the single-transcript supply: deployed acceptance and a
  Fiat–Shamir tree at the honest IPA base.

The remaining input, `HonestCompletenessSupply`, is the standard AGM-completeness bridge — a clean
opening yields deployed acceptance and a tree at the honest base. It mentions neither `extracted`
nor any measure.

## Discharging the supply from a clean opening

The final sections discharge the supply's own inputs: the IPA fold challenges
(`exists_ipaFoldChallenges` exhibits `1, 2, 3` in `Fp`), deployed acceptance
(`deployedAccepts_of_verifierEq`), the value shift (forced on the witness tie), and the tie itself
(`honestCompletenessSupply_or_relation`: *either* the supply *or* a nontrivial `(g, u, w)`
relation). What no single accepting run supplies is the tie's batch — a rewinding product, priced
by `deployed_member_budget`, the residual `hcont` pays for. -/

namespace Zcash.Snark

open Polynomial
open scoped ENNReal
open Classical

/-- Named `Inhabited VestaG` matching the algebraic family's value, so the VestaG-instance lemmas
below do not shadow it with an auto-named copy (which tangles `whnf` on `multiopenCommitment`). -/
local instance vestaInhabitedCompleteness : Inhabited VestaG := ⟨0⟩

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

/-! ## Discharging the supply's standing inputs

The fold-challenge facts, deployed acceptance, and the value shift, in turn. -/

/-- Distinct nonzero naturals below the field order stay distinct in `Fp`: the cast is injective
below the modulus (`ZMod.val_cast_of_lt`). -/
theorem natCast_ne_of_lt_scalarFieldOrder {a b : ℕ} (ha : a < scalarFieldOrder)
    (hb : b < scalarFieldOrder) (hab : a ≠ b) : (a : Fp) ≠ (b : Fp) := by
  intro hEq
  exact hab (((ZMod.val_cast_of_lt ha).symm.trans (congrArg ZMod.val hEq)).trans
    (ZMod.val_cast_of_lt hb))

/-- **The IPA fold-challenge facts, discharged.** `ForkedTranscript.nonempty_of_opening` needs three
pairwise-distinct nonzero fold challenges; `Fp` is a prime field of order `≈ 2²⁵⁴`, so `1, 2, 3`
serve. This removes the six field side conditions carried by
`forkedTranscript_nonempty_of_instanceOpening`. -/
theorem exists_ipaFoldChallenges :
    ∃ u₁ u₂ u₃ : Fp, u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 := by
  have hlt : ∀ n : ℕ, n ≤ 3 → n < scalarFieldOrder := by
    intro n hn
    have : (3 : ℕ) < scalarFieldOrder := by
      simp only [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
      norm_num
    omega
  have key : ∀ a b : ℕ, a ≤ 3 → b ≤ 3 → a ≠ b → (a : Fp) ≠ (b : Fp) := fun a b ha hb hab =>
    natCast_ne_of_lt_scalarFieldOrder (hlt a ha) (hlt b hb) hab
  refine ⟨((1 : ℕ) : Fp), ((2 : ℕ) : Fp), ((3 : ℕ) : Fp),
    key 1 2 (by norm_num) (by norm_num) (by norm_num),
    key 1 3 (by norm_num) (by norm_num) (by norm_num),
    key 2 3 (by norm_num) (by norm_num) (by norm_num), ?_, ?_, ?_⟩
  · simpa using key 1 0 (by norm_num) (by norm_num) (by norm_num)
  · simpa using key 2 0 (by norm_num) (by norm_num) (by norm_num)
  · simpa using key 3 0 (by norm_num) (by norm_num) (by norm_num)

/-- **Deployed acceptance from the deployed verifier equation.** The converse of
`deployedAccepts_verifierEq` (`Soundness.Main`), modulo the assembly being defined: `assemble?`
returns `some m` exactly when the reader's proof-string well-formedness check passes, and on that
branch `m` *is* the assembled final MSM (`assemble?_eq_some`), whose evaluation
`deployed_verification_eq` rewrites to the explicit halo2 verifier equation. So the family's accept
predicate `fullAlgebraicAccept` (a `DeployedIpaVerifierEq`) yields the `DeployedAccepts` that
`honest_tuple_mem_memberBadEvent` consumes. -/
theorem deployedAccepts_of_verifierEq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {m : Msm shape.k Fp G} (hm : assemble? vk ps ch = some m)
    (h : DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps ch) :
    DeployedAccepts urs hk vk ps ch := by
  unfold DeployedAccepts
  rw [hm]
  simp only []
  rw [eval_cast hk m, assemble?_eq_some vk ps ch hm,
    deployed_verification_eq (hk ▸ urs.g) urs.w urs.u ps ch
      (constructIntermediateSets (assembleQueries vk ps ch))]
  exact h

set_option maxHeartbeats 1000000 in
/-- **The honest-completeness supply with the shift derived.**
`honestCompletenessSupply_of_instanceOpening` with `hshift` discharged by
`shift_eq_zero_of_openings_agree` (`Soundness.Composition.Bridge`): the clean opening's witness `o.1` agreeing
with a batch witness `a₀` that opens the inner product at `multiopenValue` *forces* the shift to
vanish, so no honest-value-shift hypothesis is carried. The fold challenges are discharged by
`exists_ipaFoldChallenges`. -/
theorem honestCompletenessSupply_of_openings_agree {shape : Shape}
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
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (hval₀ : innerProduct a₀ (evalVector shape.k (ν 7))
      = multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)))
    (hae : o.1 = a₀)
    (hacc : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0))) :
    HonestCompletenessSupply (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0)) := by
  obtain ⟨u₁, u₂, u₃, h12, h13, h23, hu₁, hu₂, hu₃⟩ := exists_ipaFoldChallenges
  exact honestCompletenessSupply_of_instanceOpening p ν cert hz hvalid o
    (shift_eq_zero_of_openings_agree p ν cert hz hvalid o hval₀ hae)
    u₁ u₂ u₃ h12 h13 h23 hu₁ hu₂ hu₃ hacc

set_option maxHeartbeats 1000000 in
/-- **The honest-completeness supply from a family clean opening.** `cleanOpening_provenance`
(`Soundness.VestaBudget`) exposes the `AlgebraicWfProof`, oracle scalars, certificate, and clean
opening behind a produced instance; this theorem turns that data into the supply, with the fold
challenges and the value shift discharged and deployed acceptance reduced to the family's own accept
predicate. The two premises left are the ones a single accepting run does not carry: the witness tie
`hae` (a rewinding product, priced by `deployed_member_budget`) and the assembly being defined. -/
theorem honestCompletenessSupply_of_cleanOpening {shape : Shape}
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
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (hval₀ : innerProduct a₀ (evalVector shape.k (ν 7))
      = multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)))
    (hae : o.1 = a₀)
    {m : Msm shape.k Fp VestaG}
    (hm : assemble? vk p.proof.1 (chRecord ν (fun _ => 0)) = some m)
    (hverify : fullAlgebraicAccept basis vk p ν (fun _ => 0)) :
    HonestCompletenessSupply (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0)) :=
  honestCompletenessSupply_of_openings_agree p ν cert hz hvalid o hval₀ hae
    (deployedAccepts_of_verifierEq (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0)) hm hverify)

/-! ### Acceptance through `assemble?`

`fullAlgebraicAccept` asserts the verifier's MSM equation but not its *rejection* paths:
`assemble?` returns `none` on a malformed proof string, at `ch.x ^ vk.n = 1`, on duplicate
queries, and when `x₃` hits an opened point, and `DeployedAccepts` is `False` on every one. Taking
the deployed decision as the family's acceptance closes that gap by construction and removes the
`assemble? = some m` side condition. Additive: the strengthened predicate implies the current one
(`fullAlgebraicAccept_of_deployed`), so everything proved about the weaker predicate carries over. -/

/-- The family's accept predicate strengthened to the deployed decision: the verifier reaches a
decision *and* accepts. -/
def fullAlgebraicAcceptDeployed {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (p : AlgebraicWfProof basis vk)
    (ν : Fin 11 → Fp) (χ : Fin shape.k → Fp) : Prop :=
  DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1 (chRecord ν χ)

/-- The strengthened acceptance implies the one the family currently uses, so nothing proved about
`fullAlgebraicAccept` is lost by moving to it (`deployedAccepts_verifierEq`, `Soundness.Main`). -/
theorem fullAlgebraicAccept_of_deployed {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (p : AlgebraicWfProof basis vk)
    (ν : Fin 11 → Fp) (χ : Fin shape.k → Fp)
    (h : fullAlgebraicAcceptDeployed basis vk p ν χ) :
    fullAlgebraicAccept basis vk p ν χ :=
  deployedAccepts_verifierEq (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
    (chRecord ν χ) h

/-- The knowledge-error event at the *deployed decision*: full deployed acceptance — the verifier
reaches a decision and accepts — with no SNARK extraction. Same shape as
`snarkExtractionFailureEvent`, with `fullAlgebraicAcceptDeployed` in place of the verifier-equation
predicate, so the rejection paths are excluded by construction. -/
def snarkExtractionFailureEventDeployed {shape : Shape}
    (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins) :=
  {q | fsWinsFull (family.adversary q.1) (fullAlgebraicAcceptDeployed q.1 (family.vk q.1))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2.1 ∧
    ¬ extracted q.1 q.2}

/-- Deployed acceptance is the stronger event, so its knowledge-error event sits inside the one the
family's existing bounds are stated over. -/
theorem snarkExtractionFailureEventDeployed_subset {shape : Shape}
    (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop) :
    snarkExtractionFailureEventDeployed family extracted
      ⊆ family.snarkExtractionFailureEvent extracted := by
  rintro q ⟨hacc, hnex⟩
  exact ⟨fullAlgebraicAccept_of_deployed q.1 (family.vk q.1)
    ((family.adversary q.1).run q.2.1) _ _ hacc, hnex⟩

open scoped ENNReal in
/-- **Every knowledge-error bound transfers to deployed acceptance.** The deployed failure event is
contained in the one the existing endpoints bound
(`snarkExtractionFailureEventDeployed_subset`), so monotonicity carries any such bound across — the
endpoints stay as they are, and the bound is read where a verifier panic is non-accepting. -/
theorem snarkExtractionFailureEventDeployed_measure_le {shape : Shape} {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ shape.k) → T)
    (family : ComputedAlgebraicFSFamily shape)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    {bound : ℝ≥0∞}
    (h : (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype family.Coins)).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            family.snarkExtractionFailureEvent extracted) ≤ bound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family extracted) ≤ bound :=
  le_trans (MeasureTheory.measure_mono
    (Set.preimage_mono (snarkExtractionFailureEventDeployed_subset family extracted))) h

set_option maxHeartbeats 1000000 in
/-- **The honest-completeness supply from a clean opening, with no `assemble?` premise.**
`honestCompletenessSupply_of_cleanOpening` with acceptance taken as the deployed decision: because
`fullAlgebraicAcceptDeployed` *is* `DeployedAccepts`, the rejection-path side condition disappears
rather than being assumed. The remaining premises are the clean opening's provenance data and the
witness tie — and `honestCompletenessSupply_or_relation` discharges the tie into the standard
agree-or-collide disjunction. -/
theorem honestCompletenessSupply_of_cleanOpening_deployed {shape : Shape}
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
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (hval₀ : innerProduct a₀ (evalVector shape.k (ν 7))
      = multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)))
    (hae : o.1 = a₀)
    (hverify : fullAlgebraicAcceptDeployed basis vk p ν (fun _ => 0)) :
    HonestCompletenessSupply (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0)) :=
  honestCompletenessSupply_of_openings_agree p ν cert hz hvalid o hval₀ hae hverify

set_option maxHeartbeats 1000000 in
/-- **The supply, or binding breaks.** The clean opening `o` and the batch witness `a₀` commit to
the same group element (`opening_commit_deployed_of_instance` and `hcommit₀`), so *either* they
agree — `honestCompletenessSupply_of_openings_agree` produces the supply, shift forced — *or* they
are two distinct openings of one commitment, a nontrivial `(g, u, w)` relation
(`hasNontrivialRelation_of_two_openings`). The same agree-or-collide split as
`member_relation_or_dlr_of_instance`, so the witness tie stops being a premise. -/
theorem honestCompletenessSupply_or_relation {shape : Shape}
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
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (hcommit₀ : commit (ursOfAugmentedBasis shape.k basis) a₀
      = deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0))
        - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
        - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
    (hval₀ : innerProduct a₀ (evalVector shape.k (ν 7))
      = multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)))
    (hacc : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0))) :
    HonestCompletenessSupply (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0))
    ∨ HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w := by
  by_cases hae : o.1 = a₀
  · exact Or.inl (honestCompletenessSupply_of_openings_agree p ν cert hz hvalid o hval₀ hae hacc)
  · refine Or.inr (hasNontrivialRelation_of_two_openings _ hae ?_)
    rw [opening_commit_deployed_of_instance p ν cert hz hvalid o, hcommit₀]

end Zcash.Snark
