import Zcash.Snark.Soundness.Composition.Decomposition
import Zcash.Snark.Soundness.Multiopen.BudgetedExtraction

/-!
# The forking reduction closing the clean-but-not-extracted residual

This module closes the residual `μ(cleanButNotExtracted)` to the multiopen knowledge error, given
exactly two non-circular facts:

* **(a) the coupling** — the four fresh multiopen challenges, read from the coins by
  reading/reprogramming the oracle at the sealed multiopen prefixes, are jointly uniform (the shape
  proven for the IPA rounds by `roChallenges_ipaRound_uniform`);
* **(b) the containment** — on the residual, the challenge tuple lands in the per-base accept event
  whose measure is below the threshold (`deployed_member_budget`: extraction fails only when the
  joint accept measure is `≤ Σtᵢ`).

Neither mentions `extracted`'s measure — (a) is about the challenge distribution, (b) is a set
containment. Given both, the reduction is proven (`residual_le_of_coupling_containment`): the accept
set varies with the coins, so the *fibered* single-slot counting bound applies per base and
integrates, giving the single-number bound `(Q+k)·3/|Fp| + (Q+1)/|Fp| + |basis|·ε + t`. What this
module does not discharge is (a) and (b) for the concrete family — (a) is the genuine modelling
step (`reprogramX*` are pointwise-only), (b) the protocol decomposition of a clean opening into the
four canonical-run accept events.
-/

namespace Zcash.Snark

-- The deployed grouping definitions appear inside index types, so a defeq check on an index can
-- pull the whole `constructIntermediateSets (assembleQueries …)` computation through `whnf`.
-- Sealing them keeps those checks syntactic; the proofs below use their equation lemmas.
attribute [local irreducible] deployedSetQueries deployedSetCommIds deployedX4PairCount
  x4BatchCommitments x4BatchEvals

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

open ComputedAlgebraicFSFamily in
/-- **The unconditional single-number knowledge-error bound, modulo the forking coupling.** The
decomposed bound with the residual closed to the threshold `t` from two isolated facts: `hcouple`
(the coins push forward to the uniform product on base × challenges) and `hcont` (the residual
lands in the accept-below-threshold event, instantiated by `deployed_member_budget`). Everything
else is proven; `hcouple` is the random-oracle modelling step and `hcont` the clean-opening
decomposition — the standard forking-lemma inputs. -/
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

/-- **Honest completeness gives joint accept membership — the structural half of `hcont`.** When
the honest transcript deployed-accepts and admits a Fiat–Shamir tree at the honest IPA base with an
opened `x₄` batch, the honest challenge tuple lies in `memberJointAccept`: the honest-preferring
canonical selectors collapse the four rewind bases to the honest transcript, so each level is the
honest run's own accept. -/
theorem memberJointAccept_of_honest {G : Type*} [AddCommGroup G] [Module Fp G] [DecidableEq G]
    [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    {z blind : Fp} (hz : z ≠ 0)
    (hFS : FiatShamirTree urs hk vk ps ch (evalVector urs.k ch.x3) z blind)
    (hacc : DeployedAccepts urs hk vk ps ch)
    (aR : Fin (2 ^ urs.k) → Fp) (pUR pWR : Fp)
    (hbatch : Nonempty (OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) aR pUR pWR)) :
    (ch.x1, ch.x2, ch.x3, ch.x4) ∈
      memberJointAccept urs hk vk ps ch (fun _ => evalVector urs.k ch.x3) := by
  -- the honest run's clean accepting IPA opening at the honest base (off the DL branch)
  have fs : ForkedTranscript urs hk vk ps ch (evalVector urs.k ch.x3) z blind :=
    ForkedTranscript.ofAccepts urs hk vk ps ch hacc hFS
  have hRunAcc : ∃ (z' blind' : Fp)
      (fs' : ForkedTranscript urs hk vk ps ch (evalVector urs.k ch.x3) z' blind')
      (t : IpaTreeV Fp G urs.k),
      IpaAcceptV urs.g (evalVector urs.k ch.x3) fs'.openedCommitment
        (multiopenValue vk ps ch) t := by
    rcases deployed_to_acceptV hz urs.g (evalVector urs.k ch.x3) fs.openedCommitment
        (multiopenValue vk ps ch) blind fs.tree fs.accepts with hclean | hrel
    · exact ⟨z, blind, fs, projTree fs.tree, hclean⟩
    · exact absurd hrel hnrel
  -- honest-run accept payloads (honest splices/challenges are the identity, by `rfl`)
  have hX1 : X1PinnedRunAccepts urs hk vk ps ch ch.x1 (honestX1Run ps ch) :=
    ⟨aR, pUR, pWR, hacc, hbatch⟩
  have hX2 : X2RunAccepts urs hk vk ps ch (evalVector urs.k ch.x3) ch.x2 (honestX2Run ps ch) :=
    hRunAcc
  have hX3 : X3RunAccepts urs hk vk ps ch (evalVector urs.k ch.x3) ch.x3 (honestX3Run ps ch) :=
    hRunAcc
  -- the four honest-run accept events (bases already honest)
  have h1 : OpenedX1PinnedAccept urs hk vk ps ch ch.x1 := ⟨honestX1Run ps ch, hX1⟩
  have h2 : OpenedX2Accept urs hk vk ps ch (evalVector urs.k ch.x3) ch.x2 :=
    ⟨honestX2Run ps ch, hX2⟩
  have h3 : OpenedX3Accept urs hk vk ps ch (evalVector urs.k ch.x3) ch.x3 :=
    ⟨honestX3Run ps ch, hX3⟩
  have h4 : OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3) ch.x4 :=
    openedX4Accept_of_deployedAccepts urs hk vk ps ch hz hnrel (honestX4Run ps ch) ch.x4 hFS hacc
  -- collapse the canonical selectors to the honest runs and discharge each level
  have hc1 := canonicalX1Run_honest urs hk vk ps ch hX1
  have hc2 := canonicalX2Run_honest urs hk vk ps ch (evalVector urs.k ch.x3) hX2
  have hc3 := canonicalX3Run_honest urs hk vk ps ch (evalVector urs.k ch.x3) hX3
  simp only [memberJointAccept, innerJointAccept, Set.mem_setOf_eq, hc1,
    honestX1Run_spliced, honestX1Run_challenges, hc2, honestX2Run_spliced,
    honestX2Run_challenges, hc3, honestX3Run_spliced, honestX3Run_challenges]
  exact ⟨h1, h2, h3, h4⟩

/-! ## The batch produced on the good event

`memberJointAccept_of_honest` consumes an opened `x₄` batch. That batch is a *rewinding output*,
not a single-transcript object — but its production is already priced: given the honest fork and
the `x₄` accept floor at the honest base, `openedX4Rewind_of_x4Prob_forked` produces it, and when
the floor *fails*, the honest challenge tuple sits in the single-slot floor-failure event whose
measure is at most the threshold (`uniformOfFintype_accept_below_threshold_le`). The lemmas below
package both branches: the batch hypothesis disappears in favor of a priced event. -/

open Classical in
/-- **Honest membership with the batch derived from the `x₄` floor.** As
`memberJointAccept_of_honest`, but instead of assuming the opened `x₄` batch, derive it: the honest
fork's clean accepting opening (off the `(g,U,W)` branch) seeds `openedX4Rewind_of_x4Prob_forked`
at the honest base, and the floor pays for the rewound family. -/
theorem memberJointAccept_of_honest_of_floor {G : Type*} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    {z blind : Fp} (hz : z ≠ 0)
    (hFS : FiatShamirTree urs hk vk ps ch (evalVector urs.k ch.x3) z blind)
    (hacc : DeployedAccepts urs hk vk ps ch)
    (hprob4 : ((deployedX4PairCount vk ps ch : ℝ≥0∞)) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3)))) :
    (ch.x1, ch.x2, ch.x3, ch.x4) ∈
      memberJointAccept urs hk vk ps ch (fun _ => evalVector urs.k ch.x3) := by
  have fs : ForkedTranscript urs hk vk ps ch (evalVector urs.k ch.x3) z blind :=
    ForkedTranscript.ofAccepts urs hk vk ps ch hacc hFS
  rcases deployed_to_acceptV hz urs.g (evalVector urs.k ch.x3) fs.openedCommitment
      (multiopenValue vk ps ch) blind fs.tree fs.accepts with hclean | hrel
  · have ext := ipaRelation_extract urs (evalVector urs.k ch.x3) fs.openedCommitment
      (multiopenValue vk ps ch) (projTree fs.tree) hclean
    have batch := openedX4Rewind_of_x4Prob_forked urs hk vk ps ch fs
      ⟨projTree fs.tree, hclean⟩ hprob4 ext.1 ext.2
    exact memberJointAccept_of_honest urs hk vk ps ch hnrel hz hFS hacc
      ext.1 fs.pU fs.pW ⟨batch⟩
  · exact absurd hrel hnrel

open Classical in
/-- **The priced bad event for the deployed member extraction at point set `i`.** Three parts, each
with its own price: the joint accept holds but its measure is within the knowledge budget
(`deployed_member_budget`'s left branch); the honest-base `x₄` squeeze accepts at the drawn slot but
its floor fails; the honest-base `x₁` squeeze accepts at the drawn slot but its floor fails. The
containment lemma below shows a clean-but-not-extracted run's honest challenge tuple always lands
here — the floor failures pay for the two rewinding productions (the `x₄` batch and the member
decode) that bare acceptance does not supply. -/
noncomputable def memberBadEvent {G : Type*} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (i : ℕ) : Set (Fp × Fp × Fp × Fp) :=
  {w : Fp × Fp × Fp × Fp |
      w ∈ memberJointAccept urs hk vk ps ch (fun _ => evalVector urs.k ch.x3) ∧
      (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk ps ch (fun _ => evalVector urs.k ch.x3))
        ≤ (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (((deployedX4PairCount vk ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
            + ((max (2 ^ urs.k) (deployedAllPts vk ps ch).card
                + (deployedAllPts vk ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
            + (deployedX4PairCount vk ps ch : ℝ≥0∞) / Fintype.card Fp)}
    ∪ {w : Fp × Fp × Fp × Fp |
        OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3) w.2.2.2 ∧
        (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3)))
          ≤ (deployedX4PairCount vk ps ch : ℝ≥0∞) / Fintype.card Fp}
    ∪ {w : Fp × Fp × Fp × Fp |
        OpenedX1Accept urs hk vk ps ch w.1 ∧
        (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk ps ch))
          ≤ (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp}

open Classical in
/-- **The containment, discharged: a clean-but-not-extracted honest tuple lands in the priced bad
event.** Given deployed acceptance, a Fiat–Shamir tree at the honest IPA base, and the failure of
extraction (`hnex`), the honest tuple lies in `memberBadEvent`: a failed `x₄` floor puts it in the
`x₄` part; otherwise the floor produces the batch, and a failed `x₁` floor puts it in the `x₁`
part; with both floors the member decode exists and `hnex` turns `deployed_member_budget` into the
below-threshold bound. Everything is produced or priced; no batch, decode, or measure is assumed. -/
theorem honest_tuple_mem_memberBadEvent {G : Type*} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    {z blind : Fp} (hz : z ≠ 0)
    (hFS : FiatShamirTree urs hk vk ps ch (evalVector urs.k ch.x3) z blind)
    (hacc : DeployedAccepts urs hk vk ps ch)
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
  by_cases hp4 : ((deployedX4PairCount vk ps ch : ℝ≥0∞)) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3)))
  · -- the x₄ floor holds: produce the batch from the honest fork's clean opening
    have fs : ForkedTranscript urs hk vk ps ch (evalVector urs.k ch.x3) z blind :=
      ForkedTranscript.ofAccepts urs hk vk ps ch hacc hFS
    rcases deployed_to_acceptV hz urs.g (evalVector urs.k ch.x3) fs.openedCommitment
        (multiopenValue vk ps ch) blind fs.tree fs.accepts with hclean | hrel
    swap
    · exact absurd hrel hnrel
    have ext := ipaRelation_extract urs (evalVector urs.k ch.x3) fs.openedCommitment
      (multiopenValue vk ps ch) (projTree fs.tree) hclean
    have batch := openedX4Rewind_of_x4Prob_forked urs hk vk ps ch fs
      ⟨projTree fs.tree, hclean⟩ hp4 ext.1 ext.2
    by_cases hp1 : (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk ps ch))
    · -- both floors: member decode + joint membership + the budget's below-threshold branch
      have md := openedMemberDecode_of_x1Prob urs hk vk ps ch batch i hi hlen hp1 hacc
      have hmem : (ch.x1, ch.x2, ch.x3, ch.x4) ∈
          memberJointAccept urs hk vk ps ch (fun _ => evalVector urs.k ch.x3) :=
        memberJointAccept_of_honest urs hk vk ps ch hnrel hz hFS hacc
          ext.1 fs.pU fs.pW ⟨batch⟩
      have hbudget := memberJointAccept_measure_le_of_not_extraction urs hk vk ps ch i hi md
        (fun _ => evalVector urs.k ch.x3) havoid (hnex ext.1 fs.pU fs.pW batch md)
      exact Or.inl (Or.inl ⟨hmem, hbudget⟩)
    · -- x₁ floor fails: the batch witnesses the honest x₁ accept
      have hx₁ : OpenedX1Accept urs hk vk ps ch ch.x1 :=
        ⟨honestX1Run ps ch, evalVector urs.k ch.x3, ext.1, fs.pU, fs.pW, hacc, ⟨batch⟩⟩
      exact Or.inr ⟨hx₁, not_lt.mp hp1⟩
  · -- x₄ floor fails: the honest slot's opened accept (deployed→opened bridge)
    have h4 : OpenedX4Accept urs hk vk ps ch (evalVector urs.k ch.x3) ch.x4 :=
      openedX4Accept_of_deployedAccepts urs hk vk ps ch hz hnrel
        (honestX4Run ps ch) ch.x4 hFS hacc
    exact Or.inl (Or.inr ⟨h4, not_lt.mp hp4⟩)

/-! ## Pricing the bad event: per-base thresholds and slot cylinders -/

/-- `fibered_accept_below_threshold_le` with a *base-dependent* threshold dominated by a constant:
the per-base thresholds (the deployed counts vary with the proof string behind the base) are
absorbed into their worst case. -/
theorem fibered_accept_below_threshold_le_of_le {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] [DecidableEq B] (acc : A → B → Prop)
    [∀ a, DecidablePred (acc a)] (t : A → ℝ≥0∞) {T : ℝ≥0∞} (hT : ∀ a, t a ≤ T) :
    (PMF.uniformOfFintype (A × B)).toOuterMeasure
        {x : A × B | acc x.1 x.2 ∧
          (PMF.uniformOfFintype B).toOuterMeasure (Finset.univ.filter (acc x.1)) ≤ t x.1}
      ≤ T := by
  have h := uniformOfFintype_prod_fiber_bound_right
    (S := fun a => {b : B | acc a b ∧
      (PMF.uniformOfFintype B).toOuterMeasure (Finset.univ.filter (acc a)) ≤ t a})
    (fun a => le_trans (uniformOfFintype_accept_below_threshold_le (acc a) (t a)) (hT a))
  convert h using 2

/-- The uniform measure of a first-coordinate cylinder is the coordinate's own measure. -/
theorem uniformOfFintype_fst_cylinder {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (E : Set α) :
    (PMF.uniformOfFintype (α × β)).toOuterMeasure {p : α × β | p.1 ∈ E}
      = (PMF.uniformOfFintype α).toOuterMeasure E := by
  have hset : {p : α × β | p.1 ∈ E} = E ×ˢ (Set.univ : Set β) := by
    ext ⟨a, b⟩; simp [Set.mem_prod]
  rw [hset, uniformOfFintype_toOuterMeasure_prod, uniformOfFintype_toOuterMeasure_univ, mul_one]

/-- The uniform measure of a fourth-coordinate cylinder over the challenge quadruple. -/
theorem uniformOfFintype_x4_cylinder (E : Set Fp) :
    (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
        {w : Fp × Fp × Fp × Fp | w.2.2.2 ∈ E}
      = (PMF.uniformOfFintype Fp).toOuterMeasure E := by
  have hset : {w : Fp × Fp × Fp × Fp | w.2.2.2 ∈ E}
      = reindexX4 ⁻¹' {p : Fp × (Fp × Fp × Fp) | p.1 ∈ E} := rfl
  rw [hset, uniformOfFintype_toOuterMeasure_preimage_equiv reindexX4,
    uniformOfFintype_fst_cylinder]

open Classical in
/-- **The fibered slot floor-failure bound.** For a per-base single-slot accept family read through
a slot projection `g` whose cylinders have the slot's own measure, the event "the drawn slot
accepts at the base and that base's floor is at most `s(base)`" is bounded by the worst-case
threshold `S`. Per base the set is either empty (floor above `s`) or the accept cylinder, whose
measure is the accept measure `≤ s(base) ≤ S`. -/
theorem fibered_slot_floor_le {A B' : Type*} [Fintype A] [Nonempty A]
    [Fintype B'] [Nonempty B'] (g : B' → Fp)
    (hg : ∀ E : Set Fp, (PMF.uniformOfFintype B').toOuterMeasure {w : B' | g w ∈ E}
      = (PMF.uniformOfFintype Fp).toOuterMeasure E)
    (acc : A → Fp → Prop) (s : A → ℝ≥0∞) {S : ℝ≥0∞} (hS : ∀ a, s a ≤ S) :
    (PMF.uniformOfFintype (A × B')).toOuterMeasure
        {x : A × B' | acc x.1 (g x.2) ∧
          (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc x.1)) ≤ s x.1}
      ≤ S := by
  have hfiber : ∀ a, (PMF.uniformOfFintype B').toOuterMeasure
      {w : B' | acc a (g w) ∧
        (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc a)) ≤ s a}
      ≤ S := by
    intro a
    by_cases hc : (PMF.uniformOfFintype Fp).toOuterMeasure
        (Finset.univ.filter (acc a)) ≤ s a
    · have hset : {w : B' | acc a (g w) ∧
          (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc a)) ≤ s a}
          = {w : B' | g w ∈ {χ : Fp | acc a χ}} :=
        Set.ext fun w => ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩
      rw [hset, hg, uniformOfFintype_toOuterMeasure_setOf_filter]
      exact le_trans hc (hS a)
    · have hset : {w : B' | acc a (g w) ∧
          (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc a)) ≤ s a}
          = (∅ : Set B') :=
        Set.ext fun w => ⟨fun h => absurd h.2 hc, fun h => h.elim⟩
      rw [hset]
      simp
  have h := uniformOfFintype_prod_fiber_bound_right
    (S := fun a => {w : B' | acc a (g w) ∧
      (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc a)) ≤ s a})
    hfiber
  convert h using 2

/-- The set-form fibered below-threshold bound: per base, the event is either the accept set itself
(measure within the base's threshold) or empty. The `memberBadEvent` first part is fibered in this
shape — the accept set is `memberJointAccept` at the base, whole, not a filtered slot. -/
theorem fibered_mem_below_threshold_le {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (SA : A → Set B) (t : A → ℝ≥0∞) {T : ℝ≥0∞}
    (hT : ∀ a, t a ≤ T) :
    (PMF.uniformOfFintype (A × B)).toOuterMeasure
        {x : A × B | x.2 ∈ SA x.1 ∧
          (PMF.uniformOfFintype B).toOuterMeasure (SA x.1) ≤ t x.1}
      ≤ T := by
  have hfiber : ∀ a, (PMF.uniformOfFintype B).toOuterMeasure
      {b : B | b ∈ SA a ∧ (PMF.uniformOfFintype B).toOuterMeasure (SA a) ≤ t a} ≤ T := by
    intro a
    by_cases hc : (PMF.uniformOfFintype B).toOuterMeasure (SA a) ≤ t a
    · have hset : {b : B | b ∈ SA a ∧ (PMF.uniformOfFintype B).toOuterMeasure (SA a) ≤ t a}
          = SA a := Set.ext fun b => ⟨fun h => h.1, fun h => ⟨h, hc⟩⟩
      rw [hset]
      exact le_trans hc (hT a)
    · have hset : {b : B | b ∈ SA a ∧ (PMF.uniformOfFintype B).toOuterMeasure (SA a) ≤ t a}
          = (∅ : Set B) := Set.ext fun b => ⟨fun h => absurd h.2 hc, fun h => h.elim⟩
      rw [hset]
      simp
  have h := uniformOfFintype_prod_fiber_bound_right
    (S := fun a => {b : B | b ∈ SA a ∧ (PMF.uniformOfFintype B).toOuterMeasure (SA a) ≤ t a})
    hfiber
  convert h using 2

set_option maxRecDepth 4000 in
open Classical in
/-- **The residual bound over the priced union.** The union analogue of
`residual_le_of_coupling_containment`: the containment now lands in the three-part bad event —
per-base joint accept within its threshold, or a floor failure at the `x₄` or `x₁` slot — and the
bound is the sum of the three worst-case prices. At the deployed instantiation the fiber of the
target set at base `a` is exactly `memberBadEvent` (with `SA` the joint accept, `acc4`/`acc1` the
honest-base squeeze accepts, and the thresholds the deployed counts), so
`honest_tuple_mem_memberBadEvent` discharges the containment pointwise from the per-coins supply. -/
theorem residual_le_of_coupling_containment_union {Ω A : Type*} [Fintype A] [Nonempty A]
    (μ : PMF Ω) (f : Ω → A × (Fp × Fp × Fp × Fp))
    (SA : A → Set (Fp × Fp × Fp × Fp)) (t : A → ℝ≥0∞)
    (acc4 acc1 : A → Fp → Prop) (s4 s1 : A → ℝ≥0∞) {T S4 S1 : ℝ≥0∞}
    (hT : ∀ a, t a ≤ T) (hS4 : ∀ a, s4 a ≤ S4) (hS1 : ∀ a, s1 a ≤ S1)
    (R : Set Ω)
    (hcouple : μ.map f = PMF.uniformOfFintype (A × (Fp × Fp × Fp × Fp)))
    (hcont : R ⊆ f ⁻¹'
      ({x : A × (Fp × Fp × Fp × Fp) | x.2 ∈ SA x.1 ∧
          (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure (SA x.1) ≤ t x.1}
        ∪ {x : A × (Fp × Fp × Fp × Fp) | acc4 x.1 x.2.2.2.2 ∧
            (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (acc4 x.1)) ≤ s4 x.1}
        ∪ {x : A × (Fp × Fp × Fp × Fp) | acc1 x.1 x.2.1 ∧
            (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (acc1 x.1)) ≤ s1 x.1})) :
    μ.toOuterMeasure R ≤ T + S4 + S1 := by
  set BadSet : Set (A × (Fp × Fp × Fp × Fp)) :=
    {x : A × (Fp × Fp × Fp × Fp) | x.2 ∈ SA x.1 ∧
        (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure (SA x.1) ≤ t x.1}
      ∪ {x : A × (Fp × Fp × Fp × Fp) | acc4 x.1 x.2.2.2.2 ∧
          (PMF.uniformOfFintype Fp).toOuterMeasure
            (Finset.univ.filter (acc4 x.1)) ≤ s4 x.1}
      ∪ {x : A × (Fp × Fp × Fp × Fp) | acc1 x.1 x.2.1 ∧
          (PMF.uniformOfFintype Fp).toOuterMeasure
            (Finset.univ.filter (acc1 x.1)) ≤ s1 x.1} with hBad
  calc μ.toOuterMeasure R
      ≤ μ.toOuterMeasure (f ⁻¹' BadSet) := μ.toOuterMeasure.mono hcont
    _ = (μ.map f).toOuterMeasure BadSet := (PMF.toOuterMeasure_map_apply f μ BadSet).symm
    _ = (PMF.uniformOfFintype (A × (Fp × Fp × Fp × Fp))).toOuterMeasure BadSet := by
        rw [hcouple]
    _ ≤ T + S4 + S1 := by
        rw [hBad]
        refine le_trans (MeasureTheory.measure_union_le _ _) ?_
        refine add_le_add (le_trans (MeasureTheory.measure_union_le _ _) ?_) ?_
        · exact add_le_add (fibered_mem_below_threshold_le SA t hT)
            (fibered_slot_floor_le (B' := Fp × Fp × Fp × Fp) (fun w => w.2.2.2)
              (fun E => uniformOfFintype_x4_cylinder E) acc4 s4 hS4)
        · exact fibered_slot_floor_le (B' := Fp × Fp × Fp × Fp) (fun w => w.1)
            (fun E => uniformOfFintype_fst_cylinder (α := Fp) (β := Fp × Fp × Fp) E) acc1 s1 hS1

/-! ## Structural bounds on the deployed thresholds

The per-base thresholds vary with the base's proof string only through the deployed counts. The
`x₄` pair count is at most the shape's point-set count (the pair list zips against the fixed-arity
claimed-evaluation vector), and the point union is at most the query list's length (every grouped
point is some query's opening point). -/

/-- The deployed `x₄` pair count is at most the shape's point-set arity. -/
theorem deployedX4PairCount_le_numPointSets {G : Type*} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    deployedX4PairCount vk ps ch ≤ shape.numPointSets := by
  simp only [deployedX4PairCount, deployedX4Pairs, List.length_zip, List.length_ofFn]
  exact min_le_right _ _

/-- Members of the first-appearance point fold are opening points of the folded queries. -/
private theorem mem_dedup_points_foldl {k : ℕ} {F G' : Type*} [DecidableEq F] :
    ∀ (queries : List (VerifierQuery k F G')) (init : List F) (x : F),
      x ∈ queries.foldl (fun acc q => if q.point ∈ acc then acc else acc ++ [q.point]) init →
      x ∈ init ∨ ∃ q ∈ queries, q.point = x := by
  intro queries
  induction queries with
  | nil => intro init x hx; exact Or.inl hx
  | cons q L ih =>
      intro init x hx
      rw [List.foldl_cons] at hx
      rcases ih _ x hx with hin | ⟨q', hq', hpt⟩
      · by_cases hq : q.point ∈ init
        · rw [if_pos hq] at hin
          exact Or.inl hin
        · rw [if_neg hq] at hin
          rcases List.mem_append.mp hin with h | h
          · exact Or.inl h
          · exact Or.inr ⟨q, List.mem_cons_self .., (List.mem_singleton.mp h).symm⟩
      · exact Or.inr ⟨q', List.mem_cons_of_mem _ hq', hpt⟩

/-- Every point of a grouped point set is some query's opening point — the reverse direction of
`constructIntermediateSets_point_mem`, for cardinality bounds. -/
theorem constructIntermediateSets_points_getD_mem_queries {k : ℕ} {F G' : Type*}
    [DecidableEq F] [DecidableEq G'] (queries : List (VerifierQuery k F G')) (si : ℕ)
    {x : F} (hx : x ∈ (constructIntermediateSets queries).points.getD si []) :
    ∃ q ∈ queries, q.point = x := by
  classical
  have key : ∀ pl ∈ (constructIntermediateSets queries).points, x ∈ pl →
      ∃ q ∈ queries, q.point = x := by
    intro pl hpl hxpl
    simp only [constructIntermediateSets] at hpl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hpl
    obtain ⟨i, hi, hix⟩ := List.mem_filterMap.mp hxpl
    rw [List.getElem?_eq_some_iff] at hix
    obtain ⟨hilt, rfl⟩ := hix
    rcases mem_dedup_points_foldl queries [] _ (List.getElem_mem hilt) with h0 | h
    · exact absurd h0 (List.not_mem_nil)
    · exact h
  rcases lt_or_ge si (constructIntermediateSets queries).points.length with hlt | hge
  · rw [List.getD_eq_getElem _ _ hlt] at hx
    exact key _ (List.getElem_mem hlt) hx
  · rw [List.getD_eq_default _ _ hge] at hx
    exact absurd hx (List.not_mem_nil)

/-- The deployed point union has at most as many points as the verifier has opening queries. -/
theorem deployedAllPts_card_le {G : Type*} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    (deployedAllPts vk ps ch).card ≤ (assembleQueries vk ps ch).length := by
  classical
  have hsub : deployedAllPts vk ps ch
      ⊆ ((assembleQueries vk ps ch).map (·.point)).toFinset := by
    intro x hx
    rw [deployedAllPts, Finset.mem_biUnion] at hx
    obtain ⟨j, -, hj⟩ := hx
    rw [deployedSetPts, List.mem_toFinset] at hj
    obtain ⟨q, hq, hqx⟩ := constructIntermediateSets_points_getD_mem_queries _ j hj
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨q, hq, hqx⟩
  calc (deployedAllPts vk ps ch).card
      ≤ ((assembleQueries vk ps ch).map (·.point)).toFinset.card := Finset.card_le_card hsub
    _ ≤ ((assembleQueries vk ps ch).map (·.point)).length := List.toFinset_card_le _
    _ = (assembleQueries vk ps ch).length := List.length_map ..

open Classical in
open ComputedAlgebraicFSFamily in
/-- **The single-number knowledge-error bound over the priced union, modulo the coupling.** The
unconditional bound with the containment target enlarged to `memberBadEvent`, so the containment is
dischargeable pointwise from single-transcript supply (`honest_tuple_mem_memberBadEvent`). The
price is `T + S4 + S1` — the worst-case knowledge budget plus the two floor-failure prices. The one
remaining hypothesis is `hcouple`, the challenge-uniformity coupling. -/
theorem snarkExtraction_prob_le_of_generatorRO_textbookDL_unconditional_priced {shape : Shape}
    {T' : Type*} [DecidableEq T'] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T') (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    {A : Type*} [Fintype A] [Nonempty A]
    (f : (↥(Set.range query) → VestaG) × family.Coins → A × (Fp × Fp × Fp × Fp))
    (SA : A → Set (Fp × Fp × Fp × Fp)) (t : A → ℝ≥0∞)
    (acc4 acc1 : A → Fp → Prop) (s4 s1 : A → ℝ≥0∞) {T S4 S1 : ℝ≥0∞}
    (hT : ∀ a, t a ≤ T) (hS4 : ∀ a, s4 a ≤ S4) (hS1 : ∀ a, s1 a ≤ S1)
    (hcouple : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).map f
        = PMF.uniformOfFintype (A × (Fp × Fp × Fp × Fp)))
    (hcont : ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.cleanButNotExtracted extracted)
        ⊆ f ⁻¹'
          ({x : A × (Fp × Fp × Fp × Fp) | x.2 ∈ SA x.1 ∧
              (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure (SA x.1) ≤ t x.1}
            ∪ {x : A × (Fp × Fp × Fp × Fp) | acc4 x.1 x.2.2.2.2 ∧
                (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (acc4 x.1)) ≤ s4 x.1}
            ∪ {x : A × (Fp × Fp × Fp × Fp) | acc1 x.1 x.2.1 ∧
                (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (acc1 x.1)) ≤ s1 x.1})) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkExtractionFailureEvent extracted)
      ≤ ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound)
        + (T + S4 + S1) := by
  refine le_trans
    (snarkExtraction_prob_le_of_generatorRO_textbookDL_decomposed B hB query hquery family hDL
      extracted) ?_
  refine add_le_add le_rfl ?_
  exact residual_le_of_coupling_containment_union
    (independentProductPMF (orchardGeneratorROSetup query) (PMF.uniformOfFintype family.Coins))
    f SA t acc4 acc1 s4 s1 hT hS4 hS1 _ hcouple hcont

end Zcash.Snark
