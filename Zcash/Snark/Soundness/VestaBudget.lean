import Zcash.Snark.Soundness.Compose67
import Zcash.Snark.Soundness.Multiopen.BudgetedExtraction

/-!
# The budgeted deployed capstone and the budgeted computed path

`Soundness.Vesta` proves the derived deployed member capstone
(`orchard_verifier_vesta_member_constraint_derived`), whose extraction floors are universally
quantified over the splice runs `X1Run`/`X2Run`/`X3Run`; `Soundness.Multiopen.BudgetedExtraction`
re-proves the member extraction from a single joint accept floor along the canonical rewind path.
This module joins the two ends:

* `orchard_verifier_vesta_member_constraint_budgeted` — the derived capstone with its seven
  run-quantified floor premises (`hξ₀p`/`hprob1p`/`hx2`/`hx3anchor`/`hprob3`/`hprob4` and the
  run-quantified `havoid`) replaced by one joint accept floor `t₁ + (t₂ + t₃ + t₄) <
  μ(memberJointAccept)` at the honest-base thresholds, plus sample avoidance at the canonical runs
  only.
* `member_relation_or_dlr_of_instance_budgeted` / `member_snark_of_instance_budgeted` /
  `orchard_verifier_sound_vesta_budgeted` — the computed path (`Soundness.Compose67`) routed
  through the budgeted capstone: the member decode is *constructed*
  (`openedMemberDecode_of_x1Prob`) and the quotient identity `hquot` is *derived*
  (`quotientCheck_of_claimed` from the member bindings), so neither is a hypothesis. The premises
  that remain are acceptance itself (`hacc0`), the two accept-measure floors (`hprob1`, the joint
  floor `hJ`), sample avoidance at the canonical runs, the gate-structure fingerprint surfaces
  (`hfold`, `hgood`), the layout identities, and the committed-quotient identity — each an honest
  trust surface, none of them extraction data.

  The layout/committed-quotient identities (`hadviceLayout`/`hinstanceLayout`/`hquotCommitted`) are
  the halo2 faithfulness boundary — that the VK's declared query layout is the circuit's real column
  structure and that the quotient is a committed column — not derivable without modeling keygen. They
  are *fail-safe*, not silently satisfiable: each demands `(deployedSetCommIds …).getD idx d = c`
  where the default `d` is a `CommitmentId` constructor distinct from the demanded `c`
  (`vanishingH` vs `adviceCol`/`instanceCol`; `randomPoly` vs `vanishingH`, `Verifier.Checks`), so an
  out-of-range or mismatched layout makes the premise *false*, never vacuously true.

The `x₁` floor `hprob1` feeds the member-decode construction and is stated at the honest base; it
follows from the joint floor by the first-coordinate marginal bound, but stays a named hypothesis
because the statement's decode terms carry its proof.
-/

namespace Zcash.Snark

-- Match the instance set `AlgebraicWfProof.multiopen_repr` is stated against (`Soundness.Compose67`
-- and `Forking.Adversary.Algebraic` use the same concrete `Inhabited VestaG`); a binder would be a
-- different instance term, forcing the `multiopenCommitment` fold through `whnf`. Named to avoid an
-- auto-generated-name collision on co-import.
local instance vestaInhabitedVestaBudget : Inhabited VestaG := ⟨0⟩

open Polynomial in
open scoped ENNReal in
open Classical in
set_option maxHeartbeats 4000000 in
/-- **Budgeted deployed member capstone: the floor family priced by one joint accept floor.** The
conclusion of `orchard_verifier_vesta_member_constraint_derived` (`Soundness.Vesta`) — the gate
check runs at the deployed opening challenge `ch.x` on the decoded member columns, with the
columns' claimed evaluations *derived* via the member node binding and `hquot` produced by
`quotientCheck_of_claimed` — from a single joint accept floor per point set:
`t₁(i) + (t₂ + t₃ + t₄) < μ(memberJointAccept)` at the honest-base thresholds
(`deployed_member_node_binding_at_point_budgeted`), in place of the derived capstone's seven
run-quantified floor premises. Sample avoidance (`havoid`) is required only at the canonical runs.

Named assumptions: `hacc0` (the deployed run accepts), `hprob1` (the honest-base `x₁` accept
floor, feeding the member-decode construction), `hJ` (the joint accept floor), `havoid`
(canonical-run sample avoidance), `hfold` (the gate fold at the deployed claimed evaluations — the
gate-structure fingerprint surface), `hgood` (the Schwartz–Zippel surface *at the fixed* `ch.x`: if
the gate identity fails as polynomials, its difference is nonzero at `ch.x`), `hadviceLayout`/
`hinstanceLayout` (VK query-layout identities), `hquotCommitted` (the quotient is a committed
column), `hencodes` (the member-relation consumer).

`hgood` is irreducible at the *fixed* `ch.x`: proving `ch.x ∉ szBadSet` would require resampling.
`hgood_of_xProb` (`Soundness.Multiopen.Claimed`) produces the surface only at a *resampled* good
challenge (the `_xgood` rung `member_constraint_of_relation_and_batch_xgood`,
`Soundness.Multiopen.Opened`), which the deployed architecture cannot route through here: the decoded
member columns are pinned at `ch.x`'s rotation points (the deployed query points), so the gate check
is coupled to `ch.x` and cannot move to a separate challenge without re-running the value binding at
that challenge's rotations. So `hgood` stays a faithfulness surface at `ch.x`, exactly as the base
rung's docstring records (`Opened.member_constraint_of_relation_and_batch_xgood`) — but its failure
over the `x`-squeeze is priced (`hgood_failure_priced`/`hgood_of_good_challenge`, this module), and
`hfold` decomposes into the vanishing-slot value binding + `ch.x^vk.n ≠ 1` + the sharpened fold
fingerprint (`vanishing_query_mem_assembleQueries`/`hfold_of_expectedHEval_binding`, this module) —
see the `hfold`/`hgood` section note at the end of this file. -/
theorem orchard_verifier_vesta_member_constraint_budgeted {shape : Shape}
    (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk ps ch
      → 0 < (deployedSetQueries vk ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk ps ch →
      (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk ps ch)))
    (hacc0 : DeployedAccepts urs hk vk ps ch)
    (p : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.adviceEvals p)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.instanceEvals p)).length)
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk ps ch →
      (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk ps ch).card
              + (deployedAllPts vk ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk ps ch b₂f))
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
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval (fun n => (fixedCols n).eval ch.x)
          (deployedClaimedFeed vk ps ch adviceSet adviceMem vk.adviceQueryLayout)
          (deployedClaimedFeed vk ps ch instanceSet instanceMem vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0 = hpoly.eval ch.x * (ch.x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval ch.x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk ps ch)
        (hMem : Fin (deployedSetQueries vk ps ch hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns urs hk vk ps ch
        (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk ps ch) p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg pU pW a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  by_cases hrel : HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
  · exact Or.inr hrel
  -- derive `hadvice`: the rotated advice feed's value at `ch.x` is the deployed claimed eval
  have hadvice : ∀ n, (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (adviceSet j)
        (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
          (adviceMem j))) n).eval ch.x
      = deployedClaimedFeed vk ps ch adviceSet adviceMem vk.adviceQueryLayout n := by
    intro n
    by_cases h : n < numAdvice
    · obtain ⟨q, hqmem, hqid, hqpt⟩ := advice_query_mem_assembleQueries vk ps ch p
        (hadvLen ⟨n, h⟩).1 (hadvLen ⟨n, h⟩).2
      have hltm : ((adviceMem ⟨n, h⟩ : ℕ))
          < (deployedSetCommIds vk ps ch (adviceSet ⟨n, h⟩)).length := by
        rw [deployedSetCommIds_length]
        exact (adviceMem ⟨n, h⟩).isLt
      have hid : (deployedSetCommIds vk ps ch (adviceSet ⟨n, h⟩)).getD ((adviceMem ⟨n, h⟩ : ℕ))
          CommitmentId.vanishingH = q.commId := (hadviceLayout ⟨n, h⟩).trans hqid.symm
      have hpt := deployed_query_point_mem vk ps ch hqmem hltm hid
      rw [hqpt] at hpt
      have hb := deployed_member_node_binding_at_point_budgeted urs hk vk ps ch (adviceSet ⟨n, h⟩)
        (hadviceSet ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (adviceSet ⟨n, h⟩)
          (hadviceSet ⟨n, h⟩) (hlen _ (hadviceSet ⟨n, h⟩)) (hprob1 _ (hadviceSet ⟨n, h⟩)) hacc0)
        b₂f (hJ _ (hadviceSet ⟨n, h⟩)) havoid hpt (adviceMem ⟨n, h⟩)
      rcases hb with hb | hdlr
      swap
      · exact absurd hdlr hrel
      rw [rotatedFeed_eval vk.omega vk.adviceQueryLayout _ h ch.x, hb, deployedClaimedFeed,
        dif_pos h]
    · rw [rotatedFeed_eval_of_ge vk.omega vk.adviceQueryLayout _ (Nat.not_lt.mp h) ch.x,
        deployedClaimedFeed, dif_neg h]
  -- derive `hinstance` symmetrically
  have hinstance : ∀ n, (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (instanceSet j)
        (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
          (instanceMem j))) n).eval ch.x
      = deployedClaimedFeed vk ps ch instanceSet instanceMem vk.instanceQueryLayout n := by
    intro n
    by_cases h : n < numInstance
    · obtain ⟨q, hqmem, hqid, hqpt⟩ := instance_query_mem_assembleQueries vk ps ch p
        (hinstLen ⟨n, h⟩).1 (hinstLen ⟨n, h⟩).2
      have hltm : ((instanceMem ⟨n, h⟩ : ℕ))
          < (deployedSetCommIds vk ps ch (instanceSet ⟨n, h⟩)).length := by
        rw [deployedSetCommIds_length]
        exact (instanceMem ⟨n, h⟩).isLt
      have hid : (deployedSetCommIds vk ps ch (instanceSet ⟨n, h⟩)).getD
          ((instanceMem ⟨n, h⟩ : ℕ)) CommitmentId.vanishingH = q.commId :=
        (hinstanceLayout ⟨n, h⟩).trans hqid.symm
      have hpt := deployed_query_point_mem vk ps ch hqmem hltm hid
      rw [hqpt] at hpt
      have hb := deployed_member_node_binding_at_point_budgeted urs hk vk ps ch (instanceSet ⟨n, h⟩)
        (hinstanceSet ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (instanceSet ⟨n, h⟩)
          (hinstanceSet ⟨n, h⟩) (hlen _ (hinstanceSet ⟨n, h⟩)) (hprob1 _ (hinstanceSet ⟨n, h⟩))
          hacc0)
        b₂f (hJ _ (hinstanceSet ⟨n, h⟩)) havoid hpt (instanceMem ⟨n, h⟩)
      rcases hb with hb | hdlr
      swap
      · exact absurd hdlr hrel
      rw [rotatedFeed_eval vk.omega vk.instanceQueryLayout _ h ch.x, hb, deployedClaimedFeed,
        dif_pos h]
    · rw [rotatedFeed_eval_of_ge vk.omega vk.instanceQueryLayout _ (Nat.not_lt.mp h) ch.x,
        deployedClaimedFeed, dif_neg h]
  -- the gate check at the deployed opening challenge, from the derived claimed evaluations
  exact orchard_verifier_vesta_member_constraint_deployed_x4 urs hk vk ps ch pU pW adviceSet
    hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg ch.x
    pbatch hξcur hlen hprob1 hacc0
    (quotientCheck_of_claimed fixedCols _ _ y gates hpoly deg ch.x
      (fun n => (fixedCols n).eval ch.x)
      (deployedClaimedFeed vk ps ch adviceSet adviceMem vk.adviceQueryLayout)
      (deployedClaimedFeed vk ps ch instanceSet instanceMem vk.instanceQueryLayout)
      (fun _ => rfl) hadvice hinstance hfold)
    hgood p hadviceLayout hinstanceLayout hquotCommitted hencodes

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}

open Polynomial in
open scoped ENNReal in
open Classical in
set_option maxHeartbeats 4000000 in
/-- **The budgeted witness tie on the computed path.** `member_relation_or_dlr_of_instance`
(`Soundness.Compose67`) with the member decode *constructed* and `hquot` *derived*: on the
agreement branch the budgeted deployed capstone runs at the algebraic instance's base
`(p.proof.1, chRecord ν)`; on the disagreement branch the two openings of the shared commitment
collide into a computed `(g, u, w)` relation. No `mdec`/`hquot` hypothesis remains — the measure
premises are the honest-base `x₁` floor and the joint accept floor. -/
theorem member_relation_or_dlr_of_instance_budgeted
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
    (pbatch : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0)))
      (x4BatchEvals vk p.proof.1 (chRecord ν (fun _ => 0))) a₀ (p.multiU ν) (p.multiBlind ν))
    (hξcur : pbatch.batchChallenge pbatch.current
      = (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x4)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (adviceMem : ∀ j : Fin numAdvice,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ)
    (hlen : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0))
      → 0 < (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)))))
    (hacc0 : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0)))
    (pp : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).adviceEvals pp)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).instanceEvals pp)).length)
    (b₂f : Fp → Fin (2 ^ shape.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        + (((deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) - 1 : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + ((max (2 ^ shape.k)
                (deployedAllPts vk p.proof.1 (chRecord ν (fun _ => 0))).card
              + (deployedAllPts vk p.proof.1 (chRecord ν (fun _ => 0))).card : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + (deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) : ℝ≥0∞)
            / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) b₂f))
    (havoid : ∀ (ξv ζv χv : Fp),
      OpenedX3Accept (ursOfAugmentedBasis shape.k basis) rfl vk
        ((canonicalX2Run (ursOfAugmentedBasis shape.k basis) rfl vk
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv)
            (b₂f ξv) ζv).spliced
          ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1))
        ((canonicalX2Run (ursOfAugmentedBasis shape.k basis) rfl vk
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv)
            (b₂f ξv) ζv).challenges
          ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv) ζv)
        (evalVector shape.k χv) χv →
      ∀ k', χv ∉ deployedSetPts vk
        ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
          (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
        ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
          (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv) k')
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval
          (fun n => (fixedCols n).eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x)
          (deployedClaimedFeed vk p.proof.1 (chRecord ν (fun _ => 0)) adviceSet adviceMem
            vk.adviceQueryLayout)
          (deployedClaimedFeed vk p.proof.1 (chRecord ν (fun _ => 0)) instanceSet instanceMem
            vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0
        = hpoly.eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x
          * ((chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval
          (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).getD
          (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol pp (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).getD
          (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol pp (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ)
        (hhSet : hSet < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
        (hMem : Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl
          vk p.proof.1 (chRecord ν (fun _ => 0)) pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).getD (hMem : ℕ)
          CommitmentId.randomPoly = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0))
        (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0))
          - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
          - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
        (evalVector shape.k (ν 7)) (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)))
        pp adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem
        fixedCols y gates hpoly deg (p.multiU ν) (p.multiBlind ν) a → S) :
    S ∨ HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w := by
  by_cases hae : o.1 = a₀
  · exact orchard_verifier_vesta_member_constraint_budgeted (ursOfAugmentedBasis shape.k basis)
      rfl vk p.proof.1 (chRecord ν (fun _ => 0)) (p.multiU ν) (p.multiBlind ν)
      adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates
      hpoly deg pbatch hξcur hlen hprob1 hacc0 pp hadvLen hinstLen b₂f hJ havoid hfold hgood
      hadviceLayout hinstanceLayout hquotCommitted hencodes
  · exact Or.inr (hasNontrivialRelation_of_two_openings (ursOfAugmentedBasis shape.k basis) hae
      ((opening_commit_deployed_of_instance p ν cert hz hvalid o).trans
        (pbatch.ipaRelation_of_x4Current hξcur).1.symm))

open Polynomial in
open scoped ENNReal in
open Classical in
set_option maxHeartbeats 1000000 in
/-- The budgeted `runToSnark`-analogue on the computed path: `member_snark_of_instance`
(`Soundness.Compose67`) with the clean-opening branch routed through the budgeted witness tie, so
no member decode or quotient identity is hypothesised. On the clean-opening branch the budgeted
capstone produces the member SNARK relation (or a binding `HasNontrivialRelation`); on the
relation branch, the algebraic extraction's own `AlgebraicRelationWitness`. -/
noncomputable def member_snark_of_instance_budgeted
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
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (pbatch : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0)))
      (x4BatchEvals vk p.proof.1 (chRecord ν (fun _ => 0))) a₀ (p.multiU ν) (p.multiBlind ν))
    (hξcur : pbatch.batchChallenge pbatch.current
      = (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x4)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (adviceMem : ∀ j : Fin numAdvice,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ)
    (hlen : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0))
      → 0 < (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)))))
    (hacc0 : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0)))
    (pp : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).adviceEvals pp)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).instanceEvals pp)).length)
    (b₂f : Fp → Fin (2 ^ shape.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        + (((deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) - 1 : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + ((max (2 ^ shape.k)
                (deployedAllPts vk p.proof.1 (chRecord ν (fun _ => 0))).card
              + (deployedAllPts vk p.proof.1 (chRecord ν (fun _ => 0))).card : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + (deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) : ℝ≥0∞)
            / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) b₂f))
    (havoid : ∀ (ξv ζv χv : Fp),
      OpenedX3Accept (ursOfAugmentedBasis shape.k basis) rfl vk
        ((canonicalX2Run (ursOfAugmentedBasis shape.k basis) rfl vk
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv)
            (b₂f ξv) ζv).spliced
          ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1))
        ((canonicalX2Run (ursOfAugmentedBasis shape.k basis) rfl vk
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv)
            (b₂f ξv) ζv).challenges
          ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv) ζv)
        (evalVector shape.k χv) χv →
      ∀ k', χv ∉ deployedSetPts vk
        ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
          (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
        ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
          (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv) k')
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval
          (fun n => (fixedCols n).eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x)
          (deployedClaimedFeed vk p.proof.1 (chRecord ν (fun _ => 0)) adviceSet adviceMem
            vk.adviceQueryLayout)
          (deployedClaimedFeed vk p.proof.1 (chRecord ν (fun _ => 0)) instanceSet instanceMem
            vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0
        = hpoly.eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x
          * ((chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval
          (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).getD
          (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol pp (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).getD
          (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol pp (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ)
        (hhSet : hSet < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
        (hMem : Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl
          vk p.proof.1 (chRecord ν (fun _ => 0)) pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).getD (hMem : ℕ)
          CommitmentId.randomPoly = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0))
        (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0))
          - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
          - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
        (evalVector shape.k (ν 7)) (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)))
        pp adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem
        fixedCols y gates hpoly deg (p.multiU ν) (p.multiBlind ν) a → S) :
    (S ∨ HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)
      ⊕' AlgebraicRelationWitness (F := Fp) basis :=
  match (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).run with
  | PSum.inl o =>
      PSum.inl (member_relation_or_dlr_of_instance_budgeted p ν cert hz hvalid o pbatch hξcur
        adviceSet hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates
        hpoly deg hlen hprob1 hacc0 pp hadvLen hinstLen b₂f hJ havoid hfold hgood
        hadviceLayout hinstanceLayout hquotCommitted hencodes)
  | PSum.inr rel => PSum.inr rel

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **Deployed soundness on the computed path, extraction data derived.** The budgeted counterpart
of `orchard_verifier_sound_vesta_computed` (`Soundness.Compose67`): the same
`KnowledgeSoundness.SnarkRelation`-based `S` / `HasNontrivialRelation` / `AlgebraicRelationWitness`
trichotomy, but with the member decode constructed and the quotient identity derived — no
`mdec`/`hquot` hypothesis. What remains hypothesised: the deployed acceptance `hacc0`, the two
accept-measure floors (`hprob1` and the joint floor `hJ`), canonical-run sample avoidance, the
fingerprint surfaces `hfold`/`hgood`, the layout identities, the committed-quotient identity, and
the batch `pbatch` itself (an `x₄`-rewind output; producing it from bare acceptance is the open
composition surface recorded in `Soundness.Multiopen.Decode`). -/
noncomputable def orchard_verifier_sound_vesta_budgeted
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
    {a₀ : Fin (2 ^ shape.k) → Fp}
    (pbatch : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
        (chRecord ν (fun _ => 0)))
      (x4BatchEvals vk p.proof.1 (chRecord ν (fun _ => 0))) a₀ (p.multiU ν) (p.multiBlind ν))
    (hξcur : pbatch.batchChallenge pbatch.current
      = (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x4)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (adviceMem : ∀ j : Fin numAdvice,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j
      < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp) (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp)
    (hpoly : Polynomial Fp) (deg : ℕ)
    (hlen : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0))
      → 0 < (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)))))
    (hacc0 : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
      (chRecord ν (fun _ => 0)))
    (pp : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).adviceEvals pp)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn ((p.proof.1 : ProofString shape Fp VestaG).instanceEvals pp)).length)
    (b₂f : Fp → Fin (2 ^ shape.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) →
      (((deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) i).length - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        + (((deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) - 1 : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + ((max (2 ^ shape.k)
                (deployedAllPts vk p.proof.1 (chRecord ν (fun _ => 0))).card
              + (deployedAllPts vk p.proof.1 (chRecord ν (fun _ => 0))).card : ℕ) : ℝ≥0∞)
            / Fintype.card Fp
          + (deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)) : ℝ≥0∞)
            / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) b₂f))
    (havoid : ∀ (ξv ζv χv : Fp),
      OpenedX3Accept (ursOfAugmentedBasis shape.k basis) rfl vk
        ((canonicalX2Run (ursOfAugmentedBasis shape.k basis) rfl vk
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv)
            (b₂f ξv) ζv).spliced
          ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1))
        ((canonicalX2Run (ursOfAugmentedBasis shape.k basis) rfl vk
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
            ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
              (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv)
            (b₂f ξv) ζv).challenges
          ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv) ζv)
        (evalVector shape.k χv) χv →
      ∀ k', χv ∉ deployedSetPts vk
        ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
          (chRecord ν (fun _ => 0)) ξv).spliced p.proof.1)
        ((canonicalX1Run (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
          (chRecord ν (fun _ => 0)) ξv).challenges (chRecord ν (fun _ => 0)) ξv) k')
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval
          (fun n => (fixedCols n).eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x)
          (deployedClaimedFeed vk p.proof.1 (chRecord ν (fun _ => 0)) adviceSet adviceMem
            vk.adviceQueryLayout)
          (deployedClaimedFeed vk p.proof.1 (chRecord ν (fun _ => 0)) instanceSet instanceMem
            vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0
        = hpoly.eval (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x
          * ((chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
              (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl vk
            p.proof.1 (chRecord ν (fun _ => 0)) pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
              (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval
          (chRecord ν (fun _ => 0) : Challenges shape.k Fp).x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (adviceSet j)).getD
          (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol pp (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) (instanceSet j)).getD
          (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol pp (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ)
        (hhSet : hSet < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0)))
        (hMem : Fin (deployedSetQueries vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob (ursOfAugmentedBasis shape.k basis) rfl
          vk p.proof.1 (chRecord ν (fun _ => 0)) pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk p.proof.1 (chRecord ν (fun _ => 0)) hSet).getD (hMem : ℕ)
          CommitmentId.randomPoly = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ (a : Fin (2 ^ shape.k) → Fp)
        (bo : OpenedBatchOpenings (ursOfAugmentedBasis shape.k basis) (evalVector shape.k (ν 7))
          (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)))
          (x4BatchEvals vk p.proof.1 (chRecord ν (fun _ => 0))) a (p.multiU ν) (p.multiBlind ν))
        (md : ∀ i (hi : i < deployedX4PairCount vk p.proof.1 (chRecord ν (fun _ => 0))),
          OpenedMemberDecode (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0)) bo i hi),
      SnarkRelation (ursOfAugmentedBasis shape.k basis)
        (deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk p.proof.1
            (chRecord ν (fun _ => 0))
          - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
          - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w)
        (evalVector shape.k (ν 7)) (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)))
        (circuitSatViaGates fixedCols
          (fun _ => rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
            coeffsToPoly ((md (adviceSet j) (hadviceSet j)).cols (adviceMem j))))
          (fun _ => rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
            coeffsToPoly ((md (instanceSet j) (hinstanceSet j)).cols (instanceMem j))))
          y gates hpoly deg) a → S) :
    (S ∨ HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)
      ⊕' AlgebraicRelationWitness (F := Fp) basis :=
  member_snark_of_instance_budgeted p ν cert hz hvalid pbatch hξcur adviceSet hadviceSet adviceMem
    instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg hlen hprob1 hacc0 pp
    hadvLen hinstLen b₂f hJ havoid hfold hgood hadviceLayout hinstanceLayout hquotCommitted
    (S := S)
    (fun a hmem => hencodes a hmem.batchOpenings hmem.memberDecode
      (snarkRelation_of_memberColumns hmem))

/-! ## The clean-opening extraction hand-off

`hasCleanOpening` (`Forking.Adversary.Algebraic`) packages an instance the computed family
produced together with its clean-opening branch. `instanceAttempt_provenance`
(`Soundness.Compose67`) exposes the `AlgebraicWfProof` behind that instance, and the budgeted
witness tie above turns the opening into the member SNARK relation given the multiopen rewind
data. The two theorems below chain these: the extraction *logic* of the conditional
knowledge-error bound's `hExtract` hypothesis is discharged, leaving a data-supply obligation
that receives the concrete proof, oracle scalars, and opening.

What remains for a fully unconditional bound is the *coupling*: the supply's inputs — the batch
`pbatch` and the accept floors `hprob1`/`hJ` — are outputs of the multiopen challenge draw, which
the family's coin space does not range over. `deployed_member_budget`
(`Soundness.Multiopen.BudgetedExtraction`) prices exactly that draw's failure event at
`t₁ + (t₂ + t₃ + t₄)`; joining it to the family bound needs a product space over
(oracle coins × the four fresh challenges) and a measure statement relating the two draws — a
genuine probabilistic modeling step, not a composition of what exists. -/

/-- A clean opening's provenance: the produced instance is a `deployedAlgebraicInstanceOfCert` of
a concrete `AlgebraicWfProof`, oracle scalars, and certificate, and its run took the clean-opening
branch. `hasCleanOpening` unpacked through `instanceAttempt_provenance`. -/
theorem cleanOpening_provenance (family : ComputedAlgebraicFSFamily shape)
    (coins : family.Coins) (h : family.hasCleanOpening basis coins) :
    ∃ (p : AlgebraicWfProof basis (family.vk basis)) (ν : Fin 11 → Fp)
      (cert : AlgebraicDForkCert (F := Fp)
        (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
      (hz : ν 10 ≠ 0)
      (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
        (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w (ν 10)
        (commit (ursOfAugmentedBasis shape.k basis)
            (adjustedWitness (p.aMulti ν) p.s
              (multiopenValue (family.vk basis) p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
          (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
          (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
        cert.toDForkCert),
      (family.instanceAttempt basis coins).output
          = some (deployedAlgebraicInstanceOfCert p ν cert hz hvalid) ∧
      ∃ o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening,
        (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).run = PSum.inl o := by
  obtain ⟨x, hout, o, hrun⟩ := h
  obtain ⟨p, ν, cert, hz, hvalid, hx⟩ := instanceAttempt_provenance family coins hout
  subst hx
  exact ⟨p, ν, cert, hz, hvalid, hout, o, hrun⟩

open scoped ENNReal in
open ComputedAlgebraicFSFamily in
/-- **The knowledge-error bound with the extraction logic discharged.**
`snarkExtraction_prob_le_of_generatorRO_textbookDL` (`Soundness.Compose67`) with its `hExtract`
hypothesis reduced through the clean-opening provenance: the supply obligation `hSupply` receives
the concrete `AlgebraicWfProof`, oracle scalars, certificate, and clean opening behind each
produced instance — exactly the inputs of the budgeted witness tie
(`member_relation_or_dlr_of_instance_budgeted`), which concludes the extraction given the
multiopen rewind data at that instance's base. The bound is the clean-opening bound
`(Q+k)·3/|Fp| + (Q+1)/|Fp| + |basis|·ε`, verbatim. The residual for a fully unconditional bound
is the coin–challenge coupling recorded in this section's note. -/
theorem snarkExtraction_prob_le_of_generatorRO_textbookDL_budgeted {shape : Shape}
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T) (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (extracted : (AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins → Prop)
    (hSupply : ∀ (bs : AugmentedIndex (2 ^ shape.k) → VestaG) (coins : family.Coins)
      (p : AlgebraicWfProof bs (family.vk bs)) (ν : Fin 11 → Fp)
      (cert : AlgebraicDForkCert (F := Fp)
        (augmentedBasis (ursOfAugmentedBasis shape.k bs).g
          (ursOfAugmentedBasis shape.k bs).u (ursOfAugmentedBasis shape.k bs).w) shape.k)
      (hz : ν 10 ≠ 0)
      (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k bs).g
        (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k bs).u
        (ursOfAugmentedBasis shape.k bs).w (ν 10)
        (commit (ursOfAugmentedBasis shape.k bs)
            (adjustedWitness (p.aMulti ν) p.s
              (multiopenValue (family.vk bs) p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
          (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k bs).u +
          (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k bs).w)
        cert.toDForkCert),
      (family.instanceAttempt bs coins).output
          = some (deployedAlgebraicInstanceOfCert p ν cert hz hvalid) →
      ∀ o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening,
        (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).run = PSum.inl o →
        extracted bs coins) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.snarkExtractionFailureEvent extracted)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound :=
  snarkExtraction_prob_le_of_generatorRO_textbookDL B hB query hquery family hDL extracted
    (fun bs coins h => by
      obtain ⟨p, ν, cert, hz, hvalid, hout, o, hrun⟩ := cleanOpening_provenance family coins h
      exact hSupply bs coins p ν cert hz hvalid hout o hrun)

/-! ## The `hfold`/`hgood` surfaces: derivation core and price

The two gate-check surfaces of the budgeted capstone decompose further; neither is an opaque
assumption.

* **`hfold` is a value binding, not a check the verifier skips.** The deployed verifier *computes*
  the expected quotient evaluation from the full claimed-evaluation expression list — halo2's
  `expected_h_eval`: `expectedHEval exprs ch.y (ch.x ^ vk.n) = fold(exprs) · (ch.x^vk.n − 1)⁻¹`
  over `exprs = allExpressions` (gates ++ permutation ++ lookup, all sub-proofs) — and pins the
  vanishing-`h` opening query at exactly that value (`vanishing_query_mem_assembleQueries`). The
  member node binding at that slot (`hquotCommitted` routes `hpoly` there) therefore binds
  `hpoly.eval ch.x` to `expectedHEval …`, and `hfold_of_expectedHEval_binding` turns that binding
  into the capstone's `hfold` equation given two side conditions: `ch.x ^ vk.n ≠ 1` (root-of-unity
  avoidance, a `vk.n / p`-priced squeeze exclusion), and the *sharpened* fingerprint `hfp` — the
  parameter gate fold equals the deployed `allExpressions` fold, the zcash/ironwood#11/#13 surface
  stated as one explicit equation. The grouping's eval faithfulness at the vanishing slot is now
  proven here (`vanishing_slot_routed`): `constructIntermediateSets` routes the (unique — no other
  query carries `CommitmentId.vanishingH`) vanishing query to a member whose point list is `[ch.x]`
  and whose eval list is `[expectedHEval …]`, so the routed `getD` value *is* `expectedHEval …`.
  `hfold_of_vanishing_slot_binding` reads `hbind` through that route. Both of its remaining inputs
  are now settled rather than open: `hxn` is a consequence of acceptance (`deployedAccepts_xn_ne_one`
  — `assemble?` rejects at `xⁿ = 1`), and `hfp` is the *fixed* zcash/ironwood#11/#13 fingerprint,
  which `hfp_of_expressions_eq` reduces to a per-instance list equality. `hbind` itself is supplied
  by `hfold_of_member_budget` from the good branch of `deployed_member_budget`, and
  `orchard_verifier_vesta_member_constraint_budgeted_hfold_derived` runs the whole composition
  through the budgeted capstone.

* **`hgood`'s failure is Schwartz–Zippel-priced.** For the capstone's difference polynomial the
  failure event of the exact `hgood` implication has uniform-squeeze measure at most
  `max (deg numerator) (deg hpoly + deg) / p` (`hgood_failure_priced`), and every challenge
  outside the bad set satisfies the implication verbatim (`hgood_of_good_challenge`). The two
  hooks a probabilistic assembly must supply are the same random-oracle coupling the joint accept
  floor carries: that `ch.x` is one fresh uniform squeeze, and that the difference polynomial is
  pinned before `x` is squeezed (`adviceCommitments_mem_preXTranscript` /
  `hPieces_mem_preXTranscript`, `Soundness.Forking.Ordering`). -/

/-- The vanishing-`h` opening query is a deployed opening query with its claimed evaluation
*computed* by the verifier: slot identity `vanishingH`, opening point `ch.x`, and evaluation
`expectedHEval` of the full claimed-evaluation expression list — the fact `hfold`'s derivation
consumes. (halo2 `plonk/verifier.rs`: the verifier recomputes `expected_h_eval` and queries the
`h` commitment at it; `assembleQueries` appends `vanishingQueries` last, so the query is the
head of that suffix.) -/
theorem vanishing_query_mem_assembleQueries {G : Type*} [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    ∃ q ∈ assembleQueries vk ps ch,
      q.commId = CommitmentId.vanishingH ∧ q.point = ch.x ∧
      q.eval = expectedHEval
        (allExpressions vk ps ch
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
        ch.y (ch.x ^ vk.n) := by
  refine ⟨{ point := ch.x,
            commitment := .msm (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces)),
            eval := expectedHEval
              (allExpressions vk ps ch
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
              ch.y (ch.x ^ vk.n),
            commId := .vanishingH }, ?_, rfl, rfl, rfl⟩
  simp only [assembleQueries, vanishingQueries]
  exact List.mem_append.mpr (Or.inr (List.mem_cons_self))

/-- **The vanishing slot's routed member, carrying the verifier-computed evaluation.** Composing
three in-tree facts: `vanishing_query_mem_assembleQueries` (the vanishing query is in the flat query
list, at point `ch.x`, with evaluation `expectedHEval …`), `assembleQueries_vanishingH_unique`
(no other query carries the `vanishingH` slot), and `constructIntermediateSets_unique_comm_routed`
(a unique-slot query is routed to a single point set, whose point list is the singleton of its
opening point and whose member records that slot and the singleton evaluation list). So the grouping
routes the vanishing query to member `m` of point set `i`, `points i = [ch.x]`, the member's recorded
identity is `vanishingH`, and its recorded evaluation list is `[expectedHEval …]`.

This is the grouping's eval faithfulness at the vanishing slot — the single bookkeeping fact the
`hfold` derivation was missing, so `hfold_of_vanishing_slot_binding` below now reads the routed value
rather than assuming it. -/
theorem vanishing_slot_routed {G : Type*} [AddCommGroup G] [Module Fp G] [DecidableEq G]
    [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    ∃ i, i < (constructIntermediateSets (assembleQueries vk ps ch)).sets.length ∧
      (constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [] = [ch.x] ∧
      ∃ m, m < (deployedSetQueries vk ps ch i).length ∧
        (∀ c₀, (deployedSetCommIds vk ps ch i).getD m c₀ = CommitmentId.vanishingH) ∧
        ∀ d₀, ((deployedSetQueries vk ps ch i).getD m d₀).2
          = [expectedHEval
              (allExpressions vk ps ch
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
                (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
              ch.y (ch.x ^ vk.n)] := by
  obtain ⟨q, hq, hid, hpt, hev⟩ := vanishing_query_mem_assembleQueries vk ps ch
  have huniq : ∀ q' ∈ assembleQueries vk ps ch, q'.commId = q.commId → q' = q := by
    intro q' hq' hq'id
    exact assembleQueries_vanishingH_unique vk ps ch hq' hq (hq'id.trans hid) hid
  obtain ⟨i, hi, hpts, m, hm, hids, hsets⟩ :=
    constructIntermediateSets_unique_comm_routed (assembleQueries vk ps ch) hq huniq
  refine ⟨i, hi, by rw [hpts, hpt], m, ?_, ?_, ?_⟩
  · simp only [deployedSetQueries, constructIntermediateSets_zip_sets_getD]
    exact hm
  · intro c₀
    simp only [deployedSetCommIds]
    rw [hids c₀]
    exact hid
  · intro d₀
    simp only [deployedSetQueries, constructIntermediateSets_zip_sets_getD]
    rw [hsets d₀, hev]

/-- **The `hfold` derivation core.** The capstone's gate-fold equation from the vanishing-slot
value binding: if the extracted quotient's evaluation at `ch.x` is the verifier-computed
`expectedHEval` (`hbind` — supplied by the member node binding at the `hquotCommitted` slot),
the squeeze avoids the `deg`-th roots of unity (`hxn`), and the parameter gate fold equals the
deployed expression fold (`hfp` — the zcash/ironwood#11/#13 fingerprint, sharpened to one
equation), then `hfold` holds verbatim. Pure field algebra: `expectedHEval` clears its
`(x^deg − 1)⁻¹` against `hxn`. -/
theorem hfold_of_expectedHEval_binding {ng : ℕ} (gates : Fin ng → Expr Fp)
    (fixedClaimed adviceClaimed instanceClaimed : ℕ → Fp) (y x : Fp)
    (hpoly : Polynomial Fp) (deg : ℕ) (exprs : List Fp)
    (hxn : x ^ deg ≠ 1)
    (hbind : hpoly.eval x = expectedHEval exprs y (x ^ deg))
    (hfp : (List.ofFn (fun i : Fin ng =>
          (gates i).eval fixedClaimed adviceClaimed instanceClaimed)).foldl
            (fun acc v => acc * y + v) 0
        = exprs.foldl (fun acc v => acc * y + v) 0) :
    (List.ofFn (fun i : Fin ng =>
        (gates i).eval fixedClaimed adviceClaimed instanceClaimed)).foldl
          (fun acc v => acc * y + v) 0
      = hpoly.eval x * (x ^ deg - 1) := by
  rw [hfp, hbind, expectedHEval, mul_assoc,
    inv_mul_cancel₀ (sub_ne_zero.mpr hxn), mul_one]

/-- **The root-of-unity exclusion is a consequence of acceptance, not a priced assumption.**
`assemble?` returns `none` at `ch.x ^ vk.n = 1` — the deployed verifier panics there on
`(xⁿ − 1).invert().unwrap()` (halo2 `vanishing/verifier.rs`), which the model renders as a rejection
— and `DeployedAccepts` is `False` on the `none` branch. So an accepting transcript already has
`ch.x ^ vk.n ≠ 1`, and `hfold`'s side condition `hxn` needs no separate `vk.n / p` squeeze budget. -/
theorem deployedAccepts_xn_ne_one {G : Type*} [AddCommGroup G] [Module Fp G] [DecidableEq G]
    [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk ps ch) : ch.x ^ vk.n ≠ 1 := by
  intro hx
  have hnone : assemble? vk ps ch = none := by
    unfold assemble?
    by_cases hwf : proofStringWellFormed ps = true
    · rw [if_pos hwf, if_pos hx]
    · rw [if_neg hwf]
  unfold DeployedAccepts at hacc
  rw [hnone] at hacc
  exact hacc

/-- **The `hfold` derivation, reading the routed vanishing-slot value.**
`hfold_of_expectedHEval_binding` with its `hbind` premise supplied through the grouping: the member
node binding at the `hquotCommitted` slot pins `hpoly.eval ch.x` to the value the grouping recorded
for the vanishing member, and `vanishing_slot_routed` says that value *is* the verifier-computed
`expectedHEval`. The two standing side conditions are unchanged and explicit: root-of-unity
avoidance `hxn` (a `vk.n / p`-priced squeeze exclusion) and the sharpened fingerprint `hfp`
(zcash/ironwood#11/#13). -/
theorem hfold_of_vanishing_slot_binding {G : Type*} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {ng : ℕ} (gates : Fin ng → Expr Fp)
    (fixedClaimed adviceClaimed instanceClaimed : ℕ → Fp)
    (hpoly : Polynomial Fp) (i m : ℕ)
    (hrouted : ∀ d₀, ((deployedSetQueries vk ps ch i).getD m d₀).2
      = [expectedHEval
          (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
          ch.y (ch.x ^ vk.n)])
    (hbind : hpoly.eval ch.x
      = ((deployedSetQueries vk ps ch i).getD m (CommitmentRef.point 0, [])).2.getD 0 0)
    (hxn : ch.x ^ vk.n ≠ 1)
    (hfp : (List.ofFn (fun j : Fin ng =>
          (gates j).eval fixedClaimed adviceClaimed instanceClaimed)).foldl
            (fun acc v => acc * ch.y + v) 0
        = (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2).foldl
            (fun acc v => acc * ch.y + v) 0) :
    (List.ofFn (fun j : Fin ng =>
        (gates j).eval fixedClaimed adviceClaimed instanceClaimed)).foldl
          (fun acc v => acc * ch.y + v) 0
      = hpoly.eval ch.x * (ch.x ^ vk.n - 1) := by
  refine hfold_of_expectedHEval_binding gates fixedClaimed adviceClaimed instanceClaimed
    ch.y ch.x hpoly vk.n _ hxn ?_ hfp
  rw [hbind, hrouted (CommitmentRef.point 0, [])]
  rfl

set_option maxHeartbeats 1000000 in
/-- **`hfold` from the budget's good branch — the terminal supply of `hbind`.**
`deployed_member_budget` (`Soundness.Multiopen.BudgetedExtraction`) ends in a disjunction: either
the joint accept measure sits inside the four-threshold budget, or *every* decoded member column
takes its claimed evaluation at every point of its set (or a `(g, u, w)` relation is at hand). This
theorem consumes the second branch — passed as `hbindAll`, the shape that branch produces — at the
vanishing slot located by `vanishing_slot_routed`, and concludes the capstone's `hfold` equation.

Everything the derivation needed is now supplied rather than assumed: the routed point list is the
singleton `[ch.x]` (`hroute`), so the binding at index `0` is a binding at `ch.x`; the routed
evaluation is the verifier-computed `expectedHEval` (`hevals`); the root-of-unity exclusion comes
from acceptance (`deployedAccepts_xn_ne_one`). The one input that remains is `hfp`, the sharpened
zcash/ironwood#11/#13 fingerprint — the gate fold equals the deployed `allExpressions` fold.

`hquot` is `hquotCommitted` at the *routed* slot: the caller must exhibit the extracted quotient as
the column of the member `vanishing_slot_routed` names, rather than at an arbitrary member recording
the `vanishingH` identity. -/
theorem hfold_of_member_budget {G : Type*} [AddCommGroup G] [Module Fp G] [DecidableEq G]
    [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {ng : ℕ} (gates : Fin ng → Expr Fp)
    (fixedClaimed adviceClaimed instanceClaimed : ℕ → Fp)
    (hpoly : Polynomial Fp) (i m : ℕ) (hm : m < (deployedSetQueries vk ps ch i).length)
    (colPoly : Fin (deployedSetQueries vk ps ch i).length → Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries vk ps ch)).points.getD i []).length)
        (m₀ : Fin (deployedSetQueries vk ps ch i).length),
        (colPoly m₀).eval
            (((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [])[idx])
          = ((deployedSetQueries vk ps ch i).getD (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [] = [ch.x])
    (hevals : ∀ d₀, ((deployedSetQueries vk ps ch i).getD m d₀).2
      = [expectedHEval
          (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
          ch.y (ch.x ^ vk.n)])
    (hacc : DeployedAccepts urs hk vk ps ch)
    (hfp : (List.ofFn (fun j : Fin ng =>
          (gates j).eval fixedClaimed adviceClaimed instanceClaimed)).foldl
            (fun acc v => acc * ch.y + v) 0
        = (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2).foldl
            (fun acc v => acc * ch.y + v) 0) :
    (List.ofFn (fun j : Fin ng =>
        (gates j).eval fixedClaimed adviceClaimed instanceClaimed)).foldl
          (fun acc v => acc * ch.y + v) 0
      = hpoly.eval ch.x * (ch.x ^ vk.n - 1)
    ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hlt : 0 < ((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i []).length := by
    rw [hroute]; simp
  rcases hbindAll ⟨0, hlt⟩ ⟨m, hm⟩ with hb | hrel
  · refine Or.inl (hfold_of_vanishing_slot_binding vk ps ch gates fixedClaimed adviceClaimed
      instanceClaimed hpoly i m hevals ?_ (deployedAccepts_xn_ne_one urs hk vk ps ch hacc) hfp)
    have hx : ((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [])[(0 : ℕ)]'hlt
        = ch.x := by
      rw [List.getElem_of_eq hroute hlt]
      simp
    rw [hquot, ← hx]
    exact hb
  · exact Or.inr hrel

open Polynomial in
open scoped ENNReal in
/-- **The `hgood` failure event, Schwartz–Zippel-priced.** The set of squeezes at which the
budgeted capstone's exact `hgood` implication *fails* — the gate identity fails as polynomials
yet its difference vanishes at the squeeze — is the difference's root set, of uniform measure at
most `max (deg numerator) (deg hq + n) / p` (the caller-computable budget of
`szBadSet_quotient_card_le`). The assembly hooks (that `ch.x` is one fresh uniform squeeze and
the difference is pinned pre-squeeze) are recorded in this section's note. -/
theorem hgood_failure_priced (numerator hq : Polynomial Fp) (n : ℕ) :
    uniformChallenge.toOuterMeasure
        {x : Fp | ¬(numerator ≠ hq * (X ^ n - 1) →
          (numerator - hq * (X ^ n - 1)).eval x ≠ 0)}
      ≤ ((max numerator.natDegree (hq.natDegree + n) : ℕ) : ℝ≥0∞)
        / (Fintype.card Fp : ℝ≥0∞) := by
  have hset : {x : Fp | ¬(numerator ≠ hq * (X ^ n - 1) →
        (numerator - hq * (X ^ n - 1)).eval x ≠ 0)}
      = ↑(szBadSet (numerator - hq * (X ^ n - 1))) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_szBadSet, Classical.not_imp, not_not,
      sub_ne_zero]
  rw [hset, uniformChallenge_badSet]
  gcongr
  exact_mod_cast szBadSet_quotient_card_le numerator hq n

open Polynomial in
/-- Any squeeze outside the priced bad set satisfies the budgeted capstone's `hgood` implication
verbatim (`not_mem_szBadSet` at the quotient difference). -/
theorem hgood_of_good_challenge (numerator hq : Polynomial Fp) (n : ℕ) {x : Fp}
    (hx : x ∉ szBadSet (numerator - hq * (X ^ n - 1))) :
    numerator ≠ hq * (X ^ n - 1) → (numerator - hq * (X ^ n - 1)).eval x ≠ 0 :=
  fun hne => (not_mem_szBadSet.mp hx) (sub_ne_zero.mpr hne)

/-- **The fold fingerprint reduces to list equality.** `hfold`'s remaining premise `hfp` compares
two `y`-power folds: the parameter gates' evaluated list against the deployed `allExpressions`. The
fold is a function of the list, so the premise holds as soon as the two *lists* agree — there is
nothing analytic left in it.

The zcash/ironwood#11/#13 fingerprint is fixed, so for any given circuit this is a syntactic check
of the gate list against `allExpressions vk ps ch …` at that instance, not an open obligation: with
`gates` instantiated at the deployed expressions, `hfp` is `rfl`. Callers that already have the list
identity should go through this lemma rather than restating the fold. -/
theorem hfp_of_expressions_eq {ng : ℕ} (gates : Fin ng → Expr Fp)
    (fixedClaimed adviceClaimed instanceClaimed : ℕ → Fp) (y : Fp) (exprs : List Fp)
    (h : List.ofFn (fun i : Fin ng =>
        (gates i).eval fixedClaimed adviceClaimed instanceClaimed) = exprs) :
    (List.ofFn (fun i : Fin ng =>
        (gates i).eval fixedClaimed adviceClaimed instanceClaimed)).foldl
          (fun acc v => acc * y + v) 0
      = exprs.foldl (fun acc v => acc * y + v) 0 := by
  rw [h]

open Polynomial in
open scoped ENNReal in
open Classical in
set_option maxHeartbeats 4000000 in
/-- **The budgeted member capstone with `hfold` derived — the terminal integration.**
`orchard_verifier_vesta_member_constraint_budgeted` at the deployed instantiation (`y := ch.y`,
`deg := vk.n`, forced by `hy`/`hdeg`), with its `hfold` premise supplied internally by
`hfold_of_member_budget` rather than assumed. The pieces fit without adaptation: that lemma is
generic in the three claimed-evaluation feeds, so it instantiates directly at the capstone's
`fun n => (fixedCols n).eval ch.x` and the two `deployedClaimedFeed`s, and its conclusion is the
capstone's `hfold` slot verbatim. Its relation branch merges into the capstone's own
`HasNontrivialRelation` disjunct, so nothing is lost on that side.

What the caller now supplies in place of `hfold` is the routed vanishing-slot data
(`vanishing_slot_routed` gives `hroute` and `hevals`), the budget's good branch (`hbindAll`, the
shape `deployed_member_budget` produces), the quotient at that routed member (`hquot`), and the
sharpened zcash/ironwood#11/#13 fingerprint (`hfp`). The root-of-unity exclusion is not among them:
`deployedAccepts_xn_ne_one` reads it off the capstone's own `hacc0`.

`hgood` remains a premise — its failure is priced (`hgood_failure_priced`), but the pricing needs
the random-oracle coupling that `Soundness.Compose67Prefixes` records as the standing gap, so it
is not discharged here. -/
theorem orchard_verifier_vesta_member_constraint_budgeted_hfold_derived {shape : Shape}
    (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk ps ch
      → 0 < (deployedSetQueries vk ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk ps ch →
      (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk ps ch)))
    (hacc0 : DeployedAccepts urs hk vk ps ch)
    (p : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.adviceEvals p)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.instanceEvals p)).length)
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk ps ch →
      (((deployedSetQueries vk ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk ps ch).card
              + (deployedAllPts vk ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk ps ch b₂f))
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
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval ch.x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk ps ch)
        (hMem : Fin (deployedSetQueries vk ps ch hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk ps ch pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns urs hk vk ps ch
        (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk ps ch) p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg pU pW a → S)
    (hy : y = ch.y) (hdeg : deg = vk.n)
    (i m : ℕ) (hm : m < (deployedSetQueries vk ps ch i).length)
    (colPoly : Fin (deployedSetQueries vk ps ch i).length → Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries vk ps ch)).points.getD i []).length)
        (m₀ : Fin (deployedSetQueries vk ps ch i).length),
        (colPoly m₀).eval
            (((constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [])[idx])
          = ((deployedSetQueries vk ps ch i).getD (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets (assembleQueries vk ps ch)).points.getD i [] = [ch.x])
    (hevals : ∀ d₀, ((deployedSetQueries vk ps ch i).getD m d₀).2
      = [expectedHEval
          (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
          ch.y (ch.x ^ vk.n)])
    (hfp : (List.ofFn (fun j : Fin ng =>
          (gates j).eval (fun n => (fixedCols n).eval ch.x)
            (deployedClaimedFeed vk ps ch adviceSet adviceMem vk.adviceQueryLayout)
            (deployedClaimedFeed vk ps ch instanceSet instanceMem vk.instanceQueryLayout))).foldl
            (fun acc v => acc * ch.y + v) 0
        = (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2).foldl
            (fun acc v => acc * ch.y + v) 0) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  subst hy
  subst hdeg
  rcases hfold_of_member_budget urs hk vk ps ch gates
      (fun n => (fixedCols n).eval ch.x)
      (deployedClaimedFeed vk ps ch adviceSet adviceMem vk.adviceQueryLayout)
      (deployedClaimedFeed vk ps ch instanceSet instanceMem vk.instanceQueryLayout)
      hpoly i m hm colPoly hbindAll hquot hroute hevals hacc0 hfp with hfold | hrel
  · exact orchard_verifier_vesta_member_constraint_budgeted urs hk vk ps ch pU pW adviceSet
      hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols ch.y gates hpoly vk.n
      pbatch hξcur hlen hprob1 hacc0 p hadvLen hinstLen b₂f hJ havoid hfold hgood
      hadviceLayout hinstanceLayout hquotCommitted hencodes
  · exact Or.inr hrel

end Zcash.Snark
