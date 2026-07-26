import Zcash.Snark.Soundness.Deployed.Ipa
import Zcash.Snark.Soundness.Deployed.Binding

/-!
# Peeling the deployed IPA onto the clean recursive IPA, as a binding reduction

`Zcash.Snark.Soundness.Deployed.Ipa` modelled halo2's deployed IPA — the clean recursion plus the
`U`/`W` apparatus (`S`/`ξ` stays in the verifier equation, not the tree) — as `DeployedIpaAcceptV`.
This module peels that apparatus off onto the clean `IpaAcceptV`, so the deployed opening reduces
to `ipa_soundV`, with commitment binding expressed per the breaks-as-computed-data convention: a
deployed tree that does *not* peel cleanly computes a nontrivial discrete-log relation among the
augmented generators.

* `decIpaAcceptV` — the clean accept is decidable, so the peel can locate a failing subtree.
* `NontrivialRelation.ofFoldedGens` — a relation among the folded generators lifts to one among
  the originals, so the per-round peel reports its relation against the fixed URS generators `g`.
* `NontrivialRelation.ofLeafPeel` — a combined leaf equation whose clean leaf checks fail
  computes a relation among `(g, U, W)` (via `ofCombinationCollision`).
* `NontrivialRelation.ofDeployedTree` — recurse the peel over the tree: an accepting deployed
  tree whose projection is *not* cleanly accepted computes a nontrivial relation among
  `(g, U, W)`.

The clean case is the hypothesis (`¬ IpaAcceptV …` is what the reduction consumes), so the peel
is a plain computable `def` producing the break — see `The reduction form` in
`Zcash.Snark.Soundness.Main`.
-/

namespace Zcash.Snark

open Zcash.Arithmetic

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The clean IPA accept is decidable (given decidable equality on scalars and points): it is a
finite conjunction of (in)equalities over the tree. This is what lets the peel *locate* a failing
subtree computably. -/
instance decIpaAcceptV [DecidableEq F] [DecidableEq G] :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (P : G) → (v : F) →
      (t : IpaTreeV F G d) → Decidable (IpaAcceptV g b P v t)
  | 0, g, b, P, v, .leaf c =>
      inferInstanceAs (Decidable (P = commitGen g (fun _ => c) ∧ v = commitGen b (fun _ => c)))
  | _ + 1, g, b, P, v, .node L R Lv Rv u₁ u₂ u₃ t₁ t₂ t₃ =>
      letI := decIpaAcceptV (foldGens g u₁) (foldGens b u₁)
        (P + u₁⁻¹ • L + u₁ • R) (v + u₁⁻¹ • Lv + u₁ • Rv) t₁
      letI := decIpaAcceptV (foldGens g u₂) (foldGens b u₂)
        (P + u₂⁻¹ • L + u₂ • R) (v + u₂⁻¹ • Lv + u₂ • Rv) t₂
      letI := decIpaAcceptV (foldGens g u₃) (foldGens b u₃)
        (P + u₃⁻¹ • L + u₃ • R) (v + u₃⁻¹ • Lv + u₃ • Rv) t₃
      inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A relation among the folded generators lifts to one among the originals, as a computable map:
with `foldGens g u = loHalf g + u⁻¹ • hiHalf g`, the coefficients `append a (u⁻¹ • a)` carry the
relation to `g`, staying nontrivial because `loHalf (append a _) = a`. So the per-round peel can
always report its relation against the fixed `g`. -/
def NontrivialRelation.ofFoldedGens {k : ℕ} {g : Fin (2 ^ (k + 1)) → G} {U W : G} (u : F)
    (r : NontrivialRelation (F := F) (foldGens g u) U W) : NontrivialRelation (F := F) g U W where
  a := append r.a (u⁻¹ • r.a)
  α := r.α
  β := r.β
  nontrivial := by
    rcases r.nontrivial with ha | hαβ
    · refine Or.inl (fun hc => ha ?_)
      have h0 : loHalf (append r.a (u⁻¹ • r.a)) = r.a := loHalf_append r.a (u⁻¹ • r.a)
      rw [hc] at h0
      simpa [loHalf] using h0.symm
    · exact Or.inr hαβ
  relation := by
    show commitGen g (append r.a (u⁻¹ • r.a)) + r.α • U + r.β • W = 0
    have hcg : commitGen g (append r.a (u⁻¹ • r.a)) = commitGen (foldGens g u) r.a := by
      unfold foldGens
      rw [commitGen_append, commitGen_add_gen, commitGen_smul_gen, commitGen_smul_left]
    rw [hcg]; exact r.relation

/-- One deployed leaf peels, as a computed relation. If the reformulated leaf relation
`⟨aP, g⟩ + [z·v]U + [blind]W = [c]g₀ + [z·c·b₀]U + [f]W` (value carried on `U` via `z`; halo2's
literal check instead uses `g₀`/`[ξ]S`, see `DeployedIpaVerifierEq`) holds but the clean leaf
checks `⟨aP, g⟩ = [c]g₀` and `v = c·b₀` do not both, the coordinate differences are a nontrivial
relation among `(g, U, W)` — `ofCombinationCollision`, with `z ≠ 0` cancelling the `U`-side. -/
def NontrivialRelation.ofLeafPeel [DecidableEq F] {n : ℕ} {g : Fin n → G} {b : Fin n → F}
    {U W : G} {z : F} {aP : Fin n → F} {v blind c f : F} (hz : z ≠ 0)
    (e : commitGen g aP + (z * v) • U + blind • W
       = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W)
    (hne : ¬(commitGen g aP = commitGen g (fun _ => c) ∧ v = commitGen b (fun _ => c))) :
    NontrivialRelation (F := F) g U W :=
  NontrivialRelation.ofCombinationCollision e
    (fun h => hne ⟨congrArg (commitGen g) h.1, mul_left_cancel₀ hz h.2.1⟩)

/-- **The deployed peel, as a computed relation.** An accepting deployed tree whose projection is
*not* cleanly accepted computes a nontrivial relation among `(g, U, W)`. By recursion on the
tree: a failing leaf peels via `ofLeafPeel`; at a node, decidability of the clean accept
(`decIpaAcceptV`) locates a failing subtree, whose relation (against `foldGens g uᵢ`) lifts to
`g` (`ofFoldedGens`) — if all three subtrees peel cleanly, the clean node accept holds,
contradicting the hypothesis. -/
def NontrivialRelation.ofDeployedTree [DecidableEq F] [DecidableEq G] {U W : G} {z : F}
    (hz : z ≠ 0) :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (P : G) → (v blind : F) →
      (t : DeployedIpaTreeV F G d) → DeployedIpaAcceptV g b U W z P v blind t →
      ¬ IpaAcceptV g b P v (projTree t) → NontrivialRelation (F := F) g U W
  | 0, _, _, _, _, _, .leaf _ _ _, h, hne =>
      NontrivialRelation.ofLeafPeel hz h.2
        (fun hcl => hne ⟨h.1.trans hcl.1, hcl.2⟩)
  | _ + 1, g, b, P, v, _, .node L R Lv Rv _ _ u₁ u₂ u₃ t₁ t₂ t₃, h, hne =>
      if hc₁ : IpaAcceptV (foldGens g u₁) (foldGens b u₁)
          (P + u₁⁻¹ • L + u₁ • R) (v + u₁⁻¹ • Lv + u₁ • Rv) (projTree t₁) then
        if hc₂ : IpaAcceptV (foldGens g u₂) (foldGens b u₂)
            (P + u₂⁻¹ • L + u₂ • R) (v + u₂⁻¹ • Lv + u₂ • Rv) (projTree t₂) then
          if hc₃ : IpaAcceptV (foldGens g u₃) (foldGens b u₃)
              (P + u₃⁻¹ • L + u₃ • R) (v + u₃⁻¹ • Lv + u₃ • Rv) (projTree t₃) then
            absurd ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, hc₁, hc₂, hc₃⟩
              hne
          else
            NontrivialRelation.ofFoldedGens u₃
              (NontrivialRelation.ofDeployedTree hz _ _ _ _ _ t₃ h.2.2.2.2.2.2.2.2 hc₃)
        else
          NontrivialRelation.ofFoldedGens u₂
            (NontrivialRelation.ofDeployedTree hz _ _ _ _ _ t₂ h.2.2.2.2.2.2.2.1 hc₂)
      else
        NontrivialRelation.ofFoldedGens u₁
          (NontrivialRelation.ofDeployedTree hz _ _ _ _ _ t₁ h.2.2.2.2.2.2.1 hc₁)

end Zcash.Snark
