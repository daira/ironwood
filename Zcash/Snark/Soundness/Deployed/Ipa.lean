import Zcash.Snark.Soundness.IpaSoundness

/-!
# The deployed IPA's `U`/`W` apparatus, peeled to the clean recursive IPA

`Zcash.Snark.ipa_soundV` proves knowledge soundness of the *clean* inner-product argument
(`IpaAcceptV`: fold `g`, `b`, `P`, `v`; leaf `P = [c]g₀ ∧ v = c·b₀`). halo2's deployed IPA
(`poly/commitment/verifier.rs`) runs that same recursion plus three extra fixed generators,
verified in one group equation:

* `U` — the inner-product (value) generator: the value `v` is checked through `[-c·b·z]U`
  (`z` a challenge that stops the prover interfering with the `U` term).
* `W` — the commitment blinding: the prover's synthetic blinding factor `f` rides on `[-f]W`.
* `S`/`ξ` — the synthetic blinding of the opening (zero knowledge): the adjusted commitment is
  `P' = P − [v]g₀ + [ξ]S`, `S` a commitment to a random polynomial vanishing at the point. *Not
  modelled here*: the `[ξ]S` term and the value term `[-v]g₀` stay in the verifier equation and
  are folded into the opened commitment by the equation-to-tree bridge (`FiatShamirTree`), not by
  the binding peel (`NontrivialRelation.ofDeployedTree`).

This file supplies the binding-free scaffolding for the `U`/`W` part of that apparatus — the tree
(`DeployedIpaTreeV`, whose nodes carry `U`/`W` data but not `S`), its projection (`projTree`), the
deployed accept predicate (`DeployedIpaAcceptV`), and the accept's satisfiability from an opening
witness (`deployedIpaAcceptV_of_witness`, the completeness gate). The peel
(`Zcash.Snark.Soundness.Deployed.IpaPeel`) separates the combined check into the clean `g`-side
commitment and `U`-side value checks (the `W`-side blinding identity is discarded), closing the
deployed IPA onto `ipa_soundV`; a check that does not separate *computes* a nontrivial
discrete-log relation among `(g, U, W)` (`NontrivialRelation.ofDeployedTree` — see
`The reduction form` in `Zcash.Snark.Soundness.Main`).
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A deployed 3-ary IPA transcript tree: `IpaTreeV` plus, per node, the blinding cross-terms
`Lw`, `Rw` (the `W`-side of the prover's `L`/`R`) and, at the leaf, the synthetic blinding scalar
`f` and the `g`-representation `aP` of the folded commitment. `aP` is extraction content the
bridge supplies as *data* — behind an `∃` it would be unrecoverable (see the
breaks-as-computed-data convention in `Zcash.Security.RandomOracle`). The `U`/`W` generators and
the binding challenge `z` are global (carried in `DeployedIpaAcceptV`), matching halo2 —
`params.u`, `params.w`, and `z` are fixed across rounds.

Label caveat: the names follow `IpaTreeV`'s fold convention, not halo2's read order. With tree
challenge `û = uⱼ⁻¹` (so `foldGens` matches the deployed generator fold — see `sFun_fold`), a node
folds `P + û⁻¹•L + û•R = P + uⱼ•L + uⱼ⁻¹•R`; the deployed check is `P + uⱼ⁻¹•L_dep + uⱼ•R_dep`,
so the intended instantiation *swaps* the labels: `L := R_dep`, `R := L_dep` (likewise `Lv`/`Rv`
and `Lw`/`Rw`). -/
inductive DeployedIpaTreeV (F G : Type*) : ℕ → Type _ where
  | leaf : F → F → (Fin (2 ^ 0) → F) → DeployedIpaTreeV F G 0
  | node {d : ℕ} : G → G → F → F → F → F → F → F → F →
      DeployedIpaTreeV F G d → DeployedIpaTreeV F G d → DeployedIpaTreeV F G d → DeployedIpaTreeV F G (d + 1)

/-- Forget the deployed decorations (`Lw`, `Rw`, `f`, `aP`), recovering the clean `IpaTreeV` that
`ipa_soundV` consumes. -/
def projTree : {d : ℕ} → DeployedIpaTreeV F G d → IpaTreeV F G d
  | _, .leaf c _ _ => .leaf c
  | _, .node L R Lv Rv _ _ u₁ u₂ u₃ t₁ t₂ t₃ =>
      .node L R Lv Rv u₁ u₂ u₃ (projTree t₁) (projTree t₂) (projTree t₃)

/-- Acceptance for the deployed IPA, carrying the `U`/`W` apparatus (`S`/`ξ` stays in the verifier
equation, folded by the equation-to-tree bridge). The recursion folds the generators `g`, the eval
vector `b`, the commitment `P` (by `L`,`R`), the value `v` (by `Lv`,`Rv`) and the blinding `blind`
(by `Lw`,`Rw`) — the `g`/`b`/`P`/`v` folds are exactly `IpaAcceptV`'s; `U`, `W`, `z` are fixed.
The leaf *reformulates* halo2's folded check as
`P + [z·v]U + [blind]W = [c]g₀ + [z·c·b₀]U + [f]W` — the value rides on `U` via the challenge `z`
(sound for `z ≠ 0` under binding), where halo2's literal check bakes the value into `g₀` and keeps
`[ξ]S`; the faithful flat form is `DeployedIpaVerifierEq`. The leaf pins `P` to the tree's
`g`-representation data `aP` (`P = ⟨aP, g⟩`) — bridge-supplied extraction content, inventoried at
`FiatShamirTree`. -/
def DeployedIpaAcceptV : {d : ℕ} → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → G → G → F → G → F → F →
    DeployedIpaTreeV F G d → Prop
  | 0, g, b, U, W, z, P, v, blind, .leaf c f aP =>
      P = commitGen g aP ∧
        commitGen g aP + (z * v) • U + blind • W
          = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W
  | _ + 1, g, b, U, W, z, P, v, blind, .node L R Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        DeployedIpaAcceptV (foldGens g u₁) (foldGens b u₁) U W z
          (P + u₁⁻¹ • L + u₁ • R) (v + u₁⁻¹ • Lv + u₁ • Rv) (blind + u₁⁻¹ • Lw + u₁ • Rw) t₁ ∧
        DeployedIpaAcceptV (foldGens g u₂) (foldGens b u₂) U W z
          (P + u₂⁻¹ • L + u₂ • R) (v + u₂⁻¹ • Lv + u₂ • Rv) (blind + u₂⁻¹ • Lw + u₂ • Rw) t₂ ∧
        DeployedIpaAcceptV (foldGens g u₃) (foldGens b u₃) U W z
          (P + u₃⁻¹ • L + u₃ • R) (v + u₃⁻¹ • Lv + u₃ • Rv) (blind + u₃⁻¹ • Lw + u₃ • Rw) t₃

/-- One deployed round, honest side: folding the witness by `u` (`foldVec`) against the folded
generators `foldGens g u` opens the parent commitment plus the cross-terms `[u⁻¹]L + [u]R`. Here
`L = ⟨loHalf a, hiHalf g⟩` and `R = ⟨hiHalf a, loHalf g⟩` — `commitGen_round` in the tree's fold
convention. -/
theorem commitGen_foldGens_foldVec {k : ℕ} (g : Fin (2 ^ (k + 1)) → G)
    (a : Fin (2 ^ (k + 1)) → F) {u : F} (hu : u ≠ 0) :
    commitGen (foldGens g u) (foldVec (loHalf a) (hiHalf a) u)
      = commitGen g a + u⁻¹ • commitGen (hiHalf g) (loHalf a)
        + u • commitGen (loHalf g) (hiHalf a) := by
  have h := commitGen_round (loHalf g) (hiHalf g) (loHalf a) (hiHalf a) (inv_ne_zero hu)
  rw [inv_inv] at h
  rw [foldGens, foldVec, h, ← commitGen_split]

/-- **The deployed accept is satisfiable from an opening witness (completeness).** For any
witness `a`, blind, and binding challenge `z`, some deployed tree accepts the commitment
`⟨a, g⟩` opened to the value `⟨a, b⟩`. The honest construction: cross-terms from the witness
halves (`commitGen_foldGens_foldVec`), zero blinding cross-terms, one triple of distinct nonzero
challenges reused at every node. The sanity gate: the accept does not exclude honest executions.
`ForkedTranscript.nonempty_of_opening` lifts it to the deployed interface. -/
theorem deployedIpaAcceptV_of_witness (u₁ u₂ u₃ : F)
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0) :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (U W : G) → (z blind : F) →
      (a : Fin (2 ^ d) → F) →
      ∃ t : DeployedIpaTreeV F G d,
        DeployedIpaAcceptV g b U W z (commitGen g a) (commitGen b a) blind t
  | 0, g, b, U, W, z, blind, a => by
      have ha : a = fun _ => a ⟨0, Nat.one_pos⟩ :=
        funext fun i => congrArg a (Fin.ext (Nat.lt_one_iff.mp i.isLt))
      exact ⟨.leaf (a ⟨0, Nat.one_pos⟩) blind a, rfl, by rw [← ha]⟩
  | d + 1, g, b, U, W, z, blind, a => by
      obtain ⟨t₁, h₁⟩ := deployedIpaAcceptV_of_witness u₁ u₂ u₃ h12 h13 h23 hu₁ hu₂ hu₃
        (foldGens g u₁) (foldGens b u₁) U W z blind (foldVec (loHalf a) (hiHalf a) u₁)
      obtain ⟨t₂, h₂⟩ := deployedIpaAcceptV_of_witness u₁ u₂ u₃ h12 h13 h23 hu₁ hu₂ hu₃
        (foldGens g u₂) (foldGens b u₂) U W z blind (foldVec (loHalf a) (hiHalf a) u₂)
      obtain ⟨t₃, h₃⟩ := deployedIpaAcceptV_of_witness u₁ u₂ u₃ h12 h13 h23 hu₁ hu₂ hu₃
        (foldGens g u₃) (foldGens b u₃) U W z blind (foldVec (loHalf a) (hiHalf a) u₃)
      exact ⟨.node (commitGen (hiHalf g) (loHalf a)) (commitGen (loHalf g) (hiHalf a))
          (commitGen (hiHalf b) (loHalf a)) (commitGen (loHalf b) (hiHalf a)) 0 0 u₁ u₂ u₃ t₁ t₂ t₃,
        h12, h13, h23, hu₁, hu₂, hu₃,
        by rw [smul_zero, smul_zero, add_zero, add_zero, ← commitGen_foldGens_foldVec g a hu₁,
             ← commitGen_foldGens_foldVec b a hu₁]; exact h₁,
        by rw [smul_zero, smul_zero, add_zero, add_zero, ← commitGen_foldGens_foldVec g a hu₂,
             ← commitGen_foldGens_foldVec b a hu₂]; exact h₂,
        by rw [smul_zero, smul_zero, add_zero, add_zero, ← commitGen_foldGens_foldVec g a hu₃,
             ← commitGen_foldGens_foldVec b a hu₃]; exact h₃⟩

end Zcash.Snark
