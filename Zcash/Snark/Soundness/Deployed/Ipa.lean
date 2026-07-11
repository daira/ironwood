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
(`DeployedIpaTreeV`, whose nodes carry `U`/`W` data but not `S`), its projection (`projTree`), and
the deployed accept predicate (`DeployedIpaAcceptV`). The peel
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

end Zcash.Snark
