import Zcash.Snark.Soundness.Vesta
import Zcash.Snark.Soundness.Forking.Adversary.Algebraic
import Zcash.Snark.Soundness.AGM.Capstone

/-!
# Composing the algebraic forking extraction with the deployed decoded capstone

`Soundness.Forking.Adversary.Algebraic` models the algebraic forking family; `Soundness.Vesta`
proves the deployed decoded capstone. The two are architecturally
disjoint — one runs over an adversary-produced `AlgebraicWfProof` at oracle-derived challenges
`chRecord ν`, the other over a deployed `(vk, ps, ch)` run. This module builds the identification
bridge the composition needs on the *computed path*: the algebraic instance's clean `Opening` — an
`IpaRelation` at `commit … aMulti` — is exactly the `IpaRelation` at the deployed opened commitment
`deployedCommitment − pU•u − pW•w` the capstone consumes, once `AlgebraicWfProof.multiopen_repr`
rewrites the commitment. The collision branch needs only the commitment identification
(`opening_commit_deployed_of_instance`).

## The extracted `U`/`W` coordinates (`pU`, `pW`)

`pU`/`pW` are outputs, never hypotheses: the AGM representation (`AlgebraicWfProof.multiopen_repr`)
exposes the adversary's aggregate commitment as `commit(aMulti) + pU•u + pW•w`, so the extracted
opening is the generalized Pedersen triple `(aMulti, pU, pW)` in the augmented basis `(g, u, w)`.
The relation is stated at the de-blinded point `deployedCommitment − pU•u − pW•w` because
`IpaRelation` is the `g`-span opening. `pW` is the `w`-weight of the AGM representation — an
adversary may set it to anything, so the argument never assumes it is nonzero. Its value is
immaterial because the de-blinding subtracts `pW•w` (and `pU•u`) off whatever they are
(`opening_commit_deployed_of_instance`, no value-shift hypothesis). Weight on `u` shifts the opened
value by `z⁻¹·vU`; against the deployed batch opening of the same point that shift either vanishes
or the witnesses collide into a computed `(g,u,w)` relation — a dichotomy the rewind-free AGM
route returns as explicit relation coefficients.
-/

namespace Zcash.Snark

-- The deployed grouping definitions appear inside index types, so a defeq check on an index can
-- pull the whole `constructIntermediateSets (assembleQueries …)` computation through `whnf`.
-- Sealing them keeps those checks syntactic; the proofs below use their equation lemmas.
attribute [local irreducible] deployedSetQueries deployedSetCommIds deployedX4PairCount
  x4BatchCommitments x4BatchEvals

-- Match the instance set `AlgebraicWfProof.multiopen_repr` is stated against
-- (`Forking.Adversary.Algebraic` uses the same concrete `Inhabited VestaG`); a local `[Inhabited]`
-- binder would be a *different* instance term, forcing the `multiopenCommitment` fold through `whnf`.
-- Named (not anonymous) to avoid an auto-generated-name collision with the identical
-- `local instance` in `Forking.Adversary.Provenance` when both are imported into `TrustBoundary`.
local instance vestaInhabitedCompositionBridge : Inhabited VestaG := ⟨0⟩

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}

/-- `deployedCommitment` at the split URS unfolds to `multiopenCommitment`: definitional (the `hk`
cast is `rfl` on `ursOfAugmentedBasis`, whose `.k` is `shape.k`). Isolated so downstream terms match
`AlgebraicWfProof.multiopen_repr`'s `multiopenCommitment` without forcing the fold through `whnf`. -/
theorem deployedCommitment_eq_multiopen
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp) :
    deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment ps ch
      = multiopenCommitment (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).w (ursOfAugmentedBasis shape.k basis).u vk instanceCommitment ps ch :=
  rfl

/-- **The g-span representation of the multiopen commitment (P-identification).** The algebraic
proof's aggregate witness `aMulti ν` commits to `multiopenCommitment − multiU•u − multiBlind•w`:
immediate from `AlgebraicWfProof.multiopen_repr`. -/
theorem commit_aMulti_eq_multiopen
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (p : AlgebraicWfProof basis vk instanceCommitment) (ν : Fin 11 → Fp) :
    commit (ursOfAugmentedBasis shape.k basis) (p.aMulti ν)
      = multiopenCommitment (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).w (ursOfAugmentedBasis shape.k basis).u
          vk instanceCommitment p.algebraicProof.erase (chRecord ν (fun _ => 0))
        - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
        - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w := by
  have h := p.multiopen_repr ν
  rw [sub_sub, eq_sub_iff_add_eq, ← add_assoc]
  exact h



/-- The extracted opening commits to the de-blinded deployed commitment
`deployedCommitment − multiU•u − multiBlind•w` — the commitment conjunct of
`ipaRelation_deployed_of_instance`, available with no value-shift hypothesis. -/
theorem opening_commit_deployed_of_instance
    {vk : VerifyingKey shape Fp VestaG} {instanceCommitment : Fin shape.numProofs → ℕ → VestaG} (p : AlgebraicWfProof basis vk instanceCommitment) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk instanceCommitment p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (o : (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).Opening) :
    commit (ursOfAugmentedBasis shape.k basis) o.1
      = deployedCommitment (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment p.proof.1
            (chRecord ν (fun _ => 0))
        - p.multiU ν • (ursOfAugmentedBasis shape.k basis).u
        - p.multiBlind ν • (ursOfAugmentedBasis shape.k basis).w :=
  o.2.1.trans (by
    simp only [deployedAlgebraicInstanceOfCert]
    rw [deployedCommitment_eq_multiopen,
      show (p.proof.1 : ProofString shape Fp VestaG) = p.algebraicProof.erase from rfl]
    exact commit_aMulti_eq_multiopen p ν)



namespace ComputedAlgebraicFSFamily

variable {shape : Shape}



end ComputedAlgebraicFSFamily



end Zcash.Snark
