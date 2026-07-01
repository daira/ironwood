import Mathlib
import Zcash.Snark.Soundness.KnowledgeSoundness
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Soundness.Consistency
import Zcash.Snark.Soundness.IpaSoundness
import Zcash.Snark.Soundness.DeployedIpaPeel
import Zcash.Snark.Soundness.DeployedVerification

/-!
# Soundness composition: conditional, and the deployed accept condition

This module formalizes the composition that turns IPA knowledge soundness into the SNARK relation, in
two layers: a `_conditional` family over an opaque `accepts : Prop`, and a `_deployed` family over the
concrete accept condition `DeployedAccepts` (the rejecting `assemble?` succeeds and its MSM — the §1
fingerprint — evaluates to the identity). The conditional
theorems are named with a `_conditional` suffix to avoid overclaiming: they are scaffolds, not finished
soundness. The deployed `_opening` / `_constraint` theorems below derive the IPA opening (via `ipa_soundV`,
after peeling the `U`/`W` apparatus) and the gate constraint from the accept, with `P`/`v` **pinned** to
the proof's `multiopenCommitment`/`multiopenValue`. The accept is **proven** to entail the explicit
closed-form `DeployedIpaVerifierEq` (`deployedAccepts_verifierEq`, via `Zcash.Snark.Soundness.DeployedVerification`
— an implication, the direction soundness consumes; the accept also comprises the rejection guards);
fidelity of that closed form to halo2's Rust is the §1 transcription (`assembleFinalMsm`/`ipaFold`, checked
by the fingerprint), not re-proved here. The residual `FiatShamirTree` bridge is the Fiat–Shamir
forking **plus the special-soundness extraction content**: the node `L`/`R`↦value/blinding decomposition,
the leaf `g`-representation of the folded commitment, and the adjusted-commitment step
`P' = P − [v]g₀ + [ξ]S` (folding the value and `S`/`ξ` terms into the opened commitment — which needs a
representation of the adversary point `S`, so it is not a deterministic rewrite) — all issue #11.
Commitment binding is load-bearing *in the proof* (the `U`/`W` separation is derived from a discrete-log
relation reduction, `Zcash.Snark.Soundness.DeployedIpaPeel`), so the deployed conclusion is
`SnarkRelation ∨ HasNontrivialRelation` — a *reduction*: it exhibits a discrete-log relation rather than
asserting soundness outright. A relation always *exists* in a prime-order group, so at the concrete curve this
disjunction is propositionally `True` and the *statement* is vacuous; the soundness force is the DLR/AGM
layer — no feasible adversary can *find* the relation, which is not formalized in Lean — not the proposition.

## Assumptions (the conditional family)

* **Opaque accept.** `accepts` is a free `Prop`, so `orchard_verifier_sound_conditional` says
  nothing about the fingerprint. The `_deployed` variants take `DeployedAccepts` instead.
* **Extraction bundled with Fiat–Shamir.** `ExtractableFromAcceptance` assumes the IPA
  knowledge-soundness conclusion, so the proven extraction lemmas (`accepting_fold_eq`,
  `extract_correct`) are off this path.
* **Circuit satisfaction assumed.** It also supplies `circuitSat a` rather than deriving it from
  the deployed gate check (`constraint_identity_of_accept` + the multiopen decode).

What is proven lives in the component lemmas (`extract_correct`, `accepting_fold_eq`,
`quotientCheck_sound`, and the computed binding reduction `NontrivialDLRelation.ofCollision`);
the open work is wiring
them onto this path. `Soundness.Vesta` instantiates the capstones at the concrete curve;
`Soundness.KnowledgeSoundness` lists the assumptions.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Assumption: if the proof is accepted, there exist a consistent transcript tree and a witness
`a` opening the commitment (`IpaRelation urs P b v a`) and satisfying the circuit
(`circuitSat a`). This assumes more than Fiat–Shamir: it bundles the extraction conclusion that
`accepting_fold_eq`/`extract_correct` already prove, so those lemmas are off this path; splitting
the two apart is open. -/
def ExtractableFromAcceptance (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    (circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop) (accepts : Prop) : Prop :=
  accepts → ∃ (t : Tree Fp urs.k) (a : Fin (2 ^ urs.k) → Fp),
    Consistent t a ∧ IpaRelation urs P b v a ∧ circuitSat a

-- Tracked semantic-adequacy gap: `S` is a free `Prop` and `hencodes` an assumed hypothesis, so
-- the chain stops at "the extracted witness satisfies the gates" (`SnarkRelation`) and never
-- reaches "…therefore a valid Orchard action" (note well-formed, value balanced, nullifier
-- correctly derived, spend authorized). Closing it means instantiating `S` to the concrete
-- Orchard statement and proving `hencodes` — the output-side dual of the input-side
-- VK-correctness gap (see `Verifier/Assemble.lean`). Large; not started.
/-- **Conditional soundness (the scaffold).** *If* acceptance yields the extraction data
(`hextract`), then the statement `S` follows via `hencodes`. `accepts` is opaque and the
extraction is assumed (see the module docstring's assumption list); the deployed
`_opening`/`_constraint` theorems below take the concrete accept and derive what is assumed
here. -/
theorem orchard_verifier_sound_conditional (urs : URS G)
    {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance urs P b v circuitSat accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs P b v circuitSat a → S) :
    S := by
  obtain ⟨t, a, hcons, hopen, hsat⟩ := hextract haccepts
  exact hencodes a (knowledge_sound urs hcons hopen hsat).2

/-- The deployed verifier's accept condition: `assemble? vk ps ch` succeeds and the assembled MSM
evaluates to the group identity against the URS. Proof data that `assemble?` rejects (duplicate
queries, a mismatched `multiopenU` count, malformed permutation last-evals, zero inverse
denominators) is `False`. `hk` aligns the circuit shape's `k` with the URS's. -/
def DeployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Prop :=
  match assemble? vk ps ch with
  | some m => (hk ▸ m : Msm urs.k Fp G).eval urs = 0
  | none => False

/-- The `urs.k`↔`shape.k` transport, isolated: evaluating the `hk`-transported MSM against `urs` is the same
as evaluating `m` against the URS rebuilt at `shape.k` with `urs`'s (transported) generators. With `urs`
free here, `cases urs` + `subst hk` collapses the cast to `rfl`. This lets `deployedAccepts_verifierEq` reach
the `⟨shape.k, …⟩`-indexed `deployed_verification_eq` without destructuring the URS in place (which would
tangle the accept hypothesis's own `hk`-cast). -/
theorem eval_cast {shape : Shape} {urs : URS G} (hk : shape.k = urs.k) (m : Msm shape.k Fp G) :
    (hk ▸ m : Msm urs.k Fp G).eval urs = m.eval ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
  obtain ⟨k, g, w, u⟩ := urs
  change shape.k = k at hk
  subst hk
  rfl

/-- Structural faithfulness, **proven** (was assumed by the Fiat–Shamir bridge): the deployed accept
*entails* halo2's explicit IPA verifier equation. (An implication, not an `Iff` — the accept additionally
comprises the rejection guards; this is the direction soundness consumes.) From `DeployedAccepts` (the
rejecting fingerprint `assemble?` succeeds and
evaluates to the identity), `assemble?_eq_some` identifies the accepted MSM with the non-rejecting
`assembleFinalMsm`, and `deployed_verification_eq` rewrites its evaluation to the explicit equation — so
`DeployedIpaVerifierEq` holds for the proof's actual `(vk, ps, ch)`. This discharges the MSM↔equation
correspondence the bridge used to absorb; the residual bundle in `FiatShamirTree` is the forking and the
extraction-content data it supplies — the node decomposition, the leaf `g`-representation, and the
adjusted-commitment step `P' = P − [v]g₀ + [ξ]S` (issue #11). The `urs.k`↔`shape.k`
transport is `eval_cast`. -/
theorem deployedAccepts_verifierEq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (h : DeployedAccepts urs hk vk ps ch) :
    DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps ch := by
  unfold DeployedAccepts at h
  cases hm : assemble? vk ps ch with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some m =>
      rw [hm] at h
      simp only [] at h
      rw [eval_cast hk m] at h
      have hmeq := assemble?_eq_some vk ps ch hm
      unfold DeployedIpaVerifierEq
      rw [← deployed_verification_eq (hk ▸ urs.g) urs.w urs.u ps ch
            (constructIntermediateSets (assembleQueries vk ps ch)), ← hmeq]
      exact h

/-! ## `IpaRelation` is derived from the transcript tree, not assumed

`Zcash.Snark.ipa_soundV` derives the full opening relation — `commit g a = P` and `⟨a,b⟩ = v` — from an
accepting IPA transcript tree (`IpaAcceptV`), binding-free, by 3-special soundness. So the bridge no
longer assumes `IpaRelation`. Honest caveat for `FiatShamirTree` below: beyond the Fiat–Shamir rewinding it
still absorbs (i) the node-level `L`/`R`↦value/blinding decomposition, (ii) the leaf `g`-representation of
the folded commitment (`DeployedIpaAcceptV`'s `∃ aP` span condition), and (iii) the
adjusted-commitment step `P' = P − [v]g₀ + [ξ]S` (folding the value and `S`/`ξ` terms — this needs a
representation of the adversary point `S`, so it is rewinding- or AGM-content, not a deterministic
rewrite). (i)–(ii) are what the special-soundness extraction would *derive* from the forked flat equations
by Vandermonde over the augmented `(g, U, W)` basis; here they arrive as bridge-supplied tree data. The
MSM↔equation correspondence and the `P`/`v` pinning it used to also absorb are now discharged
(`deployedAccepts_verifierEq`); the cryptographic opening and the `g`/`U`/`W` separation are derived. -/

/-- `IpaAcceptV` over the URS generators derives `IpaRelation`: the witness `ipa_soundV` extracts
opens `P` and gives the inner product. Derived, not assumed. -/
theorem ipaRelation_of_acceptV (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (P : G) (v : Fp)
    (t : IpaTreeV Fp G urs.k) (h : IpaAcceptV urs.g b P v t) :
    ∃ a, IpaRelation urs P b v a := by
  obtain ⟨a, hP, hv⟩ := ipa_soundV urs.g b P v t h
  refine ⟨a, hP, ?_⟩
  have hib : innerProduct a b = commitGen b a := by simp only [innerProduct, commitGen, smul_eq_mul]
  rw [hib]; exact hv

/-- The deployed commitment the IPA verifier opens (`multiopenCommitment` with `urs`'s generators
transported to the proof's `shape.k`): the pinned `P`, read off `(vk, ps, ch)`. Reducible, so it is defeq to
its body for matching against `DeployedIpaVerifierEq`'s leading term. -/
abbrev deployedCommitment [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : G :=
  multiopenCommitment (hk ▸ urs.g) urs.w urs.u vk ps ch

/-- The forking bridge — the *residual* assumption. Its premise is halo2's explicit verifier equation
`DeployedIpaVerifierEq` (which `deployedAccepts_verifierEq` *proves* the deployed
accept entails), and its conclusion opens the pinned `deployedCommitment`/`multiopenValue` — the actual
`P`/`v` from `(vk, ps, ch)`, not free parameters. So what this assumes is: the verifier equation holding
yields a consistent deployed IPA transcript tree (`DeployedIpaAcceptV`, carrying the `U`/`W` apparatus).
That bundles the Fiat–Shamir **forking** — (a) the rewinding that produces three accepting continuations
per node at distinct nonzero challenges — with the special-soundness **extraction** content, knowledge the
forked transcripts would pin by Vandermonde over the augmented `(g, U, W)` basis but that here arrives as
bridge-supplied tree data: (b) the node-level `L`/`R`↦value/blinding **decomposition**
(`Lv`/`Rv`/`Lw`/`Rw` — each round point's `(g, U, W)`-representation, which must not depend on `z`);
(c) the leaf **`g`-representation** `∃ aP, P = ⟨aP, g⟩` of the folded commitment (the span condition
`DeployedIpaAcceptV`'s leaf demands); and (d) the **adjusted-commitment** step `P' = P − [v]g₀ + [ξ]S`,
which folds the value term `[-v]g₀` and the `S`/`ξ` blinding-poly `[ξ]S` (both present in
`DeployedIpaVerifierEq`) into the commitment the tree opens — this needs a representation of the adversary
point `S` (ξ-side rewinding or AGM), so it is not a deterministic rewrite of the equation. The
MSM↔equation correspondence is discharged separately
(`deployedAccepts_verifierEq`), not assumed here; the per-leaf `g`/`U`/`W` separation is *derived*
(`deployed_to_acceptV`) — but `S`/`ξ` is not peeled, it lives in (d). `b`/`z`/`blind` are bridge-mediated
(the protocol fixes `b = evalVector urs.k ch.x3` — whose per-round fold telescopes to the leaf
`b₀ = computeB ch.x3 ·` — and `z = ch.z`); only `P`/`v` are pinned. All of (a)–(d) are issue #11. -/
def FiatShamirTree [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp) : Prop :=
  DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps ch →
    ∃ t : DeployedIpaTreeV Fp G urs.k,
      DeployedIpaAcceptV urs.g b urs.u urs.w z
        (deployedCommitment urs hk vk ps ch) (multiopenValue vk ps ch) blind t

/-- The deployed Orchard verifier opening, as a binding **reduction**, with `P`/`v` **pinned** to the proof
(`deployedCommitment`/`multiopenValue` from `(vk, ps, ch)`, not free parameters). From the deployed accept,
`deployedAccepts_verifierEq` *proves* the explicit `DeployedIpaVerifierEq` form; the forking
bridge `hFS` turns that equation into the deployed transcript tree opening the pinned commitment (via the
adjusted-commitment step `P' = P − [v]g₀ + [ξ]S`); `deployed_to_acceptV` peels the `U`/`W` apparatus onto the
clean `IpaAcceptV` (deriving the per-leaf separation from binding); and `ipa_soundV` extracts the opening.

The conclusion is `S ∨ HasNontrivialRelation g U W` — a reduction (it exhibits a discrete-log relation
rather than asserting soundness outright). A relation always *exists* in a prime-order group, so at the
concrete curve this disjunction is propositionally `True`
and the theorem is vacuous *as a statement* (provable as `Or.inr` without the hypotheses); its content is
the constructive extraction plus the assumption that no efficient adversary can *find* the relation (DLR/AGM
hardness, not formalized in Lean). Commitment binding is load-bearing in the *proof structure*, not the
Vesta statement.
Named assumptions: the residual bridge (`hFS`, issue #11), `z ≠ 0`, the circuit side (`hcirc`), and
VK-correctness (`hencodes`).

Caveat on `hcirc`'s shape: it quantifies over *every* mathematical opening `a` of the pinned `(P, b, v)`.
At a prime-order curve those openings form an affine subspace of dimension `≥ 2^k − 2` (two linear
conditions on `2^k` coordinates), so any `circuitSat` that genuinely reads the witness fails on almost
all of it — the hypothesis is unsatisfiable for the intended instantiation, the `AugmentedBinding`
failure mode in hypothesis position. `circuitSatViaGates_of_check` does not discharge it: that lemma
derives `circuitSat` for *one* `a` from that `a`'s own point-check, never the quantified premise.
The fix is restating the constraint side as a derived fact about the *extracted* witness via the
multiopen decode — issue #18. -/
theorem orchard_verifier_deployed_opening_reduction [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop} (hz : z ≠ 0)
    (haccepts : DeployedAccepts urs hk vk ps ch)
    (hFS : FiatShamirTree urs hk vk ps ch b z blind)
    (hcirc : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) b (multiopenValue vk ps ch) a →
      circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps ch) b
      (multiopenValue vk ps ch) circuitSat a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨t, ht⟩ := hFS (deployedAccepts_verifierEq urs hk vk ps ch haccepts)
  rcases deployed_to_acceptV hz urs.g b (deployedCommitment urs hk vk ps ch) (multiopenValue vk ps ch)
    blind t ht with hclean | hrel
  · obtain ⟨a, hrel'⟩ := ipaRelation_of_acceptV urs b (deployedCommitment urs hk vk ps ch)
      (multiopenValue vk ps ch) (projTree t) hclean
    exact Or.inl (hencodes a ⟨hrel', hcirc a hrel'⟩)
  · exact Or.inr hrel

/-! ## `circuitSat` is derived from the verifier's gate check + Schwartz–Zippel

The constraint side mirrors the opening side. The verifier checks the gate identity only at the
challenge `x` — a point check (`quotientCheck`: `numerator.eval x = h.eval x · (xⁿ−1)`).
`circuitSatViaGates_of_check` lifts that point check to the polynomial identity
`circuitSatViaGates` (the witness's decoded columns satisfy the gates) provided `x` avoids the
Schwartz–Zippel *bad set* — the roots of the difference polynomial when it is nonzero, which is
what `hgood` excludes. So `circuitSat`, instantiated to the concrete `circuitSatViaGates`, is
derived from the verifier's actual gate check rather than taken as an opaque hypothesis. -/

open Polynomial in
/-- The deployed Orchard verifier opening and constraint, as a binding **reduction**, with `P`/`v` **pinned**
to the proof (`deployedCommitment`/`multiopenValue`). As `orchard_verifier_deployed_opening_reduction`, with
the circuit side derived too: `circuitSat` — instantiated to
`circuitSatViaGates` — from the verifier's quotient/gate point check `hquot` at the challenge `x`, lifted to
the polynomial identity by Schwartz–Zippel (`hgood`), via `circuitSatViaGates_of_check`. The deployed accept
reaches the forking bridge through the *proven* `deployedAccepts_verifierEq`. The conclusion is
`S ∨ HasNontrivialRelation g U W` — a reduction (it exhibits a discrete-log relation, not soundness
outright); a relation always *exists* at a prime-order curve, so this disjunction is propositionally `True`
and the theorem is vacuous as a *statement*, the force being the DLR/AGM hardness layer (not formalized in
Lean) that no adversary can *find* one.

Named assumptions: the residual bridge (`hFS`, issue #11), `z ≠ 0`, the gate point-check (`hquot`), the SZ good
challenge (`hgood`), and VK-correctness (`hencodes`).

Caveat on the `hquot`/`hgood` shape (as for `hcirc` above): both quantify over *every* mathematical
opening `a` of the pinned `(P, b, v)` — an affine subspace of dimension `≥ 2^k − 2` at a prime-order
curve — so for any decode that genuinely reads columns out of `a` they are unsatisfiable, not merely
undischarged: the verifier's actual gate check constrains the *claimed* evaluations, not every
opening's decode. Restating them as facts about the *extracted* witness — binding the decode to the
real columns via `batch_open_soundV` — is issue #18. -/
theorem orchard_verifier_deployed_constraint_reduction [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp) (hz : z ≠ 0)
    (haccepts : DeployedAccepts urs hk vk ps ch)
    (hFS : FiatShamirTree urs hk vk ps ch b z blind)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) b (multiopenValue vk ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) b (multiopenValue vk ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps ch) b (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨t, ht⟩ := hFS (deployedAccepts_verifierEq urs hk vk ps ch haccepts)
  rcases deployed_to_acceptV hz urs.g b (deployedCommitment urs hk vk ps ch) (multiopenValue vk ps ch)
    blind t ht with hclean | hrel
  · obtain ⟨a, hrel'⟩ := ipaRelation_of_acceptV urs b (deployedCommitment urs hk vk ps ch)
      (multiopenValue vk ps ch) (projTree t) hclean
    have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
      circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
        (hquot a hrel') (hgood a hrel')
    exact Or.inl (hencodes a ⟨hrel', hsat⟩)
  · exact Or.inr hrel

end Zcash.Snark
