import Mathlib
import Zcash.Snark.Soundness.KnowledgeSoundness
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Soundness.Consistency
import Zcash.Snark.Soundness.IpaSoundness

/-!
# Soundness composition: conditional, and the deployed accept condition

This module composes IPA knowledge soundness into SNARK-relation soundness for the Orchard
verifier. Its endpoint theorems — the *capstones* — come in two layers:

* the `_conditional` family, over an opaque `accepts : Prop`. The suffix avoids overclaiming:
  these are scaffolds, not finished soundness.
* the `_deployed` family, over the concrete accept condition `DeployedAccepts`: the assembled
  MSM — the *fingerprint*, the transcribed form of halo2's final verifier check — evaluates to
  the group identity.

The deployed `_opening`/`_constraint` theorems derive the IPA opening (via `ipa_soundV`) and the
gate constraint from the accept, under the Fiat–Shamir bridge `hFS`. An earlier deployed layer
that peeled the blinding terms off the transcript (the URS generators `U`, `W` and the blinding
commitment `S`) was removed; re-expressing binding as a DLR-hardness reduction (see
`relation_of_collision` in `Zcash.Snark.Soundness.CommitFold`) is the planned follow-up.

## Assumptions (the conditional family)

* **Opaque accept.** `accepts` is a free `Prop`, so `orchard_verifier_sound_conditional` says
  nothing about the fingerprint. The `_deployed` variants take `DeployedAccepts` instead.
* **Extraction bundled with Fiat–Shamir.** `ExtractableFromAcceptance` assumes the IPA
  knowledge-soundness conclusion, so the proven extraction lemmas (`accepting_fold_eq`,
  `extract_correct`) are off this path.
* **Circuit satisfaction assumed.** It also supplies `circuitSat a` rather than deriving it from
  the deployed gate check (`constraint_identity_of_accept` + the multiopen decode).
* **Binding inert.** `hbind` (DLR hardness) reaches `knowledge_sound` but only feeds its
  uniqueness conjunct, which this proof discards.

What is proven lives in the component lemmas (`extract_correct`, `accepting_fold_eq`,
`quotientCheck_sound`, `ipaRelation_unique`, and the binding reduction); the open work is wiring
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
theorem orchard_verifier_sound_conditional (urs : URS G) (hbind : CommitmentBinding (F := Fp) urs)
    {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance urs P b v circuitSat accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs P b v circuitSat a → S) :
    S := by
  obtain ⟨t, a, hcons, hopen, hsat⟩ := hextract haccepts
  exact hencodes a (knowledge_sound urs hbind hcons hopen hsat).2.1

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

/-! ## `IpaRelation` is derived from the transcript tree, not assumed

`Zcash.Snark.ipa_soundV` derives the full opening relation — `commit g a = P` and `⟨a,b⟩ = v` —
from an accepting IPA transcript tree (`IpaAcceptV`), binding-free, by 3-special soundness. So
the bridge below no longer assumes `IpaRelation`: the cryptographic opening is genuinely derived.
What `FiatShamirTree` still absorbs beyond the rewinding is structural — see its docstring. -/

/-- `IpaAcceptV` over the URS generators derives `IpaRelation`: the witness `ipa_soundV` extracts
opens `P` and gives the inner product. Derived, not assumed. -/
theorem ipaRelation_of_acceptV (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (P : G) (v : Fp)
    (t : IpaTreeV Fp G urs.k) (h : IpaAcceptV urs.g b P v t) :
    ∃ a, IpaRelation urs P b v a := by
  obtain ⟨a, hP, hv⟩ := ipa_soundV urs.g b P v t h
  refine ⟨a, hP, ?_⟩
  have hib : innerProduct a b = commitGen b a := by simp only [innerProduct, commitGen, smul_eq_mul]
  rw [hib]; exact hv

/-- The Fiat–Shamir bridge — the residual assumption: an accepted proof yields an accepting
transcript tree (`IpaAcceptV`), from which the opening is *derived* (`ipaRelation_of_acceptV`),
not assumed. Besides the rewinding itself, the bridge absorbs that the accepted MSM really
unfolds into the tree's checks for the proof's own `P`, `b`, `v`, and the separation of the
blinding terms (`IpaAcceptV` is the blinding-free IPA). An earlier layer discharged these; it was
removed pending a DLR-hardness reduction. -/
def FiatShamirTree (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (P : G) (v : Fp) (accepts : Prop) : Prop :=
  accepts → ∃ t : IpaTreeV Fp G urs.k, IpaAcceptV urs.g b P v t

/-- **Deployed soundness, opening derived.** From the deployed accept (`assemble.eval = 0`) and
the Fiat–Shamir bridge `hFS`, some witness opens `(P, b, v)` — derived by `ipa_soundV`, not
assumed — and, given the constraint side `hcirc` and VK-correctness `hencodes`, the statement `S`
follows. `hFS` still absorbs what `FiatShamirTree` lists; the `_constraint` variant below derives
`hcirc` from the verifier's gate check. -/
theorem orchard_verifier_sound_deployed_opening [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    (haccepts : DeployedAccepts urs hk vk ps ch)
    (hFS : FiatShamirTree urs b P v (DeployedAccepts urs hk vk ps ch))
    (hcirc : ∀ a, IpaRelation urs P b v a → circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs P b v circuitSat a → S) :
    S := by
  obtain ⟨t, ht⟩ := hFS haccepts
  obtain ⟨a, hrel⟩ := ipaRelation_of_acceptV urs b P v t ht
  exact hencodes a ⟨hrel, hcirc a hrel⟩

/-! ## `circuitSat` is derived from the verifier's gate check + Schwartz–Zippel

The constraint side mirrors the opening side. The verifier checks the gate identity only at the
challenge `x` — a point check (`quotientCheck`: `numerator.eval x = h.eval x · (xⁿ−1)`).
`circuitSatViaGates_of_check` lifts that point check to the polynomial identity
`circuitSatViaGates` (the witness's decoded columns satisfy the gates) provided `x` avoids the
Schwartz–Zippel *bad set* — the roots of the difference polynomial when it is nonzero, which is
what `hgood` excludes. So `circuitSat`, instantiated to the concrete `circuitSatViaGates`, is
derived from the verifier's actual gate check rather than taken as an opaque hypothesis. -/

open Polynomial in
/-- **Deployed soundness, opening and constraint derived.** As the opening theorem above, with the
circuit side now derived too: the verifier's gate check holds at the challenge (`hquot`), and a
good challenge (`hgood`) lifts it to the polynomial identity `circuitSatViaGates`
(`circuitSatViaGates_of_check`). `hquot`/`hgood` play for the constraint side the role `hFS`
plays for the opening — the gate check is part of the accept, modulo the multiopen decode. -/
theorem orchard_verifier_sound_deployed_constraint [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (haccepts : DeployedAccepts urs hk vk ps ch)
    (hFS : FiatShamirTree urs b P v (DeployedAccepts urs hk vk ps ch))
    (hquot : ∀ a, IpaRelation urs P b v a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs P b v a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs P b v
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S := by
  obtain ⟨t, ht⟩ := hFS haccepts
  obtain ⟨a, hrel⟩ := ipaRelation_of_acceptV urs b P v t ht
  have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
    circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
      (hquot a hrel) (hgood a hrel)
  exact hencodes a ⟨hrel, hsat⟩

end Zcash.Snark
