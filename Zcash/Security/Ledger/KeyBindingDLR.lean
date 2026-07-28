import Mathlib
import Zcash.Security.Ledger.Pool
import Zcash.Security.Ledger.SinsemillaDLR

/-!
# The deployed key-binding break computes a discrete-log relation

The pre-quantum discharge of the key-binding arm's ε: a `KeyBinding.Pool.Break` — two
valid `Commit^ivk` openings of the same `ivk` disagreeing on their opening projection —
computes a nontrivial discrete-log relation among the Sinsemilla table generators, the
`CommitIvk` domain point, and the `CommitIvk` randomness base. This folds ε_kb into the
same DL terminal as the Merkle and note-commitment arms, with no random-oracle model
and no probability accounting: the reduction is deterministic.

The shared machinery is `Bridge.relationOfChainPmEq` (`SinsemillaDLR`); this module
instantiates it at the `CommitIvk` domain point and randomness base, unpacking the
break's two openings into their defined hash chains and turning the equal-`ivk`
extraction into the up-to-sign equation via the `Extract_ℙ` ±-fibre property.
-/

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Circuits.Specs (K)
open Zcash.Circuits.Specs.Sinsemilla
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Pool

/-- The `CommitIvk` domain point `Q("z.cash:Orchard-CommitIvk-M")`, as a group element. -/
def ivkQpt : PallasGroup := PallasGroup.ofPoint ivkQ (Or.inl ivkQ_onCurve)

/-- The `CommitIvk` randomness base, as a group element — the `commitIvkR` argument of
the deployed `keyBinding` interface. -/
def commitIvkRpt : PallasGroup :=
  PallasGroup.ofPoint Ecc.MulFixed.Certs.commitIvkR.point
    (Or.inl Ecc.MulFixed.Certs.commitIvkR.onCurve)

/-- A defined `commitIvkHash` hit names a defined, valid `hashToPoint` chain. -/
theorem commitIvkHash_isSome {a n : Fp} {g : PallasGroup}
    (h : commitIvkHash a n = some g) :
    (hashToPoint orchardGenerators.S ivkQ (commitIvkChunks a.val n.val)).isSome := by
  unfold commitIvkHash at h
  rcases Option.bind_eq_some_iff.mp h with ⟨p, hp, -⟩
  exact hp ▸ rfl

/-- The chain a defined `commitIvkHash` hit names is valid, and the hit is its image. -/
theorem commitIvkHash_get_spec {a n : Fp} {g : PallasGroup}
    (h : commitIvkHash a n = some g) :
    ∃ hv : ((hashToPoint orchardGenerators.S ivkQ
        (commitIvkChunks a.val n.val)).get (commitIvkHash_isSome h)).Valid,
      g = PallasGroup.ofPoint _ hv := by
  unfold commitIvkHash at h
  rcases Option.bind_eq_some_iff.mp h with ⟨p, hp, hop⟩
  have hget : (hashToPoint orchardGenerators.S ivkQ
      (commitIvkChunks a.val n.val)).get (commitIvkHash_isSome h) = p := by
    simp [hp]
  rw [hget]
  unfold PallasGroup.ofPoint? at hop
  split at hop
  · rename_i hv
    exact ⟨hv, (Option.some_inj.mp hop).symm⟩
  · exact absurd hop (by simp)

/-- **The deployed key-binding break computes a discrete-log relation.** Two valid
`Commit^ivk` openings of the same `ivk` disagreeing on their opening projection land in
the chain-collision reducer at the `CommitIvk` domain point and randomness base.
`hcoeffs` is the chunk-coefficient injectivity (the binary-expansion core of spec
Theorem 5.4.3) and `hchunks` the injectivity of the 51-chunk `(ak, nk)` encoding, both
at the break's own two chunk lists; discharging them from the digit machinery is
tracked alongside this reduction. -/
def relationOfKeyBindingBreak
    {w₁ w₂ : KeyBinding.Pool.Witness Fq PallasGroup Fp}
    (b : KeyBinding.Pool.Break extract commitIvkHash commitIvkRpt w₁ w₂)
    (hcoeffs :
      preCoeffs (commitIvkChunks (extract w₁.akP).val w₁.nk.val)
          = preCoeffs (commitIvkChunks (extract w₂.akP).val w₂.nk.val) →
        commitIvkChunks (extract w₁.akP).val w₁.nk.val
          = commitIvkChunks (extract w₂.akP).val w₂.nk.val)
    (hchunks :
      commitIvkChunks (extract w₁.akP).val w₁.nk.val
          = commitIvkChunks (extract w₂.akP).val w₂.nk.val →
        extract w₁.akP = extract w₂.akP ∧ w₁.nk = w₂.nk) :
    NontrivialRelation (F := Fq) pallasS ivkQpt commitIvkRpt :=
  let hs₁ := commitIvkHash_isSome b.kb₁.hash_eq
  let hs₂ := commitIvkHash_isSome b.kb₂.hash_eq
  relationOfChainPmEq (Q := ivkQ) (Or.inl ivkQ_onCurve) (W := commitIvkRpt)
    (fun _ hm => chunksOf_mem_lt hm) (fun _ hm => chunksOf_mem_lt hm)
    (by simp)
    (Option.some_get hs₁).symm (commitIvkHash_get_spec b.kb₁.hash_eq).choose
    (Option.some_get hs₂).symm (commitIvkHash_get_spec b.kb₂.hash_eq).choose
    (by
      have hx : extract (w₁.hashPoint + w₁.rivk • commitIvkRpt)
          = extract (w₂.hashPoint + w₂.rivk • commitIvkRpt) := by
        rw [← b.kb₁.ivk_eq, ← b.kb₂.ivk_eq]
        exact b.ivk_eq
      have hpm := (PallasGroup.toPoint_x_eq_iff _ _).mp hx
      rwa [(commitIvkHash_get_spec b.kb₁.hash_eq).choose_spec,
        (commitIvkHash_get_spec b.kb₂.hash_eq).choose_spec] at hpm)
    hcoeffs
    (by
      rintro ⟨hl, hr⟩
      obtain ⟨hak, hnk⟩ := hchunks hl
      refine b.projection_ne ?_
      unfold KeyBinding.Pool.Witness.breakProjection
      rw [hak, hnk, hr])

end Zcash.Security.Ledger.Bridge
