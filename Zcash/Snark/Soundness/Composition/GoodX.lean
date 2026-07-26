import Zcash.Snark.Soundness.Multiopen.NodeBinding

/-!
# The chosen committed openings for the concrete squeeze bad set

Fix, per committed group element, one augmented opening `(a, α, β)` with
`commit a + α•u + β•w = C`, and build the pre-`x` bad set from the chosen data.  Any decoded
witness opening the same element either equals the chosen one or collides with it — a nontrivial
`(g, u, w)` relation (`chosenOpening_eq_or_relation`).  This module provides the choice and its
disagreement residue.
-/

namespace Zcash.Snark

open Classical

variable {G : Type*} [AddCommGroup G] [Module Fp G]

open Classical in
/-- The chosen augmented opening of a group element: some `(a, α, β)` with
`commit a + α•u + β•w = C` when one exists, else zeros. -/
noncomputable def chosenOpening (urs : URS G) (C : G) : (Fin (2 ^ urs.k) → Fp) × Fp × Fp :=
  if h : ∃ x : (Fin (2 ^ urs.k) → Fp) × Fp × Fp,
      commit urs x.1 + x.2.1 • urs.u + x.2.2 • urs.w = C then h.choose else (0, 0, 0)

/-- The chosen opening opens `C` whenever some augmented opening exists. -/
theorem chosenOpening_spec (urs : URS G) {C : G}
    (h : ∃ x : (Fin (2 ^ urs.k) → Fp) × Fp × Fp,
      commit urs x.1 + x.2.1 • urs.u + x.2.2 • urs.w = C) :
    commit urs (chosenOpening urs C).1 + (chosenOpening urs C).2.1 • urs.u
      + (chosenOpening urs C).2.2 • urs.w = C := by
  rw [chosenOpening, dif_pos h]
  exact h.choose_spec

/-- **Any augmented opening's witness agrees with the chosen one, or binding breaks.**  Witness
agreement is all the szBadSet receiver needs — the `u`/`w` components never enter the constraint
polynomials. -/
theorem chosenOpening_eq_or_relation (urs : URS G) {C : G}
    {a : Fin (2 ^ urs.k) → Fp} {cu cw : Fp}
    (hopen : commit urs a + cu • urs.u + cw • urs.w = C) :
    a = (chosenOpening urs C).1
    ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  hasNontrivialRelation_of_two_augmented_openings urs
    (hopen.trans (chosenOpening_spec urs ⟨(a, cu, cw), hopen⟩).symm)

/-! ## The decoded-column reroute

A decode's column at a plain-commitment slot opens that pre-`x` commitment, so its witness equals
the chosen opening or binding breaks.  This pins the constraint polynomial before the `x` squeeze,
keyed by the `x`-independent query layout.  Only the vanishing quotient's slot — the reassembled
`Σ hᵢ·(xⁿ)ⁱ`, `x`-dependent through `xⁿ` — is rerouted separately through the pieces. -/

variable [DecidableEq G] [Inhabited G]

/-- **The column reroute at a plain-commitment slot.**  A decoded column at a query committing
the plain pre-`x` point `P` is the chosen opening of `P`, or a nontrivial relation exists. -/
theorem decodedCols_eq_chosenOpening_or_relation {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b a : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      (x4BatchEvals vk instanceCommitment ps ch) a pU pW}
    {i : ℕ} {hi : i < deployedX4PairCount vk instanceCommitment ps ch}
    (md : OpenedMemberDecode urs hk vk instanceCommitment ps ch pbatch i hi)
    (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) {P : G}
    (hP : ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).1
      = CommitmentRef.point P) :
    md.cols m = (chosenOpening urs P).1
    ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine chosenOpening_eq_or_relation urs (C := P) (cu := md.uComp m) (cw := md.wComp m) ?_
  have h := md.commitment m
  rw [hP] at h
  simpa only [CommitmentRef.eval] using h

end Zcash.Snark
