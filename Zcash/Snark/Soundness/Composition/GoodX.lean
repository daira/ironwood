import Zcash.Snark.Soundness.Composition.Capstone

/-!
# The chosen committed openings for the concrete squeeze bad set

The composite's good-challenge term wants a bad set that is a function of the pre-`x` transcript
alone (`badX_le_via_squeeze_factored`), while the supply's szBadSet receiver
(`constraints_supply_derived`) is stated at polynomials decoded from the multiopen rewinds. The
bridge is a *choice*: fix, per committed group element, one augmented opening `(a, α, β)` with
`commit a + α•u + β•w = C`, and build the bad set from the chosen data. Any decoded witness
opening the same element then either equals the chosen one — so the bad set read off the
transcript is the receiver's — or collides with it, a nontrivial `(g, u, w)` relation
(`chosenOpening_eq_or_relation`). This module provides the choice and its disagreement residue.
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

/-- **Any augmented opening's witness agrees with the chosen one, or binding breaks.** The
disagreement residue of reading committed polynomials through the choice: a decoded witness
opening the same element either *is* the chosen witness — the `u`/`w` components never enter the
constraint polynomials, so witness agreement is all the szBadSet receiver needs — or the two
openings collide (`hasNontrivialRelation_of_two_augmented_openings`). -/
theorem chosenOpening_eq_or_relation (urs : URS G) {C : G}
    {a : Fin (2 ^ urs.k) → Fp} {cu cw : Fp}
    (hopen : commit urs a + cu • urs.u + cw • urs.w = C) :
    a = (chosenOpening urs C).1
    ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  hasNontrivialRelation_of_two_augmented_openings urs
    (hopen.trans (chosenOpening_spec urs ⟨(a, cu, cw), hopen⟩).symm)

/-! ## The decoded-column reroute

A member decode's column at a slot backed by a *plain* commitment (`CommitmentRef.point P`, the
form advice/fixed/instance/permutation/lookup queries take — everything but the vanishing
quotient) opens that pre-`x` commitment `P`; the decode's witness therefore equals the chosen
opening of `P`, or binding breaks. This reroutes the szBadSet receiver from the rewind-decoded
columns to the chosen openings of the pre-`x` commitments, keyed by the (`x`-independent) query
layout — the step that pins the constraint polynomial before the `x` squeeze. The vanishing
quotient's slot is backed by the reassembled `Σ hᵢ·(xⁿ)ⁱ` commitment, `x`-dependent through
`xⁿ`, and is rerouted separately through the pieces. -/

variable [DecidableEq G] [Inhabited G]

/-- **The column reroute at a plain-commitment slot.** If member `m` of point set `i`'s decode
sits at a query whose commitment is the plain point `P`, then the decoded column is the chosen
opening of `P`, or a nontrivial relation exists. `P` is a pre-`x` commitment (the advice/fixed/
instance/permutation/lookup commitments are all absorbed before the `x` squeeze). -/
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
