import Zcash.Circuits.Action.Bundle
import Zcash.Circuits.Action.RealBases
import Zcash.Circuits.Specs.Pallas
import Zcash.Security.Ledger.Pool

/-!
# The post-NU6.3 Action-to-ledger refinement boundary

This module is deliberately the only place which translates the extracted Action
circuit witness into the games-facing ledger statement.  In particular, the
Sinsemilla exceptional branches are kept explicit: a circuit witness is not a
ledger action until all three hash openings and the Merkle computation are in
their successful branches.

The Merkle exporter supplies the final raw-encoding path fact.  The small
success-or-break decomposition below is independent of that exporter and is
used by the final refinement theorem once that fact is available.

The Action circuit represents the signed net value by a 64-bit magnitude and a
field element sign (`1` or `-1`).  The ledger statement uses integer
subtraction.  The arithmetic bridges near the top discharge the only subtlety in
passing between those views: the circuit equation lives in `Fp`, so its use at
the ledger layer requires ruling out reduction modulo the Pallas base modulus.
-/

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Circuits.Action.Circuit
open Zcash.Circuits.Specs.Sinsemilla
open Zcash.Security.Concrete
open Zcash.Security.Ledger
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Halo2

/-- A positive 64-bit difference in `Fp` is the corresponding difference in
the integers.  The sum on the right is below `2^65`, hence below the Pallas
base modulus. -/
theorem int_sub_eq_of_fp_sub_eq
    {vOld vNew magnitude : Fp}
    (hvNew : vNew.val < 2 ^ 64)
    (hMagnitude : magnitude.val < 2 ^ 64)
    (h : vOld - vNew = magnitude) :
    (vOld.val : ℤ) - (vNew.val : ℤ) = (magnitude.val : ℤ) := by
  have heq : vOld = vNew + magnitude := sub_eq_iff_eq_add'.mp h
  have hsum : vNew.val + magnitude.val < PALLAS_BASE_CARD := by
    have hp : 2 ^ 64 + 2 ^ 64 < PALLAS_BASE_CARD := by
      norm_num [PALLAS_BASE_CARD]
    omega
  have hcast :
      (vOld.val : Fp) = ((vNew.val + magnitude.val : ℕ) : Fp) := by
    rw [ZMod.natCast_zmod_val, heq, Nat.cast_add, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
  have hv : vOld.val = vNew.val + magnitude.val := by
    calc
      vOld.val = ZMod.val (vOld.val : Fp) := by
        rw [ZMod.val_natCast_of_lt (ZMod.val_lt vOld)]
      _ = ZMod.val ((vNew.val + magnitude.val : ℕ) : Fp) :=
        congrArg ZMod.val hcast
      _ = vNew.val + magnitude.val := ZMod.val_natCast_of_lt hsum
  omega

/-- The signed-magnitude equation enforced by the circuit agrees with the
integer net value consumed by `ActionSatisfied`. -/
theorem signedMagnitude_eq_int_sub
    {vOld vNew magnitude sign : Fp}
    (hvOld : vOld.val < 2 ^ 64)
    (hvNew : vNew.val < 2 ^ 64)
    (hMagnitude : magnitude.val < 2 ^ 64)
    (hSign : sign = 1 ∨ sign = -1)
    (hValue : vOld - vNew = magnitude * sign) :
    ((vOld.val : ℤ) - (vNew.val : ℤ) =
        if sign = 1 then (magnitude.val : ℤ) else -(magnitude.val : ℤ)) := by
  rcases hSign with hpos | hneg
  · subst sign
    simp only [mul_one] at hValue ⊢
    exact int_sub_eq_of_fp_sub_eq hvNew hMagnitude hValue
  · have hnot : sign ≠ 1 := by
      subst sign
      native_decide
    rw [if_neg hnot]
    have hrev : vNew - vOld = magnitude := by
      rw [hneg, mul_neg, mul_one] at hValue
      linear_combination -hValue
    have h := int_sub_eq_of_fp_sub_eq hvOld hMagnitude hrev
    omega

abbrev LedgerWitness :=
  ActionWitness (KeyBinding.Pool.Witness Fq PallasGroup Fp) Fq PallasGroup Fp Fp
    Pool.Encoding 32

/-- Coordinate equality is preserved by the checked affine-to-group adapter. -/
theorem lift_eq_of_point_eq {p q : Point Fp} (hp : p.Valid) (hq : q.Valid)
    (h : p = q) : PallasGroup.ofPoint p hp = PallasGroup.ofPoint q hq := by
  subst q
  rfl

/-- The affine view of the Pallas wrapper is injective. -/
private theorem pallasGroup_ext {p q : PallasGroup}
    (h : PallasGroup.toPoint p = PallasGroup.toPoint q) : p = q := by
  rw [← PallasGroup.ofPoint_toPoint p, ← PallasGroup.ofPoint_toPoint q]
  congr

/-- Translate the Action circuit's natural scalar multiplication into the
ledger wrapper's embedded base-field scalar action. -/
private theorem ofPoint_eq_embed_smul {p q : Point Fp} {s : Fp}
    (hp : p.Valid) (hq : q.Valid) (h : p = s.val • q) :
    PallasGroup.ofPoint p hp =
      PallasGroup.embedFp s • PallasGroup.ofPoint q hq := by
  apply pallasGroup_ext
  simpa only [PallasGroup.toPoint_smul, PallasGroup.toPoint_ofPoint,
    PallasGroup.embedFp_val] using h

/-- The circuit and ledger modules expose the same deployed domain points under
different names.  Keeping these tiny definitional bridges named prevents the
main refinement proof from unfolding their large coordinate literals. -/
private theorem orchard_ivkQ_eq : Pool.ivkQ = orchardBases.ivkQ := rfl
private theorem orchard_noteQ_eq : Pool.noteQ = orchardBases.noteQ := rfl

/-- Transport a successful Action note-commitment hash into the concrete ledger
primitive, after the circuit equation has been normalized to the certified
`noteCommitR.point`. -/
private theorem noteCommit_of_action_hash {gd pkd bp cm : Point Fp}
    {v rho psi : Fp} {rcm : Fq}
    (hgd : gd.OnCurve) (hpkd : pkd.OnCurve) (hcm : cm.Valid)
    (hh : hashToPoint orchardGenerators.S orchardBases.noteQ
      (NoteCommit.noteScalars gd pkd v rho psi).chunks = some bp)
    (heq : cm = bp + rcm.val • Ecc.MulFixed.Certs.noteCommitR.point) :
    Pool.noteCommit rcm
      { gd := PallasGroup.ofPoint gd (.inl hgd),
        pkd := PallasGroup.ofPoint pkd (.inl hpkd),
        v := v.val, ρ := rho, ψ := psi } = some (PallasGroup.ofPoint cm hcm) := by
  refine Pool.noteCommit_eq_some_of_hashToPoint (bp := bp) ?_ heq hcm
  simpa only [Pool.noteHash, Pool.noteScalars, Pool.notePoint,
    PallasGroup.toPoint_ofPoint, ZMod.natCast_zmod_val, orchard_noteQ_eq] using hh

/-- Transport a successful Action `Commit^ivk` hash into the concrete ledger
key-binding hash. -/
private theorem commitIvkHash_of_action_hash {ak nk : Fp} {bp : Point Fp}
    (hbp : hashToPoint orchardGenerators.S orchardBases.ivkQ
      (commitIvkChunks ak.val nk.val) = some bp) :
    Pool.commitIvkHash ak nk = some (PallasGroup.ofPoint bp
      (hashToPoint_valid (Or.inl orchardBases.ivkQ_onCurve)
        (fun _ hm => chunksOf_mem_lt hm) hbp)) := by
  apply Pool.commitIvkHash_eq_some_of_hashToPoint
  rw [orchard_ivkQ_eq]
  exact hbp

/-- The circuit's randomized-key public coordinates are the affine view of the
concrete ledger randomization. -/
theorem public_rk_eq_randomizePublic {wit : ActionData}
    (hak : wit.akP.OnCurve)
    (h : ({ x := wit.rkX, y := wit.rkY } : Point Fp) =
      wit.alpha.2 • orchardBases.spendAuthG + wit.akP) :
    PallasGroup.toPoint
      (Pool.primitives.randomizePublic wit.alpha.2
        (PallasGroup.ofPoint wit.akP (.inl hak))) =
      ({ x := wit.rkX, y := wit.rkY } : Point Fp) := by
  change PallasGroup.toPoint
      (Pool.randomizePublic wit.alpha.2
        (PallasGroup.ofPoint wit.akP (.inl hak))) =
      ({ x := wit.rkX, y := wit.rkY } : Point Fp)
  simpa [Pool.randomizePublic, orchardBases,
    Ecc.MulFixed.FixedBase.scalarMul] using h.symm

/-- The circuit's signed-magnitude value-commitment equation has the same
affine public coordinates as the ledger's integer-valued commitment.  The
64-bit bounds are precisely what make the field subtraction no-wrap. -/
theorem public_cv_net_eq_valueCommit {wit : ActionData}
    (hvOld : wit.vOld.val < 2 ^ 64) (hvNew : wit.vNew.val < 2 ^ 64)
    (hmag : wit.magnitude.val < 2 ^ 64)
    (hvalue : wit.vOld - wit.vNew = wit.magnitude * wit.sign)
    (hcv :
      (wit.sign = 1 ∧ ({ x := wit.cvX, y := wit.cvY } : Point Fp) =
        (wit.magnitude.val : Fq) • orchardBases.valueCommitV +
          wit.rcv.2 • orchardBases.valueCommitR) ∨
      (wit.sign = -1 ∧ ({ x := wit.cvX, y := wit.cvY } : Point Fp) =
        -(wit.magnitude.val : Fq) • orchardBases.valueCommitV +
          wit.rcv.2 • orchardBases.valueCommitR)) :
    PallasGroup.toPoint
      (Pool.primitives.valueCommit
        ((wit.vOld.val : ℤ) - (wit.vNew.val : ℤ)) wit.rcv.2) =
      ({ x := wit.cvX, y := wit.cvY } : Point Fp) := by
  change PallasGroup.toPoint
      (Pool.valueCommit ((wit.vOld.val : ℤ) - (wit.vNew.val : ℤ)) wit.rcv.2) =
      ({ x := wit.cvX, y := wit.cvY } : Point Fp)
  rcases hcv with ⟨hsign, hcv⟩ | ⟨hsign, hcv⟩
  · have hdiff : (wit.vOld.val : ℤ) - (wit.vNew.val : ℤ) =
        (wit.magnitude.val : ℤ) := by
      simpa [hsign] using
        signedMagnitude_eq_int_sub hvOld hvNew hmag
          (Or.inl hsign) hvalue
    rw [Pool.toPoint_valueCommit, hdiff]
    simpa [Pool.intScalar, orchardBases,
      Ecc.MulFixed.Short.FixedBase.scalarMul,
      Ecc.MulFixed.FixedBase.scalarMul] using hcv.symm
  · have hdiff : (wit.vOld.val : ℤ) - (wit.vNew.val : ℤ) =
        -(wit.magnitude.val : ℤ) := by
      simpa [hsign] using
        signedMagnitude_eq_int_sub hvOld hvNew hmag
          (Or.inr hsign) hvalue
    rw [Pool.toPoint_valueCommit, hdiff]
    simpa [Pool.intScalar, orchardBases,
      Ecc.MulFixed.Short.FixedBase.scalarMul,
      Ecc.MulFixed.FixedBase.scalarMul] using hcv.symm

/-- The canonical data-preserving Merkle contract, specialized to the exact
`ActionData` exports.  Its raw inputs intentionally remain natural-number
encodings, so a noncanonical 255-bit child is never reduced prematurely. -/
abbrev ExactMerklePathData (wit : ActionData) (root : Fp) : Prop :=
  Sinsemilla.Merkle.ExactMerklePathData orchardGenerators orchardBases.merkleQ 0 32
    wit.cmOld.x root
    (merkleLeftEncoding wit) (merkleRightEncoding wit) (merkleSide wit)

private theorem merkleLeftEncoding_fin (wit : ActionData) (i : Fin 32) :
    merkleLeftEncoding wit i.1 = wit.leftEncoding i := by
  simp [merkleLeftEncoding]

private theorem merkleRightEncoding_fin (wit : ActionData) (i : Fin 32) :
    merkleRightEncoding wit i.1 = wit.rightEncoding i := by
  simp [merkleRightEncoding]

private theorem merkleSide_fin (wit : ActionData) (i : Fin 32) :
    merkleSide wit i.1 = wit.merkleSide i := by
  simp [merkleSide]

/-- The five public values consumed by the ledger games are exactly the corresponding
Action primary inputs.  The enable rows deliberately do not occur in the ledger
instance. -/
def PublicProjection (wit : ActionData) (inst : ActionInstance PallasGroup Fp Fp Fp) : Prop :=
  inst.rt = wit.anchor ∧
  inst.nf_old = wit.nfOld ∧
  PallasGroup.toPoint inst.rk = ({ x := wit.rkX, y := wit.rkY } : Point Fp) ∧
  PallasGroup.toPoint inst.cv_net = ({ x := wit.cvX, y := wit.cvY } : Point Fp) ∧
  inst.cmx_new = wit.cmx

/-- Preserve the post-NU6.3 cross-address gate with its actual field semantics:
every nonzero value of `disableCrossAddress`, not merely the value one, activates
the address equality. -/
def CrossAddressSatisfied (wit : ActionData) (w : LedgerWitness) : Prop :=
  wit.disableCrossAddress ≠ 0 →
    w.note_old.gd = w.note_new.gd ∧ w.note_old.pkd = w.note_new.pkd

/-- The spend/output enable gates, preserved with their exact circuit semantics: a
disabled flag (any value other than one) forces the corresponding note value to zero. -/
def EnableFlagsSatisfied (wit : ActionData) (w : LedgerWitness) : Prop :=
  (w.note_old.v ≠ 0 → wit.enableSpend = 1) ∧
  (w.note_new.v ≠ 0 → wit.enableOutput = 1)

/-- The four circuit-facing exceptional outcomes, each tied to the witness's own
exact Sinsemilla hash query via a `hashToPointB … = .inr br` equation.  These are
proposition-valued on purpose: `SpecPost` retains the Merkle result propositionally,
so it cannot in general be eliminated into a computational `Type` witness. -/
inductive ActionBreak (wit : ActionData) : Prop
  | commitIvk (br : BreakData) :
      hashToPointB orchardGenerators.S orchardBases.ivkQ
          (commitIvkChunks wit.akP.x.val wit.nk.val) = .inr br →
      ValidBreak orchardGenerators.S orchardBases.ivkQ br → ActionBreak wit
  | noteCommitOld (br : BreakData) :
      hashToPointB orchardGenerators.S orchardBases.noteQ
          (NoteCommit.noteScalars wit.gdOld wit.pkdOld wit.vOld wit.rhoOld wit.psiOld).chunks
        = .inr br →
      ValidBreak orchardGenerators.S orchardBases.noteQ br → ActionBreak wit
  | noteCommitNew (br : BreakData) :
      hashToPointB orchardGenerators.S orchardBases.noteQ
          (NoteCommit.noteScalars wit.gdNew wit.pkdNew wit.vNew wit.nfOld wit.psiNew).chunks
        = .inr br →
      ValidBreak orchardGenerators.S orchardBases.noteQ br → ActionBreak wit
  | merkle (i : Fin 32) (br : BreakData) :
      hashToPointB orchardGenerators.S orchardBases.merkleQ
          (merkleChunks i.1 (wit.leftEncoding i) (wit.rightEncoding i)) = .inr br →
      ValidBreak orchardGenerators.S orchardBases.merkleQ br → ActionBreak wit

private theorem merkle_chunk_onCurve {i lv rv m : ℕ}
    (hm : m ∈ merkleChunks i lv rv) : (orchardGenerators.S m).OnCurve := by
  apply orchardGenerators.S_onCurve
  simp only [merkleChunks, List.mem_map, List.mem_range] at hm
  obtain ⟨j, -, rfl⟩ := hm
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Package an exact raw-encoding Merkle escape in the circuit-facing break
vocabulary.  The `hashToPointB` equation certifies that this is the escape of the
exact witness query, exactly as for the three note/key openings. -/
theorem merkle_break_of_inr {wit : ActionData} (i : Fin 32) (br : BreakData)
    (hb : hashToPointB orchardGenerators.S orchardBases.merkleQ
      (merkleChunks i.1 (wit.leftEncoding i) (wit.rightEncoding i)) = .inr br) :
    ActionBreak wit :=
  .merkle i br hb
    (validBreak_of_inr (Or.inl orchardBases.merkleQ_onCurve)
      (fun _ hm => merkle_chunk_onCurve hm) hb)

/-- Splitting the exact raw queries either leaves every Merkle layer defined or
exhibits its first exceptional hash evaluation. -/
theorem exactMerkle_hashes_or_break {wit : ActionData} {root : Fp}
    (hpath : ExactMerklePathData wit root) :
    (∀ i : Fin 32, ∃ B, hashToPoint orchardGenerators.S orchardBases.merkleQ
      (merkleChunks i.1 (wit.leftEncoding i) (wit.rightEncoding i)) = some B) ∨
      ActionBreak wit := by
  classical
  by_cases hall : ∀ i : Fin 32, ∃ B, hashToPoint orchardGenerators.S orchardBases.merkleQ
      (merkleChunks i.1 (wit.leftEncoding i) (wit.rightEncoding i)) = some B
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    obtain ⟨_, _, _, _⟩ := hpath
    cases hb : hashToPointB orchardGenerators.S orchardBases.merkleQ
        (merkleChunks i.1 (wit.leftEncoding i) (wit.rightEncoding i)) with
    | inl B => exact False.elim (hi B (hashToPointB_inl hb))
    | inr br => exact merkle_break_of_inr i br hb

/-- Successful `Commit^ivk` information obtained by choosing the left branch of its
`SpecOrBreak` clause. -/
def CommitIvkSuccess (wit : ActionData) : Prop :=
  ∃ ivk : Fp, ∃ hashPoint : Point Fp,
    hashToPoint orchardGenerators.S orchardBases.ivkQ
      (commitIvkChunks wit.akP.x.val wit.nk.val) = some hashPoint ∧
    ivk = (hashPoint + wit.rivk.2 • orchardBases.commitIvkR).x ∧
    wit.pkdOld = ivk.val • wit.gdOld

/-- The successful incoming viewing key cannot be zero.  This is a circuit fact,
not an additional ledger assumption: the address-integrity equation would otherwise
make the witnessed, on-curve `pkdOld` the affine identity sentinel. -/
theorem CommitIvkSuccess.ivk_ne {wit : ActionData} {ivk : Fp}
    (hpkd : wit.pkdOld.OnCurve)
    (h : ∃ hashPoint : Point Fp,
      hashToPoint orchardGenerators.S orchardBases.ivkQ
        (commitIvkChunks wit.akP.x.val wit.nk.val) = some hashPoint ∧
      ivk = (hashPoint + wit.rivk.2 • orchardBases.commitIvkR).x ∧
      wit.pkdOld = ivk.val • wit.gdOld) : ivk ≠ 0 := by
  rcases h with ⟨_, _, _, hpkdEq⟩
  intro hiz
  have hval : ivk.val = 0 := by simp [hiz]
  have hzero : wit.pkdOld = 0 := by
    rw [hpkdEq, hval]
    rfl
  exact Point.ne_zero_of_onCurve hpkd hzero

/-- Convert the successful `Commit^ivk` branch into the exact deployed Orchard
key-binding witness used by the ledger statement.  The returned equations keep
the affine Action points available in their Pallas-wrapper form for the final
address and spend-authority fields. -/
theorem commitIvkSuccess_to_ledger {wit : ActionData}
    (hgd : wit.gdOld.OnCurve) (hak : wit.akP.OnCurve)
    (hpkd : wit.pkdOld.OnCurve) (h : CommitIvkSuccess wit) :
    ∃ (ivk : Fp) (kw : KeyBinding.Pool.Witness Fq PallasGroup Fp),
      Pool.keyBinding.KB kw ∧
      Pool.keyBinding.ivk kw ≠ 0 ∧
      Pool.keyBinding.ivk kw = ivk ∧
      Pool.keyBinding.nk kw = wit.nk ∧
      Pool.keyBinding.akP kw = PallasGroup.ofPoint wit.akP (.inl hak) ∧
      PallasGroup.ofPoint wit.pkdOld (.inl hpkd) =
        PallasGroup.embedFp (Pool.keyBinding.ivk kw) •
          PallasGroup.ofPoint wit.gdOld (.inl hgd) := by
  rcases h with ⟨ivk, bp, hbp, hivk, hpkdEq⟩
  have hbpValid : bp.Valid :=
    hashToPoint_valid (Or.inl orchardBases.ivkQ_onCurve)
      (fun _ hm => chunksOf_mem_lt hm) hbp
  let kw : KeyBinding.Pool.Witness Fq PallasGroup Fp :=
    { ivk := ivk,
      akP := PallasGroup.ofPoint wit.akP (.inl hak),
      nk := wit.nk,
      rivk := wit.rivk.2,
      hashPoint := PallasGroup.ofPoint bp hbpValid }
  have hivk' : ivk =
      (bp + wit.rivk.2.val • Ecc.MulFixed.Certs.commitIvkR.point).x := by
    simpa [orchardBases, Ecc.MulFixed.FixedBase.scalarMul] using hivk
  have hkb : Pool.keyBinding.KB kw := by
    change KeyBinding.Pool.KB Pool.extract Pool.commitIvkHash
      (PallasGroup.ofPoint Ecc.MulFixed.Certs.commitIvkR.point
        (Or.inl Ecc.MulFixed.Certs.commitIvkR.onCurve)) kw
    refine ⟨?_, ?_, ?_⟩
    · dsimp [kw]
      exact commitIvkHash_of_action_hash hbp
    · dsimp [kw]
      simpa only [Pool.extract, PallasGroup.toPoint_add,
        PallasGroup.toPoint_smul, PallasGroup.toPoint_nsmul,
        PallasGroup.toPoint_ofPoint] using hivk'
    · dsimp [kw]
      apply CommitIvkSuccess.ivk_ne hpkd
      exact ⟨bp, hbp, hivk, hpkdEq⟩
  refine ⟨ivk, kw, hkb, hkb.ivk_ne, rfl, rfl, rfl, ?_⟩
  · exact ofPoint_eq_embed_smul (.inl hpkd) (.inl hgd) hpkdEq

/-- Successful old-note Sinsemilla opening. -/
def NoteCommitOldSuccess (wit : ActionData) : Prop :=
  ∃ hashPoint : Point Fp,
    hashToPoint orchardGenerators.S orchardBases.noteQ
      (NoteCommit.noteScalars wit.gdOld wit.pkdOld wit.vOld wit.rhoOld wit.psiOld).chunks
        = some hashPoint ∧
    wit.cmOld = hashPoint + wit.rcmOld.2 • orchardBases.noteCommitR

/-- Successful new-note Sinsemilla opening. -/
def NoteCommitNewSuccess (wit : ActionData) : Prop :=
  ∃ hashPoint : Point Fp,
    hashToPoint orchardGenerators.S orchardBases.noteQ
      (NoteCommit.noteScalars wit.gdNew wit.pkdNew wit.vNew wit.nfOld wit.psiNew).chunks
        = some hashPoint ∧
    wit.cmx = (hashPoint + wit.rcmNew.2 • orchardBases.noteCommitR).x

/-- Turn the successful output-note opening retained by the Action statement
into the concrete ledger commitment.  Unlike the circuit public input, the
ledger keeps the full commitment point; this lemma supplies that point together
with the coordinate equation used for `cmx_new_eq`. -/
theorem noteCommitNewSuccess_to_ledger {wit : ActionData}
    (hgd : wit.gdNew.OnCurve) (hpkd : wit.pkdNew.OnCurve)
    (h : NoteCommitNewSuccess wit) :
    ∃ (cmNewP : Point Fp) (hcmNewP : cmNewP.Valid),
      cmNewP.x = wit.cmx ∧
      Pool.primitives.noteCommit wit.rcmNew.2
        { gd := PallasGroup.ofPoint wit.gdNew (.inl hgd),
          pkd := PallasGroup.ofPoint wit.pkdNew (.inl hpkd),
          v := wit.vNew.val, ρ := wit.nfOld, ψ := wit.psiNew } =
        some (PallasGroup.ofPoint cmNewP hcmNewP) := by
  rcases h with ⟨bp, hbp, hcmx⟩
  have hbpValid : bp.Valid :=
    hashToPoint_valid (Or.inl orchardBases.noteQ_onCurve)
      (fun _ hm => chunksOf_mem_lt hm) hbp
  let cmNewP : Point Fp :=
    bp + wit.rcmNew.2.val • Ecc.MulFixed.Certs.noteCommitR.point
  have hcmNewP : cmNewP.Valid := by
    dsimp [cmNewP]
    exact Point.valid_add hbpValid
      (Point.valid_nsmul (Or.inl Ecc.MulFixed.Certs.noteCommitR.onCurve) _)
  refine ⟨cmNewP, hcmNewP, ?_, ?_⟩
  · simpa [cmNewP, orchardBases, Ecc.MulFixed.FixedBase.scalarMul] using hcmx.symm
  · change Pool.noteCommit wit.rcmNew.2
      { gd := PallasGroup.ofPoint wit.gdNew (.inl hgd),
        pkd := PallasGroup.ofPoint wit.pkdNew (.inl hpkd),
        v := wit.vNew.val, ρ := wit.nfOld, ψ := wit.psiNew } =
        some (PallasGroup.ofPoint cmNewP hcmNewP)
    apply noteCommit_of_action_hash hgd hpkd hcmNewP hbp
    rfl

/-- The successful Merkle outcome as consumed by the ledger refinement: the exact
raw-encoding path together with every layer's hash landing in its defined branch,
and the dummy-spend anchor gate.  The raw child encodings are tied to these defined
hashes before any `Merkle.Path` is constructed. -/
def MerkleSuccess (wit : ActionData) : Prop :=
  ∃ root : Fp,
    ExactMerklePathData wit root ∧
    (∀ i : Fin 32, ∃ B, hashToPoint orchardGenerators.S orchardBases.merkleQ
      (merkleChunks i.1 (wit.leftEncoding i) (wit.rightEncoding i)) = some B) ∧
    wit.vOld * (root - wit.anchor) = 0

theorem commitIvk_success_or_break {wit : ActionData} {input : Value PrivateInputs Fp}
    (h : SpecPost orchardGenerators orchardBases input () wit) :
    CommitIvkSuccess wit ∨ ActionBreak wit := by
  rcases h.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, ⟨ivk, hivk, hpkd⟩,
    _, _, _, _, _, _⟩
  cases hb : hashToPointB orchardGenerators.S orchardBases.ivkQ
      (commitIvkChunks wit.akP.x.val wit.nk.val) with
  | inl bp =>
    left
    refine ⟨ivk, bp, ?_, ?_, hpkd⟩
    · exact hashToPointB_inl hb
    · simpa only [SpecOrBreak, hb] using hivk
  | inr br =>
    right
    exact .commitIvk br hb (by simpa only [SpecOrBreak, hb] using hivk)

theorem noteCommitOld_success_or_break {wit : ActionData} {input : Value PrivateInputs Fp}
    (h : SpecPost orchardGenerators orchardBases input () wit) :
    NoteCommitOldSuccess wit ∨ ActionBreak wit := by
  rcases h.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hold, _, _, _, _, _⟩
  cases hb : hashToPointB orchardGenerators.S orchardBases.noteQ
      (NoteCommit.noteScalars wit.gdOld wit.pkdOld wit.vOld wit.rhoOld wit.psiOld).chunks with
  | inl bp =>
    left
    exact ⟨bp, hashToPointB_inl hb, by simpa only [SpecOrBreak, hb] using hold⟩
  | inr br =>
    right
    exact .noteCommitOld br hb (by simpa only [SpecOrBreak, hb] using hold)

theorem noteCommitNew_success_or_break {wit : ActionData} {input : Value PrivateInputs Fp}
    (h : SpecPost orchardGenerators orchardBases input () wit) :
    NoteCommitNewSuccess wit ∨ ActionBreak wit := by
  rcases h.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hnew, _, _, _, _⟩
  cases hb : hashToPointB orchardGenerators.S orchardBases.noteQ
      (NoteCommit.noteScalars wit.gdNew wit.pkdNew wit.vNew wit.nfOld wit.psiNew).chunks with
  | inl bp =>
    left
    exact ⟨bp, hashToPointB_inl hb, by simpa only [SpecOrBreak, hb] using hnew⟩
  | inr br =>
    right
    exact .noteCommitNew br hb (by simpa only [SpecOrBreak, hb] using hnew)

theorem merkle_success_or_break {wit : ActionData} {input : Value PrivateInputs Fp}
    (h : SpecPost orchardGenerators orchardBases input () wit) :
    MerkleSuccess wit ∨ ActionBreak wit := by
  rcases h.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨root, -, -, hexact, hanchor⟩,
    _, _, _⟩
  rcases exactMerkle_hashes_or_break hexact with hhash | hbreak
  · exact Or.inl ⟨root, hexact, hhash, hanchor⟩
  · exact Or.inr hbreak

/-- Split all four exceptional sites in the circuit statement at once. -/
theorem successes_or_break {wit : ActionData} {input : Value PrivateInputs Fp}
    (h : SpecPost orchardGenerators orchardBases input () wit) :
    (CommitIvkSuccess wit ∧ NoteCommitOldSuccess wit ∧ NoteCommitNewSuccess wit ∧
      MerkleSuccess wit) ∨ ActionBreak wit := by
  rcases commitIvk_success_or_break h with hci | hbr
  · rcases noteCommitOld_success_or_break h with hco | hbr
    · rcases noteCommitNew_success_or_break h with hcn | hbr
      · rcases merkle_success_or_break h with hm | hbr
        · exact Or.inl ⟨hci, hco, hcn, hm⟩
        · exact Or.inr hbr
      · exact Or.inr hbr
    · exact Or.inr hbr
  · exact Or.inr hbr

/-- If the caller rules out all four exhibited exceptional cases, the circuit's
breaks-as-data clauses reduce to their successful openings.  The exact-Merkle
export subsequently turns the final component into a ledger `Merkle.Path`. -/
theorem successes_of_noBreak {wit : ActionData} {input : Value PrivateInputs Fp}
    (h : SpecPost orchardGenerators orchardBases input () wit)
    (hno : ¬ ActionBreak wit) :
    CommitIvkSuccess wit ∧ NoteCommitOldSuccess wit ∧ NoteCommitNewSuccess wit ∧
      MerkleSuccess wit :=
  (successes_or_break h).resolve_right hno

/-- An exact, escape-free circuit Merkle chain yields the ledger's raw
authentication path.  The raw encodings are retained verbatim: the only
conversion is the ledger decoder from a bounded 255-bit representative to its
field element. -/
theorem merkle_path_of_exact {wit : ActionData} {root : Fp}
    (hpath : ExactMerklePathData wit root)
    (hhash : ∀ i : Fin 32, ∃ B,
      hashToPoint orchardGenerators.S orchardBases.merkleQ
        (merkleChunks i.1 (wit.leftEncoding i) (wit.rightEncoding i)) = some B) :
    Merkle.Path Pool.merkle wit.cmOld.x root
      (fun i : Fin 32 =>
        (⟨wit.leftEncoding i, by
            rcases hpath with ⟨_, _, _, hsteps⟩
            simpa only [merkleLeftEncoding_fin] using (hsteps i i.isLt).1⟩,
         ⟨wit.rightEncoding i, by
            rcases hpath with ⟨_, _, _, hsteps⟩
            simpa only [merkleRightEncoding_fin] using (hsteps i i.isLt).2.1⟩))
      wit.merkleSide := by
  rcases hpath with ⟨nodes, hstart, hroot, hsteps⟩
  unfold Pool.merkle
  constructor
  · intro i
    rcases i with ⟨i, hi⟩
    cases i with
    | zero =>
      change 0 < 32 at hi
      let k : Fin 32 := ⟨0, hi⟩
      have hleft : merkleLeftEncoding wit 0 = wit.leftEncoding k :=
        merkleLeftEncoding_fin wit k
      have hright : merkleRightEncoding wit 0 = wit.rightEncoding k :=
        merkleRightEncoding_fin wit k
      have hs := hsteps 0 (by omega)
      cases hside : wit.merkleSide k with
      | false =>
        have hside' : merkleSide wit 0 = false :=
          (merkleSide_fin wit k).trans hside
        -- Layer 0's running node is `some leaf`; the selected raw child decodes to it.
        change some wit.cmOld.x = some (wit.leftEncoding k : Fp)
        have hE : (wit.leftEncoding k : Fp) = wit.cmOld.x := by
          calc
            _ = nodes 0 := by simpa [hleft, hright, hside'] using hs.2.2.1
            _ = _ := hstart
        exact congrArg some hE.symm
      | true =>
        have hside' : merkleSide wit 0 = true :=
          (merkleSide_fin wit k).trans hside
        change some wit.cmOld.x = some (wit.rightEncoding k : Fp)
        have hE : (wit.rightEncoding k : Fp) = wit.cmOld.x := by
          calc
            _ = nodes 0 := by simpa [hleft, hright, hside'] using hs.2.2.1
            _ = _ := hstart
        exact congrArg some hE.symm
    | succ j =>
      change j + 1 < 32 at hi
      have hj : j < 32 := by omega
      let k : Fin 32 := ⟨j, hj⟩
      let k' : Fin 32 := ⟨j + 1, hi⟩
      have hleft : merkleLeftEncoding wit j = wit.leftEncoding k :=
        merkleLeftEncoding_fin wit k
      have hright : merkleRightEncoding wit j = wit.rightEncoding k :=
        merkleRightEncoding_fin wit k
      have hleft' : merkleLeftEncoding wit (j + 1) = wit.leftEncoding k' :=
        merkleLeftEncoding_fin wit k'
      have hright' : merkleRightEncoding wit (j + 1) = wit.rightEncoding k' :=
        merkleRightEncoding_fin wit k'
      have hcurr := hsteps (j + 1) hi
      obtain ⟨B, hB⟩ := hhash k
      have hprev := (hsteps j hj).2.2.2 B (by
        simpa [hleft, hright] using hB)
      -- The compression producing the running node at layer `j+1` succeeds with `some B.x`.
      have hcomp : Pool.merkleCompress k
          (⟨wit.leftEncoding k, by simpa [hleft] using (hsteps j hj).1⟩,
           ⟨wit.rightEncoding k, by simpa [hright] using (hsteps j hj).2.1⟩) = some B.x :=
        Pool.merkleCompress_eq_of_hashToPoint (by
          simpa [k, orchardBases, Zcash.Circuits.Action.merkleQ,
            Pool.merkleQ] using hB)
      cases hside : wit.merkleSide k' with
      | false =>
        have hside' : merkleSide wit (j + 1) = false :=
          (merkleSide_fin wit k').trans hside
        change Pool.merkleCompress k
          (⟨wit.leftEncoding k, by simpa [hleft] using (hsteps j hj).1⟩,
           ⟨wit.rightEncoding k, by simpa [hright] using (hsteps j hj).2.1⟩) =
            some (wit.leftEncoding k' : Fp)
        calc
          _ = some B.x := hcomp
          _ = some (nodes (j + 1)) := congrArg some hprev.symm
          _ = some (wit.leftEncoding k' : Fp) := by
            have he : (wit.leftEncoding k' : Fp) = nodes (j + 1) := by
              simpa [hleft', hright', hside'] using hcurr.2.2.1
            rw [he]
      | true =>
        have hside' : merkleSide wit (j + 1) = true :=
          (merkleSide_fin wit k').trans hside
        change Pool.merkleCompress k
          (⟨wit.leftEncoding k, by simpa [hleft] using (hsteps j hj).1⟩,
           ⟨wit.rightEncoding k, by simpa [hright] using (hsteps j hj).2.1⟩) =
            some (wit.rightEncoding k' : Fp)
        calc
          _ = some B.x := hcomp
          _ = some (nodes (j + 1)) := congrArg some hprev.symm
          _ = some (wit.rightEncoding k' : Fp) := by
            have he : (wit.rightEncoding k' : Fp) = nodes (j + 1) := by
              simpa [hleft', hright', hside'] using hcurr.2.2.1
            rw [he]
  · let k : Fin 32 := ⟨31, by omega⟩
    have hleft : merkleLeftEncoding wit 31 = wit.leftEncoding k :=
      merkleLeftEncoding_fin wit k
    have hright : merkleRightEncoding wit 31 = wit.rightEncoding k :=
      merkleRightEncoding_fin wit k
    -- The final compression yields the root, in its defined branch.
    change Pool.merkleCompress k
      (⟨wit.leftEncoding k, by simpa [hleft] using (hsteps 31 (by omega)).1⟩,
       ⟨wit.rightEncoding k, by simpa [hright] using (hsteps 31 (by omega)).2.1⟩) = some root
    obtain ⟨B, hB⟩ := hhash k
    have hnext := (hsteps 31 (by omega)).2.2.2 B (by
      simpa [hleft, hright] using hB)
    have hcomp : Pool.merkleCompress k
        (⟨wit.leftEncoding k, by simpa [hleft] using (hsteps 31 (by omega)).1⟩,
         ⟨wit.rightEncoding k, by simpa [hright] using (hsteps 31 (by omega)).2.1⟩) = some B.x :=
      Pool.merkleCompress_eq_of_hashToPoint (by
        simpa [k, orchardBases, Zcash.Circuits.Action.merkleQ,
          Pool.merkleQ] using hB)
    calc
      _ = some B.x := hcomp
      _ = some (nodes 32) := congrArg some hnext.symm
      _ = some root := congrArg some hroot

/-- The Action postcondition refines to either one of its explicitly exhibited
Sinsemilla escapes or a fully satisfied concrete Orchard ledger action.  The ledger
alternative additionally reports the spend/output enable gates as a side fact
(`EnableFlagsSatisfied`), with their exact circuit semantics. -/
theorem specPost_to_ledger {input : Halo2.Value PrivateInputs Fp} {wit : ActionData}
    (h : SpecPost orchardGenerators orchardBases input () wit) :
    ActionBreak wit ∨
      ∃ inst w, PublicProjection wit inst ∧
        ActionSatisfied Pool.primitives Pool.keyBinding inst w ∧
        CrossAddressSatisfied wit w ∧
        EnableFlagsSatisfied wit w := by
  rcases successes_or_break h with hs | hbreak
  · rcases hs with ⟨hivk, hold, hnew, hmerkle⟩
    rcases hmerkle with ⟨root, hpath, hhash, hanchor⟩
    rcases h.1 with ⟨hcmOld, hgdOld, hakP, hpkdOld, hgdNew, hpkdNew,
      hvOld, hvNew, hvc, hnf, hrk, -, -, -, -, hvalue, hes, heo⟩
    rcases hvc with ⟨hmag, hcv⟩
    rcases hold with ⟨bold, hbold, hcmOldEq⟩
    rcases commitIvkSuccess_to_ledger hgdOld hakP hpkdOld hivk with
      ⟨ivk, kw, hkb, hivne, hkwivk, hkwNk, hkwAk, hpkdLedger⟩
    have hkwNk' : kw.nk = wit.nk := hkwNk
    rcases noteCommitNewSuccess_to_ledger hgdNew hpkdNew hnew with
      ⟨cmNewP, hcmNewP, hcmNewX, hcommitNew⟩
    have hcmOldEq' : wit.cmOld =
        bold + wit.rcmOld.2.val • Ecc.MulFixed.Certs.noteCommitR.point := by
      simpa [orchardBases, Ecc.MulFixed.FixedBase.scalarMul] using hcmOldEq
    have hnf' : wit.nfOld =
        (wit.cmOld +
          ((Poseidon.Hash.ConstantLength.value #v[wit.nk, wit.rhoOld] +
            wit.psiOld).val : Fq).val •
            Ecc.MulFixed.Certs.nullifierK.point).x := by
      simpa [orchardBases, Ecc.MulFixed.FixedBase.scalarMul] using hnf
    have hcommitOld : Pool.noteCommit wit.rcmOld.2
        { gd := PallasGroup.ofPoint wit.gdOld (.inl hgdOld),
          pkd := PallasGroup.ofPoint wit.pkdOld (.inl hpkdOld),
          v := wit.vOld.val, ρ := wit.rhoOld, ψ := wit.psiOld } =
        some (PallasGroup.ofPoint wit.cmOld hcmOld) :=
      noteCommit_of_action_hash hgdOld hpkdOld hcmOld hbold hcmOldEq'
    let path : Fin 32 → Pool.Encoding × Pool.Encoding := fun i =>
      (⟨wit.leftEncoding i, by
          rcases hpath with ⟨_, _, _, hsteps⟩
          simpa only [merkleLeftEncoding_fin] using (hsteps i i.isLt).1⟩,
       ⟨wit.rightEncoding i, by
          rcases hpath with ⟨_, _, _, hsteps⟩
          simpa only [merkleRightEncoding_fin] using (hsteps i i.isLt).2.1⟩)
    let inst : ActionInstance PallasGroup Fp Fp Fp :=
      { rt := wit.anchor,
        nf_old := wit.nfOld,
        rk := Pool.primitives.randomizePublic wit.alpha.2
          (PallasGroup.ofPoint wit.akP (.inl hakP)),
        cv_net := Pool.primitives.valueCommit
          ((wit.vOld.val : ℤ) - (wit.vNew.val : ℤ)) wit.rcv.2,
        cmx_new := wit.cmx }
    let w : LedgerWitness :=
      { path := path,
        side := wit.merkleSide,
        note_old :=
          { gd := PallasGroup.ofPoint wit.gdOld (.inl hgdOld),
            pkd := PallasGroup.ofPoint wit.pkdOld (.inl hpkdOld),
            v := wit.vOld.val, ρ := wit.rhoOld, ψ := wit.psiOld },
        note_new :=
          { gd := PallasGroup.ofPoint wit.gdNew (.inl hgdNew),
            pkd := PallasGroup.ofPoint wit.pkdNew (.inl hpkdNew),
            v := wit.vNew.val, ρ := wit.nfOld, ψ := wit.psiNew },
        cm_old := PallasGroup.ofPoint wit.cmOld hcmOld,
        cm_new := PallasGroup.ofPoint cmNewP hcmNewP,
        kw := kw,
        α := wit.alpha.2,
        rcv := wit.rcv.2,
        rcm_old := wit.rcmOld.2,
        rcm_new := wit.rcmNew.2 }
    refine Or.inr ⟨inst, w, ?_, ?_, ?_, ?_⟩
    · refine ⟨rfl, rfl, ?_, ?_, rfl⟩
      · simpa [inst] using public_rk_eq_randomizePublic hakP hrk
      · simpa [inst] using public_cv_net_eq_valueCommit hvOld hvNew hmag hvalue hcv
    · refine
        { commit_old := ?_,
          merkle_path := ?_,
          nf_old_eq := ?_,
          key_binding := ?_,
          pkd_eq := ?_,
          gd_ne := ?_,
          rk_eq := ?_,
          commit_new := ?_,
          cmx_new_eq := ?_,
          ρ_new_eq := ?_,
          v_old_lt := ?_,
          v_new_lt := ?_,
          cv_net_eq := ?_ }
      · simpa [w] using hcommitOld
      · intro hv
        have hv' : wit.vOld ≠ 0 := by
          intro hz
          apply hv
          dsimp [w]
          simp [hz]
        have hroot : root = wit.anchor := by
          have hz : root - wit.anchor = 0 :=
            (mul_eq_zero.mp hanchor).resolve_left hv'
          exact sub_eq_zero.mp hz
        have hp := merkle_path_of_exact hpath hhash
        simpa [w, inst, path, Pool.leafOf, Pool.extract, hroot] using hp
      · simpa [inst, w, Pool.primitives, Pool.keyBinding,
          KeyBinding.Pool.toInterface, hkwNk', Pool.deriveNullifier] using hnf'
      · simpa [w] using hkb
      · simpa [w, Pool.primitives, hkwivk] using hpkdLedger
      · intro hzero
        have hpzero : wit.gdOld = 0 := by
          have hz := congrArg PallasGroup.toPoint hzero
          simpa [w] using hz
        exact Point.ne_zero_of_onCurve hgdOld hpzero
      · change Pool.primitives.randomizePublic wit.alpha.2
            (PallasGroup.ofPoint wit.akP (.inl hakP)) =
          Pool.primitives.randomizePublic wit.alpha.2
            (Pool.keyBinding.akP kw)
        rw [hkwAk]
      · simpa [w] using hcommitNew
      · change wit.cmx = cmNewP.x
        exact hcmNewX.symm
      · rfl
      · exact hvOld
      · exact hvNew
      · rfl
    · intro henabled
      rcases h.2 henabled with ⟨hgd, hpkd⟩
      change
        PallasGroup.ofPoint wit.gdOld (.inl hgdOld) =
            PallasGroup.ofPoint wit.gdNew (.inl hgdNew) ∧
          PallasGroup.ofPoint wit.pkdOld (.inl hpkdOld) =
            PallasGroup.ofPoint wit.pkdNew (.inl hpkdNew)
      exact ⟨lift_eq_of_point_eq (.inl hgdOld) (.inl hgdNew) hgd,
        lift_eq_of_point_eq (.inl hpkdOld) (.inl hpkdNew) hpkd⟩
    · refine ⟨fun hv => ?_, fun hv => ?_⟩
      · have hvOld0 : wit.vOld ≠ 0 := by
          intro hz
          apply hv
          dsimp [w]
          simp [hz]
        exact (sub_eq_zero.mp ((mul_eq_zero.mp hes).resolve_left hvOld0)).symm
      · have hvNew0 : wit.vNew ≠ 0 := by
          intro hz
          apply hv
          dsimp [w]
          simp [hz]
        exact (sub_eq_zero.mp ((mul_eq_zero.mp heo).resolve_left hvNew0)).symm
  · exact Or.inl hbreak

/-- End-to-end refinement for a satisfying run of the deployed post-NU6.3
Action circuit.  This is the direct composition of the circuit soundness
contract with `specPost_to_ledger`; it deliberately leaves the exceptional
Sinsemilla branch explicit and reports the enable gates as `EnableFlagsSatisfied`. -/
theorem circuit_soundness_to_ledger (cfg : Config) (i₀ : RegionIndex)
    (env : Placed Environment Fp) (input : Var PrivateInputs Fp)
    (henv : EnvAssumptions orchardGenerators cfg env)
    (hconstraints : Constraints env.place env.env
      ((mainPost orchardGenerators orchardBases cfg input).operations i₀) i₀) :
    ActionBreak (extract cfg input i₀ env) ∨
      ∃ inst w, PublicProjection (extract cfg input i₀ env) inst ∧
        ActionSatisfied Pool.primitives Pool.keyBinding inst w ∧
        CrossAddressSatisfied (extract cfg input i₀ env) w ∧
        EnableFlagsSatisfied (extract cfg input i₀ env) w := by
  have hpost := soundnessPost orchardGenerators orchardBases cfg i₀ env input
    henv trivial hconstraints
  exact specPost_to_ledger (by simpa using hpost)

end Zcash.Security.Ledger.Bridge
