import Zcash.Circuits.Action.RealBases

/-!
# The Orchard Action specification

This is the canonical, circuit-independent statement over extracted Action data.
The formal-circuit bundle retains its parameterized `Circuit.SpecPost`; the theorem
at the end of this file is the explicit boundary between that implementation
spelling and the deployed Action specification.
-/

namespace Zcash.Circuits.Action

open Circuit
open NoteCommit (noteScalars)
open Specs.Sinsemilla (HashGuarded commitIvkChunks)
open CompElliptic.Fields.Pasta (Fq)

/-- The deployed Orchard Action statement over its extracted witness data. -/
def ActionSpec (wit : ActionData) : Prop :=
  (-- the witnessed points are well-formed
  wit.cmOld.Valid ∧ wit.gdOld.OnCurve ∧ wit.akP.OnCurve ∧ wit.pkdOld.OnCurve ∧
  wit.gdNew.OnCurve ∧ wit.pkdNew.OnCurve ∧
  -- the note values are 64-bit
  wit.vOld.val < 2 ^ 64 ∧ wit.vNew.val < 2 ^ 64 ∧
  -- value-commitment integrity: `cv_net = [v_old − v_new] V + [rcv] R`
  (wit.magnitude.val < 2 ^ 64 ∧
    ((wit.sign = 1 ∧ (⟨wit.cvX, wit.cvY⟩ : Point Fp)
        = (wit.magnitude.val : Fq) • orchardBases.valueCommitV
          + wit.rcv.2 • orchardBases.valueCommitR) ∨
     (wit.sign = -1 ∧ (⟨wit.cvX, wit.cvY⟩ : Point Fp)
        = -(wit.magnitude.val : Fq) • orchardBases.valueCommitV
          + wit.rcv.2 • orchardBases.valueCommitR))) ∧
  -- nullifier integrity: `nf_old = Extract([PRF(nk, ρ) + ψ] K + cm_old)`
  wit.nfOld = (wit.cmOld +
    ((Poseidon.Hash.ConstantLength.value #v[wit.nk, wit.rhoOld] + wit.psiOld).val : Fq)
      • orchardBases.nullifierK).x ∧
  -- spend authority: `rk = [α] SpendAuthG + ak_P`
  (⟨wit.rkX, wit.rkY⟩ : Point Fp)
    = wit.alpha.2 • orchardBases.spendAuthG + wit.akP ∧
  -- diversified-address integrity
  (∃ ivk : Fp,
    HashGuarded Specs.Sinsemilla.orchardGenerators.S orchardBases.ivkQ
      (commitIvkChunks wit.akP.x.val wit.nk.val)
      (fun bp => ivk = (bp + wit.rivk.2 • orchardBases.commitIvkR).x) ∧
    wit.pkdOld = ivk.val • wit.gdOld) ∧
  -- old note-commitment integrity
  HashGuarded Specs.Sinsemilla.orchardGenerators.S orchardBases.noteQ
    (noteScalars wit.gdOld wit.pkdOld wit.vOld wit.rhoOld wit.psiOld).chunks
    (fun bp => wit.cmOld = bp + wit.rcmOld.2 • orchardBases.noteCommitR) ∧
  -- new note-commitment integrity, with `ρ_new = nf_old`
  HashGuarded Specs.Sinsemilla.orchardGenerators.S orchardBases.noteQ
    (noteScalars wit.gdNew wit.pkdNew wit.vNew wit.nfOld wit.psiNew).chunks
    (fun bp => wit.cmx = (bp + wit.rcmNew.2 • orchardBases.noteCommitR).x) ∧
  -- exact raw-encoding Merkle path and dummy-spend anchor gate
  (∃ root : Fp,
    Sinsemilla.Merkle.ExactMerklePathData Specs.Sinsemilla.orchardGenerators
      orchardBases.merkleQ 0 32 wit.cmOld.x root
      (merkleLeftEncoding wit) (merkleRightEncoding wit) (merkleSide wit) ∧
    wit.vOld * (root - wit.anchor) = 0) ∧
  -- remaining `q_orchard` value checks
  wit.vOld - wit.vNew = wit.magnitude * wit.sign ∧
  wit.vOld * (1 - wit.enableSpend) = 0 ∧
  wit.vNew * (1 - wit.enableOutput) = 0) ∧
  -- post-NU6.3 cross-address binding
  (wit.disableCrossAddress ≠ 0 →
    wit.gdOld = wit.gdNew ∧ wit.pkdOld = wit.pkdNew)

/-- The canonical Action specification is the concrete instantiation of the
formal circuit bundle's parameterized postcondition. -/
theorem actionSpec_iff_specPost (wit : ActionData) :
    ActionSpec wit ↔
      SpecPost Specs.Sinsemilla.orchardGenerators orchardBases () () wit := by
  rfl

end Zcash.Circuits.Action
