import Zcash.Circuits.Action.Circuit
import Zcash.Snark.Soundness.GateProjection

/-!
# Action configure gate coherence

The Action circuit's nested configure programs preserve the generic static
`ConstraintSystem.GatesWellFormed` invariant.  Certificates are deliberately local
to the gate and chip that introduce each constraint; the top-level proof composes
those certificates rather than reducing the completed constraint system.
-/

namespace Zcash.Circuits

open Halo2

set_option maxHeartbeats 20000

namespace AddChip

@[circuit_norm]
theorem addGate_wellFormed (cfg : Config) :
    (addGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (a b c : Column .advice) :
    Configure.PreservesGateWellFormedness (configure a b c) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    Configure.PreservesGateWellFormedness.selector fun qAdd =>
      Configure.PreservesGateWellFormedness.bind
        (Configure.PreservesGateWellFormedness.createGate _
          (addGate_wellFormed { a, b, c, qAdd })) fun _ =>
            Configure.PreservesGateWellFormedness.pure _

end AddChip

namespace CondSwap

@[circuit_norm]
theorem swapGate_wellFormed (cfg : Config) :
    (swapGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (a b aSwapped bSwapped swap : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure a b aSwapped bSwapped swap) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (Configure.PreservesGateWellFormedness.enableEquality a.toAny) fun _ =>
      Configure.PreservesGateWellFormedness.bind
        Configure.PreservesGateWellFormedness.selector fun qSwap =>
          Configure.PreservesGateWellFormedness.bind
            (Configure.PreservesGateWellFormedness.createGate _
              (swapGate_wellFormed
                { qSwap, a, b, aSwapped, bSwapped, swap })) fun _ =>
                  Configure.PreservesGateWellFormedness.pure _

end CondSwap

namespace Ecc.WitnessPoint

@[circuit_norm]
theorem pointGate_wellFormed
    (qPoint : Selector) (x y : Column .advice) :
    (pointGate qPoint x y).WellFormed := by
  change List.Forall
    (fun constraint : Constraint Fp =>
      constraint.poly.GatedBy qPoint)
    [({ name := "x == 0 v on_curve"
        poly := querySelector qPoint * queryAdvice x 0 *
          curveEqn x y } : Constraint Fp),
     ({ name := "y == 0 v on_curve"
        poly := querySelector qPoint * queryAdvice y 0 *
          curveEqn x y } : Constraint Fp)]
  rw [List.forall_iff_forall_mem]
  intro constraint hconstraint
  simp only [List.mem_cons] at hconstraint
  rcases hconstraint with rfl | hconstraint
  · exact (Expression.gatedBy_querySelector qPoint).mul_right
      (by rfl) |>.mul_right
      (by simp [curveEqn, Expression.selectorFree, queryAdvice])
  · simp only [List.not_mem_nil, or_false] at hconstraint
    subst constraint
    exact (Expression.gatedBy_querySelector qPoint).mul_right
      (by rfl) |>.mul_right
      (by simp [curveEqn, Expression.selectorFree, queryAdvice])

@[circuit_norm]
theorem pointNonIdGate_wellFormed
    (qPointNonId : Selector) (x y : Column .advice) :
    (pointNonIdGate qPointNonId x y).WellFormed := by
  change List.Forall
    (fun constraint : Constraint Fp =>
      constraint.poly.GatedBy qPointNonId)
    [({ name := "on_curve"
        poly := querySelector qPointNonId * curveEqn x y } :
      Constraint Fp)]
  rw [List.forall_iff_forall_mem]
  intro constraint hconstraint
  simp only [List.mem_singleton] at hconstraint
  subst constraint
  exact (Expression.gatedBy_querySelector qPointNonId).mul_right
    (by simp [curveEqn, Expression.selectorFree, queryAdvice])

theorem configure_preservesGateWellFormedness
    (x y : Column .advice) :
    Configure.PreservesGateWellFormedness (configure x y) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    Configure.PreservesGateWellFormedness.selector fun qPoint =>
      Configure.PreservesGateWellFormedness.bind
        Configure.PreservesGateWellFormedness.selector fun qPointNonId =>
          Configure.PreservesGateWellFormedness.bind
            (Configure.PreservesGateWellFormedness.createGate _
              (pointGate_wellFormed qPoint x y)) fun _ =>
                Configure.PreservesGateWellFormedness.bind
                  (Configure.PreservesGateWellFormedness.createGate _
                    (pointNonIdGate_wellFormed qPointNonId x y)) fun _ =>
                      Configure.PreservesGateWellFormedness.pure _

end Ecc.WitnessPoint

namespace Action.Circuit

theorem orchardGate_wellFormed
    (qOrchard : Selector) (advices : Fin 10 → Column .advice) :
    (orchardGate qOrchard advices).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end Action.Circuit

namespace CommitIvk

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [boolCheck, Expression.selectorFree, queryAdvice]

end CommitIvk

namespace Ecc.Add

theorem gate_wellFormed
    (qAdd : Selector)
    (lambda xP yP xQR yQR alpha beta gamma delta :
      Column .advice) :
    (gate qAdd lambda xP yP xQR yQR alpha beta gamma delta).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end Ecc.Add

namespace Ecc.AddIncomplete

theorem gate_wellFormed
    (qAddIncomplete : Selector)
    (xP yP xQR yQR : Column .advice) :
    (gate qAddIncomplete xP yP xQR yQR).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end Ecc.AddIncomplete

namespace Ecc.Mul

theorem lsbGate_wellFormed (cfg : Config) :
    (lsbGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end Ecc.Mul

namespace Ecc.MulComplete

theorem decomposeGate_wellFormed (cfg : Config) :
    (decomposeGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end Ecc.MulComplete

namespace Ecc.MulOverflow

theorem overflowGate_wellFormed (K : ℕ) (cfg : Config K) :
    (overflowGate K cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end Ecc.MulOverflow

namespace LookupRangeCheck

theorem bitshiftGate_wellFormed (K : ℕ) (cfg : Config K) :
    (bitshiftGate K cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end LookupRangeCheck

namespace DecomposeRunningSum

@[simp]
theorem rangeCheckExpr_selectorFree
    (range : ℕ) (word : Expression Fp Query)
    (hword : word.selectorFree = true) :
    (rangeCheckExpr range word).selectorFree = true := by
  unfold rangeCheckExpr
  have foldlSelectorFree
      (indices : List ℕ) (acc : Expression Fp Query)
      (hacc : acc.selectorFree = true) :
      (indices.foldl
        (fun result (index : ℕ) =>
          result * (Expression.const (index : Fp) - word))
        acc).selectorFree = true := by
    induction indices generalizing acc with
    | nil => exact hacc
    | cons index rest ih =>
        rw [List.foldl_cons]
        apply ih
        simp [Expression.selectorFree, hacc, hword]
  exact foldlSelectorFree _ word hword

theorem rangeCheckGate_wellFormed (W : ℕ) (cfg : Config) :
    (rangeCheckGate W cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  rw [List.forall_iff_forall_mem]
  intro constraint hconstraint
  simp only [List.mem_singleton] at hconstraint
  subst constraint
  apply rangeCheckExpr_selectorFree
  simp [Expression.selectorFree, queryAdvice]

end DecomposeRunningSum

namespace Sinsemilla.Merkle.Gate

theorem decomposeGate_wellFormed (cfg : Config) :
    (decomposeGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end Sinsemilla.Merkle.Gate

namespace Sinsemilla.HashPiece

theorem initialYQGate_wellFormed (cfg : Config) :
    (initialYQGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [yAExpr, xRExpr, Expression.selectorFree, queryAdvice, queryFixed]

theorem sinsemillaGate_wellFormed (cfg : Config) :
    (sinsemillaGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [yAExpr, xRExpr, qS3Expr, Expression.selectorFree,
    queryAdvice, queryFixed]

end Sinsemilla.HashPiece

namespace Poseidon

theorem fullRoundGate_wellFormed (cfg : Config) :
    (fullRoundGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [pow5Expr, Expression.selectorFree, queryAdvice, queryFixed]

theorem partialRoundsGate_wellFormed (cfg : Config) :
    (partialRoundsGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [pow5Expr, Expression.selectorFree, queryAdvice, queryFixed]

theorem padAndAddGate_wellFormed (cfg : Config) :
    (padAndAddGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end Poseidon

namespace Ecc.MulIncomplete

theorem qMul1Gate_wellFormed (cfg : Config) :
    (qMul1Gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [yA, xRExpr, Expression.selectorFree, queryAdvice]

theorem qMul2Gate_wellFormed (cfg : Config) :
    (qMul2Gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [forLoopPolys, yA, xRExpr,
    Expression.selectorFree, queryAdvice]

theorem qMul3Gate_wellFormed (cfg : Config) :
    (qMul3Gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [forLoopPolys, yA, xRExpr,
    Expression.selectorFree, queryAdvice]

end Ecc.MulIncomplete

namespace NoteCommit.DecomposeB

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [NoteCommit.boolCheck, Expression.selectorFree, queryAdvice]

end NoteCommit.DecomposeB

namespace NoteCommit.DecomposeD

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [NoteCommit.boolCheck, Expression.selectorFree, queryAdvice]

end NoteCommit.DecomposeD

namespace NoteCommit.DecomposeE

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end NoteCommit.DecomposeE

namespace NoteCommit.DecomposeG

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [NoteCommit.boolCheck, Expression.selectorFree, queryAdvice]

end NoteCommit.DecomposeG

namespace NoteCommit.DecomposeH

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [NoteCommit.boolCheck, Expression.selectorFree, queryAdvice]

end NoteCommit.DecomposeH

namespace NoteCommit.GdCanonicity

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end NoteCommit.GdCanonicity

namespace NoteCommit.PkdCanonicity

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end NoteCommit.PkdCanonicity

namespace NoteCommit.ValueCanonicity

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end NoteCommit.ValueCanonicity

namespace NoteCommit.RhoCanonicity

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end NoteCommit.RhoCanonicity

namespace NoteCommit.PsiCanonicity

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end NoteCommit.PsiCanonicity

namespace NoteCommit.YCanonicity

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [NoteCommit.boolCheck, Expression.selectorFree, queryAdvice]

end NoteCommit.YCanonicity

namespace Ecc.MulFixed

@[simp]
theorem windowPow_selectorFree
    (word : Expression Fp Query)
    (hword : word.selectorFree = true) (k : ℕ) :
    (windowPow word k).selectorFree = true := by
  unfold windowPow
  have foldlSelectorFree
      (indices : List ℕ) (acc : Expression Fp Query)
      (hacc : acc.selectorFree = true) :
      (indices.foldl (fun result _ => result * word) acc).selectorFree =
        true := by
    induction indices generalizing acc with
    | nil => exact hacc
    | cons index rest ih =>
        rw [List.foldl_cons]
        apply ih
        simp [Expression.selectorFree, hacc, hword]
  exact foldlSelectorFree _ _ (by rfl)

theorem coordsCheck_selectorFree
    (cfg : Config) (word : Expression Fp Query)
    (hword : word.selectorFree = true) :
    (coordsCheck cfg word).Forall fun constraint =>
      constraint.2.selectorFree = true := by
  simp [coordsCheck, interpolatedX, Expression.selectorFree,
    queryAdvice, queryFixed, hword]

theorem coordsGate_wellFormed (cfg : Config) :
    (coordsGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  apply coordsCheck_selectorFree
  simp [Expression.selectorFree, queryAdvice]

end Ecc.MulFixed

namespace Ecc.MulFixed.BaseFieldElem

theorem canonGate_wellFormed (cfg : Config) :
    (canonGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [DecomposeRunningSum.rangeCheckExpr_selectorFree,
    Expression.mulConstant, Expression.selectorFree, queryAdvice]

end Ecc.MulFixed.BaseFieldElem

namespace Ecc.MulFixed.Short

theorem shortGate_wellFormed (cfg : Config) :
    (shortGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [DecomposeRunningSum.rangeCheckExpr_selectorFree,
    Expression.selectorFree, queryAdvice]

end Ecc.MulFixed.Short

namespace Ecc.MulFixed.FullWidth

theorem fullWidthGate_wellFormed (cfg : Config) :
    (fullWidthGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  rw [List.forall_append]
  constructor
  · apply MulFixed.coordsCheck_selectorFree
    simp [Expression.selectorFree, queryAdvice]
  · rw [List.forall_iff_forall_mem]
    intro constraint hconstraint
    simp only [List.mem_singleton] at hconstraint
    subst constraint
    apply DecomposeRunningSum.rangeCheckExpr_selectorFree
    simp [Expression.selectorFree, queryAdvice]

end Ecc.MulFixed.FullWidth

end Zcash.Circuits
