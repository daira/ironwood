import Zcash.Circuits.Action.GateCoherence
import Zcash.Snark.Soundness.SelectorCoherence

/-!
# Action configure selector coherence

Compositional certificates that every selector reference registered by the Orchard
Action configure program was allocated by that same program.  This is the syntactic
companion to `Action.GateCoherence`: semantic gate shape and selector allocation are
kept separate because neither implies the other.
-/

namespace Zcash.Circuits

open Halo2

set_option maxHeartbeats 20000

namespace AddChip

@[circuit_norm]
theorem addGate_selectorsOwned (cfg : Config) :
    (addGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (a b c : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure a b c) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qAdd => addGate { a, b, c, qAdd })
      (fun qAdd => ({ a, b, c, qAdd } : Config))
      (fun _ => rfl)
      (fun qAdd => addGate_selectorsOwned
        { a, b, c, qAdd })

end AddChip

namespace CondSwap

@[circuit_norm]
theorem swapGate_selectorsOwned (cfg : Config) :
    (swapGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (a b aSwapped bSwapped swap : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure a b aSwapped bSwapped swap) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      a.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qSwap =>
        swapGate
          { qSwap, a, b, aSwapped, bSwapped, swap })
      (fun qSwap =>
        ({ qSwap, a, b, aSwapped, bSwapped, swap } :
          Config))
      (fun _ => rfl)
      (fun qSwap => swapGate_selectorsOwned
        { qSwap, a, b, aSwapped, bSwapped, swap })

end CondSwap

namespace CommitIvk

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [boolCheck, Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (advices : Fin 10 → Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure advices) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qCommitIvk => gate { qCommitIvk, advices })
      (fun qCommitIvk =>
        ({ qCommitIvk, advices } : Config))
      (fun _ => rfl)
      (fun qCommitIvk => gate_selectorsOwned
        { qCommitIvk, advices })

end CommitIvk

namespace Ecc.Add

@[circuit_norm]
theorem gate_selectorsOwned
    (qAdd : Selector)
    (lambda xP yP xQR yQR alpha beta gamma delta :
      Column .advice) :
    (gate qAdd lambda xP yP xQR yQR
      alpha beta gamma delta).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (xP yP xQR yQR lambda alpha beta gamma delta :
      Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (add.configure
        (xP, yP, xQR, yQR, lambda,
          alpha, beta, gamma, delta)) := by
  change Configure.PreservesGateSelectorsAllocated (do
    enableEquality xP.toAny
    enableEquality yP.toAny
    enableEquality xQR.toAny
    enableEquality yQR.toAny
    let qAdd ← selector
    createGate
      (gate qAdd lambda xP yP xQR yQR
        alpha beta gamma delta)
    (pure
      ({ qAdd := qAdd, lambda := lambda,
         xP := xP, yP := yP, xQR := xQR,
         yQR := yQR, alpha := alpha,
         beta := beta, gamma := gamma,
         delta := delta } : Config) :
      Configure Fp Config))
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      xP.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        yP.toAny) fun _ =>
      Configure.PreservesGateSelectorsAllocated.bind
        (Configure.PreservesGateSelectorsAllocated.enableEquality
          xQR.toAny) fun _ =>
        Configure.PreservesGateSelectorsAllocated.bind
          (Configure.PreservesGateSelectorsAllocated.enableEquality
            yQR.toAny) fun _ =>
          Configure.PreservesGateSelectorsAllocated.selectorCreateGate
            (fun qAdd =>
              gate qAdd lambda xP yP xQR yQR
                alpha beta gamma delta)
            (fun qAdd =>
              ({ qAdd := qAdd, lambda := lambda,
                 xP := xP, yP := yP, xQR := xQR,
                 yQR := yQR, alpha := alpha,
                 beta := beta, gamma := gamma,
                 delta := delta } : Config))
            (fun _ => rfl)
            (fun qAdd => gate_selectorsOwned qAdd
              lambda xP yP xQR yQR
              alpha beta gamma delta)

end Ecc.Add

namespace Ecc.WitnessPoint

@[circuit_norm]
theorem pointGate_selectorsOwned
    (qPoint : Selector) (x y : Column .advice) :
    (pointGate qPoint x y).SelectorsOwned := by
  change List.Forall
    (fun constraint : Constraint Fp =>
      constraint.poly.selectorsCovered
        (fun index => decide (index = qPoint.index)) = true)
    [({ name := "x == 0 v on_curve"
        poly := querySelector qPoint * queryAdvice x 0 *
          curveEqn x y } : Constraint Fp),
     ({ name := "y == 0 v on_curve"
        poly := querySelector qPoint * queryAdvice y 0 *
          curveEqn x y } : Constraint Fp)]
  simp [Expression.selectorsCovered, querySelector, queryAdvice,
    curveEqn]

@[circuit_norm]
theorem pointNonIdGate_selectorsOwned
    (qPointNonId : Selector) (x y : Column .advice) :
    (pointNonIdGate qPointNonId x y).SelectorsOwned := by
  change List.Forall
    (fun constraint : Constraint Fp =>
      constraint.poly.selectorsCovered
        (fun index =>
          decide (index = qPointNonId.index)) = true)
    [({ name := "on_curve"
        poly := querySelector qPointNonId * curveEqn x y } :
      Constraint Fp)]
  simp [Expression.selectorsCovered, querySelector, queryAdvice,
    curveEqn]

theorem configure_preservesGateSelectorsAllocated
    (x y : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure x y) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.twoSelectorsTwoGates
      (fun qPoint _ => pointGate qPoint x y)
      (fun _ qPointNonId =>
        pointNonIdGate qPointNonId x y)
      (fun qPoint qPointNonId =>
        ({ qPoint, qPointNonId, x, y } : Config))
      (fun _ _ => rfl)
      (fun _ _ => rfl)
      (fun qPoint _ =>
        pointGate_selectorsOwned qPoint x y)
      (fun _ qPointNonId =>
        pointNonIdGate_selectorsOwned qPointNonId x y)

end Ecc.WitnessPoint

namespace Ecc.AddIncomplete

@[circuit_norm]
theorem gate_selectorsOwned
    (qAddIncomplete : Selector)
    (xP yP xQR yQR : Column .advice) :
    (gate qAddIncomplete xP yP xQR yQR).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (xP yP xQR yQR : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (add.configure (xP, yP, xQR, yQR)) := by
  change Configure.PreservesGateSelectorsAllocated (do
    enableEquality xP.toAny
    enableEquality yP.toAny
    enableEquality xQR.toAny
    enableEquality yQR.toAny
    let qAddIncomplete ← selector
    createGate (gate qAddIncomplete xP yP xQR yQR)
    (pure
      ({ qAddIncomplete := qAddIncomplete,
         xP := xP, yP := yP, xQR := xQR,
         yQR := yQR } : Config) :
      Configure Fp Config))
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      xP.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        yP.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        xQR.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        yQR.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qAddIncomplete =>
        gate qAddIncomplete xP yP xQR yQR)
      (fun qAddIncomplete =>
        ({ qAddIncomplete := qAddIncomplete,
           xP := xP, yP := yP, xQR := xQR,
           yQR := yQR } : Config))
      (fun _ => rfl)
      (fun qAddIncomplete =>
        gate_selectorsOwned qAddIncomplete xP yP xQR yQR)

end Ecc.AddIncomplete

namespace Ecc.Mul

@[circuit_norm]
theorem lsbGate_selectorsOwned (cfg : Config) :
    (lsbGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

end Ecc.Mul

namespace Ecc.MulComplete

@[circuit_norm]
theorem decomposeGate_selectorsOwned (cfg : Config) :
    (decomposeGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (zComplete : Column .advice)
    (addConfig : Ecc.Add.Config) :
    Configure.PreservesGateSelectorsAllocated
      (configure zComplete addConfig) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      zComplete.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qDecompose =>
        decomposeGate { qDecompose, zComplete, addConfig })
      (fun qDecompose =>
        ({ qDecompose, zComplete, addConfig } : Config))
      (fun _ => rfl)
      (fun qDecompose =>
        decomposeGate_selectorsOwned
          { qDecompose, zComplete, addConfig })

end Ecc.MulComplete

namespace Ecc.MulOverflow

@[circuit_norm]
theorem overflowGate_selectorsOwned
    (K : ℕ) (cfg : Config K) :
    (overflowGate K cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (K : ℕ) (lookupConfig : LookupRangeCheck.Config K)
    (adv0 adv1 adv2 : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure K lookupConfig adv0 adv1 adv2) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      adv0.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        adv1.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        adv2.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qOverflow =>
        overflowGate K
          { qOverflow, lookupConfig, adv0, adv1, adv2 })
      (fun qOverflow =>
        ({ qOverflow, lookupConfig, adv0, adv1, adv2 } :
          Config K))
      (fun _ => rfl)
      (fun qOverflow =>
        overflowGate_selectorsOwned K
          { qOverflow, lookupConfig, adv0, adv1, adv2 })

end Ecc.MulOverflow

namespace Poseidon

@[circuit_norm]
theorem fullRoundGate_selectorsOwned (cfg : Config) :
    (fullRoundGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [pow5Expr, Expression.selectorFree,
    queryAdvice, queryFixed]

@[circuit_norm]
theorem partialRoundsGate_selectorsOwned (cfg : Config) :
    (partialRoundsGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [pow5Expr, Expression.selectorFree,
    queryAdvice, queryFixed]

@[circuit_norm]
theorem padAndAddGate_selectorsOwned (cfg : Config) :
    (padAndAddGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (state : Fin 3 → Column .advice)
    (partialSbox : Column .advice)
    (rcA rcB : Fin 3 → Column .fixed) :
    Configure.PreservesGateSelectorsAllocated
      (configure state partialSbox rcA rcB) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      (state 0).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (state 1).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (state 2).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (rcB 0).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (rcB 1).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (rcB 2).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.threeSelectorsThreeGates
      (fun sFull sPartial sPadAndAdd =>
        fullRoundGate
          { state, partialSbox, rcA, rcB,
            sFull, sPartial, sPadAndAdd })
      (fun sFull sPartial sPadAndAdd =>
        partialRoundsGate
          { state, partialSbox, rcA, rcB,
            sFull, sPartial, sPadAndAdd })
      (fun sFull sPartial sPadAndAdd =>
        padAndAddGate
          { state, partialSbox, rcA, rcB,
            sFull, sPartial, sPadAndAdd })
      (fun sFull sPartial sPadAndAdd =>
        ({ state, partialSbox, rcA, rcB,
           sFull, sPartial, sPadAndAdd } : Config))
      (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)
      (fun sFull sPartial sPadAndAdd =>
        fullRoundGate_selectorsOwned
          { state, partialSbox, rcA, rcB,
            sFull, sPartial, sPadAndAdd })
      (fun sFull sPartial sPadAndAdd =>
        partialRoundsGate_selectorsOwned
          { state, partialSbox, rcA, rcB,
            sFull, sPartial, sPadAndAdd })
      (fun sFull sPartial sPadAndAdd =>
        padAndAddGate_selectorsOwned
          { state, partialSbox, rcA, rcB,
            sFull, sPartial, sPadAndAdd })

end Poseidon

namespace Ecc.MulIncomplete

@[circuit_norm]
theorem qMul1Gate_selectorsOwned (cfg : Config) :
    (qMul1Gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [yA, xRExpr, Expression.selectorFree, queryAdvice]

@[circuit_norm]
theorem qMul2Gate_selectorsOwned (cfg : Config) :
    (qMul2Gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [forLoopPolys, yA, xRExpr,
    Expression.selectorFree, queryAdvice]

@[circuit_norm]
theorem qMul3Gate_selectorsOwned (cfg : Config) :
    (qMul3Gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [forLoopPolys, yA, xRExpr,
    Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (z xA xP yP lambda1 lambda2 : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure z xA xP yP lambda1 lambda2) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      z.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        lambda1.toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.threeSelectorsThreeGates
      (fun qMul1 qMul2 qMul3 =>
        qMul1Gate
          { qMul1, qMul2, qMul3, z, xA, xP, yP,
            lambda1, lambda2 })
      (fun qMul1 qMul2 qMul3 =>
        qMul2Gate
          { qMul1, qMul2, qMul3, z, xA, xP, yP,
            lambda1, lambda2 })
      (fun qMul1 qMul2 qMul3 =>
        qMul3Gate
          { qMul1, qMul2, qMul3, z, xA, xP, yP,
            lambda1, lambda2 })
      (fun qMul1 qMul2 qMul3 =>
        ({ qMul1, qMul2, qMul3, z, xA, xP, yP,
           lambda1, lambda2 } : Config))
      (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)
      (fun _ _ _ => rfl)
      (fun qMul1 qMul2 qMul3 =>
        qMul1Gate_selectorsOwned
          { qMul1, qMul2, qMul3, z, xA, xP, yP,
            lambda1, lambda2 })
      (fun qMul1 qMul2 qMul3 =>
        qMul2Gate_selectorsOwned
          { qMul1, qMul2, qMul3, z, xA, xP, yP,
            lambda1, lambda2 })
      (fun qMul1 qMul2 qMul3 =>
        qMul3Gate_selectorsOwned
          { qMul1, qMul2, qMul3, z, xA, xP, yP,
            lambda1, lambda2 })

end Ecc.MulIncomplete

namespace Ecc.Mul

theorem configure_preservesGateSelectorsAllocated
    (addConfig : Ecc.Add.Config)
    (lookupConfig : LookupRangeCheck.Config 10)
    (advices : Fin 10 → Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure addConfig lookupConfig advices) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Ecc.MulIncomplete.configure_preservesGateSelectorsAllocated
      (advices 9) (advices 3) (advices 0) (advices 1)
      (advices 4) (advices 5)) fun hiConfig =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Ecc.MulIncomplete.configure_preservesGateSelectorsAllocated
        (advices 6) (advices 7) (advices 0) (advices 1)
        (advices 8) (advices 2)) fun loConfig =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Ecc.MulComplete.configure_preservesGateSelectorsAllocated
        (advices 9) addConfig) fun completeConfig =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Ecc.MulOverflow.configure_preservesGateSelectorsAllocated
        10 lookupConfig (advices 6) (advices 7)
        (advices 8)) fun overflowConfig =>
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qMulLsb =>
        lsbGate
          { qMulLsb, addConfig, hiConfig, loConfig,
            completeConfig, overflowConfig })
      (fun qMulLsb =>
        ({ qMulLsb, addConfig, hiConfig, loConfig,
           completeConfig, overflowConfig } : Config))
      (fun _ => rfl)
      (fun qMulLsb =>
        lsbGate_selectorsOwned
          { qMulLsb, addConfig, hiConfig, loConfig,
            completeConfig, overflowConfig })

end Ecc.Mul

namespace NoteCommit.DecomposeB

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [NoteCommit.boolCheck, Expression.selectorFree,
    queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitB =>
        gate { qNotecommitB, colL, colM, colR })
      (fun qNotecommitB =>
        ({ qNotecommitB, colL, colM, colR } : Config))
      (fun _ => rfl)
      (fun qNotecommitB => gate_selectorsOwned
        { qNotecommitB, colL, colM, colR })

end NoteCommit.DecomposeB

namespace NoteCommit.DecomposeD

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [NoteCommit.boolCheck, Expression.selectorFree,
    queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitD =>
        gate { qNotecommitD, colL, colM, colR })
      (fun qNotecommitD =>
        ({ qNotecommitD, colL, colM, colR } : Config))
      (fun _ => rfl)
      (fun qNotecommitD => gate_selectorsOwned
        { qNotecommitD, colL, colM, colR })

end NoteCommit.DecomposeD

namespace NoteCommit.DecomposeE

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitE =>
        gate { qNotecommitE, colL, colM, colR })
      (fun qNotecommitE =>
        ({ qNotecommitE, colL, colM, colR } : Config))
      (fun _ => rfl)
      (fun qNotecommitE => gate_selectorsOwned
        { qNotecommitE, colL, colM, colR })

end NoteCommit.DecomposeE

namespace NoteCommit.DecomposeG

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [NoteCommit.boolCheck, Expression.selectorFree,
    queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitG =>
        gate { qNotecommitG, colL, colM })
      (fun qNotecommitG =>
        ({ qNotecommitG, colL, colM } : Config))
      (fun _ => rfl)
      (fun qNotecommitG => gate_selectorsOwned
        { qNotecommitG, colL, colM })

end NoteCommit.DecomposeG

namespace NoteCommit.DecomposeH

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [NoteCommit.boolCheck, Expression.selectorFree,
    queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitH =>
        gate { qNotecommitH, colL, colM, colR })
      (fun qNotecommitH =>
        ({ qNotecommitH, colL, colM, colR } : Config))
      (fun _ => rfl)
      (fun qNotecommitH => gate_selectorsOwned
        { qNotecommitH, colL, colM, colR })

end NoteCommit.DecomposeH

namespace NoteCommit.GdCanonicity

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR colZ) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitGd =>
        gate { qNotecommitGd, colL, colM, colR, colZ })
      (fun qNotecommitGd =>
        ({ qNotecommitGd, colL, colM, colR, colZ } :
          Config))
      (fun _ => rfl)
      (fun qNotecommitGd => gate_selectorsOwned
        { qNotecommitGd, colL, colM, colR, colZ })

end NoteCommit.GdCanonicity

namespace NoteCommit.PkdCanonicity

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR colZ) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitPkd =>
        gate { qNotecommitPkd, colL, colM, colR, colZ })
      (fun qNotecommitPkd =>
        ({ qNotecommitPkd, colL, colM, colR, colZ } :
          Config))
      (fun _ => rfl)
      (fun qNotecommitPkd => gate_selectorsOwned
        { qNotecommitPkd, colL, colM, colR, colZ })

end NoteCommit.PkdCanonicity

namespace NoteCommit.ValueCanonicity

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR colZ) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitValue =>
        gate { qNotecommitValue, colL, colM, colR, colZ })
      (fun qNotecommitValue =>
        ({ qNotecommitValue, colL, colM, colR, colZ } :
          Config))
      (fun _ => rfl)
      (fun qNotecommitValue => gate_selectorsOwned
        { qNotecommitValue, colL, colM, colR, colZ })

end NoteCommit.ValueCanonicity

namespace NoteCommit.RhoCanonicity

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR colZ) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitRho =>
        gate { qNotecommitRho, colL, colM, colR, colZ })
      (fun qNotecommitRho =>
        ({ qNotecommitRho, colL, colM, colR, colZ } :
          Config))
      (fun _ => rfl)
      (fun qNotecommitRho => gate_selectorsOwned
        { qNotecommitRho, colL, colM, colR, colZ })

end NoteCommit.RhoCanonicity

namespace NoteCommit.PsiCanonicity

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure colL colM colR colZ) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qNotecommitPsi =>
        gate { qNotecommitPsi, colL, colM, colR, colZ })
      (fun qNotecommitPsi =>
        ({ qNotecommitPsi, colL, colM, colR, colZ } :
          Config))
      (fun _ => rfl)
      (fun qNotecommitPsi => gate_selectorsOwned
        { qNotecommitPsi, colL, colM, colR, colZ })

end NoteCommit.PsiCanonicity

namespace NoteCommit.YCanonicity

@[circuit_norm]
theorem gate_selectorsOwned (cfg : Config) :
    (gate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [NoteCommit.boolCheck, Expression.selectorFree,
    queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (advices : Fin 10 → Column .advice) :
    Configure.PreservesGateSelectorsAllocated
      (configure advices) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qYCanon => gate { qYCanon, advices })
      (fun qYCanon => ({ qYCanon, advices } : Config))
      (fun _ => rfl)
      (fun qYCanon => gate_selectorsOwned
        { qYCanon, advices })

end NoteCommit.YCanonicity

namespace Ecc.MulFixed.BaseFieldElem

@[circuit_norm]
theorem canonGate_selectorsOwned (cfg : Config) :
    (canonGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [DecomposeRunningSum.rangeCheckExpr_selectorFree,
    Expression.mulConstant, Expression.selectorFree,
    queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (canonAdvices : Fin 3 → Column .advice)
    (lookupConfig : LookupRangeCheck.Config 10)
    (superConfig : MulFixed.Config) :
    Configure.PreservesGateSelectorsAllocated
      (configure canonAdvices lookupConfig superConfig) := by
  unfold configure
  exact Configure.PreservesGateSelectorsAllocated.bind
    (Configure.PreservesGateSelectorsAllocated.enableEquality
      (canonAdvices 0).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (canonAdvices 1).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.bind
      (Configure.PreservesGateSelectorsAllocated.enableEquality
        (canonAdvices 2).toAny) fun _ =>
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qMulFixedBaseField =>
        canonGate
          { qMulFixedBaseField, canonAdvices,
            lookupConfig, superConfig })
      (fun qMulFixedBaseField =>
        ({ qMulFixedBaseField, canonAdvices,
           lookupConfig, superConfig } : Config))
      (fun _ => rfl)
      (fun qMulFixedBaseField =>
        canonGate_selectorsOwned
          { qMulFixedBaseField, canonAdvices,
            lookupConfig, superConfig })

end Ecc.MulFixed.BaseFieldElem

namespace Ecc.MulFixed.Short

@[circuit_norm]
theorem shortGate_selectorsOwned (cfg : Config) :
    (shortGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
  simp [DecomposeRunningSum.rangeCheckExpr_selectorFree,
    Expression.selectorFree, queryAdvice]

theorem configure_preservesGateSelectorsAllocated
    (superConfig : MulFixed.Config) :
    Configure.PreservesGateSelectorsAllocated
      (configure superConfig) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qMulFixedShort =>
        shortGate { qMulFixedShort, superConfig })
      (fun qMulFixedShort =>
        ({ qMulFixedShort, superConfig } : Config))
      (fun _ => rfl)
      (fun qMulFixedShort =>
        shortGate_selectorsOwned
          { qMulFixedShort, superConfig })

end Ecc.MulFixed.Short

namespace Ecc.MulFixed.FullWidth

@[circuit_norm]
theorem fullWidthGate_selectorsOwned (cfg : Config) :
    (fullWidthGate cfg).SelectorsOwned := by
  apply Gate.selectorsOwned_of_withSelector
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

theorem configure_preservesGateSelectorsAllocated
    (superConfig : MulFixed.Config) :
    Configure.PreservesGateSelectorsAllocated
      (configure superConfig) := by
  unfold configure
  exact
    Configure.PreservesGateSelectorsAllocated.selectorCreateGate
      (fun qMulFixedFull =>
        fullWidthGate { qMulFixedFull, superConfig })
      (fun qMulFixedFull =>
        ({ qMulFixedFull, superConfig } : Config))
      (fun _ => rfl)
      (fun qMulFixedFull =>
        fullWidthGate_selectorsOwned
          { qMulFixedFull, superConfig })

end Ecc.MulFixed.FullWidth

end Zcash.Circuits
