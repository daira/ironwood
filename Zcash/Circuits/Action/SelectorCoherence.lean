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

end Zcash.Circuits
