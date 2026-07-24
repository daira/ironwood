import Zcash.Circuits.Action.Circuit
import Clean.Halo2.Keygen.GateProjection

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
  simp [Expression.SelectorFree, queryAdvice]

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
  simp [Expression.SelectorFree, queryAdvice]

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
      (by selector_free) |>.mul_right
      (by simp [curveEqn, Expression.SelectorFree, queryAdvice])
  · simp only [List.not_mem_nil, or_false] at hconstraint
    subst constraint
    exact (Expression.gatedBy_querySelector qPoint).mul_right
      (by selector_free) |>.mul_right
      (by simp [curveEqn, Expression.SelectorFree, queryAdvice])

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
    (by simp [curveEqn, Expression.SelectorFree, queryAdvice])

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
  simp [Expression.SelectorFree, queryAdvice]

end Action.Circuit

namespace CommitIvk

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [boolCheck, Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (advices : Fin 10 → Column .advice) :
    Configure.PreservesGateWellFormedness (configure advices) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qCommitIvk => gate { qCommitIvk, advices })
    (fun qCommitIvk => ({ qCommitIvk, advices } : Config))
    (fun qCommitIvk => gate_wellFormed { qCommitIvk, advices })

end CommitIvk

namespace Ecc.Add

theorem gate_wellFormed
    (qAdd : Selector)
    (lambda xP yP xQR yQR alpha beta gamma delta :
      Column .advice) :
    (gate qAdd lambda xP yP xQR yQR alpha beta gamma delta).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (xP yP xQR yQR lambda alpha beta gamma delta :
      Column .advice) :
    Configure.PreservesGateWellFormedness
      (add.configure
        (xP, yP, xQR, yQR, lambda, alpha, beta, gamma, delta)) := by
  change Configure.PreservesGateWellFormedness (do
    enableEquality xP.toAny
    enableEquality yP.toAny
    enableEquality xQR.toAny
    enableEquality yQR.toAny
    let qAdd ← selector
    createGate
      (gate qAdd lambda xP yP xQR yQR alpha beta gamma delta)
    (pure
      ({ qAdd := qAdd, lambda := lambda, xP := xP, yP := yP,
         xQR := xQR, yQR := yQR, alpha := alpha, beta := beta,
         gamma := gamma, delta := delta } : Config) :
      Configure Fp Config))
  exact Configure.PreservesGateWellFormedness.bind
    (Configure.PreservesGateWellFormedness.enableEquality xP.toAny) fun _ =>
      Configure.PreservesGateWellFormedness.bind
        (Configure.PreservesGateWellFormedness.enableEquality yP.toAny) fun _ =>
        Configure.PreservesGateWellFormedness.bind
          (Configure.PreservesGateWellFormedness.enableEquality xQR.toAny) fun _ =>
          Configure.PreservesGateWellFormedness.bind
            (Configure.PreservesGateWellFormedness.enableEquality yQR.toAny) fun _ =>
            Configure.PreservesGateWellFormedness.selectorCreateGate
              (fun qAdd =>
                gate qAdd lambda xP yP xQR yQR alpha beta gamma delta)
              (fun qAdd =>
                ({ qAdd := qAdd, lambda := lambda, xP := xP, yP := yP,
                   xQR := xQR, yQR := yQR, alpha := alpha, beta := beta,
                   gamma := gamma, delta := delta } : Config))
              (fun qAdd =>
                gate_wellFormed qAdd lambda xP yP xQR yQR
                  alpha beta gamma delta)

end Ecc.Add

namespace Ecc.AddIncomplete

theorem gate_wellFormed
    (qAddIncomplete : Selector)
    (xP yP xQR yQR : Column .advice) :
    (gate qAddIncomplete xP yP xQR yQR).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (xP yP xQR yQR : Column .advice) :
    Configure.PreservesGateWellFormedness
      (add.configure (xP, yP, xQR, yQR)) := by
  change Configure.PreservesGateWellFormedness (do
    enableEquality xP.toAny
    enableEquality yP.toAny
    enableEquality xQR.toAny
    enableEquality yQR.toAny
    let qAddIncomplete ← selector
    createGate (gate qAddIncomplete xP yP xQR yQR)
    (pure
      ({ qAddIncomplete := qAddIncomplete, xP := xP, yP := yP,
         xQR := xQR, yQR := yQR } : Config) :
      Configure Fp Config))
  exact Configure.PreservesGateWellFormedness.bind
    (Configure.PreservesGateWellFormedness.enableEquality xP.toAny) fun _ =>
      Configure.PreservesGateWellFormedness.bind
        (Configure.PreservesGateWellFormedness.enableEquality yP.toAny) fun _ =>
        Configure.PreservesGateWellFormedness.bind
          (Configure.PreservesGateWellFormedness.enableEquality xQR.toAny) fun _ =>
          Configure.PreservesGateWellFormedness.bind
            (Configure.PreservesGateWellFormedness.enableEquality yQR.toAny) fun _ =>
            Configure.PreservesGateWellFormedness.selectorCreateGate
              (fun qAddIncomplete =>
                gate qAddIncomplete xP yP xQR yQR)
              (fun qAddIncomplete =>
                ({ qAddIncomplete := qAddIncomplete, xP := xP, yP := yP,
                   xQR := xQR, yQR := yQR } : Config))
              (fun qAddIncomplete =>
                gate_wellFormed qAddIncomplete xP yP xQR yQR)

end Ecc.AddIncomplete

namespace Ecc.Mul

theorem lsbGate_wellFormed (cfg : Config) :
    (lsbGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

end Ecc.Mul

namespace Ecc.MulComplete

theorem decomposeGate_wellFormed (cfg : Config) :
    (decomposeGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (zComplete : Column .advice) (addConfig : Ecc.Add.Config) :
    Configure.PreservesGateWellFormedness
      (configure zComplete addConfig) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (Configure.PreservesGateWellFormedness.enableEquality
      zComplete.toAny) fun _ =>
        Configure.PreservesGateWellFormedness.selectorCreateGate
          (fun qDecompose =>
            decomposeGate { qDecompose, zComplete, addConfig })
          (fun qDecompose =>
            ({ qDecompose, zComplete, addConfig } : Config))
          (fun qDecompose =>
            decomposeGate_wellFormed
              { qDecompose, zComplete, addConfig })

end Ecc.MulComplete

namespace Ecc.MulOverflow

theorem overflowGate_wellFormed (K : ℕ) (cfg : Config K) :
    (overflowGate K cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (K : ℕ) (lookupConfig : LookupRangeCheck.Config K)
    (adv0 adv1 adv2 : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure K lookupConfig adv0 adv1 adv2) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (Configure.PreservesGateWellFormedness.enableEquality adv0.toAny) fun _ =>
      Configure.PreservesGateWellFormedness.bind
        (Configure.PreservesGateWellFormedness.enableEquality adv1.toAny) fun _ =>
        Configure.PreservesGateWellFormedness.bind
          (Configure.PreservesGateWellFormedness.enableEquality adv2.toAny) fun _ =>
          Configure.PreservesGateWellFormedness.selectorCreateGate
            (fun qOverflow =>
              overflowGate K
                { qOverflow, lookupConfig, adv0, adv1, adv2 })
            (fun qOverflow =>
              ({ qOverflow, lookupConfig, adv0, adv1, adv2 } : Config K))
            (fun qOverflow =>
              overflowGate_wellFormed K
                { qOverflow, lookupConfig, adv0, adv1, adv2 })

end Ecc.MulOverflow

namespace LookupRangeCheck

theorem bitshiftGate_wellFormed (K : ℕ) (cfg : Config K) :
    (bitshiftGate K cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (K : ℕ) (runningSum : Column .advice)
    (tableIdx : TableColumn) :
    Configure.PreservesGateWellFormedness
      (configure K runningSum tableIdx) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (Configure.PreservesGateWellFormedness.enableEquality
      runningSum.toAny) fun _ =>
      Configure.PreservesGateWellFormedness.bind
        Configure.PreservesGateWellFormedness.complexSelector fun qLookup =>
        Configure.PreservesGateWellFormedness.bind
          Configure.PreservesGateWellFormedness.complexSelector fun qRunning =>
          Configure.PreservesGateWellFormedness.bind
            Configure.PreservesGateWellFormedness.selector fun qBitshift =>
            let cfg : Config K :=
              { qLookup, qRunning, qBitshift, runningSum, tableIdx }
            Configure.PreservesGateWellFormedness.bind
              (Configure.PreservesGateWellFormedness.lookup
                [queryAdvice runningSum 0, queryAdvice runningSum 1]
                [((rangeCheckLookup K cfg).inputs.headI, tableIdx)]) fun _ =>
              Configure.PreservesGateWellFormedness.bind
                (Configure.PreservesGateWellFormedness.createGate _
                  (bitshiftGate_wellFormed K cfg)) fun _ =>
                Configure.PreservesGateWellFormedness.pure cfg

end LookupRangeCheck

namespace DecomposeRunningSum

@[simp]
theorem rangeCheckExpr_selectorFree
    (range : ℕ) (word : Expression Fp Query)
    (hword : word.SelectorFree) :
    (rangeCheckExpr range word).SelectorFree := by
  unfold rangeCheckExpr
  have foldlSelectorFree
      (indices : List ℕ) (acc : Expression Fp Query)
      (hacc : acc.SelectorFree) :
      (indices.foldl
        (fun result (index : ℕ) =>
          result * (Expression.const (index : Fp) - word))
        acc).SelectorFree := by
    induction indices generalizing acc with
    | nil => exact hacc
    | cons index rest ih =>
        rw [List.foldl_cons]
        apply ih
        simp [Expression.SelectorFree, hacc, hword]
  exact foldlSelectorFree _ word hword

theorem rangeCheckGate_wellFormed (W : ℕ) (cfg : Config) :
    (rangeCheckGate W cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  rw [List.forall_iff_forall_mem]
  intro constraint hconstraint
  simp only [List.mem_singleton] at hconstraint
  subst constraint
  apply rangeCheckExpr_selectorFree
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (W : ℕ) (qRangeCheck : Selector) (z : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure W qRangeCheck z) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (Configure.PreservesGateWellFormedness.enableEquality z.toAny) fun _ =>
      let cfg : Config := { qRangeCheck, z }
      Configure.PreservesGateWellFormedness.bind
        (Configure.PreservesGateWellFormedness.createGate _
          (rangeCheckGate_wellFormed W cfg)) fun _ =>
        Configure.PreservesGateWellFormedness.pure cfg

end DecomposeRunningSum

namespace Sinsemilla.Merkle.Gate

theorem decomposeGate_wellFormed (cfg : Config) :
    (decomposeGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole :
      Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure aWhole bWhole cWhole leftNode rightNode
        z1A z1B b1 b2 lWhole) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qDecompose =>
      decomposeGate
        (Config.mk qDecompose aWhole bWhole cWhole leftNode rightNode
          z1A z1B b1 b2 lWhole))
    (fun qDecompose =>
      Config.mk qDecompose aWhole bWhole cWhole leftNode rightNode
        z1A z1B b1 b2 lWhole)
    (fun qDecompose =>
      decomposeGate_wellFormed
        (Config.mk qDecompose aWhole bWhole cWhole leftNode rightNode
          z1A z1B b1 b2 lWhole))

end Sinsemilla.Merkle.Gate

namespace Sinsemilla.Merkle

theorem configure_preservesGateWellFormedness
    (scfg : HashPiece.Config) :
    Configure.PreservesGateWellFormedness (configure scfg) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (CondSwap.configure_preservesGateWellFormedness
      scfg.xA scfg.xP scfg.bits scfg.lambda1 scfg.lambda2) fun condSwap =>
      Configure.PreservesGateWellFormedness.bind
        (Gate.configure_preservesGateWellFormedness
          scfg.xA scfg.xP scfg.bits scfg.lambda1 scfg.lambda2
          scfg.xA scfg.xP scfg.bits scfg.lambda1 scfg.lambda2) fun gate =>
        Configure.PreservesGateWellFormedness.pure
          ({ condSwap, gate, sinsemilla := scfg } : Config)

end Sinsemilla.Merkle

namespace Sinsemilla.HashPiece

theorem initialYQGate_wellFormed (cfg : Config) :
    (initialYQGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [yAExpr, xRExpr, Expression.SelectorFree, queryAdvice, queryFixed]

theorem sinsemillaGate_wellFormed (cfg : Config) :
    (sinsemillaGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [yAExpr, xRExpr, qS3Expr, Expression.SelectorFree,
    queryAdvice, queryFixed]

theorem configure_preservesGateWellFormedness
    (G : Specs.Sinsemilla.Generators)
    (xA xP bits lambda1 lambda2 witnessPieces : Column .advice)
    (fixedYQ : Column .fixed)
    (genTable : Sinsemilla.GeneratorTableConfig) :
    Configure.PreservesGateWellFormedness
      (configure G xA xP bits lambda1 lambda2
        witnessPieces fixedYQ genTable) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (Configure.PreservesGateWellFormedness.enableEquality xA.toAny) fun _ =>
      Configure.PreservesGateWellFormedness.bind
        (Configure.PreservesGateWellFormedness.enableEquality xP.toAny) fun _ =>
        Configure.PreservesGateWellFormedness.bind
          (Configure.PreservesGateWellFormedness.enableEquality bits.toAny) fun _ =>
          Configure.PreservesGateWellFormedness.bind
            (Configure.PreservesGateWellFormedness.enableEquality
              lambda1.toAny) fun _ =>
            Configure.PreservesGateWellFormedness.bind
              (Configure.PreservesGateWellFormedness.enableEquality
                lambda2.toAny) fun _ =>
              Configure.PreservesGateWellFormedness.bind
                Configure.PreservesGateWellFormedness.complexSelector fun qS1 =>
                Configure.PreservesGateWellFormedness.bind
                  Configure.PreservesGateWellFormedness.fixedColumn fun qS2 =>
                  Configure.PreservesGateWellFormedness.bind
                    Configure.PreservesGateWellFormedness.selector fun qS4 =>
                    let cfg : Config :=
                      { qS1, qS2, qS4, fixedYQ, xA, xP, lambda1, lambda2,
                        bits, witnessPieces, generatorTable := genTable }
                    Configure.PreservesGateWellFormedness.bind
                      (Configure.PreservesGateWellFormedness.lookup
                        [queryFixed cfg.qS2, queryAdvice cfg.bits 0,
                         queryAdvice cfg.bits 1, queryAdvice cfg.xP 0,
                         queryAdvice cfg.lambda1 0, queryAdvice cfg.xA 0,
                         queryAdvice cfg.lambda2 0]
                        [((generatorLookup G cfg).inputs[0]!, genTable.tableIdx),
                         ((generatorLookup G cfg).inputs[1]!, genTable.tableX),
                         ((generatorLookup G cfg).inputs[2]!, genTable.tableY)]) fun _ =>
                      Configure.PreservesGateWellFormedness.bind
                        (Configure.PreservesGateWellFormedness.createGate _
                          (initialYQGate_wellFormed cfg)) fun _ =>
                        Configure.PreservesGateWellFormedness.bind
                          (Configure.PreservesGateWellFormedness.createGate _
                            (sinsemillaGate_wellFormed cfg)) fun _ =>
                          Configure.PreservesGateWellFormedness.pure cfg

end Sinsemilla.HashPiece

namespace Poseidon

theorem fullRoundGate_wellFormed (cfg : Config) :
    (fullRoundGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [pow5Expr, Expression.SelectorFree, queryAdvice, queryFixed]

theorem partialRoundsGate_wellFormed (cfg : Config) :
    (partialRoundsGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [pow5Expr, Expression.SelectorFree, queryAdvice, queryFixed]

theorem padAndAddGate_wellFormed (cfg : Config) :
    (padAndAddGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (state : Fin 3 → Column .advice)
    (partialSbox : Column .advice)
    (rcA rcB : Fin 3 → Column .fixed) :
    Configure.PreservesGateWellFormedness
      (configure state partialSbox rcA rcB) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (Configure.PreservesGateWellFormedness.enableEquality
      (state 0).toAny) fun _ =>
      Configure.PreservesGateWellFormedness.bind
        (Configure.PreservesGateWellFormedness.enableEquality
          (state 1).toAny) fun _ =>
        Configure.PreservesGateWellFormedness.bind
          (Configure.PreservesGateWellFormedness.enableEquality
            (state 2).toAny) fun _ =>
          Configure.PreservesGateWellFormedness.bind
            (Configure.PreservesGateWellFormedness.enableEquality
              (rcB 0).toAny) fun _ =>
            Configure.PreservesGateWellFormedness.bind
              (Configure.PreservesGateWellFormedness.enableEquality
                (rcB 1).toAny) fun _ =>
              Configure.PreservesGateWellFormedness.bind
                (Configure.PreservesGateWellFormedness.enableEquality
                  (rcB 2).toAny) fun _ =>
                Configure.PreservesGateWellFormedness.bind
                  Configure.PreservesGateWellFormedness.selector fun sFull =>
                  Configure.PreservesGateWellFormedness.bind
                    Configure.PreservesGateWellFormedness.selector fun sPartial =>
                    Configure.PreservesGateWellFormedness.bind
                      Configure.PreservesGateWellFormedness.selector fun sPadAndAdd =>
                      let cfg : Config :=
                        { state, partialSbox, rcA, rcB,
                          sFull, sPartial, sPadAndAdd }
                      Configure.PreservesGateWellFormedness.bind
                        (Configure.PreservesGateWellFormedness.createGate _
                          (fullRoundGate_wellFormed cfg)) fun _ =>
                        Configure.PreservesGateWellFormedness.bind
                          (Configure.PreservesGateWellFormedness.createGate _
                            (partialRoundsGate_wellFormed cfg)) fun _ =>
                          Configure.PreservesGateWellFormedness.bind
                            (Configure.PreservesGateWellFormedness.createGate _
                              (padAndAddGate_wellFormed cfg)) fun _ =>
                            Configure.PreservesGateWellFormedness.pure cfg

end Poseidon

namespace Ecc.MulIncomplete

theorem qMul1Gate_wellFormed (cfg : Config) :
    (qMul1Gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [yA, xRExpr, Expression.SelectorFree, queryAdvice]

theorem qMul2Gate_wellFormed (cfg : Config) :
    (qMul2Gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [forLoopPolys, yA, xRExpr,
    Expression.SelectorFree, queryAdvice]

theorem qMul3Gate_wellFormed (cfg : Config) :
    (qMul3Gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [forLoopPolys, yA, xRExpr,
    Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (z xA xP yP lambda1 lambda2 : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure z xA xP yP lambda1 lambda2) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (Configure.PreservesGateWellFormedness.enableEquality z.toAny) fun _ =>
      Configure.PreservesGateWellFormedness.bind
        (Configure.PreservesGateWellFormedness.enableEquality
          lambda1.toAny) fun _ =>
        Configure.PreservesGateWellFormedness.bind
          Configure.PreservesGateWellFormedness.selector fun qMul1 =>
          Configure.PreservesGateWellFormedness.bind
            Configure.PreservesGateWellFormedness.selector fun qMul2 =>
            Configure.PreservesGateWellFormedness.bind
              Configure.PreservesGateWellFormedness.selector fun qMul3 =>
              let cfg : Config :=
                { qMul1, qMul2, qMul3, z, xA, xP, yP, lambda1, lambda2 }
              Configure.PreservesGateWellFormedness.bind
                (Configure.PreservesGateWellFormedness.createGate _
                  (qMul1Gate_wellFormed cfg)) fun _ =>
                Configure.PreservesGateWellFormedness.bind
                  (Configure.PreservesGateWellFormedness.createGate _
                    (qMul2Gate_wellFormed cfg)) fun _ =>
                  Configure.PreservesGateWellFormedness.bind
                    (Configure.PreservesGateWellFormedness.createGate _
                      (qMul3Gate_wellFormed cfg)) fun _ =>
                    Configure.PreservesGateWellFormedness.pure cfg

end Ecc.MulIncomplete

namespace Ecc.Mul

theorem configure_preservesGateWellFormedness
    (addConfig : Ecc.Add.Config)
    (lookupConfig : LookupRangeCheck.Config 10)
    (advices : Fin 10 → Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure addConfig lookupConfig advices) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (Ecc.MulIncomplete.configure_preservesGateWellFormedness
      (advices 9) (advices 3) (advices 0) (advices 1)
      (advices 4) (advices 5)) fun hiConfig =>
      Configure.PreservesGateWellFormedness.bind
        (Ecc.MulIncomplete.configure_preservesGateWellFormedness
          (advices 6) (advices 7) (advices 0) (advices 1)
          (advices 8) (advices 2)) fun loConfig =>
        Configure.PreservesGateWellFormedness.bind
          (Ecc.MulComplete.configure_preservesGateWellFormedness
            (advices 9) addConfig) fun completeConfig =>
          Configure.PreservesGateWellFormedness.bind
            (Ecc.MulOverflow.configure_preservesGateWellFormedness
              10 lookupConfig (advices 6) (advices 7) (advices 8))
              fun overflowConfig =>
            Configure.PreservesGateWellFormedness.selectorCreateGate
              (fun qMulLsb =>
                lsbGate
                  { qMulLsb, addConfig, hiConfig, loConfig,
                    completeConfig, overflowConfig })
              (fun qMulLsb =>
                ({ qMulLsb, addConfig, hiConfig, loConfig,
                   completeConfig, overflowConfig } : Config))
              (fun qMulLsb =>
                lsbGate_wellFormed
                  { qMulLsb, addConfig, hiConfig, loConfig,
                    completeConfig, overflowConfig })

end Ecc.Mul

namespace NoteCommit.DecomposeB

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [NoteCommit.boolCheck, Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (colL colM colR : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure colL colM colR) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qNotecommitB =>
      gate { qNotecommitB, colL, colM, colR })
    (fun qNotecommitB =>
      ({ qNotecommitB, colL, colM, colR } : Config))
    (fun qNotecommitB =>
      gate_wellFormed { qNotecommitB, colL, colM, colR })

end NoteCommit.DecomposeB

namespace NoteCommit.DecomposeD

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [NoteCommit.boolCheck, Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (colL colM colR : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure colL colM colR) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qNotecommitD =>
      gate { qNotecommitD, colL, colM, colR })
    (fun qNotecommitD =>
      ({ qNotecommitD, colL, colM, colR } : Config))
    (fun qNotecommitD =>
      gate_wellFormed { qNotecommitD, colL, colM, colR })

end NoteCommit.DecomposeD

namespace NoteCommit.DecomposeE

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (colL colM colR : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure colL colM colR) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qNotecommitE =>
      gate { qNotecommitE, colL, colM, colR })
    (fun qNotecommitE =>
      ({ qNotecommitE, colL, colM, colR } : Config))
    (fun qNotecommitE =>
      gate_wellFormed { qNotecommitE, colL, colM, colR })

end NoteCommit.DecomposeE

namespace NoteCommit.DecomposeG

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [NoteCommit.boolCheck, Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (colL colM : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure colL colM) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qNotecommitG => gate { qNotecommitG, colL, colM })
    (fun qNotecommitG =>
      ({ qNotecommitG, colL, colM } : Config))
    (fun qNotecommitG =>
      gate_wellFormed { qNotecommitG, colL, colM })

end NoteCommit.DecomposeG

namespace NoteCommit.DecomposeH

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [NoteCommit.boolCheck, Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (colL colM colR : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure colL colM colR) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qNotecommitH =>
      gate { qNotecommitH, colL, colM, colR })
    (fun qNotecommitH =>
      ({ qNotecommitH, colL, colM, colR } : Config))
    (fun qNotecommitH =>
      gate_wellFormed { qNotecommitH, colL, colM, colR })

end NoteCommit.DecomposeH

namespace NoteCommit.GdCanonicity

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure colL colM colR colZ) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qNotecommitGd =>
      gate { qNotecommitGd, colL, colM, colR, colZ })
    (fun qNotecommitGd =>
      ({ qNotecommitGd, colL, colM, colR, colZ } : Config))
    (fun qNotecommitGd =>
      gate_wellFormed
        { qNotecommitGd, colL, colM, colR, colZ })

end NoteCommit.GdCanonicity

namespace NoteCommit.PkdCanonicity

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure colL colM colR colZ) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qNotecommitPkd =>
      gate { qNotecommitPkd, colL, colM, colR, colZ })
    (fun qNotecommitPkd =>
      ({ qNotecommitPkd, colL, colM, colR, colZ } : Config))
    (fun qNotecommitPkd =>
      gate_wellFormed
        { qNotecommitPkd, colL, colM, colR, colZ })

end NoteCommit.PkdCanonicity

namespace NoteCommit.ValueCanonicity

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure colL colM colR colZ) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qNotecommitValue =>
      gate { qNotecommitValue, colL, colM, colR, colZ })
    (fun qNotecommitValue =>
      ({ qNotecommitValue, colL, colM, colR, colZ } : Config))
    (fun qNotecommitValue =>
      gate_wellFormed
        { qNotecommitValue, colL, colM, colR, colZ })

end NoteCommit.ValueCanonicity

namespace NoteCommit.RhoCanonicity

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure colL colM colR colZ) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qNotecommitRho =>
      gate { qNotecommitRho, colL, colM, colR, colZ })
    (fun qNotecommitRho =>
      ({ qNotecommitRho, colL, colM, colR, colZ } : Config))
    (fun qNotecommitRho =>
      gate_wellFormed
        { qNotecommitRho, colL, colM, colR, colZ })

end NoteCommit.RhoCanonicity

namespace NoteCommit.PsiCanonicity

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (colL colM colR colZ : Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure colL colM colR colZ) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qNotecommitPsi =>
      gate { qNotecommitPsi, colL, colM, colR, colZ })
    (fun qNotecommitPsi =>
      ({ qNotecommitPsi, colL, colM, colR, colZ } : Config))
    (fun qNotecommitPsi =>
      gate_wellFormed
        { qNotecommitPsi, colL, colM, colR, colZ })

end NoteCommit.PsiCanonicity

namespace NoteCommit.YCanonicity

theorem gate_wellFormed (cfg : Config) :
    (gate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [NoteCommit.boolCheck, Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (advices : Fin 10 → Column .advice) :
    Configure.PreservesGateWellFormedness
      (configure advices) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qYCanon => gate { qYCanon, advices })
    (fun qYCanon => ({ qYCanon, advices } : Config))
    (fun qYCanon => gate_wellFormed { qYCanon, advices })

end NoteCommit.YCanonicity

namespace NoteCommit

theorem configure_preservesGateWellFormedness
    (advices : Fin 10 → Column .advice) :
    Configure.PreservesGateWellFormedness (configure advices) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (DecomposeB.configure_preservesGateWellFormedness
      (advices 6) (advices 7) (advices 8)) fun b =>
      Configure.PreservesGateWellFormedness.bind
        (DecomposeD.configure_preservesGateWellFormedness
          (advices 6) (advices 7) (advices 8)) fun d =>
        Configure.PreservesGateWellFormedness.bind
          (DecomposeE.configure_preservesGateWellFormedness
            (advices 6) (advices 7) (advices 8)) fun e =>
          Configure.PreservesGateWellFormedness.bind
            (DecomposeG.configure_preservesGateWellFormedness
              (advices 6) (advices 7)) fun g =>
            Configure.PreservesGateWellFormedness.bind
              (DecomposeH.configure_preservesGateWellFormedness
                (advices 6) (advices 7) (advices 8)) fun h =>
              Configure.PreservesGateWellFormedness.bind
                (GdCanonicity.configure_preservesGateWellFormedness
                  (advices 6) (advices 7) (advices 8) (advices 9)) fun gd =>
                Configure.PreservesGateWellFormedness.bind
                  (PkdCanonicity.configure_preservesGateWellFormedness
                    (advices 6) (advices 7) (advices 8) (advices 9)) fun pkd =>
                  Configure.PreservesGateWellFormedness.bind
                    (ValueCanonicity.configure_preservesGateWellFormedness
                      (advices 6) (advices 7) (advices 8) (advices 9)) fun value =>
                    Configure.PreservesGateWellFormedness.bind
                      (RhoCanonicity.configure_preservesGateWellFormedness
                        (advices 6) (advices 7) (advices 8) (advices 9)) fun rho =>
                      Configure.PreservesGateWellFormedness.bind
                        (PsiCanonicity.configure_preservesGateWellFormedness
                          (advices 6) (advices 7) (advices 8) (advices 9)) fun psi =>
                        Configure.PreservesGateWellFormedness.bind
                          (YCanonicity.configure_preservesGateWellFormedness
                            advices) fun y =>
                          Configure.PreservesGateWellFormedness.pure
                            ({ b, d, e, g, h, gd, pkd, value, rho, psi, y } :
                              Config)

end NoteCommit

namespace Ecc.MulFixed

@[simp]
theorem windowPow_selectorFree
    (word : Expression Fp Query)
    (hword : word.SelectorFree) (k : ℕ) :
    (windowPow word k).SelectorFree := by
  unfold windowPow
  have foldlSelectorFree
      (indices : List ℕ) (acc : Expression Fp Query)
      (hacc : acc.SelectorFree) :
      (indices.foldl (fun result _ => result * word) acc).SelectorFree := by
    induction indices generalizing acc with
    | nil => exact hacc
    | cons index rest ih =>
        rw [List.foldl_cons]
        apply ih
        simp [Expression.SelectorFree, hacc, hword]
  exact foldlSelectorFree _ _ (by selector_free)

theorem coordsCheck_selectorFree
    (cfg : Config) (word : Expression Fp Query)
    (hword : word.SelectorFree) :
    (coordsCheck cfg word).Forall fun constraint =>
      constraint.2.SelectorFree := by
  simp [coordsCheck, interpolatedX, Expression.SelectorFree,
    queryAdvice, queryFixed, hword]

theorem coordsGate_wellFormed (cfg : Config) :
    (coordsGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  apply coordsCheck_selectorFree
  simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (window u : Column .advice)
    (addConfig : Ecc.Add.Config)
    (addIncompleteConfig : Ecc.AddIncomplete.Config) :
    Configure.PreservesGateWellFormedness
      (configure lagrangeCoeffs window u addConfig
        addIncompleteConfig) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (Configure.PreservesGateWellFormedness.enableEquality
      window.toAny) fun _ =>
      Configure.PreservesGateWellFormedness.bind
        (Configure.PreservesGateWellFormedness.enableEquality
          u.toAny) fun _ =>
        Configure.PreservesGateWellFormedness.bind
          Configure.PreservesGateWellFormedness.selector fun qRunningSum =>
          Configure.PreservesGateWellFormedness.bind
            (DecomposeRunningSum.configure_preservesGateWellFormedness
              3 qRunningSum window) fun runningSumConfig =>
            Configure.PreservesGateWellFormedness.bind
              Configure.PreservesGateWellFormedness.fixedColumn fun fixedZ =>
              let cfg : Config :=
                { runningSumConfig, lagrangeCoeffs, fixedZ, window, u,
                  addConfig, addIncompleteConfig }
              Configure.PreservesGateWellFormedness.bind
                (Configure.PreservesGateWellFormedness.createGate _
                  (coordsGate_wellFormed cfg)) fun _ =>
                Configure.PreservesGateWellFormedness.pure cfg

end Ecc.MulFixed

namespace Ecc.MulFixed.BaseFieldElem

theorem canonGate_wellFormed (cfg : Config) :
    (canonGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [DecomposeRunningSum.rangeCheckExpr_selectorFree,
    Expression.mulConstant, Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (canonAdvices : Fin 3 → Column .advice)
    (lookupConfig : LookupRangeCheck.Config 10)
    (superConfig : MulFixed.Config) :
    Configure.PreservesGateWellFormedness
      (configure canonAdvices lookupConfig superConfig) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (Configure.PreservesGateWellFormedness.enableEquality
      (canonAdvices 0).toAny) fun _ =>
      Configure.PreservesGateWellFormedness.bind
        (Configure.PreservesGateWellFormedness.enableEquality
          (canonAdvices 1).toAny) fun _ =>
        Configure.PreservesGateWellFormedness.bind
          (Configure.PreservesGateWellFormedness.enableEquality
            (canonAdvices 2).toAny) fun _ =>
          Configure.PreservesGateWellFormedness.selectorCreateGate
            (fun qMulFixedBaseField =>
              canonGate
                { qMulFixedBaseField, canonAdvices,
                  lookupConfig, superConfig })
            (fun qMulFixedBaseField =>
              ({ qMulFixedBaseField, canonAdvices,
                 lookupConfig, superConfig } : Config))
            (fun qMulFixedBaseField =>
              canonGate_wellFormed
                { qMulFixedBaseField, canonAdvices,
                  lookupConfig, superConfig })

end Ecc.MulFixed.BaseFieldElem

namespace Ecc.MulFixed.Short

theorem shortGate_wellFormed (cfg : Config) :
    (shortGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  simp [DecomposeRunningSum.rangeCheckExpr_selectorFree,
    Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (superConfig : MulFixed.Config) :
    Configure.PreservesGateWellFormedness
      (configure superConfig) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qMulFixedShort =>
      shortGate { qMulFixedShort, superConfig })
    (fun qMulFixedShort =>
      ({ qMulFixedShort, superConfig } : Config))
    (fun qMulFixedShort =>
      shortGate_wellFormed { qMulFixedShort, superConfig })

end Ecc.MulFixed.Short

namespace Ecc.MulFixed.FullWidth

theorem fullWidthGate_wellFormed (cfg : Config) :
    (fullWidthGate cfg).WellFormed := by
  apply Gate.wellFormed_of_withSelector
  rw [List.forall_append]
  constructor
  · apply MulFixed.coordsCheck_selectorFree
    simp [Expression.SelectorFree, queryAdvice]
  · rw [List.forall_iff_forall_mem]
    intro constraint hconstraint
    simp only [List.mem_singleton] at hconstraint
    subst constraint
    apply DecomposeRunningSum.rangeCheckExpr_selectorFree
    simp [Expression.SelectorFree, queryAdvice]

theorem configure_preservesGateWellFormedness
    (superConfig : MulFixed.Config) :
    Configure.PreservesGateWellFormedness
      (configure superConfig) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.selectorCreateGate
    (fun qMulFixedFull =>
      fullWidthGate { qMulFixedFull, superConfig })
    (fun qMulFixedFull =>
      ({ qMulFixedFull, superConfig } : Config))
    (fun qMulFixedFull =>
      fullWidthGate_wellFormed { qMulFixedFull, superConfig })

end Ecc.MulFixed.FullWidth

namespace Ecc

theorem configure_preservesGateWellFormedness
    (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) :
    Configure.PreservesGateWellFormedness
      (configure advices lagrangeCoeffs rangeCheck) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    (WitnessPoint.configure_preservesGateWellFormedness
      (advices 0) (advices 1)) fun witnessPoint =>
      Configure.PreservesGateWellFormedness.bind
        (AddIncomplete.configure_preservesGateWellFormedness
          (advices 0) (advices 1) (advices 2) (advices 3))
          fun addIncomplete =>
        Configure.PreservesGateWellFormedness.bind
          (Add.configure_preservesGateWellFormedness
            (advices 0) (advices 1) (advices 2) (advices 3)
            (advices 4) (advices 5) (advices 6) (advices 7)
            (advices 8)) fun add =>
          Configure.PreservesGateWellFormedness.bind
            (Mul.configure_preservesGateWellFormedness
              add rangeCheck advices) fun mul =>
            Configure.PreservesGateWellFormedness.bind
              (MulFixed.configure_preservesGateWellFormedness
                lagrangeCoeffs (advices 4) (advices 5)
                add addIncomplete) fun mulFixed =>
              Configure.PreservesGateWellFormedness.bind
                (MulFixed.FullWidth.configure_preservesGateWellFormedness
                  mulFixed) fun mulFixedFull =>
                Configure.PreservesGateWellFormedness.bind
                  (MulFixed.Short.configure_preservesGateWellFormedness
                    mulFixed) fun mulFixedShort =>
                  Configure.PreservesGateWellFormedness.bind
                    (MulFixed.BaseFieldElem.configure_preservesGateWellFormedness
                      ![advices 6, advices 7, advices 8]
                      rangeCheck mulFixed) fun mulFixedBaseField =>
                    Configure.PreservesGateWellFormedness.pure
                      ({ witnessPoint, addIncomplete, add, mul,
                         mulFixedFull, mulFixedShort,
                         mulFixedBaseField } : EccConfig)

end Ecc

namespace Action.Circuit

/--
The real Action configure program registers only well-formed custom gates.  This
proof follows the configure call graph and uses each child chip's preservation
certificate; it does not evaluate the completed constraint system.
-/
theorem configure_preservesGateWellFormedness
    (G : Specs.Sinsemilla.Generators) :
    Configure.PreservesGateWellFormedness (configure G) := by
  unfold configure
  exact Configure.PreservesGateWellFormedness.bind
    Configure.PreservesGateWellFormedness.adviceColumn fun a0 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.adviceColumn fun a1 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.adviceColumn fun a2 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.adviceColumn fun a3 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.adviceColumn fun a4 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.adviceColumn fun a5 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.adviceColumn fun a6 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.adviceColumn fun a7 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.adviceColumn fun a8 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.adviceColumn fun a9 =>
    let advices : Fin 10 → Column .advice :=
      ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.selector fun qOrchard =>
    Configure.PreservesGateWellFormedness.bind
      (Configure.PreservesGateWellFormedness.createGate _
        (orchardGate_wellFormed qOrchard advices)) fun _ =>
    Configure.PreservesGateWellFormedness.bind
      (AddChip.configure_preservesGateWellFormedness a7 a8 a6)
        fun addChipConfig =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.lookupTableColumn fun tableIdx =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.lookupTableColumn fun tableX =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.lookupTableColumn fun tableY =>
    let genTable : Sinsemilla.GeneratorTableConfig :=
      { tableIdx, tableX, tableY }
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.instanceColumn fun primary =>
    Configure.PreservesGateWellFormedness.bind
      (Configure.PreservesGateWellFormedness.enableEquality
        primary.toAny) fun _ =>
    Configure.PreservesGateWellFormedness.bind
      (Configure.PreservesGateWellFormedness.enableEquality a0.toAny) fun _ =>
    Configure.PreservesGateWellFormedness.bind
      (Configure.PreservesGateWellFormedness.enableEquality a1.toAny) fun _ =>
    Configure.PreservesGateWellFormedness.bind
      (Configure.PreservesGateWellFormedness.enableEquality a2.toAny) fun _ =>
    Configure.PreservesGateWellFormedness.bind
      (Configure.PreservesGateWellFormedness.enableEquality a3.toAny) fun _ =>
    Configure.PreservesGateWellFormedness.bind
      (Configure.PreservesGateWellFormedness.enableEquality a4.toAny) fun _ =>
    Configure.PreservesGateWellFormedness.bind
      (Configure.PreservesGateWellFormedness.enableEquality a5.toAny) fun _ =>
    Configure.PreservesGateWellFormedness.bind
      (Configure.PreservesGateWellFormedness.enableEquality a6.toAny) fun _ =>
    Configure.PreservesGateWellFormedness.bind
      (Configure.PreservesGateWellFormedness.enableEquality a7.toAny) fun _ =>
    Configure.PreservesGateWellFormedness.bind
      (Configure.PreservesGateWellFormedness.enableEquality a8.toAny) fun _ =>
    Configure.PreservesGateWellFormedness.bind
      (Configure.PreservesGateWellFormedness.enableEquality a9.toAny) fun _ =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.fixedColumn fun l0 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.fixedColumn fun l1 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.fixedColumn fun l2 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.fixedColumn fun l3 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.fixedColumn fun l4 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.fixedColumn fun l5 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.fixedColumn fun l6 =>
    Configure.PreservesGateWellFormedness.bind
      Configure.PreservesGateWellFormedness.fixedColumn fun l7 =>
    let lagrangeCoeffs : Fin 8 → Column .fixed :=
      ![l0, l1, l2, l3, l4, l5, l6, l7]
    Configure.PreservesGateWellFormedness.bind
      (Configure.PreservesGateWellFormedness.enableConstant l0) fun _ =>
    Configure.PreservesGateWellFormedness.bind
      (LookupRangeCheck.configure_preservesGateWellFormedness
        10 a9 tableIdx) fun lookupConfig =>
    Configure.PreservesGateWellFormedness.bind
      (Ecc.configure_preservesGateWellFormedness
        advices lagrangeCoeffs lookupConfig) fun eccConfig =>
    Configure.PreservesGateWellFormedness.bind
      (Poseidon.configure_preservesGateWellFormedness
        ![a6, a7, a8] a5 ![l2, l3, l4] ![l5, l6, l7])
        fun poseidonConfig =>
    Configure.PreservesGateWellFormedness.bind
      (Sinsemilla.HashPiece.configure_preservesGateWellFormedness
        G a0 a1 a2 a3 a4 a6 l0 genTable) fun sinsemilla1 =>
    Configure.PreservesGateWellFormedness.bind
      (Sinsemilla.Merkle.configure_preservesGateWellFormedness
        sinsemilla1) fun merkle1 =>
    Configure.PreservesGateWellFormedness.bind
      (Sinsemilla.HashPiece.configure_preservesGateWellFormedness
        G a5 a6 a7 a8 a9 a7 l1 genTable) fun sinsemilla2 =>
    Configure.PreservesGateWellFormedness.bind
      (Sinsemilla.Merkle.configure_preservesGateWellFormedness
        sinsemilla2) fun merkle2 =>
    Configure.PreservesGateWellFormedness.bind
      (CommitIvk.configure_preservesGateWellFormedness advices)
        fun commitIvkConfig =>
    Configure.PreservesGateWellFormedness.bind
      (NoteCommit.configure_preservesGateWellFormedness advices)
        fun noteCommitOld =>
    Configure.PreservesGateWellFormedness.bind
      (NoteCommit.configure_preservesGateWellFormedness advices)
        fun noteCommitNew =>
    Configure.PreservesGateWellFormedness.pure
      ({ primary, qOrchard, advices, addChipConfig, eccConfig,
         poseidonConfig, sinsemilla1, merkle1, sinsemilla2, merkle2,
         commitIvkConfig, noteCommitOld, noteCommitNew,
         lookupConfig } : Config)

end Action.Circuit

end Zcash.Circuits
