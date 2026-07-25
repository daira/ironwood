import Zcash.Snark.Keygen.Derivation
import Zcash.Snark.Keygen.Fast.NatKernelAdapter
import Zcash.Snark.Fixtures.SingleAction.Fixture

/-!
# Concrete certificate for the derived Action verifying key

This module contains the expensive concrete computation, separately from the reusable
derivation data: ONE bundled `native_decide` comparing every field of the derived
verifying key against the capture — the Lagrange-prefix cross-check and the two
commitment families (the group-side cost), plus the scalar/gate/layout fields and the
derived `Shape` (CS-scale).

EVALUATION-SHARING DISCIPLINE (each rule was measured, the hard way):
* The commitment passes use the SEQUENTIAL cores (`fixedCommitmentsSeqWith`/
  `permutationCommitmentsSeqWith`): nullary-definition sharing does NOT survive a
  `parMap` task fan-out in this evaluation tier — the 44 column tasks each captured
  the unforced `lagrangeBasis` thunk and re-ran the whole group FFT (44 × ~4 min =
  the CPU-hours regression this replaces). Let-binding the basis inside the decided
  proposition shares correctly at evaluation but blows the elaborator's fixed budget
  at proof-term finalization; the sequential map costs only ~26 s (scatter committer,
  0.6 s/column) and keeps both evaluation and finalization on known-good mechanisms.
* The basis and the per-column committer run through the NATIVE LANE
  (`Fast.derivedUrsGLagrangeKernel` / `Fast.commitLagrangeKernelWith`): the zero-import
  `NatKernel` twins compiled by the `NatKernelNative` `precompileModules` leaf, proven
  equal to the statement-surface functions via the kernel simulation theorems.
  Profiling note: THIS module gets the dylib automatically (the `ZcashKeygen` lib
  reaches the lane, so lake passes `--load-dynlib`); a SCRATCH probe through
  `lake env lean` does NOT, and must pass
  `--load-dynlib=.lake/build/lib/libZcash_NatKernelNative.so` explicitly or it
  measures the interpreted tier (~1.55× slower on this GMP-bound workload).
* `actionPinned` stays a nullary share: it is only touched from the main evaluation
  thread, where nullary init-once sharing does hold (the `VkMatch` fix).

The `Decidable` instance for the bundle is CONSTRUCTED leaf-by-leaf (`bundleDecEq`):
instance search on products mixing the `Fp`-typed scalars with the group-element
lists spins out in the `Fp` reducibility diamond, while every leaf synthesizes
instantly. `vk_eq_derived`/`vk_eq_toVerifierKey` assemble the record equality by
`simp only` unfolding of the named definitions on both sides until the spellings
coincide — no defeq bridges.

The `ZcashKeygen` target builds this module explicitly; ordinary clients of
`derivedActionVk` only need `Derivation`.
-/

namespace Zcash.Snark.Keygen

open Zcash.Snark
open Zcash.Snark.Fixture
open Halo2
open Zcash.Circuits.Action (orchardActionTopLevelCircuit)

/-- The Action circuit's proof-shape parameters — the only two `Shape` counts that are
not circuit data (orchard: one Action proof per statement, five multiopen point sets). -/
def actionProofParams : ProofParams := { numProofs := 1, numPointSets := 5 }

/-- The derived Lagrange basis: the SERIAL projective FFT, proven equal to the
Rust-mirroring `derivedUrsGLagrange` (`Fast.derivedUrsGLagrangeFast_eq`). Nullary —
initialized once on the main evaluation thread (all uses are single-threaded). -/
private def lagrangeBasis : List G := Fast.derivedUrsGLagrangeKernel capturedURS

/-- The per-column committer at the derived basis (scatter-projective Pippenger). -/
private def commitProj : List Fp → G :=
  Fast.commitLagrangeKernelWith Fast.Msm.defaultWindow capturedURS.w lagrangeBasis

/-- The derived pinned CS at the circuit-owned selector map — `ofOperations`' internal
`pinned` in method spelling. Nullary, so the selector-map/derive work evaluates once
per `native_decide` process (main-thread use only; see the module docstring). -/
private def actionPinned : PinnedConstraintSystem Fp :=
  PinnedConstraintSystem.derive orchardActionTopLevelCircuit.constraintSystem
    orchardActionTopLevelCircuit.selectorMap

set_option maxRecDepth 1000000 in
/-- The native-lane committer at the kernel basis IS the pipeline's affine default at
the spec basis — both sides are proven equal to `Fast.Msm.commitLagrangeSpec`, and the
two basis spellings are proven equal by `Fast.derivedUrsGLagrangeKernel_eq`. -/
private theorem committer_eq :
    Fast.commitLagrangeKernelWith Fast.Msm.defaultWindow capturedURS.w
      (Fast.derivedUrsGLagrangeKernel capturedURS)
      = Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow capturedURS.w
        (derivedUrsGLagrange capturedURS) := by
  funext coeffs
  rw [Fast.commitLagrangeKernelWith_eq _ (by decide),
    Fast.Msm.commitLagrangeFastWith_eq _ (by decide),
    Fast.derivedUrsGLagrangeKernel_eq]

/-- `Decidable` instance for the bundle, CONSTRUCTED leaf-by-leaf (see the module
docstring). -/
private instance bundleDecEq : DecidableEq (List G × List G × List G ×
    (Fp × ℕ × ℕ × Fp × ℕ) ×
    List (Expr Fp) ×
    (List (ℕ × ℤ) × List (ℕ × ℤ) × List (ℕ × ℤ)) ×
    List (List (Snark.ColumnRef × ℕ)) ×
    (List (List (Expr Fp)) × List (List (Expr Fp))) ×
    Shape) := by
  repeat' first
    | refine @instDecidableEqProd _ _ ?_ ?_
    | infer_instance

/-- **The derived verifying key matches the capture, field by field** — bundled into ONE
`native_decide` so the shared work (the Lagrange FFT, fixed contents, keygen mapping
and all 44 commitment MSMs) evaluates exactly once. Components, in order: the Lagrange
URS 10-generator prefix; the 29 fixed-column and 15 permutation commitments; the
domain/permutation scalars; the gates; the three query layouts; the permutation
chunks; the two lookup-expression families; and the derived `Shape`
(`ProofParams.mergeDerived`) against the fixture's. -/
theorem certificate :
    (lagrangeBasis.take capturedUrsGLagrange.length,
      fixedCommitmentsSeqWith commitProj
        orchardActionTopLevelCircuit.selectorMap
        orchardActionTopLevelCircuit.domainExponent
        orchardActionTopLevelCircuit.constraintSystem
        (orchardActionTopLevelCircuit.operations 0),
      permutationCommitmentsSeqWith commitProj
        orchardActionTopLevelCircuit.domainExponent
        orchardActionTopLevelCircuit.constraintSystem
        (orchardActionTopLevelCircuit.operations 0),
      (omegaOf orchardActionTopLevelCircuit.domainExponent,
        2 ^ orchardActionTopLevelCircuit.domainExponent,
        orchardActionTopLevelCircuit.constraintSystem.blindingFactors, deltaFp,
        orchardActionTopLevelCircuit.constraintSystem.chunkLen),
      actionPinned.gates.map RichExpression.toExpr,
      (actionPinned.instanceQueryLayout,
        actionPinned.adviceQueryLayout,
        actionPinned.fixedQueryLayout),
      permutationChunksOf orchardActionTopLevelCircuit.selectorMap
        orchardActionTopLevelCircuit.constraintSystem,
      (List.ofFn fun l : Fin shape.numLookups =>
          (actionPinned.lookupInputExprs.getD l.val []).map RichExpression.toExpr,
       List.ofFn fun l : Fin shape.numLookups =>
          (actionPinned.lookupTableExprs.getD l.val []).map RichExpression.toExpr),
      actionProofParams.mergeDerived orchardActionTopLevelCircuit)
    = (capturedUrsGLagrange,
       capturedFixedCommitments,
       capturedPermutationCommonCommitments,
       (vk.omega, vk.n, vk.blindingFactors, vk.delta, vk.chunkLen),
       vk.gates,
       (vk.instanceQueryLayout, vk.adviceQueryLayout, vk.fixedQueryLayout),
       vk.permutationChunks,
       (List.ofFn vk.lookupInputExprs, List.ofFn vk.lookupTableExprs),
       shape) := by
  native_decide

set_option maxRecDepth 1000000 in
/-- The derived Lagrange URS reproduces the captured 10-generator prefix. -/
theorem derivedUrsGLagrange_prefix_eq :
    (derivedUrsGLagrange capturedURS).take capturedUrsGLagrange.length
      = capturedUrsGLagrange := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  have h1 := h.1
  simp only [lagrangeBasis] at h1
  rw [← Fast.derivedUrsGLagrangeKernel_eq]
  exact h1

set_option maxRecDepth 1000000 in
/-- The derived fixed-column commitments are the captured ones. -/
theorem derivedFixedCommitments_eq :
    derivedFixedCommitments capturedURS = capturedFixedCommitments := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  have hfc := h.2.1
  simp only [commitProj, lagrangeBasis] at hfc
  rw [fixedCommitmentsSeqWith_eq, committer_eq] at hfc
  simp only [fixedCommitmentsWith] at hfc
  simp only [derivedFixedCommitments, Halo2.TopLevelCircuit.fixedCommitments,
    Halo2.TopLevelCircuit.fixedRows]
  exact hfc

set_option maxRecDepth 1000000 in
/-- The derived permutation common commitments are the captured ones. -/
theorem derivedPermutationCommonCommitments_eq :
    derivedPermutationCommonCommitments capturedURS
      = capturedPermutationCommonCommitments := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  have hpc := h.2.2.1
  simp only [commitProj, lagrangeBasis] at hpc
  rw [permutationCommitmentsSeqWith_eq, committer_eq] at hpc
  simp only [derivedPermutationCommonCommitments,
    Halo2.TopLevelCircuit.permutationCommitments, permutationCommitmentsOf]
  exact hpc

/-- The fixture's `Shape` is the proof-shape parameters merged with the circuit-derived
counts. -/
theorem shape_eq_mergeDerived :
    actionProofParams.mergeDerived orchardActionTopLevelCircuit = shape := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  exact h.2.2.2.2.2.2.2.2

set_option maxRecDepth 1000000 in
/-- **The captured Action verifying key is fully derived.** Both sides are opened with
`simp only` on the named definitions (`vk`, the derivation chain, and the
`TopLevelCircuit` keygen views) until the field spellings coincide, then assembled
field-wise from the bundle's equalities. -/
theorem vk_eq_derived : vk = derivedActionVk shape capturedURS := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, hfc, hpc, ⟨ho, hn, hb, hd, hc⟩, hg, ⟨hiq, haq, hfq⟩, hpch, ⟨hli, hlt⟩, -⟩ := h
  -- align the bundle's spellings with the keygen internals
  simp only [commitProj, lagrangeBasis] at hfc hpc
  rw [fixedCommitmentsSeqWith_eq, committer_eq] at hfc
  rw [permutationCommitmentsSeqWith_eq, committer_eq] at hpc
  simp only [actionPinned, Halo2.TopLevelCircuit.selectorMap,
    Halo2.TopLevelCircuit.selectorActivations, Halo2.TopLevelCircuit.regionStarts,
    Halo2.TopLevelCircuit.domainExponent]
    at ho hn hb hc hg hiq haq hfq hpch hli hlt hfc hpc
  -- open both records
  unfold vk
  simp only [derivedActionVk, Halo2.TopLevelCircuit.verifierKeyAt,
    VerifyingKey.ofOperations, fixedCommitmentsOf, permutationCommitmentsOf]
  rw [VerifyingKey.mk.injEq]
  refine ⟨ho.symm, hn.symm, hb.symm, hd.symm, hc.symm, hg.symm, hiq.symm, haq.symm,
    hfq.symm, ?_, ?_, hpch.symm, ?_, ?_⟩
  · rw [← hfc]
  · rw [← hpc]
  · exact (List.ofFn_inj.mp hli).symm
  · exact (List.ofFn_inj.mp hlt).symm

set_option maxRecDepth 1000000 in
/-- **`vk = orchardActionTopLevelCircuit.toVerifierKey actionProofParams capturedURS`**
— the captured Orchard Action verifying key IS the closed circuit's derived verifying
key (transported along `shape_eq_mergeDerived`): every field, including the `Shape` in
the type, comes from the circuit plus the URS and the two proof-shape counts. -/
theorem vk_eq_toVerifierKey :
    vk = shape_eq_mergeDerived
      ▸ orchardActionTopLevelCircuit.toVerifierKey actionProofParams capturedURS := by
  rw [toVerifierKey_action, vk_eq_derived]
  exact (derivedActionVk_cast shape_eq_mergeDerived capturedURS).symm

assert_no_sorry certificate
assert_no_sorry vk_eq_derived
assert_no_sorry vk_eq_toVerifierKey

end Zcash.Snark.Keygen
