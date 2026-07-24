import Zcash.Snark.Keygen.Derivation
import Zcash.Snark.Keygen.Fast.FastFftPar
import Zcash.Snark.Keygen.Fast.MsmProj
import Zcash.Snark.Fixtures.SingleAction.Fixture

/-!
# Concrete certificate for the derived Action verifying key

This module contains the expensive concrete computation, separately from the reusable
derivation data: ONE bundled `native_decide` comparing every field of the derived
verifying key against the capture — the Lagrange-prefix cross-check and the two
commitment families (the group-side cost), plus the scalar/gate/layout fields and the
derived `Shape` (CS-scale). Components are stated over the `TopLevelCircuit` methods
and the once-evaluated `lagrangeBasis` rather than projections of `derivedActionVk` —
projecting the record would strictly build ALL its fields, re-running the FFT and both
commitment passes a second time. The basis itself is computed by the PROVEN-equal
projective FFT (`Fast.derivedUrsGLagrangeFast_eq`), so the whole certificate costs one
fast FFT plus one Pippenger commitment pass. The `Decidable` instance for the bundle
is CONSTRUCTED leaf-by-leaf (`bundleDecEq`, an `instDecidableEqProd` recursion —
a global instance, since `native_decide` rejects proof-local `letI` fvars):
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

/-- The derived Lagrange basis, as a NULLARY definition: evaluated once per
`native_decide` process (function applications re-evaluate per occurrence — the
`urs`-parameterized spellings each cost a full group FFT). Computed by the
ROUND-PARALLEL projective FFT, PROVEN pointwise equal to the Rust-mirroring
`derivedUrsGLagrange` (`Fast.derivedUrsGLagrangeParFast_eq`) — the corollaries below
bridge back to the statement-surface name through that equality. -/
private def lagrangeBasis : List G := Fast.derivedUrsGLagrangeParFast capturedURS

/-- The per-column committer at the derived basis: the PROJECTIVE windowed Pippenger,
PROVEN equal to the affine default (`commitProj_eq` via the shared
`Fast.Msm.commitLagrangeSpec`). Nullary partial application so the basis closure is
built once. -/
private def commitProj : List Fp → G :=
  Fast.MsmProj.commitLagrangeProjWith Fast.Msm.defaultWindow capturedURS.w lagrangeBasis

set_option maxRecDepth 1000000 in
/-- The projective committer at the derived basis IS the pipeline's affine default at
the spec basis — both sides are proven equal to `Fast.Msm.commitLagrangeSpec`. -/
private theorem commitProj_eq :
    Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow capturedURS.w
      (derivedUrsGLagrange capturedURS) = commitProj := by
  funext coeffs
  simp only [commitProj, lagrangeBasis]
  rw [Fast.Msm.commitLagrangeFastWith_eq _ (by decide),
    Fast.MsmProj.commitLagrangeProjWith_eq _ (by decide),
    Fast.derivedUrsGLagrangeParFast_eq]

/-- The derived pinned CS at the circuit-owned selector map — `ofOperations`' internal
`pinned` in method spelling. Nullary, so the selector-map/derive work evaluates once
per `native_decide` process. -/
private def actionPinned : PinnedConstraintSystem Fp :=
  PinnedConstraintSystem.derive orchardActionTopLevelCircuit.constraintSystem
    orchardActionTopLevelCircuit.selectorMap

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
`native_decide` so the shared work (the fast Lagrange FFT, fixed contents, keygen
mapping and all 44 commitment MSMs) evaluates exactly once. Components, in order: the
Lagrange URS 10-generator prefix; the 29 fixed-column and 15 permutation commitments;
the domain/permutation scalars; the gates; the three query layouts; the permutation
chunks; the two lookup-expression families; and the derived `Shape`
(`ProofParams.mergeDerived`) against the fixture's. -/
theorem certificate :
    (lagrangeBasis.take capturedUrsGLagrange.length,
      fixedCommitmentsWith commitProj
        orchardActionTopLevelCircuit.selectorMap
        orchardActionTopLevelCircuit.domainExponent
        orchardActionTopLevelCircuit.constraintSystem
        (orchardActionTopLevelCircuit.operations 0),
      permutationCommitmentsWith commitProj
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
  rw [← Fast.derivedUrsGLagrangeParFast_eq]
  exact h1

set_option maxRecDepth 1000000 in
/-- The derived fixed-column commitments are the captured ones. -/
theorem derivedFixedCommitments_eq :
    derivedFixedCommitments capturedURS = capturedFixedCommitments := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  have hfc := h.2.1
  simp only [fixedCommitmentsWith] at hfc
  simp only [derivedFixedCommitments, Halo2.TopLevelCircuit.fixedCommitments,
    Halo2.TopLevelCircuit.fixedRows]
  rw [commitProj_eq]
  exact hfc

set_option maxRecDepth 1000000 in
/-- The derived permutation common commitments are the captured ones. -/
theorem derivedPermutationCommonCommitments_eq :
    derivedPermutationCommonCommitments capturedURS
      = capturedPermutationCommonCommitments := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  have hpc := h.2.2.1
  simp only [derivedPermutationCommonCommitments,
    Halo2.TopLevelCircuit.permutationCommitments, permutationCommitmentsOf]
  rw [commitProj_eq]
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
  rw [← commitProj_eq] at hfc hpc
  simp only [actionPinned, Halo2.TopLevelCircuit.selectorMap,
    Halo2.TopLevelCircuit.selectorActivations, Halo2.TopLevelCircuit.regionStarts,
    Halo2.TopLevelCircuit.domainExponent]
    at ho hn hb hc hg hiq haq hfq hpch hli hlt hfc hpc
  -- open both records
  unfold vk
  simp only [derivedActionVk, Halo2.TopLevelCircuit.verifierKeyAt,
    VerifyingKey.ofOperations, fixedCommitmentsOf, permutationCommitmentsOf,
    Halo2.TopLevelCircuit.domainExponent]
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
