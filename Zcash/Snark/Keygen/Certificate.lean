import Zcash.Snark.Keygen.Derivation
import Zcash.Snark.Fixtures.SingleAction.Fixture

/-!
# Concrete certificate for the derived Action verifying key

This module contains the expensive concrete computation, separately from the reusable
derivation data: ONE bundled `native_decide` evaluating the derived verifying key once
and comparing every field against the capture — the Lagrange-prefix cross-check and the
two commitment families (the group-side cost), plus the scalar/gate/layout fields and
the derived `Shape` (CS-scale). `vk_eq_derived`/`vk_eq_toVerifierKey` assemble the
record equalities from the bundle's splits; the only definitional steps are structure
eta and within-`Pipeline` unfoldings, so the certificate is robust against unrelated
refactors of the `Bridge`/fixture-side spellings.

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
`urs`-parameterized spellings each cost a full ~11k-smul group FFT). The bundle's
commitment components are stated over `lagrangeBasis` so one FFT serves the prefix
check and both commitment families; the `derived*_eq` corollaries bridge back to the
`Derivation.lean` names definitionally. -/
private def lagrangeBasis : List G := derivedUrsGLagrange capturedURS

/-- **The derived verifying key matches the capture, field by field** — bundled into ONE
`native_decide` so the derived record (and with it the Lagrange FFT, fixed contents,
keygen mapping and all 44 commitment MSMs) evaluates exactly once. Components, in
order: the Lagrange URS 10-generator prefix; the 29 fixed-column and 15 permutation
commitments; the domain/permutation scalars; the gates; the three query layouts; the
permutation chunks; the two lookup-expression families; and the derived `Shape`
(`ProofParams.mergeDerived`) against the fixture's. -/
theorem certificate :
    (let a := derivedActionVk shape capturedURS
     (lagrangeBasis.take capturedUrsGLagrange.length,
      fixedCommitmentsOf capturedURS.w lagrangeBasis
        orchardActionTopLevelCircuit.selMapDerived
        orchardActionTopLevelCircuit.domainExponent
        orchardActionTopLevelCircuit.constraintSystem
        (orchardActionTopLevelCircuit.operations 0),
      permutationCommitmentsOf capturedURS.w lagrangeBasis
        orchardActionTopLevelCircuit.domainExponent
        orchardActionTopLevelCircuit.constraintSystem
        (orchardActionTopLevelCircuit.operations 0),
      (a.omega, a.n, a.blindingFactors, a.delta, a.chunkLen),
      a.gates,
      (a.instanceQueryLayout, a.adviceQueryLayout, a.fixedQueryLayout),
      a.permutationChunks,
      (List.ofFn a.lookupInputExprs, List.ofFn a.lookupTableExprs),
      actionProofParams.mergeDerived orchardActionTopLevelCircuit))
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
  exact h.1

set_option maxRecDepth 1000000 in
/-- The derived fixed-column commitments are the captured ones. -/
theorem derivedFixedCommitments_eq :
    derivedFixedCommitments capturedURS = capturedFixedCommitments := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  -- `lagrangeBasis`-stated component, definitionally the `Derivation.lean` name
  exact h.2.1

set_option maxRecDepth 1000000 in
/-- The derived permutation common commitments are the captured ones. -/
theorem derivedPermutationCommonCommitments_eq :
    derivedPermutationCommonCommitments capturedURS
      = capturedPermutationCommonCommitments := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  exact h.2.2.1

/-- The fixture's `Shape` is the proof-shape parameters merged with the circuit-derived
counts. -/
theorem shape_eq_mergeDerived :
    actionProofParams.mergeDerived orchardActionTopLevelCircuit = shape := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  exact h.2.2.2.2.2.2.2.2

set_option maxRecDepth 1000000 in
/-- **The captured Action verifying key is fully derived.** Assembled record-wise from
the bundle's field equalities; the definitional steps are structure eta and
within-`Pipeline` unfoldings only. -/
theorem vk_eq_derived : vk = derivedActionVk shape capturedURS := by
  have h := certificate
  simp only [Prod.mk.injEq] at h
  obtain ⟨-, -, -, ⟨ho, hn, hb, hd, hc⟩, hg, ⟨hiq, haq, hfq⟩, hpch, ⟨hli, hlt⟩, -⟩ := h
  -- structure eta: the derived key is the record of its own projections
  have ha : derivedActionVk shape capturedURS
      = ⟨(derivedActionVk shape capturedURS).omega,
         (derivedActionVk shape capturedURS).n,
         (derivedActionVk shape capturedURS).blindingFactors,
         (derivedActionVk shape capturedURS).delta,
         (derivedActionVk shape capturedURS).chunkLen,
         (derivedActionVk shape capturedURS).gates,
         (derivedActionVk shape capturedURS).instanceQueryLayout,
         (derivedActionVk shape capturedURS).adviceQueryLayout,
         (derivedActionVk shape capturedURS).fixedQueryLayout,
         (derivedActionVk shape capturedURS).fixedCommitment,
         (derivedActionVk shape capturedURS).permutationCommonCommitment,
         (derivedActionVk shape capturedURS).permutationChunks,
         (derivedActionVk shape capturedURS).lookupInputExprs,
         (derivedActionVk shape capturedURS).lookupTableExprs⟩ := rfl
  rw [ha]
  unfold vk
  rw [VerifyingKey.mk.injEq]
  refine ⟨ho.symm, hn.symm, hb.symm, hd.symm, hc.symm, hg.symm, hiq.symm, haq.symm,
    hfq.symm, ?_, ?_, hpch.symm, ?_, ?_⟩
  · -- fixedCommitment: within-Pipeline unfolding + the certified list equality
    rw [show (derivedActionVk shape capturedURS).fixedCommitment
        = fun i => (derivedFixedCommitments capturedURS).getD i 0 from rfl,
      derivedFixedCommitments_eq]
  · rw [show (derivedActionVk shape capturedURS).permutationCommonCommitment
        = fun i : Fin shape.numPermutationColumns =>
            (derivedPermutationCommonCommitments capturedURS).getD i.val 0
        from rfl,
      derivedPermutationCommonCommitments_eq]
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
