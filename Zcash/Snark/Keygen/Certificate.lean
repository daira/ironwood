import Zcash.Snark.Keygen.Derivation
import Zcash.Snark.Keygen.Fast.FastFft
import Zcash.Snark.Fixtures.SingleAction.Fixture

/-!
# Concrete certificate for the derived Action verifying key

This module contains the expensive concrete computation, separately from the reusable
derivation data: `native_decide` bundles comparing every field of the derived verifying
key against the capture. Components are stated over the `TopLevelCircuit` methods and
the once-evaluated `lagrangeBasis` rather than projections of `derivedActionVk` —
projecting the record would strictly build ALL its fields, re-running the FFT and both
commitment passes a second time. The basis itself is computed by the PROVEN-equal
projective FFT (`Fast.derivedUrsGLagrangeFast_eq`), so the group-side cost is one fast
FFT plus one Pippenger commitment pass, all inside `certificate_commitments`; the
remaining bundles are CS-scale. The comparison is split across four theorems because
`Decidable` instance synthesis fails on larger products of these types (specifically,
mixing the `Fp`-typed scalars into a product with the group-element lists defeats the
search); the split keeps each bundle at a shape synthesis accepts, and only the
commitments bundle pays group-side evaluation. `vk_eq_derived`/`vk_eq_toVerifierKey`
assemble the record equality from the bundles' splits; the only definitional steps are
structure eta and within-`Pipeline` unfoldings, so the certificate is robust against
unrelated refactors of the fixture-side spellings.

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
`urs`-parameterized spellings each cost a full group FFT). Computed by the fast
projective-coordinate FFT, which is PROVEN pointwise equal to the Rust-mirroring
`derivedUrsGLagrange` (`Fast.derivedUrsGLagrangeFast_eq`) — the corollaries below
bridge back to the statement-surface name through that equality. -/
private def lagrangeBasis : List G := Fast.derivedUrsGLagrangeFast capturedURS

/-- The derived pinned CS in the `Pipeline`-native spelling (`.derive` at the derived
selector map) — definitionally `ofOperations`' internal `pinned`, which the
`vk_eq_derived` unifications need (the `TopLevelCircuit.pinnedCS` method goes through
Clean's `toPinnedCS` and is only propositionally the same record). Nullary, so the
selector-map/derive work evaluates once per `native_decide` process. -/
private def actionPinned : PinnedConstraintSystem Fp :=
  PinnedConstraintSystem.derive orchardActionTopLevelCircuit.constraintSystem
    orchardActionTopLevelCircuit.selMapDerived

/-- **The derived commitments match the capture** — the group-side bundle: the Lagrange
URS 10-generator prefix cross-check and the 29 fixed-column and 15 permutation
commitments, in ONE `native_decide` so the fast FFT, the fixed contents, the keygen
mapping and all 44 commitment MSMs evaluate exactly once. -/
theorem certificate_commitments :
    (lagrangeBasis.take capturedUrsGLagrange.length,
      fixedCommitmentsOf capturedURS.w lagrangeBasis
        orchardActionTopLevelCircuit.selMapDerived
        orchardActionTopLevelCircuit.domainExponent
        orchardActionTopLevelCircuit.constraintSystem
        (orchardActionTopLevelCircuit.operations 0),
      permutationCommitmentsOf capturedURS.w lagrangeBasis
        orchardActionTopLevelCircuit.domainExponent
        orchardActionTopLevelCircuit.constraintSystem
        (orchardActionTopLevelCircuit.operations 0))
    = (capturedUrsGLagrange,
       capturedFixedCommitments,
       capturedPermutationCommonCommitments) := by
  native_decide

/-- The derived domain/permutation scalars and gates match the captured `vk`'s. -/
theorem certificate_scalars_gates :
    ((omegaOf orchardActionTopLevelCircuit.domainExponent,
       2 ^ orchardActionTopLevelCircuit.domainExponent,
       orchardActionTopLevelCircuit.constraintSystem.blindingFactors, deltaFp,
       orchardActionTopLevelCircuit.constraintSystem.chunkLen),
      actionPinned.gates.map RichExpression.toExpr)
    = ((vk.omega, vk.n, vk.blindingFactors, vk.delta, vk.chunkLen), vk.gates) := by
  native_decide

/-- The derived query layouts match the captured `vk`'s. -/
theorem certificate_layouts :
    (actionPinned.instanceQueryLayout,
      actionPinned.adviceQueryLayout,
      actionPinned.fixedQueryLayout)
    = (vk.instanceQueryLayout, vk.adviceQueryLayout, vk.fixedQueryLayout) := by
  native_decide

/-- The derived permutation chunks, lookup-expression families, and `Shape`
(`ProofParams.mergeDerived`) match the captured `vk`'s and the fixture's. -/
theorem certificate_cs :
    (permutationChunksOf orchardActionTopLevelCircuit.selMapDerived
       orchardActionTopLevelCircuit.constraintSystem,
      (List.ofFn fun l : Fin shape.numLookups =>
          (actionPinned.lookupInputExprs.getD l.val []).map RichExpression.toExpr,
       List.ofFn fun l : Fin shape.numLookups =>
          (actionPinned.lookupTableExprs.getD l.val []).map RichExpression.toExpr),
      actionProofParams.mergeDerived orchardActionTopLevelCircuit)
    = (vk.permutationChunks,
       (List.ofFn vk.lookupInputExprs, List.ofFn vk.lookupTableExprs),
       shape) := by
  native_decide

set_option maxRecDepth 1000000 in
/-- The derived Lagrange URS reproduces the captured 10-generator prefix. -/
theorem derivedUrsGLagrange_prefix_eq :
    (derivedUrsGLagrange capturedURS).take capturedUrsGLagrange.length
      = capturedUrsGLagrange := by
  have h := certificate_commitments
  simp only [Prod.mk.injEq] at h
  rw [← Fast.derivedUrsGLagrangeFast_eq]
  exact h.1

set_option maxRecDepth 1000000 in
/-- The derived fixed-column commitments are the captured ones. -/
theorem derivedFixedCommitments_eq :
    derivedFixedCommitments capturedURS = capturedFixedCommitments := by
  have h := certificate_commitments
  simp only [Prod.mk.injEq] at h
  -- unfold the `Derivation.lean` name to the basis-explicit form, then swap in the
  -- proven-equal fast basis the bundle is stated over
  rw [show derivedFixedCommitments capturedURS
      = fixedCommitmentsOf capturedURS.w (derivedUrsGLagrange capturedURS)
          orchardActionTopLevelCircuit.selMapDerived
          orchardActionTopLevelCircuit.domainExponent
          orchardActionTopLevelCircuit.constraintSystem
          (orchardActionTopLevelCircuit.operations 0) from rfl,
    ← Fast.derivedUrsGLagrangeFast_eq]
  exact h.2.1

set_option maxRecDepth 1000000 in
/-- The derived permutation common commitments are the captured ones. -/
theorem derivedPermutationCommonCommitments_eq :
    derivedPermutationCommonCommitments capturedURS
      = capturedPermutationCommonCommitments := by
  have h := certificate_commitments
  simp only [Prod.mk.injEq] at h
  rw [show derivedPermutationCommonCommitments capturedURS
      = permutationCommitmentsOf capturedURS.w (derivedUrsGLagrange capturedURS)
          orchardActionTopLevelCircuit.domainExponent
          orchardActionTopLevelCircuit.constraintSystem
          (orchardActionTopLevelCircuit.operations 0) from rfl,
    ← Fast.derivedUrsGLagrangeFast_eq]
  exact h.2.2

/-- The fixture's `Shape` is the proof-shape parameters merged with the circuit-derived
counts. -/
theorem shape_eq_mergeDerived :
    actionProofParams.mergeDerived orchardActionTopLevelCircuit = shape := by
  have h := certificate_cs
  simp only [Prod.mk.injEq] at h
  exact h.2.2

set_option maxRecDepth 1000000 in
/-- **The captured Action verifying key is fully derived.** Assembled record-wise from
the bundles' field equalities; the definitional steps are structure eta and
within-`Pipeline` unfoldings only. -/
theorem vk_eq_derived : vk = derivedActionVk shape capturedURS := by
  have hsg := certificate_scalars_gates
  have hly := certificate_layouts
  have hcs := certificate_cs
  simp only [Prod.mk.injEq] at hsg hly hcs
  obtain ⟨⟨ho, hn, hb, hd, hc⟩, hg⟩ := hsg
  obtain ⟨hiq, haq, hfq⟩ := hly
  obtain ⟨hpch, ⟨hli, hlt⟩, -⟩ := hcs
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

assert_no_sorry certificate_commitments
assert_no_sorry vk_eq_derived
assert_no_sorry vk_eq_toVerifierKey

end Zcash.Snark.Keygen
