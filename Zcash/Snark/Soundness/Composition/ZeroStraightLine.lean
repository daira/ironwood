import Zcash.Snark.Soundness.AGM.ZeroFamilyRoots
import Zcash.Snark.Soundness.Composition.StraightLineWitness

/-!
# The straight-line deployed interface, inhabited with live IPA rounds

`Composition.StraightLineWitness` inhabits this interface at the degenerate witness shape, where
`k = 0` makes every IPA-round obligation quantify over `Fin 0`.  This module inhabits it over the
shape-generic zero prover instead, so the IPA-round obligations are real: at `k = 11` the staged
trace carries eleven live rounds, each discharged by
`straightLineIpaRootPolynomial_of_zero_coordinates` rather than by emptiness of the index type.

Two hypotheses carry the construction.  The key's two group-valued commitment families are zero —
that is what the zero prover's assembly needs — and the shape is instance-free.  The second is
what makes the constraint layer discharge: with no sub-proofs the folded constraint list is empty
and the decoded quotient pieces have zero coordinates, so the pre-`x` constraint difference is the
zero polynomial and the constraint-`x` root set is empty on every table.  The honest reading is
that this exercises the multiopen grouping, the six root events and the IPA rounds at real key
layouts, and leaves the constraint system trivial; a prover with sub-proofs would have to commit
columns that actually satisfy Orchard's gates.
-/

namespace Zcash.Snark

open Polynomial
open scoped ENNReal

local instance vestaInhabitedZeroStraightLine : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

section ConstraintX

variable (vkS : VerifyingKey shape Fp VestaG)
  (hfixed : ∀ i, vkS.fixedCommitment i = 0)
  (hperm : ∀ i, vkS.permutationCommonCommitment i = 0)

/-- With no sub-proofs the folded constraint list is empty. -/
theorem constraintPolys_nil_of_no_proofs (hproofs : shape.numProofs = 0)
    (fixedCols : ℕ → Polynomial Fp)
    (adviceCols instanceCols : Fin shape.numProofs → ℕ → Polynomial Fp)
    (gates : List (Expr Fp))
    (sets : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin shape.numProofs →
      List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta : Fp) (chunkLen : ℕ) (l0 lLast lBlind : Polynomial Fp) :
    constraintPolys fixedCols adviceCols instanceCols gates sets chunks lookups
      beta gamma delta theta chunkLen l0 lLast lBlind = [] := by
  unfold constraintPolys allConstraints
  have hnil : (List.ofFn (fun p : Fin shape.numProofs =>
      subProofConstraints fixedCols (adviceCols p) (instanceCols p) (gates.map (Expr.map C))
        (sets p) (chunks p)
        (((fun p => (lookups p).map (fun lk =>
          (lk.1, lk.2.1.map (Expr.map C), lk.2.2.map (Expr.map C)))) p))
        (C beta) (C gamma) X (C delta) (C theta) chunkLen l0 lLast lBlind)) = [] :=
    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, hproofs])
  rw [hnil]
  rfl

/-- The zero family's pre-`x` constraint difference is the zero polynomial at an instance-free
shape: no sub-proof contributes a constraint, and the decoded quotient pieces read the all-zero
assembly source. -/
theorem zeroConstraintDifference_eq_zero (hproofs : shape.numProofs = 0)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (coins : (zeroDeployedRootFamily vkS hfixed hperm).toFamily.Coins)
    (root : DeployedRootDecodeWitness (zeroDeployedRootFamily vkS hfixed hperm) basis coins) :
    deployedConstraintDifferenceOfRoot (zeroDeployedRootFamily vkS hfixed hperm) basis coins
      root = 0 := by
  have hbw : root.batchWitness = zeroBatchWitness basis vkS hfixed hperm coins.1 :=
    PSum.inl.inj root.outcome_eq.symm
  have hsource : ∀ ap ∈ deployedConstraintSource (zeroDeployedRootFamily vkS hfixed hperm) basis
      (deployedRootRunOutput (zeroDeployedRootFamily vkS hfixed hperm) basis coins)
      root.batchWitness, ap = zeroAlgebraicPoint basis := by
    rw [hbw]
    intro ap hap
    refine zeroAlgebraicProofString_source_eq basis ?_
    have hrun : (deployedRootRunOutput (zeroDeployedRootFamily vkS hfixed hperm) basis
        coins).1 = zeroWfProof basis vkS hfixed hperm :=
      zeroFamily_wrapped_run basis vkS hfixed hperm coins.1
    unfold deployedConstraintSource at hap
    rw [hrun] at hap
    exact hap
  have hpieces : ∀ i, coeffsToPoly (deployedConstraintPieceCoordinates
      (zeroDeployedRootFamily vkS hfixed hperm) basis
      (deployedRootRunOutput (zeroDeployedRootFamily vkS hfixed hperm) basis coins)
      root.batchWitness i).1 = 0 := by
    intro i
    unfold deployedConstraintPieceCoordinates
    rw [onlinePointCoordinates_zeroSource basis hsource]
    show coeffsToPoly (fun _ => (0 : Fp)) = 0
    simp [coeffsToPoly]
  simp only [deployedConstraintDifferenceOfRoot, committedPreXConstraintDifference,
    combineConstraints, constraintPolys_nil_of_no_proofs hproofs, List.foldl_nil,
    committedPreXQuotient, preXQuotient]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hpieces i, mul_zero])]
  simp

/-- Hence the zero family's constraint-`x` root set is empty on every oracle table. -/
theorem zeroConstraintXBadSet_empty (hproofs : shape.numProofs = 0)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroDeployedRootFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) :
    deployedConstraintXBadSet (zeroDeployedRootFamily vkS hfixed hperm) basis O = ∅ := by
  ext x
  simp only [deployedConstraintXBadSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨tape, root, hx⟩
  rw [zeroConstraintDifference_eq_zero vkS hfixed hperm hproofs basis (O, tape) root] at hx
  exact (mem_szBadSet.mp hx).1 rfl

/-- **The zero family's executable constraint-`x` stage.**  The root set is empty, so the stage
returns it without reading the oracle and freshness of the `x` squeeze is immediate. -/
noncomputable def zeroConstraintXTrace (hproofs : shape.numProofs = 0) :
    DeployedConstraintXOnlineTrace (zeroDeployedRootFamily vkS hfixed hperm) where
  stage := fun _basis => .pure (∅ : Set Fp)
  agrees := fun basis O => by
    rw [OracleComp.run_pure, zeroConstraintXBadSet_empty vkS hfixed hperm hproofs basis O]
  fresh := fun _basis _O => List.not_mem_nil

end ConstraintX

section IpaTrace

variable (vkS : VerifyingKey shape Fp VestaG)
  (hfixed : ∀ i, vkS.fixedCommitment i = 0)
  (hperm : ∀ i, vkS.permutationCommonCommitment i = 0)

/-- Every straight-line IPA round polynomial of the zero prover is the zero polynomial — at every
round of every `k`, not only at shapes with no rounds.  The multiopen value vanishes because the
instance-free zero proof claims only zero evaluations. -/
theorem zeroWfProof_straightLineIpaRootPolynomial (hproofs : shape.numProofs = 0)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (ν : Fin 11 → Fp) (χ : Fin shape.k → Fp) (j : Fin shape.k) :
    (zeroWfProof basis vkS hfixed hperm).straightLineIpaRootPolynomial ν χ j = 0 := by
  refine straightLineIpaRootPolynomial_of_zero_coordinates _ ν χ
    (zeroWfProof_aMulti basis vkS hfixed hperm ν)
    (zeroWfProof_multiU basis vkS hfixed hperm ν)
    (zeroWfProof_s basis vkS hfixed hperm)
    (zeroWfProof_sU basis vkS hfixed hperm) ?_ ?_ j
  · show multiopenValue vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG)
      (chRecord ν (fun _ => 0)) = 0
    exact multiopenValue_zeroProofString hproofs vkS (fun _ _ => 0) _
  · intro r
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The zero family's staged IPA trace.**  Unlike the witness family's, this one has live
rounds: the staged polynomial is the zero polynomial at every one of the shape's `k` rounds, so
`agrees` is a theorem about the discrepancy walk rather than an empty quantification. -/
noncomputable def zeroStraightLineIpaTrace (hproofs : shape.numProofs = 0) :
    StraightLineIpaOnlineTrace (zeroDeployedRootFamily vkS hfixed hperm).toFamily where
  stage := fun _basis _j => .pure 0
  agrees := fun basis j O => by
    rw [OracleComp.run_pure]
    show (0 : Polynomial Fp) = _
    rw [show ((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O =
      zeroWfProof basis vkS hfixed hperm from rfl]
    exact (zeroWfProof_straightLineIpaRootPolynomial vkS hfixed hperm hproofs basis _ _ j).symm
  fresh := fun _basis _j _O => List.not_mem_nil

/-- **An inhabitant of the straight-line deployed family interface with live IPA rounds**: the
zero prover's root family, its empty constraint-`x` stage, and the staged IPA trace over all `k`
rounds. -/
noncomputable def zeroStraightLineDeployedFamily (hproofs : shape.numProofs = 0) :
    ComputedStraightLineDeployedFSFamily shape where
  toComputedDeployedRootFSFamily := zeroDeployedRootFamily vkS hfixed hperm
  ipaTrace := zeroStraightLineIpaTrace vkS hfixed hperm hproofs
  constraintXTrace := zeroConstraintXTrace vkS hfixed hperm hproofs

/-- The zero family also inhabits the intermediate deployed constraint interface. -/
noncomputable def zeroDeployedConstraintFamily (hproofs : shape.numProofs = 0) :
    ComputedDeployedConstraintFSFamily shape :=
  .ofRoot (zeroDeployedRootFamily vkS hfixed hperm) (zeroConstraintXTrace vkS hfixed hperm hproofs)

end IpaTrace

end Zcash.Snark
