import Zcash.Snark.Soundness.AGM.ZeroFamilyRoots
import Zcash.Snark.Soundness.Composition.StraightLineWitness

/-!
# The straight-line deployed interface, inhabited with live IPA rounds

`zeroStraightLineDeployedFamily` inhabits the straight-line deployed interface over the
shape-generic zero prover, with the IPA-round obligations live: at `k = 11` the staged trace
carries eleven rounds, each discharged by `straightLineIpaRootPolynomial_of_zero_coordinates`
rather than by an empty index type.  `Composition.StraightLineWitness` inhabits the same
interface at the witness shape, where `k = 0` empties those obligations.

Two hypotheses carry it.  The key's two group-valued commitment families are zero, which is what
the zero prover's assembly needs.  And the shape is instance-free, which is what discharges the
constraint layer: with no sub-proofs the folded constraint list is empty and the decoded quotient
pieces have zero coordinates, so the pre-`x` constraint difference is the zero polynomial and the
constraint-`x` root set is empty on every table.

The instance-free hypothesis is confined to that one layer.  The staged IPA trace also comes in a
constant-walk form with the multiopen value free (`zeroConstStraightLineIpaTrace` below), so at a
shape with sub-proofs the zero prover still carries everything except the constraint-`x` stage —
`Fixtures.MultiAction.CapturedZeroFamily` instantiates those live layers at the full captured
shape and records why that last stage is exactly the honest-prover boundary.
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

/-- At an instance-free shape the zero family's pre-`x` constraint difference is the zero
polynomial: no sub-proof contributes a constraint, and the decoded quotient pieces read the
all-zero assembly source. -/
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

/-- Every straight-line IPA round polynomial of the zero prover is the zero polynomial, at every
round of every `k`.  The walk starts at zero because an instance-free zero proof claims only zero
evaluations, so its multiopen value vanishes. -/
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

/-- **The zero family's staged IPA trace.**  The staged polynomial is zero at every one of the
shape's `k` rounds, so `agrees` is a theorem about the discrepancy walk rather than an empty
quantification. -/
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

/-! ### The constant walk, without the instance-free hypothesis

With sub-proofs the zero prover's multiopen value `v` survives, and its walk is the constant
`c = -(ν₁₀ · v)`: every staged IPA polynomial is `C c * X`.  The trace below carries that walk at
any shape — the remaining instance-bearing obligation is the constraint-`x` stage, not the IPA
rounds.
-/

/-- Every straight-line IPA root polynomial of the zero prover is `C (-(ν₁₀ · v)) * X`, `v` the
zero proof's multiopen value.  No instance-free hypothesis: at `numProofs = 0` the constant
vanishes and this reduces to the zero walk. -/
theorem zeroWfProof_straightLineIpaRootPolynomial_const
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (ν : Fin 11 → Fp) (χ : Fin shape.k → Fp) (j : Fin shape.k) :
    (zeroWfProof basis vkS hfixed hperm).straightLineIpaRootPolynomial ν χ j =
      Polynomial.C (-(ν 10 * multiopenValue vkS (fun _ _ => 0)
        (zeroProofString shape Fp VestaG) (chRecord ν (fun _ => 0)))) * Polynomial.X := by
  rw [straightLineIpaRootPolynomial_of_zero_group_coordinates _ ν χ
    (fun _ => ⟨rfl, rfl, rfl, rfl⟩) j]
  rw [straightLineInitialDiscrepancy_of_zero_coordinates _ ν
    (zeroWfProof_aMulti basis vkS hfixed hperm ν)
    (zeroWfProof_multiU basis vkS hfixed hperm ν)
    (zeroWfProof_s basis vkS hfixed hperm)
    (zeroWfProof_sU basis vkS hfixed hperm)]
  have hps : (zeroWfProof basis vkS hfixed hperm).proof.1 =
      zeroProofString shape Fp VestaG := rfl
  rw [hps]

/-- The constant-walk staged polynomial: read the eleven pre-IPA squeezes, then return
`C (-(ν₁₀ · v)) * X`.  No IPA-round point is read. -/
noncomputable def zeroConstIpaStage (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (_j : Fin shape.k) :
    OracleComp
      (BTranscript Fp VestaG
        (preIpaLen shape (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init.length 10 +
          3 * shape.k)) Fp (Polynomial Fp) :=
  (OracleComp.readFin (F := Fp)
    (fun i : Fin 11 =>
      algebraicFullPrefixesPre (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
        (zeroWfProof basis vkS hfixed hperm) i)).bind
    fun ν => .pure (Polynomial.C (-(ν 10 * multiopenValue vkS (fun _ _ => 0)
      (zeroProofString shape Fp VestaG) (chRecord ν (fun _ => 0)))) * Polynomial.X)

/-- The staged polynomial is the run's actual root polynomial: both are the constant walk at the
oracle's answers on the fixed squeeze points. -/
theorem zeroConstIpaStage_agrees (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (j : Fin shape.k)
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init.length 10 +
        3 * shape.k) → Fp) :
    (zeroConstIpaStage vkS hfixed hperm basis j).run O =
      AlgebraicWfProof.straightLineIpaRootPolynomial
        (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O)
        (fun i => O (algebraicFullPrefixesPre
          (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
          (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O) i))
        (fun r => O (algebraicFullPrefixes
          (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
          (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O) r))
        j := by
  rw [zeroConstIpaStage, OracleComp.run_bind, OracleComp.run_readFin, OracleComp.run_pure]
  rw [show (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O) =
    zeroWfProof basis vkS hfixed hperm from rfl]
  show _ = AlgebraicWfProof.straightLineIpaRootPolynomial
    (vk := vkS) (instanceCommitment := fun _ _ => 0)
    (zeroWfProof basis vkS hfixed hperm) _ _ j
  exact (zeroWfProof_straightLineIpaRootPolynomial_const vkS hfixed hperm basis
    (fun i => O (algebraicFullPrefixesPre
      (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
      (zeroWfProof basis vkS hfixed hperm) i))
    (fun r => O (algebraicFullPrefixes
      (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
      (zeroWfProof basis vkS hfixed hperm) r)) j).symm

/-- The stage reads only pre-IPA squeeze points, which are strictly shorter than any IPA round
prefix. -/
theorem zeroConstIpaStage_fresh (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (j : Fin shape.k)
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init.length 10 +
        3 * shape.k) → Fp) :
    straightLineIpaRootPoint (zeroDeployedRootFamily vkS hfixed hperm).toFamily
        (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O) j ∉
      (zeroConstIpaStage vkS hfixed hperm basis j).queries O := by
  have hpoint : straightLineIpaRootPoint (zeroDeployedRootFamily vkS hfixed hperm).toFamily
      (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O) j =
      algebraicFullPrefixes (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
        (zeroWfProof basis vkS hfixed hperm) j := rfl
  rw [hpoint]
  simp only [zeroConstIpaStage, OracleComp.queries_bind, OracleComp.queries_readFin,
    OracleComp.queries, List.append_nil]
  intro hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
  have hlen := congrArg (fun t : BTranscript Fp VestaG _ => t.val.length) hi
  simp only [algebraicFullPrefixesPre, algebraicFullPrefixes,
    fullPrefixesPre, fullPrefixes, roundTranscriptFin_length] at hlen
  have hle := preIpaSqueezePoints_length_le
    (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
    (zeroWfProof basis vkS hfixed hperm).proof.1 i
  omega

/-- **The constant-walk staged IPA trace, at any shape.**  The instance-free zero trace above is
its special case; this one leaves the multiopen value free. -/
noncomputable def zeroConstStraightLineIpaTrace :
    StraightLineIpaOnlineTrace (zeroDeployedRootFamily vkS hfixed hperm).toFamily where
  stage := fun basis j => zeroConstIpaStage vkS hfixed hperm basis j
  agrees := fun basis j O => zeroConstIpaStage_agrees vkS hfixed hperm basis j O
  fresh := fun basis j O => zeroConstIpaStage_fresh vkS hfixed hperm basis j O

/-- The zero family also inhabits the intermediate deployed constraint interface. -/
noncomputable def zeroDeployedConstraintFamily (hproofs : shape.numProofs = 0) :
    ComputedDeployedConstraintFSFamily shape :=
  .ofRoot (zeroDeployedRootFamily vkS hfixed hperm) (zeroConstraintXTrace vkS hfixed hperm hproofs)

end IpaTrace

end Zcash.Snark
