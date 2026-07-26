import Zcash.Snark.Soundness.AGM.DeployedRootDecode
import Zcash.Snark.Soundness.ConstraintRouting
import Zcash.Snark.Soundness.Composition.Quotient

/-!
# Constraint supply from rewind-free deployed AGM decoding

The historical constraint-supply theorem obtains member polynomials from accepting `x1` rewind
families.  `DeployedAlgebraicDecode` already supplies the same polynomials directly from
prefix-pinned AGM coordinates, together with their values at every routed node.  This module
connects that deterministic output to the concrete Halo2 constraint layer without reintroducing
the old multiopen probability floors.
-/

namespace Zcash.Snark

open Classical Polynomial

universe u v w

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

variable {G : Type*} [AddCommGroup G] [Module Fp G]

attribute [local irreducible] deployedSetQueries deployedX4PairCount x4BatchCommitments
  x4BatchEvals deployedSetMemberCommitments

/-- Preserve an explicit relation branch while sequencing a successful result. -/
def bindOrRelationWitness {A : Sort u} {B : Sort v} {R : Sort w}
    (outcome : A ⊕' R) (next : A → B ⊕' R) : B ⊕' R :=
  match outcome with
  | PSum.inl value => next value
  | PSum.inr relation => PSum.inr relation

/-- Combine a finite family of computed equality-or-relation comparisons.  The relation branch is
obtained from one failed comparison, never from the bare proposition that some relation exists. -/
noncomputable def forallOrRelationWitness {I : Type*} [Fintype I]
    {P : I → Prop} {R : Sort u} (outcome : ∀ i, P i ⊕' R) :
    (∀ i, P i) ⊕' R := by
  classical
  by_cases hall : ∀ i, P i
  · exact PSum.inl hall
  · simp only [not_forall] at hall
    let i := Classical.choose hall
    have hnot := Classical.choose_spec hall
    cases hi : outcome i with
    | inl proof => exact absurd proof hnot
    | inr relation => exact PSum.inr relation

/-- Small proof bundle used to sequence the nine finite binding comparisons consumed by the
constraint adapter without collapsing any failed comparison to an existential proposition. -/
structure ConstraintAgreementBundle
    (A B C D E F G H I : Prop) : Prop where
  advice : A
  instanceCols : B
  fixed : C
  permutation : D
  common : E
  lookupProduct : F
  lookupInput : G
  lookupTable : H
  quotient : I

/-! ## The pre-IPA facts actually consumed by constraint routing -/

/-- Constraint routing does not consume the IPA verification equation.  It only needs the three
pre-IPA guards enforced before that equation is assembled: unique `(commitment, point)` queries,
one `multiopenU` value per grouped point set, and exclusion of an `n`th root of unity at `x`. -/
structure DeployedConstraintChecks [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Prop where
  noDuplicate : hasDuplicateCommitmentPoint (assembleQueries vk instanceCommitment ps ch) = false
  uCount : (List.ofFn ps.multiopenU).length =
    (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.length
  xnNeOne : ch.x ^ vk.n ≠ 1

/-- Actual deployed acceptance supplies the pre-IPA checks at the representation record.  The
round vector may differ because none of these checks reads `ipaRound`. -/
theorem DeployedConstraintChecks.of_accepts_chRecord [DecidableEq G] [Inhabited G]
    {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (nu : Fin 11 -> Fp) (rounds : Fin shape.k -> Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps (chRecord nu rounds)) :
    DeployedConstraintChecks vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  obtain ⟨hdup, hu⟩ := deployedAccepts_pipeline urs hk vk instanceCommitment ps (chRecord nu rounds) hacc
  have hxn := deployedAccepts_xn_ne_one urs hk vk instanceCommitment ps (chRecord nu rounds) hacc
  refine ⟨?_, ?_, ?_⟩
  · change hasDuplicateCommitmentPoint (assembleQueries vk instanceCommitment ps (chRecord nu rounds)) = false
    exact hdup
  · change (List.ofFn ps.multiopenU).length =
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps (chRecord nu rounds))).sets.length
    exact hu
  · change (chRecord nu rounds).x ^ vk.n ≠ 1
    exact hxn

/-- The pair count follows from the precise `multiopenU` guard, without the final IPA equation. -/
theorem deployedX4PairCount_eq_sets_length_of_checks [DecidableEq G] [Inhabited G]
    {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (checks : DeployedConstraintChecks vk instanceCommitment ps ch) :
    deployedX4PairCount vk instanceCommitment ps ch =
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.length := by
  rw [deployedX4PairCount_eq, deployedX4Pairs, List.length_zip, deployedX4Qs]
  simp only [List.length_map, List.length_zip, checks.uCount,
    ← constructIntermediateSets_points_length (assembleQueries vk instanceCommitment ps ch), min_self]

/-- Slot routing from the two grouping guards, with no dependence on the final IPA equation. -/
theorem deployed_slot_routed_all_of_checks [DecidableEq G] [Inhabited G]
    {shape : Shape} (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    {c : CommitmentId} {q0 : VerifierQuery shape.k Fp G}
    (hq0 : q0 ∈ assembleQueries vk instanceCommitment ps ch) (hq0c : q0.commId = c) :
    ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
      ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        (∀ c0, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 = c) ∧
        (∀ d0, ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) d0).1 = q0.commitment) ∧
        ∀ q ∈ assembleQueries vk instanceCommitment ps ch, q.commId = c ->
          q.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
          ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
              (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
                q.point) 0 = q.eval := by
  obtain ⟨i, hi, m, hmlt, hids, hcomm, hall⟩ :=
    constructIntermediateSets_comm_routed_all (assembleQueries vk instanceCommitment ps ch) hq0 hq0c
      (fun q hq q' hq' hid hpt =>
        congrArg VerifierQuery.eval
          (eq_of_not_hasDuplicateCommitmentPoint checks.noDuplicate hq' hq hid hpt))
      (fun q hq hid => assembleQueries_commitment_eq_of_commId vk instanceCommitment ps ch hq0 hq
        (hid.trans hq0c.symm))
  have hmlen : m < (deployedSetQueries vk instanceCommitment ps ch i).length := by
    simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using hmlt
  refine ⟨i, ?_, ⟨m, hmlen⟩, hids, ?_, ?_⟩
  · rw [deployedX4PairCount_eq_sets_length_of_checks vk instanceCommitment ps ch checks]
    exact hi
  · intro d0
    simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using hcomm d0
  · intro q hq hqc
    obtain ⟨hpt, hev⟩ := hall q hq hqc
    refine ⟨by rw [deployedSetPts, List.mem_toFinset]; exact hpt, ?_⟩
    have h := hev (.point 0, []) 0
    simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using h

/-- The vanishing slot retains the exact reassembled quotient commitment as well as its routed
evaluation.  This commitment-aware form is the deterministic input needed by pre-`x` quotient
recovery. -/
theorem vanishing_slot_routed_full [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    ∃ i, i < (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.length ∧
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [] = [ch.x] ∧
      ∃ m, m < (deployedSetQueries vk instanceCommitment ps ch i).length ∧
        (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD m c₀ =
          CommitmentId.vanishingH) ∧
        (∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD m d₀).1 = .msm
          (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces))) ∧
        ∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD m d₀).2 =
          [expectedHEval
            (allExpressions vk ps ch
              (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
              (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
              (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
            ch.y (ch.x ^ vk.n)] := by
  obtain ⟨i, hi, hpts, m, hm, hids, hevals⟩ :=
    vanishing_slot_routed vk instanceCommitment ps ch
  have hcommit : ∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD m d₀).1 =
      .msm (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces)) := by
    intro d₀
    have h := deployed_member_commitment_eq_assembled vk instanceCommitment ps ch i
      ⟨m, hm⟩ CommitmentId.vanishingH (hids CommitmentId.vanishingH) d₀
    simpa only [assembledCommitment] using h
  exact ⟨i, hi, hpts, m, hm, hids, hcommit, hevals⟩

/-- The polynomial represented by member `m` of deployed point set `i`. -/
noncomputable def DeployedAlgebraicDecode.memberPoly [DecidableEq G] [Inhabited G]
    {shape : Shape} {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G} {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) : Polynomial Fp :=
  coeffsToPoly ((decoded.batches.x1 i hi).coeffs m)

/-- The rewind-free decoder's member polynomial takes the proof string's recorded value at every
point routed to its set.  This is the direct AGM replacement for
`deployed_member_node_binding_at_point_budgeted`: it has no rewind probability premise and no
relation disjunction because both were discharged while constructing `DeployedAlgebraicDecode`.
-/
theorem DeployedAlgebraicDecode.memberPoly_eval_at_point [DecidableEq G] [Inhabited G]
    {shape : Shape} {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G} {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length)
    {p : Fp} (hpt : p ∈ deployedSetPts vk instanceCommitment ps ch i) :
    (decoded.memberPoly i hi m).eval p =
      ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
        (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf p) 0 := by
  have hmem : p ∈ (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [] := by
    rw [deployedSetPts] at hpt
    exact List.mem_toFinset.mp hpt
  have hmem' : p ∈ ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1 := by
    rw [deployedSetsForEval_getD_points vk instanceCommitment ps ch hi]
    exact hmem
  have hlt : ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.idxOf p <
      ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length :=
    List.idxOf_lt_length_iff.mpr hmem'
  let idx : Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.length :=
    ⟨((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.idxOf p, hlt⟩
  have hb := decoded.memberValues i hi idx m
  change (decoded.memberPoly i hi m).eval
      ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx] = _ at hb
  have hidx : ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx] = p := by
    exact List.getElem_idxOf hlt
  have hidxOf : ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.idxOf p =
      ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf p := by
    rw [deployedSetsForEval_getD_points vk instanceCommitment ps ch hi]
  rw [hidx] at hb
  change (decoded.memberPoly i hi m).eval p =
      ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
        (((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1.idxOf p) 0 at hb
  rw [hidxOf] at hb
  exact hb

/-- The exact deterministic interface consumed by the constraint layer: one polynomial per routed
member and its value at every point in that member's set. -/
structure DeployedMemberPolynomials [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) where
  poly : forall i, i < deployedX4PairCount vk instanceCommitment ps ch ->
    Fin (deployedSetQueries vk instanceCommitment ps ch i).length -> Polynomial Fp
  eval_at_point : forall i (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
      (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) (p : Fp),
    p ∈ deployedSetPts vk instanceCommitment ps ch i ->
    (poly i hi m).eval p =
      ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
        (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf p) 0

/-- Package the rewind-free AGM decode as the deterministic member-polynomial interface. -/
noncomputable def DeployedAlgebraicDecode.toMemberPolynomials [DecidableEq G] [Inhabited G]
    {shape : Shape} {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G} {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    DeployedMemberPolynomials vk instanceCommitment ps ch :=
  { poly := decoded.memberPoly
    eval_at_point := decoded.memberPoly_eval_at_point }

/-- The decoded aggregate directly opens the deployed IPA statement.  This is the algebraic
counterpart of `OpenedBatchOpenings.ipaRelation_of_x4Current`; it uses the actual `x4` power batch,
not a family of accepting rewinds. -/
theorem DeployedAlgebraicDecode.ipaRelation [DecidableEq G] [Inhabited G]
    {shape : Shape} {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G} {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW) :
    IpaRelation urs
      (deployedCommitment urs hk vk instanceCommitment ps ch - aggregateU • urs.u - aggregateW • urs.w)
      (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) aggregate := by
  let cols : AlgebraicColumnRepresentations urs (x4BatchCommitments urs hk vk instanceCommitment ps ch) :=
    { coeffs := decoded.batches.x4.coeffs
      uComp := decoded.batches.x4.uComp
      wComp := decoded.batches.x4.wComp
      commitment := decoded.batches.x4.commitment }
  have hc := cols.power_commitment ch.x4
  rw [<- decoded.batches.x4.reconstruct, <- decoded.batches.x4.reconstructU,
    <- decoded.batches.x4.reconstructW] at hc
  have hbatch := deployedCommitment_x4_batch urs hk vk instanceCommitment ps ch ch.x4
  have heta : {ch with x4 := ch.x4} = ch := by cases ch; rfl
  rw [heta] at hbatch
  have hcommit : commit urs aggregate + aggregateU • urs.u + aggregateW • urs.w =
      deployedCommitment urs hk vk instanceCommitment ps ch := hc.trans hbatch.symm
  refine ⟨?_, ?_⟩
  · rw [sub_sub, eq_sub_iff_add_eq]
    simpa [add_assoc] using hcommit
  · have hv : commitGen (evalVector urs.k ch.x3) aggregate =
        ∑ j : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1),
          ch.x4 ^ (j : Nat) *
            commitGen (evalVector urs.k ch.x3) (decoded.batches.x4.coeffs j) := by
      calc
        commitGen (evalVector urs.k ch.x3) aggregate =
            commitGen (evalVector urs.k ch.x3)
              (∑ j : Fin (deployedX4PairCount vk instanceCommitment ps ch + 1),
                ch.x4 ^ (j : Nat) • decoded.batches.x4.coeffs j) :=
          congrArg (commitGen (evalVector urs.k ch.x3)) decoded.batches.x4.reconstruct
        _ = _ := by
          rw [commitGen_sum]
          exact Finset.sum_congr rfl fun j _ => by
            rw [commitGen_smul_left, smul_eq_mul]
    have hib : innerProduct aggregate (evalVector urs.k ch.x3) =
        commitGen (evalVector urs.k ch.x3) aggregate := by
      simp [innerProduct, commitGen, smul_eq_mul]
    rw [hib, hv]
    rw [Finset.sum_congr rfl (fun j _ => by rw [decoded.x4Values j])]
    have hvalues := multiopenValue_x4_batch vk instanceCommitment ps ch ch.x4
    rw [heta] at hvalues
    exact hvalues.symm

/-! ## The canonical pre-`x` constraint polynomial -/

/-- Advice feeds built from an arbitrary pre-`x` polynomial source for committed points. -/
noncomputable def committedAdviceFeed [Inhabited G] {shape : Shape}
    (poly : G -> Polynomial Fp) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) :
    Fin shape.numProofs -> Nat -> Polynomial Fp := fun q =>
  rotatedFeed vk.omega vk.adviceQueryLayout fun j : Fin shape.numAdviceQueries =>
    poly (finFnG (ps.adviceCommitments q)
      (vk.adviceQueryLayout.getD (j : Nat) (0, 0)).1)

/-- Instance feeds built from a pre-`x` polynomial source. -/
noncomputable def committedInstanceFeed {shape : Shape} (poly : G -> Polynomial Fp)
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) :
    Fin shape.numProofs -> Nat -> Polynomial Fp := fun q =>
  rotatedFeed vk.omega vk.instanceQueryLayout fun j : Fin shape.numInstanceQueries =>
    poly (instanceCommitment q (vk.instanceQueryLayout.getD (j : Nat) (0, 0)).1)

/-- Fixed-column feed built from a pre-`x` polynomial source. -/
noncomputable def committedFixedFeed {shape : Shape} (poly : G -> Polynomial Fp)
    (vk : VerifyingKey shape Fp G) : Nat -> Polynomial Fp :=
  rotatedFeed vk.omega vk.fixedQueryLayout fun j : Fin shape.numFixedQueries =>
    poly (vk.fixedCommitment (vk.fixedQueryLayout.getD (j : Nat) (0, 0)).1)

/-- Permutation-product carriers built from a pre-`x` polynomial source. -/
noncomputable def committedPermSets {shape : Shape} (poly : G -> Polynomial Fp)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) :
    Fin shape.numProofs -> List (PermSetEval (Polynomial Fp)) := fun q =>
  List.ofFn fun s : Fin shape.numPermutationSets =>
    let z := poly (ps.permutationProduct q s)
    PermSetEval.mk z
      (z.comp (Polynomial.C (vk.omega ^ (1 : Int)) * Polynomial.X))
      ((ps.permutationSetEvals q s).lastEval.map fun le =>
        if (s : Nat) + 1 < shape.numPermutationSets then
          z.comp (Polynomial.C (vk.omega ^ (-((vk.blindingFactors : Int) + 1))) * Polynomial.X)
        else Polynomial.C le)

/-- Common permutation columns built from a pre-`x` polynomial source. -/
noncomputable def committedPermCommonFeed [Inhabited G] {shape : Shape}
    (poly : G -> Polynomial Fp) (vk : VerifyingKey shape Fp G) : Nat -> Polynomial Fp := fun c =>
  if h : c < shape.numPermutationColumns then poly (vk.permutationCommonCommitment ⟨c, h⟩)
  else 0

/-- Permutation chunks built from a pre-`x` polynomial source. -/
noncomputable def committedPermChunks [Inhabited G] {shape : Shape}
    (poly : G -> Polynomial Fp) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G) :
    Fin shape.numProofs ->
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)) := fun q =>
  ((committedPermSets poly vk ps q).zip vk.permutationChunks).map fun sc =>
    (sc.1, sc.2.map fun cr =>
      ((match cr.1 with
        | .advice i => committedAdviceFeed poly vk ps q i
        | .fixed i => committedFixedFeed poly vk i
        | .instance i => committedInstanceFeed poly vk instanceCommitment q i),
       committedPermCommonFeed poly vk cr.2))

/-- Lookup carriers built from a pre-`x` polynomial source. -/
noncomputable def committedLookups {shape : Shape} (poly : G -> Polynomial Fp)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) :
    Fin shape.numProofs ->
      List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)) := fun q =>
  List.ofFn fun l : Fin shape.numLookups =>
    let product := poly (ps.lookupProduct q l)
    let input := poly (ps.lookupPermutedInput q l)
    let table := poly (ps.lookupPermutedTable q l)
    (LookupEval.mk product
      (product.comp (Polynomial.C (vk.omega ^ (1 : Int)) * Polynomial.X)) input
      (input.comp (Polynomial.C (vk.omega ^ (-1 : Int)) * Polynomial.X)) table,
     vk.lookupInputExprs l, vk.lookupTableExprs l)

/-- Pre-`x` quotient assembled from explicit represented quotient-piece polynomials. -/
noncomputable def committedPreXQuotient {shape : Shape} (vk : VerifyingKey shape Fp G)
    (piecePoly : Fin shape.numQuotientPieces -> Polynomial Fp) : Polynomial Fp :=
  preXQuotient vk.n piecePoly

/-- The pre-`x` constraint difference built entirely from explicit online AGM coordinates. -/
noncomputable def committedPreXConstraintDifference [Inhabited G] {shape : Shape}
    (poly : G -> Polynomial Fp)
    (piecePoly : Fin shape.numQuotientPieces -> Polynomial Fp)
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : Polynomial Fp :=
  combineConstraints (committedFixedFeed poly vk) (committedAdviceFeed poly vk ps)
      (committedInstanceFeed poly vk instanceCommitment) vk.gates (committedPermSets poly vk ps)
      (committedPermChunks poly vk instanceCommitment ps) (committedLookups poly vk ps)
      ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
      (lagrangeBasisPoly vk.omega vk.n 0)
      (lagrangeBasisPoly vk.omega vk.n (-((vk.blindingFactors : Int) + 1)))
      (((List.range vk.blindingFactors).map
        (fun j => lagrangeBasisPoly vk.omega vk.n (-((j : Int) + 1)))).foldl (· + ·) 0)
    - committedPreXQuotient vk piecePoly * (Polynomial.X ^ vk.n - 1)

/-- Computed comparison between the decoded vanishing member and a pre-`x` quotient assembled
from explicit online quotient-piece coordinates. -/
noncomputable def DeployedAlgebraicDecode.quotientEvalEqCommittedPreXOrRelationWitness
    [DecidableEq G] [Inhabited G]
    {shape : Shape} {urs : URS G} {hk : shape.k = urs.k}
    {vk : VerifyingKey shape Fp G} {instanceCommitment : Fin shape.numProofs → Nat → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (pieceCoeffs : Fin shape.numQuotientPieces -> Fin (2 ^ urs.k) -> Fp)
    (pieceU pieceW : Fin shape.numQuotientPieces -> Fp)
    (piecePoly : Fin shape.numQuotientPieces -> Polynomial Fp)
    (hpieceOpen : ∀ i, commit urs (pieceCoeffs i) + pieceU i • urs.u +
      pieceW i • urs.w = ps.hPieces i)
    (hpiecePoly : ∀ i, coeffsToPoly (pieceCoeffs i) = piecePoly i)
    {i : Nat} (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hcommit : ∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) d₀).1 =
      .msm (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces))) :
    ((decoded.memberPoly i hi m).eval ch.x =
        (preXQuotient vk.n piecePoly).eval ch.x) ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  have hopen := (decoded.batches.x1 i hi).commitment m
  rw [deployedSetMemberCommitments_apply, hcommit (.point 0, [])] at hopen
  have hvanishing :
      (vanishingHCommitment shape.k (ch.x ^ vk.n) (List.ofFn ps.hPieces)).eval
          ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ =
        ∑ j : Fin shape.numQuotientPieces,
          (ch.x ^ vk.n) ^ (j : Nat) • ps.hPieces j := by
    calc
      _ = ∑ j ∈ Finset.range (List.ofFn ps.hPieces).length,
          (ch.x ^ vk.n) ^ j • (List.ofFn ps.hPieces).getD j 0 :=
        vanishingHCommitment_eval (⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ : URS G)
          (ch.x ^ vk.n) (List.ofFn ps.hPieces)
      _ = _ := by
        rw [List.length_ofFn, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt),
          List.getElem_ofFn]
  have hopen' :
      commit urs ((decoded.batches.x1 i hi).coeffs m) +
          (decoded.batches.x1 i hi).uComp m • urs.u +
          (decoded.batches.x1 i hi).wComp m • urs.w =
        ∑ j : Fin shape.numQuotientPieces,
          (ch.x ^ vk.n) ^ (j : Nat) • ps.hPieces j := by
    rw [hopen]
    exact hvanishing
  exact match decodedQuotientEqReassembledOrRelationWitness urs (ch.x ^ vk.n)
      hpieceOpen hopen' with
    | PSum.inr relation => PSum.inr relation
    | PSum.inl hdecoded => PSum.inl (by
        change (coeffsToPoly ((decoded.batches.x1 i hi).coeffs m)).eval ch.x = _
        rw [hdecoded]
        have hp : (fun j => coeffsToPoly (pieceCoeffs j)) = piecePoly := funext hpiecePoly
        rw [hp, reassembledQuotient_eval_eq_preXQuotient_eval])

/-! ## Routed feeds from a deterministic member source -/

open Classical in
/-- Advice-column feed binding from rewind-free member polynomials. -/
theorem adviceFeed_bind_of_memberPolynomials [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    (hAdvLen : shape.numAdviceQueries ≤ vk.adviceQueryLayout.length) :
    ∃ (adviceSet : Fin shape.numProofs -> Fin shape.numAdviceQueries -> Nat)
      (hadviceSet : forall q j, adviceSet q j < deployedX4PairCount vk instanceCommitment ps ch)
      (adviceMem : forall (q : Fin shape.numProofs) (j : Fin shape.numAdviceQueries),
        Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet q j)).length),
      (forall (q : Fin shape.numProofs) (j : Fin shape.numAdviceQueries),
        (deployedSetCommIds vk instanceCommitment ps ch (adviceSet q j)).getD (adviceMem q j : Nat)
            CommitmentId.vanishingH =
          CommitmentId.adviceCol q (vk.adviceQueryLayout.getD (j : Nat) (0, 0)).1) ∧
      forall (q : Fin shape.numProofs) (n : Nat),
        (rotatedFeed vk.omega vk.adviceQueryLayout
          (fun j : Fin shape.numAdviceQueries =>
            src.poly (adviceSet q j) (hadviceSet q j) (adviceMem q j)) n).eval ch.x =
          finFn (ps.adviceEvals q) n := by
  have hsel : forall (q : Fin shape.numProofs) (j : Fin shape.numAdviceQueries),
      exists i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        exists m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (forall c0, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 =
            CommitmentId.adviceCol q (vk.adviceQueryLayout.getD (j : Nat) (0, 0)).1) ∧
          rotateOmega vk.omega ch.x (vk.adviceQueryLayout.getD (j : Nat) (0, 0)).2 ∈
            deployedSetPts vk instanceCommitment ps ch i ∧
          ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
              (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
                (rotateOmega vk.omega ch.x (vk.adviceQueryLayout.getD (j : Nat) (0, 0)).2)) 0 =
            finFn (ps.adviceEvals q) (j : Nat) :=
    fun q j => by
      obtain ⟨q0, hq0, hq0id, hq0pt, hq0ev⟩ :=
        advice_query_mem_assembleQueries_eval vk instanceCommitment ps ch q
          (lt_of_lt_of_le j.isLt hAdvLen) j.isLt
      obtain ⟨i, hi, m, hids, _hcomm, hall⟩ :=
        deployed_slot_routed_all_of_checks vk instanceCommitment ps ch checks hq0 hq0id
      obtain ⟨hpt, hev⟩ := hall q0 hq0 hq0id
      exact ⟨i, hi, m, fun c0 => hids c0, hq0pt ▸ hpt,
        by rw [hq0pt, hq0ev] at hev; exact hev⟩
  choose iSel hiSel mSel hidsSel hptSel hevSel using hsel
  refine ⟨iSel, hiSel, mSel, fun q j => hidsSel q j CommitmentId.vanishingH, ?_⟩
  intro q n
  by_cases h : n < shape.numAdviceQueries
  · rw [rotatedFeed_eval vk.omega vk.adviceQueryLayout _ h ch.x]
    rw [src.eval_at_point (iSel q ⟨n, h⟩) (hiSel q ⟨n, h⟩) (mSel q ⟨n, h⟩)
      _ (hptSel q ⟨n, h⟩)]
    exact hevSel q ⟨n, h⟩
  · rw [rotatedFeed_eval_of_ge vk.omega vk.adviceQueryLayout _ (Nat.not_lt.mp h) ch.x,
      finFn, dif_neg h]

open Classical in
/-- Instance-column twin of `adviceFeed_bind_of_memberPolynomials`. -/
theorem instanceFeed_bind_of_memberPolynomials [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    (hInstLen : shape.numInstanceQueries ≤ vk.instanceQueryLayout.length) :
    ∃ (instanceSet : Fin shape.numProofs -> Fin shape.numInstanceQueries -> Nat)
      (hinstanceSet : forall q j, instanceSet q j < deployedX4PairCount vk instanceCommitment ps ch)
      (instanceMem : forall (q : Fin shape.numProofs) (j : Fin shape.numInstanceQueries),
        Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet q j)).length),
      (forall (q : Fin shape.numProofs) (j : Fin shape.numInstanceQueries),
        (deployedSetCommIds vk instanceCommitment ps ch (instanceSet q j)).getD (instanceMem q j : Nat)
            CommitmentId.vanishingH =
          CommitmentId.instanceCol q (vk.instanceQueryLayout.getD (j : Nat) (0, 0)).1) ∧
      forall (q : Fin shape.numProofs) (n : Nat),
        (rotatedFeed vk.omega vk.instanceQueryLayout
          (fun j : Fin shape.numInstanceQueries =>
            src.poly (instanceSet q j) (hinstanceSet q j) (instanceMem q j)) n).eval ch.x =
          finFn (ps.instanceEvals q) n := by
  have hsel : forall (q : Fin shape.numProofs) (j : Fin shape.numInstanceQueries),
      exists i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        exists m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (forall c0, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 =
            CommitmentId.instanceCol q (vk.instanceQueryLayout.getD (j : Nat) (0, 0)).1) ∧
          rotateOmega vk.omega ch.x (vk.instanceQueryLayout.getD (j : Nat) (0, 0)).2 ∈
            deployedSetPts vk instanceCommitment ps ch i ∧
          ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
              (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
                (rotateOmega vk.omega ch.x (vk.instanceQueryLayout.getD (j : Nat) (0, 0)).2)) 0 =
            finFn (ps.instanceEvals q) (j : Nat) :=
    fun q j => by
      obtain ⟨q0, hq0, hq0id, hq0pt, hq0ev⟩ :=
        instance_query_mem_assembleQueries_eval vk instanceCommitment ps ch q
          (lt_of_lt_of_le j.isLt hInstLen) j.isLt
      obtain ⟨i, hi, m, hids, _hcomm, hall⟩ :=
        deployed_slot_routed_all_of_checks vk instanceCommitment ps ch checks hq0 hq0id
      obtain ⟨hpt, hev⟩ := hall q0 hq0 hq0id
      exact ⟨i, hi, m, fun c0 => hids c0, hq0pt ▸ hpt,
        by rw [hq0pt, hq0ev] at hev; exact hev⟩
  choose iSel hiSel mSel hidsSel hptSel hevSel using hsel
  refine ⟨iSel, hiSel, mSel, fun q j => hidsSel q j CommitmentId.vanishingH, ?_⟩
  intro q n
  by_cases h : n < shape.numInstanceQueries
  · rw [rotatedFeed_eval vk.omega vk.instanceQueryLayout _ h ch.x]
    rw [src.eval_at_point (iSel q ⟨n, h⟩) (hiSel q ⟨n, h⟩) (mSel q ⟨n, h⟩)
      _ (hptSel q ⟨n, h⟩)]
    exact hevSel q ⟨n, h⟩
  · rw [rotatedFeed_eval_of_ge vk.omega vk.instanceQueryLayout _ (Nat.not_lt.mp h) ch.x,
      finFn, dif_neg h]

open Classical in
/-- Fixed-column feed binding from rewind-free member polynomials. -/
theorem fixedFeed_bind_of_memberPolynomials [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    (hFixedLen : shape.numFixedQueries ≤ vk.fixedQueryLayout.length) :
    ∃ (fixedSet : Fin shape.numFixedQueries -> Nat)
      (hfixedSet : forall j, fixedSet j < deployedX4PairCount vk instanceCommitment ps ch)
      (fixedMem : forall j : Fin shape.numFixedQueries,
        Fin (deployedSetQueries vk instanceCommitment ps ch (fixedSet j)).length),
      (forall j : Fin shape.numFixedQueries,
        (deployedSetCommIds vk instanceCommitment ps ch (fixedSet j)).getD (fixedMem j : Nat)
            CommitmentId.vanishingH =
          CommitmentId.fixedCol (vk.fixedQueryLayout.getD (j : Nat) (0, 0)).1) ∧
      forall n : Nat,
        (rotatedFeed vk.omega vk.fixedQueryLayout
          (fun j : Fin shape.numFixedQueries =>
            src.poly (fixedSet j) (hfixedSet j) (fixedMem j)) n).eval ch.x =
          finFn ps.fixedEvals n := by
  have hsel : forall j : Fin shape.numFixedQueries,
      exists i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        exists m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (forall c0, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 =
            CommitmentId.fixedCol (vk.fixedQueryLayout.getD (j : Nat) (0, 0)).1) ∧
          rotateOmega vk.omega ch.x (vk.fixedQueryLayout.getD (j : Nat) (0, 0)).2 ∈
            deployedSetPts vk instanceCommitment ps ch i ∧
          ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
              (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
                (rotateOmega vk.omega ch.x (vk.fixedQueryLayout.getD (j : Nat) (0, 0)).2)) 0 =
            finFn ps.fixedEvals (j : Nat) :=
    fun j => by
      obtain ⟨q0, hq0, hq0id, hq0pt, hq0ev⟩ :=
        fixed_query_mem_assembleQueries vk instanceCommitment ps ch
          (lt_of_lt_of_le j.isLt hFixedLen) j.isLt
      obtain ⟨i, hi, m, hids, _hcomm, hall⟩ :=
        deployed_slot_routed_all_of_checks vk instanceCommitment ps ch checks hq0 hq0id
      obtain ⟨hpt, hev⟩ := hall q0 hq0 hq0id
      exact ⟨i, hi, m, fun c0 => hids c0, hq0pt ▸ hpt,
        by rw [hq0pt, hq0ev] at hev; exact hev⟩
  choose iSel hiSel mSel hidsSel hptSel hevSel using hsel
  refine ⟨iSel, hiSel, mSel, fun j => hidsSel j CommitmentId.vanishingH, ?_⟩
  intro n
  by_cases h : n < shape.numFixedQueries
  · rw [rotatedFeed_eval vk.omega vk.fixedQueryLayout _ h ch.x]
    rw [src.eval_at_point (iSel ⟨n, h⟩) (hiSel ⟨n, h⟩) (mSel ⟨n, h⟩)
      _ (hptSel ⟨n, h⟩)]
    exact hevSel ⟨n, h⟩
  · rw [rotatedFeed_eval_of_ge vk.omega vk.fixedQueryLayout _ (Nat.not_lt.mp h) ch.x,
      finFn, dif_neg h]

open Classical in
/-- Permutation-set carriers from rewind-free member polynomials. -/
theorem permSets_bind_of_memberPolynomials [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch) :
    ∃ (permSel : Fin shape.numProofs -> Fin shape.numPermutationSets -> Nat)
      (hpermSel : forall q s, permSel q s < deployedX4PairCount vk instanceCommitment ps ch)
      (permMem : forall (q : Fin shape.numProofs) (s : Fin shape.numPermutationSets),
        Fin (deployedSetQueries vk instanceCommitment ps ch (permSel q s)).length),
      (forall (q : Fin shape.numProofs) (s : Fin shape.numPermutationSets),
        (deployedSetCommIds vk instanceCommitment ps ch (permSel q s)).getD (permMem q s : Nat)
            CommitmentId.vanishingH = CommitmentId.permProduct q s) ∧
      forall q : Fin shape.numProofs,
        (List.ofFn (fun s : Fin shape.numPermutationSets => PermSetEval.mk
          (src.poly (permSel q s) (hpermSel q s) (permMem q s))
          ((src.poly (permSel q s) (hpermSel q s) (permMem q s)).comp
            (Polynomial.C (vk.omega ^ (1 : Int)) * Polynomial.X))
          ((ps.permutationSetEvals q s).lastEval.map (fun le =>
            if (s : Nat) + 1 < shape.numPermutationSets then
              (src.poly (permSel q s) (hpermSel q s) (permMem q s)).comp
                (Polynomial.C (vk.omega ^ (-((vk.blindingFactors : Int) + 1))) * Polynomial.X)
            else Polynomial.C le)))).map (PermSetEval.map (fun r => r.eval ch.x)) =
          subProofPermSets ps q := by
  have hsel : forall (q : Fin shape.numProofs) (s : Fin shape.numPermutationSets),
      exists i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        exists m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (forall c0, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 =
            CommitmentId.permProduct q s) ∧
          forall q', q' ∈ assembleQueries vk instanceCommitment ps ch -> q'.commId = CommitmentId.permProduct q s ->
            q'.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
            ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
                (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
                  []).idxOf q'.point) 0 = q'.eval := by
    intro q s
    obtain ⟨q0, hq0, hq0id, -, -⟩ := perm_product_query_mem_assembleQueries vk instanceCommitment ps ch q s
    obtain ⟨i, hi, m, hids, _hcomm, hall⟩ :=
      deployed_slot_routed_all_of_checks vk instanceCommitment ps ch checks hq0 hq0id
    exact ⟨i, hi, m, hids, hall⟩
  choose iSel hiSel mSel hidsSel hallSel using hsel
  refine ⟨iSel, hiSel, mSel, fun q s => hidsSel q s CommitmentId.vanishingH, ?_⟩
  intro q
  rw [List.map_ofFn, subProofPermSets]
  refine congrArg List.ofFn (funext fun s => ?_)
  set zdec := src.poly (iSel q s) (hiSel q s) (mSel q s) with hz
  have hbindAt : forall p, p ∈ deployedSetPts vk instanceCommitment ps ch (iSel q s) ->
      zdec.eval p =
        ((deployedSetQueries vk instanceCommitment ps ch (iSel q s)).getD (mSel q s : Nat)
          (.point 0, [])).2.getD
        (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD (iSel q s)
          []).idxOf p) 0 := by
    intro p hp
    exact src.eval_at_point (iSel q s) (hiSel q s) (mSel q s) p hp
  obtain ⟨qx, hqx, hqxid, hqxpt, hqxev⟩ := perm_product_query_mem_assembleQueries vk instanceCommitment ps ch q s
  obtain ⟨hptx, hevx⟩ := hallSel q s qx hqx hqxid
  have hbx : zdec.eval ch.x = (ps.permutationSetEvals q s).eval := by
    have hb := hbindAt qx.point hptx
    rw [hqxpt] at hb hevx
    rw [hb, hevx, hqxev]
  obtain ⟨qn, hqn, hqnid, hqnpt, hqnev⟩ :=
    perm_product_next_query_mem_assembleQueries vk instanceCommitment ps ch q s
  obtain ⟨hptn, hevn⟩ := hallSel q s qn hqn hqnid
  have hbn : zdec.eval (rotateOmega vk.omega ch.x 1) =
      (ps.permutationSetEvals q s).nextEval := by
    have hb := hbindAt qn.point hptn
    rw [hqnpt] at hb hevn
    rw [hb, hevn, hqnev]
  have heta : ps.permutationSetEvals q s =
      PermSetEval.mk (ps.permutationSetEvals q s).eval
        (ps.permutationSetEvals q s).nextEval (ps.permutationSetEvals q s).lastEval := rfl
  rw [Function.comp_apply, heta]
  simp only [PermSetEval.map, PermSetEval.mk.injEq]
  refine ⟨hbx, ?_, ?_⟩
  · rw [eval_comp_rotate, <- hbn, rotateOmega, mul_comm]
  · rcases hle : (ps.permutationSetEvals q s).lastEval with _ | le
    · rfl
    · rw [Option.map_map]
      by_cases hlast : (s : Nat) + 1 < shape.numPermutationSets
      · obtain ⟨ql, hql, hqlid, hqlpt, hqlev⟩ :=
          perm_product_last_query_mem_assembleQueries vk instanceCommitment ps ch q s hlast hle
        obtain ⟨hptl, hevl⟩ := hallSel q s ql hql hqlid
        have hbl : zdec.eval
            (rotateOmega vk.omega ch.x (-((vk.blindingFactors : Int) + 1))) = le := by
          have hb := hbindAt ql.point hptl
          rw [hqlpt] at hb hevl
          rw [hb, hevl, hqlev]
        simp only [Option.map_some, Function.comp_apply, if_pos hlast]
        rw [eval_comp_rotate, <- hbl, rotateOmega, mul_comm]
      · simp only [Option.map_some, Function.comp_apply, if_neg hlast, Polynomial.eval_C]

open Classical in
/-- Lookup carriers from rewind-free member polynomials. -/
theorem lookups_bind_of_memberPolynomials [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch) :
    ∃ (prodSel inSel tabSel : Fin shape.numProofs -> Fin shape.numLookups -> Nat)
      (hprodSel : forall q l, prodSel q l < deployedX4PairCount vk instanceCommitment ps ch)
      (hinSel : forall q l, inSel q l < deployedX4PairCount vk instanceCommitment ps ch)
      (htabSel : forall q l, tabSel q l < deployedX4PairCount vk instanceCommitment ps ch)
      (prodMem : forall (q : Fin shape.numProofs) (l : Fin shape.numLookups),
        Fin (deployedSetQueries vk instanceCommitment ps ch (prodSel q l)).length)
      (inMem : forall (q : Fin shape.numProofs) (l : Fin shape.numLookups),
        Fin (deployedSetQueries vk instanceCommitment ps ch (inSel q l)).length)
      (tabMem : forall (q : Fin shape.numProofs) (l : Fin shape.numLookups),
        Fin (deployedSetQueries vk instanceCommitment ps ch (tabSel q l)).length),
      (forall (q : Fin shape.numProofs) (l : Fin shape.numLookups),
        (deployedSetCommIds vk instanceCommitment ps ch (prodSel q l)).getD (prodMem q l : Nat)
            CommitmentId.vanishingH = CommitmentId.lookupProduct q l ∧
        (deployedSetCommIds vk instanceCommitment ps ch (inSel q l)).getD (inMem q l : Nat)
            CommitmentId.vanishingH = CommitmentId.lookupPermInput q l ∧
        (deployedSetCommIds vk instanceCommitment ps ch (tabSel q l)).getD (tabMem q l : Nat)
            CommitmentId.vanishingH = CommitmentId.lookupPermTable q l) ∧
      forall q : Fin shape.numProofs,
        (List.ofFn (fun l : Fin shape.numLookups =>
          (LookupEval.mk
            (src.poly (prodSel q l) (hprodSel q l) (prodMem q l))
            ((src.poly (prodSel q l) (hprodSel q l) (prodMem q l)).comp
              (Polynomial.C (vk.omega ^ (1 : Int)) * Polynomial.X))
            (src.poly (inSel q l) (hinSel q l) (inMem q l))
            ((src.poly (inSel q l) (hinSel q l) (inMem q l)).comp
              (Polynomial.C (vk.omega ^ (-1 : Int)) * Polynomial.X))
            (src.poly (tabSel q l) (htabSel q l) (tabMem q l)),
          vk.lookupInputExprs l, vk.lookupTableExprs l))).map
            (fun lk => (lk.1.map (fun r => r.eval ch.x), lk.2.1, lk.2.2)) =
          subProofLookups vk ps q := by
  have hselP : forall (q : Fin shape.numProofs) (l : Fin shape.numLookups),
      exists i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        exists m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (forall c0, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 =
            CommitmentId.lookupProduct q l) ∧
          forall q', q' ∈ assembleQueries vk instanceCommitment ps ch ->
            q'.commId = CommitmentId.lookupProduct q l ->
            q'.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
            ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
                (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
                  []).idxOf q'.point) 0 = q'.eval := by
    intro q l
    obtain ⟨q0, hq0, hq0id, -, -⟩ := lookup_product_query_mem_assembleQueries vk instanceCommitment ps ch q l
    obtain ⟨i, hi, m, hids, _hcomm, hall⟩ :=
      deployed_slot_routed_all_of_checks vk instanceCommitment ps ch checks hq0 hq0id
    exact ⟨i, hi, m, hids, hall⟩
  have hselI : forall (q : Fin shape.numProofs) (l : Fin shape.numLookups),
      exists i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        exists m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (forall c0, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 =
            CommitmentId.lookupPermInput q l) ∧
          forall q', q' ∈ assembleQueries vk instanceCommitment ps ch ->
            q'.commId = CommitmentId.lookupPermInput q l ->
            q'.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
            ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
                (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
                  []).idxOf q'.point) 0 = q'.eval := by
    intro q l
    obtain ⟨q0, hq0, hq0id, -, -⟩ := lookup_permInput_query_mem_assembleQueries vk instanceCommitment ps ch q l
    obtain ⟨i, hi, m, hids, _hcomm, hall⟩ :=
      deployed_slot_routed_all_of_checks vk instanceCommitment ps ch checks hq0 hq0id
    exact ⟨i, hi, m, hids, hall⟩
  have hselT : forall (q : Fin shape.numProofs) (l : Fin shape.numLookups),
      exists i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        exists m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (forall c0, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 =
            CommitmentId.lookupPermTable q l) ∧
          forall q', q' ∈ assembleQueries vk instanceCommitment ps ch ->
            q'.commId = CommitmentId.lookupPermTable q l ->
            q'.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
            ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
                (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
                  []).idxOf q'.point) 0 = q'.eval := by
    intro q l
    obtain ⟨q0, hq0, hq0id, -, -⟩ := lookup_permTable_query_mem_assembleQueries vk instanceCommitment ps ch q l
    obtain ⟨i, hi, m, hids, _hcomm, hall⟩ :=
      deployed_slot_routed_all_of_checks vk instanceCommitment ps ch checks hq0 hq0id
    exact ⟨i, hi, m, hids, hall⟩
  choose iP hiP mP hidsP hallP using hselP
  choose iI hiI mI hidsI hallI using hselI
  choose iT hiT mT hidsT hallT using hselT
  refine ⟨iP, iI, iT, hiP, hiI, hiT, mP, mI, mT,
    fun q l => ⟨hidsP q l CommitmentId.vanishingH, hidsI q l CommitmentId.vanishingH,
      hidsT q l CommitmentId.vanishingH⟩, ?_⟩
  intro q
  rw [List.map_ofFn, subProofLookups]
  refine congrArg List.ofFn (funext fun l => ?_)
  rw [Function.comp_apply]
  have hbindAt : forall (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
      (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) (p : Fp),
      p ∈ deployedSetPts vk instanceCommitment ps ch i ->
      (src.poly i hi m).eval p =
        ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
          (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf p) 0 :=
    src.eval_at_point
  obtain ⟨q1, hq1, hq1id, hq1pt, hq1ev⟩ := lookup_product_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt1, hev1⟩ := hallP q l q1 hq1 hq1id
  have hb1 : (src.poly (iP q l) (hiP q l) (mP q l)).eval ch.x =
      (ps.lookupEvals q l).productEval := by
    have hb := hbindAt (iP q l) (hiP q l) (mP q l) q1.point hpt1
    rw [hq1pt] at hb hev1
    rw [hb, hev1, hq1ev]
  obtain ⟨q2, hq2, hq2id, hq2pt, hq2ev⟩ :=
    lookup_product_next_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt2, hev2⟩ := hallP q l q2 hq2 hq2id
  have hb2 : (src.poly (iP q l) (hiP q l) (mP q l)).eval
      (rotateOmega vk.omega ch.x 1) = (ps.lookupEvals q l).productNextEval := by
    have hb := hbindAt (iP q l) (hiP q l) (mP q l) q2.point hpt2
    rw [hq2pt] at hb hev2
    rw [hb, hev2, hq2ev]
  obtain ⟨q3, hq3, hq3id, hq3pt, hq3ev⟩ :=
    lookup_permInput_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt3, hev3⟩ := hallI q l q3 hq3 hq3id
  have hb3 : (src.poly (iI q l) (hiI q l) (mI q l)).eval ch.x =
      (ps.lookupEvals q l).permutedInputEval := by
    have hb := hbindAt (iI q l) (hiI q l) (mI q l) q3.point hpt3
    rw [hq3pt] at hb hev3
    rw [hb, hev3, hq3ev]
  obtain ⟨q4, hq4, hq4id, hq4pt, hq4ev⟩ :=
    lookup_permInput_inv_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt4, hev4⟩ := hallI q l q4 hq4 hq4id
  have hb4 : (src.poly (iI q l) (hiI q l) (mI q l)).eval
      (rotateOmega vk.omega ch.x (-1)) = (ps.lookupEvals q l).permutedInputInvEval := by
    have hb := hbindAt (iI q l) (hiI q l) (mI q l) q4.point hpt4
    rw [hq4pt] at hb hev4
    rw [hb, hev4, hq4ev]
  obtain ⟨q5, hq5, hq5id, hq5pt, hq5ev⟩ :=
    lookup_permTable_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt5, hev5⟩ := hallT q l q5 hq5 hq5id
  have hb5 : (src.poly (iT q l) (hiT q l) (mT q l)).eval ch.x =
      (ps.lookupEvals q l).permutedTableEval := by
    have hb := hbindAt (iT q l) (hiT q l) (mT q l) q5.point hpt5
    rw [hq5pt] at hb hev5
    rw [hb, hev5, hq5ev]
  have heta : ps.lookupEvals q l =
      LookupEval.mk (ps.lookupEvals q l).productEval (ps.lookupEvals q l).productNextEval
        (ps.lookupEvals q l).permutedInputEval (ps.lookupEvals q l).permutedInputInvEval
        (ps.lookupEvals q l).permutedTableEval := rfl
  refine congrArg (fun z => (z, vk.lookupInputExprs l, vk.lookupTableExprs l)) ?_
  rw [heta]
  simp only [LookupEval.map, LookupEval.mk.injEq]
  refine ⟨hb1, ?_, hb3, ?_, hb5⟩
  · rw [eval_comp_rotate, <- hb2, rotateOmega, mul_comm]
  · rw [eval_comp_rotate, <- hb4, rotateOmega, mul_comm]

open Classical in
/-- Permutation-common feed binding from rewind-free member polynomials. -/
theorem permCommonFeed_bind_of_memberPolynomials [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (src : DeployedMemberPolynomials vk instanceCommitment ps ch)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch) :
    ∃ (commonSel : Fin shape.numPermutationColumns -> Nat)
      (hcommonSel : ∀ c, commonSel c < deployedX4PairCount vk instanceCommitment ps ch)
      (commonMem : ∀ c : Fin shape.numPermutationColumns,
        Fin (deployedSetQueries vk instanceCommitment ps ch (commonSel c)).length),
      (∀ c : Fin shape.numPermutationColumns,
        (deployedSetCommIds vk instanceCommitment ps ch (commonSel c)).getD (commonMem c : Nat)
          CommitmentId.vanishingH = CommitmentId.permCommon c) ∧
      ∀ n : Nat, (if h : n < shape.numPermutationColumns then
        src.poly (commonSel ⟨n, h⟩) (hcommonSel ⟨n, h⟩) (commonMem ⟨n, h⟩)
        else 0).eval ch.x = finFn ps.permutationCommonEvals n := by
  have hsel : forall c : Fin shape.numPermutationColumns,
      ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (forall c0, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 =
            CommitmentId.permCommon c) ∧
          ch.x ∈ deployedSetPts vk instanceCommitment ps ch i ∧
          ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) (.point 0, [])).2.getD
              (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
                ch.x) 0 = ps.permutationCommonEvals c := by
    intro c
    obtain ⟨q0, hq0, hq0id, hq0pt, hq0ev⟩ :=
      permCommon_query_mem_assembleQueries vk instanceCommitment ps ch c
    obtain ⟨i, hi, m, hids, _hcomm, hall⟩ :=
      deployed_slot_routed_all_of_checks vk instanceCommitment ps ch checks hq0 hq0id
    obtain ⟨hpt, hev⟩ := hall q0 hq0 hq0id
    exact ⟨i, hi, m, fun c0 => hids c0, hq0pt ▸ hpt,
      by rw [hq0pt, hq0ev] at hev; exact hev⟩
  choose iSel hiSel mSel hidsSel hptSel hevSel using hsel
  refine ⟨iSel, hiSel, mSel, fun c => hidsSel c CommitmentId.vanishingH, ?_⟩
  intro n
  by_cases h : n < shape.numPermutationColumns
  · rw [dif_pos h, finFn, dif_pos h]
    rw [src.eval_at_point (iSel ⟨n, h⟩) (hiSel ⟨n, h⟩) (mSel ⟨n, h⟩)
      _ (hptSel ⟨n, h⟩)]
    exact hevSel ⟨n, h⟩
  · rw [dif_neg h, finFn, dif_neg h, Polynomial.eval_zero]

/-! ## Complete deterministic constraint supply -/

/-- The successful constraint-side output for one decoded run.  It retains the concrete carrier
polynomials used by `circuitSatViaConstraints`, so the left branch is directly composable with a
knowledge-soundness endpoint while the right branch remains an explicit relation witness. -/
structure DeployedConstraintWitness [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (aggregate : Fin (2 ^ urs.k) -> Fp) (aggregateU aggregateW : Fp) where
  fixedF : Nat -> Polynomial Fp
  adviceF : Fin shape.numProofs -> Nat -> Polynomial Fp
  instanceF : Fin shape.numProofs -> Nat -> Polynomial Fp
  setsC : Fin shape.numProofs -> List (PermSetEval (Polynomial Fp))
  chunksC : Fin shape.numProofs ->
    List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp))
  lookupsC : Fin shape.numProofs ->
    List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp))
  l0P : Polynomial Fp
  lLastP : Polynomial Fp
  lBlindP : Polynomial Fp
  hpolyP : Polynomial Fp
  relation : SnarkRelation urs
    (deployedCommitment urs hk vk instanceCommitment ps ch - aggregateU • urs.u - aggregateW • urs.w)
    (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch)
    (circuitSatViaConstraints fixedF (fun _ => adviceF) (fun _ => instanceF) vk.gates
      setsC chunksC lookupsC ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
      l0P lLastP lBlindP hpolyP vk.n) aggregate

open Polynomial in
/-- Relation-free specialization used by the computed AGM adapter once member-value decoding has
already supplied the exact routed equality. -/
theorem hfold_of_constraint_polys_of_xn_ne_direct
    [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (fixedCols : Nat -> Polynomial Fp)
    (adviceCols instanceCols : Fin shape.numProofs -> Nat -> Polynomial Fp)
    (sets : Fin shape.numProofs -> List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs ->
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin shape.numProofs ->
      List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (l0 lLast lBlind hpoly : Polynomial Fp)
    (i m : Nat) (hm : m < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (colPoly : Fin (deployedSetQueries vk instanceCommitment ps ch i).length -> Polynomial Fp)
    (hbindAll : forall
      (idx : Fin ((constructIntermediateSets
        (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length)
      (m0 : Fin (deployedSetQueries vk instanceCommitment ps ch i).length),
      (colPoly m0).eval
          (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [])[idx]) =
        ((deployedSetQueries vk instanceCommitment ps ch i).getD (m0 : Nat) (.point 0, [])).2.getD
          (idx : Nat) 0)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [] = [ch.x])
    (hevals : forall d0, ((deployedSetQueries vk instanceCommitment ps ch i).getD m d0).2 =
      [expectedHEval
        (allExpressions vk ps ch
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1
          (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2)
        ch.y (ch.x ^ vk.n)])
    (hxn : ch.x ^ vk.n ≠ 1)
    (hfixed : forall j, (fixedCols j).eval ch.x = finFn ps.fixedEvals j)
    (hadvice : forall p j, (adviceCols p j).eval ch.x = finFn (ps.adviceEvals p) j)
    (hinstance : forall p j, (instanceCols p j).eval ch.x = finFn (ps.instanceEvals p) j)
    (hsets : forall p,
      (sets p).map (PermSetEval.map (fun q => q.eval ch.x)) = subProofPermSets ps p)
    (hchunks : forall p,
      (chunks p).map (fun c => (c.1.map (fun q => q.eval ch.x),
        c.2.map (fun q => (q.1.eval ch.x, q.2.eval ch.x)))) = subProofPermChunks vk ps p)
    (hlookups : forall p,
      (lookups p).map (fun lk =>
        (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2)) = subProofLookups vk ps p)
    (hl0 : l0.eval ch.x =
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).1)
    (hlLast : lLast.eval ch.x =
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.1)
    (hlBlind : lBlind.eval ch.x =
      (lagrangeBasis vk.omega vk.n vk.blindingFactors (ch.x ^ vk.n) ch.x).2.2) :
    (combineConstraints fixedCols adviceCols instanceCols vk.gates sets chunks lookups
        ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen l0 lLast lBlind).eval ch.x =
      hpoly.eval ch.x * (ch.x ^ vk.n - 1) := by
  have hfp := eval_combineConstraints_deployed vk ps ch fixedCols adviceCols instanceCols
    sets chunks lookups l0 lLast lBlind hfixed hadvice hinstance hsets hchunks hlookups
    hl0 hlLast hlBlind
  rw [eval_combineConstraints] at hfp ⊢
  have hlt : 0 <
      ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length := by
    rw [hroute]
    simp
  refine hfold_of_vanishing_slot_binding vk instanceCommitment ps ch _ hpoly i m hevals ?_
    hxn hfp
  have hx : ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
      [])[(0 : Nat)]'hlt = ch.x := by
    rw [List.getElem_of_eq hroute hlt]
    simp
  rw [hquot, ← hx]
  exact hbindAll ⟨0, hlt⟩ ⟨m, hm⟩

open Polynomial in
open Classical in
/-- The concrete constraint supply produced directly from `DeployedAlgebraicDecode`.  Compared to
`constraints_supply_derived`, the `OpenedBatchOpenings`, `OpenedX1Accept`, and joint-acceptance
premises disappear: all member polynomials and their routed values come from prefix-pinned AGM
coordinates. -/
theorem constraints_supply_of_deployedAlgebraicDecode
    [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch aggregate aggregateU aggregateW)
    (poly : G -> Polynomial Fp)
    (pieceCoeffs : Fin shape.numQuotientPieces -> Fin (2 ^ urs.k) -> Fp)
    (pieceU pieceW : Fin shape.numQuotientPieces -> Fp)
    (piecePoly : Fin shape.numQuotientPieces -> Polynomial Fp)
    (hpieceOpen : ∀ i, commit urs (pieceCoeffs i) + pieceU i • urs.u +
      pieceW i • urs.w = ps.hPieces i)
    (hpiecePoly : ∀ i, coeffsToPoly (pieceCoeffs i) = piecePoly i)
    (hplain : forall {i : Nat} (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
      (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) {P : G},
      ((deployedSetQueries vk instanceCommitment ps ch i).getD
        (m : Nat) (.point 0, [])).1 = CommitmentRef.point P ->
      decoded.memberPoly i hi m = poly P)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    (hAdvLen : shape.numAdviceQueries ≤ vk.adviceQueryLayout.length)
    (hInstLen : shape.numInstanceQueries ≤ vk.instanceQueryLayout.length)
    (hFixedLen : shape.numFixedQueries ≤ vk.fixedQueryLayout.length)
    (homega : vk.omega ^ vk.n = 1) (hn : (vk.n : Fp) ≠ 0)
    (hxgood : ch.x ∉ szBadSet
      (committedPreXConstraintDifference poly piecePoly vk instanceCommitment ps ch)) :
    Nonempty (DeployedConstraintWitness urs hk vk instanceCommitment ps ch
        aggregate aggregateU aggregateW ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w) := by
  let src := decoded.toMemberPolynomials
  obtain ⟨aSet, haSet, aMem, haLayout, haBind⟩ :=
    adviceFeed_bind_of_memberPolynomials urs hk vk instanceCommitment ps ch src checks hAdvLen
  obtain ⟨iSet, hiSet, iMem, hiLayout, hiBind⟩ :=
    instanceFeed_bind_of_memberPolynomials urs hk vk instanceCommitment ps ch src checks hInstLen
  obtain ⟨fSet, hfSet, fMem, hfLayout, hfBind⟩ :=
    fixedFeed_bind_of_memberPolynomials urs hk vk instanceCommitment ps ch src checks hFixedLen
  obtain ⟨pSet, hpSet, pMem, hpLayout, hpBind⟩ :=
    permSets_bind_of_memberPolynomials urs hk vk instanceCommitment ps ch src checks
  obtain ⟨cSet, hcSet, cMem, hcLayout, hcommonF⟩ :=
    permCommonFeed_bind_of_memberPolynomials urs hk vk instanceCommitment ps ch src checks
  obtain ⟨lpSel, liSel, ltSel, hlpSel, hliSel, hltSel, lpMem, liMem, ltMem,
      hlLayout, hlBind⟩ := lookups_bind_of_memberPolynomials urs hk vk instanceCommitment ps ch src checks
  obtain ⟨hl0, hlLast, hlBlind⟩ :=
    lagrange_bind_derived vk.omega vk.n vk.blindingFactors ch.x homega hn checks.xnNeOne
  obtain ⟨iV, hiVsets, hroute, mV, hmV, hidsV, hcommitV, hevalsV⟩ :=
    vanishing_slot_routed_full vk instanceCommitment ps ch
  have hiV : iV < deployedX4PairCount vk instanceCommitment ps ch := by
    rw [deployedX4PairCount_eq_sets_length_of_checks vk instanceCommitment ps ch checks]
    exact hiVsets
  set adviceF : Fin shape.numProofs -> Nat -> Polynomial Fp := fun q =>
    rotatedFeed vk.omega vk.adviceQueryLayout
      (fun j : Fin shape.numAdviceQueries => src.poly (aSet q j) (haSet q j) (aMem q j))
    with hadviceF
  set instanceF : Fin shape.numProofs -> Nat -> Polynomial Fp := fun q =>
    rotatedFeed vk.omega vk.instanceQueryLayout
      (fun j : Fin shape.numInstanceQueries => src.poly (iSet q j) (hiSet q j) (iMem q j))
    with hinstanceF
  set fixedF : Nat -> Polynomial Fp :=
    rotatedFeed vk.omega vk.fixedQueryLayout
      (fun j : Fin shape.numFixedQueries => src.poly (fSet j) (hfSet j) (fMem j))
    with hfixedF
  set commonF : Nat -> Polynomial Fp := fun n =>
    if h : n < shape.numPermutationColumns then
      src.poly (cSet ⟨n, h⟩) (hcSet ⟨n, h⟩) (cMem ⟨n, h⟩)
    else 0 with hcommonDef
  set setsC : Fin shape.numProofs -> List (PermSetEval (Polynomial Fp)) := fun q =>
    List.ofFn (fun s : Fin shape.numPermutationSets => PermSetEval.mk
      (src.poly (pSet q s) (hpSet q s) (pMem q s))
      ((src.poly (pSet q s) (hpSet q s) (pMem q s)).comp
        (Polynomial.C (vk.omega ^ (1 : Int)) * Polynomial.X))
      ((ps.permutationSetEvals q s).lastEval.map (fun le =>
        if (s : Nat) + 1 < shape.numPermutationSets then
          (src.poly (pSet q s) (hpSet q s) (pMem q s)).comp
            (Polynomial.C (vk.omega ^ (-((vk.blindingFactors : Int) + 1))) * Polynomial.X)
        else Polynomial.C le))) with hsetsC
  set chunksC : Fin shape.numProofs ->
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)) := fun q =>
    ((setsC q).zip vk.permutationChunks).map (fun sc => (sc.1, sc.2.map (fun cr =>
      ((match cr.1 with
        | .advice i => adviceF q i
        | .fixed i => fixedF i
        | .instance i => instanceF q i), commonF cr.2)))) with hchunksC
  set lookupsC : Fin shape.numProofs ->
      List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)) := fun q =>
    List.ofFn (fun l : Fin shape.numLookups =>
      (LookupEval.mk
        (src.poly (lpSel q l) (hlpSel q l) (lpMem q l))
        ((src.poly (lpSel q l) (hlpSel q l) (lpMem q l)).comp
          (Polynomial.C (vk.omega ^ (1 : Int)) * Polynomial.X))
        (src.poly (liSel q l) (hliSel q l) (liMem q l))
        ((src.poly (liSel q l) (hliSel q l) (liMem q l)).comp
          (Polynomial.C (vk.omega ^ (-1 : Int)) * Polynomial.X))
        (src.poly (ltSel q l) (hltSel q l) (ltMem q l)),
      vk.lookupInputExprs l, vk.lookupTableExprs l)) with hlookupsC
  let decodedHP := src.poly iV hiV ⟨mV, hmV⟩
  let hpolyP := committedPreXQuotient vk piecePoly
  refine ⟨?_⟩
  have hplainRouted : forall {i : Nat}
      (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
      (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length)
      {c : CommitmentId} {P : G} (c0 : CommitmentId)
      (hid : (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 = c)
      (hresolve : assembledCommitment vk instanceCommitment ps ch c = CommitmentRef.point P),
      src.poly i hi m = poly P := by
    intro i hi m c P c0 hid hresolve
    apply hplain hi m
    exact (deployed_member_commitment_eq_assembled vk instanceCommitment ps ch i m c0 hid _).trans
      hresolve
  have hadviceBase : forall (q : Fin shape.numProofs) (j : Fin shape.numAdviceQueries),
      src.poly (aSet q j) (haSet q j) (aMem q j) =
        poly (finFnG (ps.adviceCommitments q)
          (vk.adviceQueryLayout.getD (j : Nat) (0, 0)).1) := by
    intro q j
    exact hplainRouted (haSet q j) (aMem q j) CommitmentId.vanishingH
      (haLayout q j) (by simp [assembledCommitment, q.isLt])
  have hinstanceBase : forall (q : Fin shape.numProofs) (j : Fin shape.numInstanceQueries),
      src.poly (iSet q j) (hiSet q j) (iMem q j) =
        poly (instanceCommitment q
          (vk.instanceQueryLayout.getD (j : Nat) (0, 0)).1) := by
    intro q j
    exact hplainRouted (hiSet q j) (iMem q j) CommitmentId.vanishingH
      (hiLayout q j) (by simp [assembledCommitment, q.isLt])
  have hfixedBase : forall j : Fin shape.numFixedQueries,
      src.poly (fSet j) (hfSet j) (fMem j) =
        poly (vk.fixedCommitment (vk.fixedQueryLayout.getD (j : Nat) (0, 0)).1) := by
    intro j
    exact hplainRouted (hfSet j) (fMem j) CommitmentId.vanishingH
      (hfLayout j) (by rfl)
  have hpermBase : forall (q : Fin shape.numProofs) (s : Fin shape.numPermutationSets),
      src.poly (pSet q s) (hpSet q s) (pMem q s) = poly (ps.permutationProduct q s) := by
    intro q s
    exact hplainRouted (hpSet q s) (pMem q s) CommitmentId.vanishingH
      (hpLayout q s) (by simp [assembledCommitment, q.isLt, finFnG, s.isLt])
  have hcommonBase : forall c : Fin shape.numPermutationColumns,
      src.poly (cSet c) (hcSet c) (cMem c) = poly (vk.permutationCommonCommitment c) := by
    intro c
    exact hplainRouted (hcSet c) (cMem c) CommitmentId.vanishingH
      (hcLayout c) (by simp [assembledCommitment, finFnG, c.isLt])
  have hlookupProductBase : forall (q : Fin shape.numProofs) (l : Fin shape.numLookups),
      src.poly (lpSel q l) (hlpSel q l) (lpMem q l) = poly (ps.lookupProduct q l) := by
    intro q l
    exact hplainRouted (hlpSel q l) (lpMem q l) CommitmentId.vanishingH
      (hlLayout q l).1 (by simp [assembledCommitment, q.isLt, finFnG, l.isLt])
  have hlookupInputBase : forall (q : Fin shape.numProofs) (l : Fin shape.numLookups),
      src.poly (liSel q l) (hliSel q l) (liMem q l) = poly (ps.lookupPermutedInput q l) := by
    intro q l
    exact hplainRouted (hliSel q l) (liMem q l) CommitmentId.vanishingH
      (hlLayout q l).2.1 (by simp [assembledCommitment, q.isLt, finFnG, l.isLt])
  have hlookupTableBase : forall (q : Fin shape.numProofs) (l : Fin shape.numLookups),
      src.poly (ltSel q l) (hltSel q l) (ltMem q l) = poly (ps.lookupPermutedTable q l) := by
    intro q l
    exact hplainRouted (hltSel q l) (ltMem q l) CommitmentId.vanishingH
      (hlLayout q l).2.2 (by simp [assembledCommitment, q.isLt, finFnG, l.isLt])
  let hquotientOutcome := decoded.quotientEvalEqCommittedPreXOrRelationWitness
    pieceCoeffs pieceU pieceW piecePoly hpieceOpen hpiecePoly hiV ⟨mV, hmV⟩ hcommitV
  refine bindOrRelationWitness hquotientOutcome ?_
  intro hquotEval
  have hadviceCanonical : adviceF = committedAdviceFeed poly vk ps := by
    funext q
    change rotatedFeed vk.omega vk.adviceQueryLayout
        (fun j => src.poly (aSet q j) (haSet q j) (aMem q j)) =
      rotatedFeed vk.omega vk.adviceQueryLayout (fun j =>
        poly (finFnG (ps.adviceCommitments q)
          (vk.adviceQueryLayout.getD (j : Nat) (0, 0)).1))
    exact congrArg (rotatedFeed vk.omega vk.adviceQueryLayout)
      (funext fun j => hadviceBase q j)
  have hinstanceCanonical : instanceF = committedInstanceFeed poly vk instanceCommitment := by
    funext q
    change rotatedFeed vk.omega vk.instanceQueryLayout
        (fun j => src.poly (iSet q j) (hiSet q j) (iMem q j)) =
      rotatedFeed vk.omega vk.instanceQueryLayout (fun j =>
        poly (instanceCommitment q
          (vk.instanceQueryLayout.getD (j : Nat) (0, 0)).1))
    exact congrArg (rotatedFeed vk.omega vk.instanceQueryLayout)
      (funext fun j => hinstanceBase q j)
  have hfixedCanonical : fixedF = committedFixedFeed poly vk := by
    change rotatedFeed vk.omega vk.fixedQueryLayout
        (fun j => src.poly (fSet j) (hfSet j) (fMem j)) =
      rotatedFeed vk.omega vk.fixedQueryLayout (fun j =>
        poly (vk.fixedCommitment
          (vk.fixedQueryLayout.getD (j : Nat) (0, 0)).1))
    exact congrArg (rotatedFeed vk.omega vk.fixedQueryLayout) (funext hfixedBase)
  have hcommonCanonical : commonF = committedPermCommonFeed poly vk := by
    funext n
    change (if h : n < shape.numPermutationColumns then
      src.poly (cSet ⟨n, h⟩) (hcSet ⟨n, h⟩) (cMem ⟨n, h⟩) else 0) = _
    by_cases h : n < shape.numPermutationColumns
    · rw [dif_pos h, committedPermCommonFeed, dif_pos h, hcommonBase]
    · rw [dif_neg h, committedPermCommonFeed, dif_neg h]
  have hsetsCanonical : setsC = committedPermSets poly vk ps := by
    funext q
    rw [hsetsC, committedPermSets]
    apply congrArg List.ofFn
    funext s
    rw [hpermBase q s]
  have hlookupsCanonical : lookupsC = committedLookups poly vk ps := by
    funext q
    rw [hlookupsC, committedLookups]
    apply congrArg List.ofFn
    funext l
    rw [hlookupProductBase q l, hlookupInputBase q l, hlookupTableBase q l]
  have hchunksCanonical : chunksC = committedPermChunks poly vk instanceCommitment ps := by
    funext q
    rw [hchunksC, committedPermChunks, hsetsCanonical, hadviceCanonical, hfixedCanonical,
      hinstanceCanonical, hcommonCanonical]
  have hbindV : forall
      (idx : Fin ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD iV []).length)
      (m0 : Fin (deployedSetQueries vk instanceCommitment ps ch iV).length),
      (src.poly iV hiV m0).eval
          (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD iV [])[idx]) =
        ((deployedSetQueries vk instanceCommitment ps ch iV).getD (m0 : Nat) (.point 0, [])).2.getD
          (idx : Nat) 0 := by
    intro idx m0
    let point := ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD iV [])[idx]
    have hpoint : point ∈ deployedSetPts vk instanceCommitment ps ch iV := by
      rw [deployedSetPts, List.mem_toFinset]
      exact List.get_mem _ idx
    have hb := src.eval_at_point iV hiV m0 point hpoint
    have hnd := constructIntermediateSets_points_nodup (assembleQueries vk instanceCommitment ps ch) iV
    have hidx : ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD iV []).idxOf
        point = (idx : Nat) := by
      exact hnd.idxOf_getElem (idx : Nat) idx.isLt
    rw [hidx] at hb
    exact hb
  have hconstraintDiff :
      combineConstraints fixedF adviceF instanceF vk.gates setsC chunksC lookupsC
          ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
          (lagrangeBasisPoly vk.omega vk.n 0)
          (lagrangeBasisPoly vk.omega vk.n (-((vk.blindingFactors : Int) + 1)))
          (((List.range vk.blindingFactors).map
            (fun j => lagrangeBasisPoly vk.omega vk.n
              (-((j : Int) + 1)))).foldl (· + ·) 0) -
        hpolyP * (Polynomial.X ^ vk.n - 1) =
          committedPreXConstraintDifference poly piecePoly vk instanceCommitment ps ch := by
    rw [hadviceCanonical, hinstanceCanonical, hfixedCanonical, hsetsCanonical,
      hchunksCanonical, hlookupsCanonical]
    rfl
  have hxgood' : ch.x ∉ szBadSet
      (combineConstraints fixedF adviceF instanceF vk.gates setsC chunksC lookupsC
          ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
          (lagrangeBasisPoly vk.omega vk.n 0)
          (lagrangeBasisPoly vk.omega vk.n (-((vk.blindingFactors : Int) + 1)))
          (((List.range vk.blindingFactors).map
            (fun j => lagrangeBasisPoly vk.omega vk.n
              (-((j : Int) + 1)))).foldl (· + ·) 0) -
        hpolyP * (Polynomial.X ^ vk.n - 1)) := by
    rw [hconstraintDiff]
    exact hxgood
  have hfold := hfold_of_constraint_polys_of_xn_ne_direct vk instanceCommitment ps ch
    fixedF adviceF instanceF setsC chunksC lookupsC _ _ _ decodedHP iV mV hmV
    (fun m0 => src.poly iV hiV m0) hbindV rfl hroute hevalsV checks.xnNeOne
    hfBind haBind hiBind hpBind
    (fun q => permChunks_bind_of_feeds vk ps ch q (setsC q) (hpBind q) fixedF (adviceF q)
      (instanceF q) commonF hfBind (haBind q) (hiBind q) hcommonF)
    hlBind hl0 hlLast hlBlind
  have hquotEval' : decodedHP.eval ch.x = hpolyP.eval ch.x := by
    change (decoded.memberPoly iV hiV ⟨mV, hmV⟩).eval ch.x =
      (committedPreXQuotient vk piecePoly).eval ch.x
    exact hquotEval
  have hfold' :
      (combineConstraints fixedF adviceF instanceF vk.gates setsC chunksC lookupsC
        ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
        (lagrangeBasisPoly vk.omega vk.n 0)
        (lagrangeBasisPoly vk.omega vk.n (-((vk.blindingFactors : Int) + 1)))
        (((List.range vk.blindingFactors).map
          (fun j => lagrangeBasisPoly vk.omega vk.n
            (-((j : Int) + 1)))).foldl (· + ·) 0)).eval ch.x =
          hpolyP.eval ch.x * (ch.x ^ vk.n - 1) := by
    rw [← hquotEval']
    exact hfold
  exact PSum.inl
    { fixedF := fixedF
      adviceF := adviceF
      instanceF := instanceF
      setsC := setsC
      chunksC := chunksC
      lookupsC := lookupsC
      l0P := lagrangeBasisPoly vk.omega vk.n 0
      lLastP := lagrangeBasisPoly vk.omega vk.n (-((vk.blindingFactors : Int) + 1))
      lBlindP := ((List.range vk.blindingFactors).map
        (fun j => lagrangeBasisPoly vk.omega vk.n (-((j : Int) + 1)))).foldl (· + ·) 0
      hpolyP := hpolyP
      relation := ⟨decoded.ipaRelation,
        circuitSatViaConstraints_of_check fixedF (fun _ => adviceF) (fun _ => instanceF)
          vk.gates setsC chunksC lookupsC ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
          _ _ _ hpolyP vk.n aggregate ch.x hfold'
          (hgood_of_good_challenge _ hpolyP vk.n hxgood')⟩ }

/-- Executable-shape constraint outcome for one decoded AGM run.  Every failed binding comparison
returns its concrete augmented-basis coefficients; the success branch carries the full SNARK
relation and its concrete constraint carriers. -/
noncomputable def deployedConstraintOutcomeOfDecode
    [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW : Fp}
    (decoded : DeployedAlgebraicDecode urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (poly : G -> Polynomial Fp)
    (pieceCoeffs : Fin shape.numQuotientPieces -> Fin (2 ^ urs.k) -> Fp)
    (pieceU pieceW : Fin shape.numQuotientPieces -> Fp)
    (piecePoly : Fin shape.numQuotientPieces -> Polynomial Fp)
    (hpieceOpen : ∀ i, commit urs (pieceCoeffs i) + pieceU i • urs.u +
      pieceW i • urs.w = ps.hPieces i)
    (hpiecePoly : ∀ i, coeffsToPoly (pieceCoeffs i) = piecePoly i)
    (hplain : forall {i : Nat} (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
      (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) {P : G},
      ((deployedSetQueries vk instanceCommitment ps ch i).getD
        (m : Nat) (.point 0, [])).1 = CommitmentRef.point P ->
      decoded.memberPoly i hi m = poly P)
    (checks : DeployedConstraintChecks vk instanceCommitment ps ch)
    (hAdvLen : shape.numAdviceQueries ≤ vk.adviceQueryLayout.length)
    (hInstLen : shape.numInstanceQueries ≤ vk.instanceQueryLayout.length)
    (hFixedLen : shape.numFixedQueries ≤ vk.fixedQueryLayout.length)
    (homega : vk.omega ^ vk.n = 1) (hn : (vk.n : Fp) ≠ 0)
    (hxgood : ch.x ∉ szBadSet
      (committedPreXConstraintDifference poly piecePoly vk instanceCommitment ps ch)) :
    DeployedConstraintWitness urs hk vk instanceCommitment ps ch
        aggregate aggregateU aggregateW ⊕'
      AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  exact Classical.choice
    (constraints_supply_of_deployedAlgebraicDecode urs hk vk instanceCommitment ps ch decoded
      poly pieceCoeffs pieceU pieceW piecePoly hpieceOpen hpiecePoly hplain checks
      hAdvLen hInstLen hFixedLen homega hn hxgood)

end Zcash.Snark
