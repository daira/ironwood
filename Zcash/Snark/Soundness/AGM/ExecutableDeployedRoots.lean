import Zcash.Snark.Soundness.AGM.AdaptiveDecode

/-!
# Executable certificates for the deployed AGM root decoder

This file traverses the six deployed checks and returns proof certificates as data, so the Action
reduction runs the decoder and terminal without selecting a proposition-level witness.
-/

namespace Zcash.Snark

open CompPoly CompPoly.CPolynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Executable coefficient polynomial for a finite power sum. -/
def powerErrorPolynomialData {n : Nat} (c : Fin n → Fp) : CPoly :=
  powerErrorPolynomial c

theorem powerErrorPolynomialData_eq {n : Nat} (c : Fin n → Fp) :
    powerErrorPolynomialData c = powerErrorPolynomial c := rfl

/-- Executable value-error polynomial for a represented power batch. -/
def algebraicBatchErrorPolynomialData {urs : URS G} {numColumns : Nat}
    (b : Fin (2 ^ urs.k) → Fp)
    (cols : Fin numColumns → Fin (2 ^ urs.k) → Fp)
    (columnEvals : Fin numColumns → Fp) : CPoly :=
  powerErrorPolynomialData fun i => commitGen b (cols i) - columnEvals i

omit [AddCommGroup G] [Module Fp G] in
theorem algebraicBatchErrorPolynomialData_eq {urs : URS G} {numColumns : Nat}
    (b : Fin (2 ^ urs.k) → Fp)
    (cols : Fin numColumns → Fin (2 ^ urs.k) → Fp)
    (columnEvals : Fin numColumns → Fp) :
    algebraicBatchErrorPolynomialData b cols columnEvals =
      algebraicBatchErrorPolynomial b cols columnEvals := by
  rw [algebraicBatchErrorPolynomialData, powerErrorPolynomialData_eq,
    algebraicBatchErrorPolynomial, powerErrorPolynomial]

/-- Executable vanishing polynomial over a finite point set. -/
def vanishingProdData (pts : Finset Fp) : CPoly :=
  vanishingProd pts

theorem vanishingProdData_eq (pts : Finset Fp) :
    vanishingProdData pts = vanishingProd pts := rfl

/-- Executable complementary vanishing polynomial. -/
def coProdData (all pts : Finset Fp) : CPoly :=
  vanishingProdData (all \ pts)

theorem coProdData_eq (all pts : Finset Fp) : coProdData all pts = coProd all pts := by
  rw [coProdData, vanishingProdData_eq, coProd]

/-- One executable Lagrange basis polynomial. -/
def lagrangeBasisData (points : List Fp) (i : Fin points.length) : CPoly :=
  CPolynomial.CLagrange.basis Finset.univ (fun j : Fin points.length => points[j]) i

theorem lagrangeBasisData_eq (points : List Fp) (i : Fin points.length) :
    (lagrangeBasisData points i).toPoly =
      Lagrange.basis Finset.univ (fun j : Fin points.length => points[j]) i :=
  CPolynomial.CLagrange.cbasis_eq_basis _ _ _

/-- Executable interpolant for a deployed point/value list. -/
def lagrangePolyData (points evals : List Fp) : CPoly :=
  lagrangePoly points evals

theorem lagrangePolyData_eq (points evals : List Fp) :
    lagrangePolyData points evals = lagrangePoly points evals := rfl

/-- Executable denominator-cleared quotient mismatch. -/
def clearedQuotientErrorPolynomialData {numSets : Nat}
    (allPts : Finset Fp) (pts : Fin numSets → Finset Fp)
    (col r : Fin numSets → CPoly) (a : Fin numSets → Fp)
    (qCol : CPoly) : CPoly :=
  clearedQuotientErrorPolynomial allPts pts col r a qCol

theorem clearedQuotientErrorPolynomialData_eq {numSets : Nat}
    (allPts : Finset Fp) (pts : Fin numSets → Finset Fp)
    (col r : Fin numSets → CPoly) (a : Fin numSets → Fp)
    (qCol : CPoly) :
    clearedQuotientErrorPolynomialData allPts pts col r a qCol =
      clearedQuotientErrorPolynomial allPts pts col r a qCol := rfl

/-- Executable set-separation polynomial at one node. -/
def nodeBindingErrorPolynomialData {numSets : Nat}
    (allPts : Finset Fp) (pts : Fin numSets → Finset Fp)
    (col r : Fin numSets → CPoly) (node : Fp) : CPoly :=
  nodeBindingErrorPolynomial allPts pts col r node

theorem nodeBindingErrorPolynomialData_eq {numSets : Nat}
    (allPts : Finset Fp) (pts : Fin numSets → Finset Fp)
    (col r : Fin numSets → CPoly) (node : Fp) :
    nodeBindingErrorPolynomialData allPts pts col r node =
      nodeBindingErrorPolynomial allPts pts col r node := rfl

/-- Executable member-separation polynomial at one node. -/
def memberBindingErrorPolynomialData {numMem : Nat}
    (mem : Fin numMem → CPoly) (claimed : Fin numMem → Fp)
    (node : Fp) : CPoly :=
  memberBindingErrorPolynomial mem claimed node

theorem memberBindingErrorPolynomialData_eq {numMem : Nat}
    (mem : Fin numMem → CPoly) (claimed : Fin numMem → Fp)
    (node : Fp) :
    memberBindingErrorPolynomialData mem claimed node =
      memberBindingErrorPolynomial mem claimed node := rfl

/-- Executable `ξ` shift polynomial. -/
def ipaShiftXiPolynomialData (delta sEval : Fp) : CPoly :=
  ipaShiftXiPolynomial delta sEval

theorem ipaShiftXiPolynomialData_eq (delta sEval : Fp) :
    ipaShiftXiPolynomialData delta sEval = ipaShiftXiPolynomial delta sEval := rfl

/-- Executable `z` shift polynomial. -/
def ipaShiftZPolynomialData (delta pU sU sEval xi : Fp) : CPoly :=
  ipaShiftZPolynomial delta pU sU sEval xi

theorem ipaShiftZPolynomialData_eq (delta pU sU sEval xi : Fp) :
    ipaShiftZPolynomialData delta pU sU sEval xi =
      ipaShiftZPolynomial delta pU sU sEval xi := rfl

/-! ## Executable deployed specialization -/

/-- Executable represented set columns in `x₂`/`x₄` order. -/
def deployedAlgebraicSetColumnsData [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4) :
    Fin (deployedX4PairCount vk instanceCommitment ps ch) → CPoly :=
  fun j => coeffsToPoly (batch.coeffs ⟨(j : Nat), Nat.lt_succ_of_lt j.isLt⟩)

theorem deployedAlgebraicSetColumnsData_eq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4) :
    deployedAlgebraicSetColumnsData urs hk vk instanceCommitment ps ch batch =
      deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch batch := rfl

/-- Executable represented top `q′` column. -/
def deployedAlgebraicQPrimeData [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4) : CPoly :=
  coeffsToPoly (batch.coeffs
    ⟨deployedX4PairCount vk instanceCommitment ps ch, Nat.lt_succ_self _⟩)

theorem deployedAlgebraicQPrimeData_eq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4) :
    deployedAlgebraicQPrimeData urs hk vk instanceCommitment ps ch batch =
      deployedAlgebraicQPrime urs hk vk instanceCommitment ps ch batch := rfl

/-- Executable deployed point-set interpolants. -/
def deployedAlgebraicSetInterpolantsData [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    Fin (deployedX4PairCount vk instanceCommitment ps ch) → CPoly :=
  fun j => lagrangePolyData
    ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD
      (j : Nat) ([], [], 0)).1
    ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD
      (j : Nat) ([], [], 0)).2.1

omit [AddCommGroup G] [Module Fp G] in
theorem deployedAlgebraicSetInterpolantsData_eq [DecidableEq G] [Inhabited G]
    {shape : Shape} (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    deployedAlgebraicSetInterpolantsData vk instanceCommitment ps ch =
      deployedAlgebraicSetInterpolants vk instanceCommitment ps ch := by
  funext j
  exact lagrangePolyData_eq _ _

/-- Executable deployed point sets in reverse `x₂` order. -/
def deployedAlgebraicSetPointsData [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    Fin (deployedX4PairCount vk instanceCommitment ps ch) → Finset Fp :=
  fun j => deployedSetPts vk instanceCommitment ps ch
    (deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : Nat))

omit [AddCommGroup G] [Module Fp G] in
theorem deployedAlgebraicSetPointsData_eq [DecidableEq G] [Inhabited G]
    {shape : Shape} (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    deployedAlgebraicSetPointsData vk instanceCommitment ps ch =
      deployedAlgebraicSetPoints vk instanceCommitment ps ch := rfl

/-- Executable deployed `x₃` mismatch. -/
def deployedX3ErrorPolynomialData [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4) : CPoly :=
  clearedQuotientErrorPolynomialData (deployedAllPts vk instanceCommitment ps ch)
    (deployedAlgebraicSetPointsData vk instanceCommitment ps ch)
    (deployedAlgebraicSetColumnsData urs hk vk instanceCommitment ps ch batch)
    (deployedAlgebraicSetInterpolantsData vk instanceCommitment ps ch)
    (fun j => ch.x2 ^ (j : Nat))
    (deployedAlgebraicQPrimeData urs hk vk instanceCommitment ps ch batch)

theorem deployedX3ErrorPolynomialData_eq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch urs (x4BatchCommitments urs hk vk instanceCommitment ps ch)
      aggregate aggregateU aggregateW ch.x4) :
    deployedX3ErrorPolynomialData urs hk vk instanceCommitment ps ch batch =
      deployedX3ErrorPolynomial urs hk vk instanceCommitment ps ch batch := by
  rw [deployedX3ErrorPolynomialData, clearedQuotientErrorPolynomialData_eq,
    deployedX3ErrorPolynomial, deployedAlgebraicSetPointsData_eq,
    deployedAlgebraicSetColumnsData_eq, deployedAlgebraicSetInterpolantsData_eq,
    deployedAlgebraicQPrimeData_eq]

/-- Executable deployed `x₁` member polynomial. -/
def deployedX1RootPolynomialData [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (idx : Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD
      i ([], [], 0)).1.length) : CPoly :=
  memberBindingErrorPolynomialData
    (fun m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length =>
      coeffsToPoly ((batches.x1 i hi).coeffs m))
    (fun m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length =>
      ((deployedSetQueries vk instanceCommitment ps ch i).getD
        (m : Nat) (.point 0, [])).2.getD (idx : Nat) 0)
    ((deployedSetsForEval vk instanceCommitment ps ch).getD i ([], [], 0)).1[idx]

theorem deployedX1RootPolynomialData_eq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (idx : Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD
      i ([], [], 0)).1.length) :
    deployedX1RootPolynomialData urs hk vk instanceCommitment ps ch batches i hi idx =
      deployedX1RootPolynomial urs hk vk instanceCommitment ps ch batches i hi idx := by
  rw [deployedX1RootPolynomialData, memberBindingErrorPolynomialData_eq,
    deployedX1RootPolynomial]

/-- A deterministic list enumerating the deployed union of opened points. -/
def deployedAllPointList [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : List Fp :=
  (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.flatten

omit [AddCommGroup G] [Module Fp G] in
theorem mem_deployedAllPointList_iff [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (x : Fp) :
    x ∈ deployedAllPointList vk instanceCommitment ps ch ↔
      x ∈ deployedAllPts vk instanceCommitment ps ch := by
  simp only [deployedAllPointList, List.mem_flatten, deployedAllPts, Finset.mem_biUnion,
    Finset.mem_range, deployedSetPts, List.mem_toFinset]
  constructor
  · rintro ⟨points, hpoints, hx⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_get.mp hpoints
    exact ⟨j, j.isLt, by simpa using hx⟩
  · rintro ⟨j, hj, hx⟩
    refine ⟨_, List.get_mem _ ⟨j, hj⟩, ?_⟩
    simpa only [List.get_eq_getElem, List.getD_eq_getElem _ _ hj] using hx

/-! ## Certificate-producing root checks -/

/-- Compute avoidance of the deployed `x₄` value root. -/
def deployedX4RootAvoidance? [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW) :
    Option (PLift (ch.x4 ∉
      deployedX4RootSet urs hk vk instanceCommitment ps ch batches)) :=
  match szBadSetAvoidance?
      (algebraicBatchErrorPolynomialData (evalVector urs.k ch.x3)
        batches.x4.coeffs (x4BatchEvals vk instanceCommitment ps ch)) ch.x4 with
  | none => none
  | some hgood => some ⟨by
      simpa only [deployedX4RootSet, algebraicBatchErrorPolynomialData_eq] using hgood.down⟩

theorem deployedX4RootAvoidance?_isSome_of [DecidableEq G] [Inhabited G]
    {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (hgood : ch.x4 ∉ deployedX4RootSet urs hk vk instanceCommitment ps ch batches) :
    (deployedX4RootAvoidance? urs hk vk instanceCommitment ps ch batches).isSome := by
  have hpoly : ch.x4 ∉ szBadSet
      (algebraicBatchErrorPolynomialData (evalVector urs.k ch.x3)
        batches.x4.coeffs (x4BatchEvals vk instanceCommitment ps ch)) := by
    simpa only [deployedX4RootSet, algebraicBatchErrorPolynomialData_eq] using hgood
  obtain ⟨certificate, hcertificate⟩ := Option.isSome_iff_exists.mp
    ((szBadSetAvoidance?_isSome_iff _ _).2 hpoly)
  simp [deployedX4RootAvoidance?, hcertificate]

/-- Compute avoidance of the deployed `x₃` polynomial and point-collision union. -/
def deployedX3RootAvoidance? [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW) :
    Option (PLift (ch.x3 ∉
      deployedX3RootSet urs hk vk instanceCommitment ps ch batches)) :=
  match szBadSetAvoidance?
      (deployedX3ErrorPolynomialData urs hk vk instanceCommitment ps ch batches.x4)
      ch.x3 with
  | none => none
  | some hpoly =>
      if hpoint : ch.x3 ∈ deployedAllPts vk instanceCommitment ps ch then none
      else some ⟨by
        intro hbad
        simp only [deployedX3RootSet, Finset.mem_coe, Finset.mem_union] at hbad
        rcases hbad with hbad | hbad
        · apply hpoly.down
          simpa only [deployedX3ErrorPolynomialData_eq] using hbad
        · exact hpoint hbad⟩

theorem deployedX3RootAvoidance?_isSome_of [DecidableEq G] [Inhabited G]
    {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (hgood : ch.x3 ∉ deployedX3RootSet urs hk vk instanceCommitment ps ch batches) :
    (deployedX3RootAvoidance? urs hk vk instanceCommitment ps ch batches).isSome := by
  have hpoly : ch.x3 ∉ szBadSet
      (deployedX3ErrorPolynomialData urs hk vk instanceCommitment ps ch batches.x4) := by
    intro hbad
    apply hgood
    simp only [deployedX3RootSet, Finset.mem_coe, Finset.mem_union]
    exact Or.inl (by simpa only [deployedX3ErrorPolynomialData_eq] using hbad)
  have hpoint : ch.x3 ∉ deployedAllPts vk instanceCommitment ps ch := by
    intro hbad
    apply hgood
    simp only [deployedX3RootSet, Finset.mem_coe, Finset.mem_union]
    exact Or.inr hbad
  obtain ⟨certificate, hcertificate⟩ := Option.isSome_iff_exists.mp
    ((szBadSetAvoidance?_isSome_iff _ _).2 hpoly)
  simp [deployedX3RootAvoidance?, hcertificate, hpoint]

/-- Executable deployed `x₂` polynomial at one enumerated node. -/
def deployedX2RootPolynomialData [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW) (node : Fp) : CPoly :=
  nodeBindingErrorPolynomialData (deployedAllPts vk instanceCommitment ps ch)
    (deployedAlgebraicSetPointsData vk instanceCommitment ps ch)
    (deployedAlgebraicSetColumnsData urs hk vk instanceCommitment ps ch batches.x4)
    (deployedAlgebraicSetInterpolantsData vk instanceCommitment ps ch) node

theorem deployedX2RootPolynomialData_eq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW) (node : Fp) :
    deployedX2RootPolynomialData urs hk vk instanceCommitment ps ch batches node =
      nodeBindingErrorPolynomial (deployedAllPts vk instanceCommitment ps ch)
        (deployedAlgebraicSetPoints vk instanceCommitment ps ch)
        (deployedAlgebraicSetColumns urs hk vk instanceCommitment ps ch batches.x4)
        (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch) node := by
  rw [deployedX2RootPolynomialData, nodeBindingErrorPolynomialData_eq,
    deployedAlgebraicSetPointsData_eq, deployedAlgebraicSetColumnsData_eq,
    deployedAlgebraicSetInterpolantsData_eq]

/-- The finite executable `x₂` checks before packaging their proof. -/
def deployedX2RootChecks? [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW) :
    Option (∀ idx : Fin (deployedAllPointList vk instanceCommitment ps ch).length,
      PLift (ch.x2 ∉ szBadSet (deployedX2RootPolynomialData urs hk vk
        instanceCommitment ps ch batches
          (deployedAllPointList vk instanceCommitment ps ch)[idx]))) :=
  finForallOption fun idx => szBadSetAvoidance?
    (deployedX2RootPolynomialData urs hk vk instanceCommitment ps ch batches
      (deployedAllPointList vk instanceCommitment ps ch)[idx]) ch.x2

theorem deployedX2RootGood_of_checks [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (hgood : ∀ idx : Fin (deployedAllPointList vk instanceCommitment ps ch).length,
      PLift (ch.x2 ∉ szBadSet (deployedX2RootPolynomialData urs hk vk
        instanceCommitment ps ch batches
          (deployedAllPointList vk instanceCommitment ps ch)[idx]))) :
    ch.x2 ∉ deployedX2RootSet urs hk vk instanceCommitment ps ch batches := by
  rintro ⟨node, hnode, hbad⟩
  have hmem : node ∈ deployedAllPointList vk instanceCommitment ps ch :=
    (mem_deployedAllPointList_iff vk instanceCommitment ps ch node).2 hnode
  obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp hmem
  subst node
  apply (hgood idx).down
  simpa only [deployedX2RootPolynomialData_eq] using hbad

/-- Compute every deployed `x₂` node-separation certificate. -/
def deployedX2RootAvoidance? [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW) :
    Option (PLift (ch.x2 ∉
      deployedX2RootSet urs hk vk instanceCommitment ps ch batches)) :=
  match deployedX2RootChecks? urs hk vk instanceCommitment ps ch batches with
  | none => none
  | some hgood => some ⟨deployedX2RootGood_of_checks
      urs hk vk instanceCommitment ps ch batches hgood⟩

theorem deployedX2RootAvoidance?_isSome_of [DecidableEq G] [Inhabited G]
    {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (hgood : ch.x2 ∉ deployedX2RootSet urs hk vk instanceCommitment ps ch batches) :
    (deployedX2RootAvoidance? urs hk vk instanceCommitment ps ch batches).isSome := by
  have hchecks : (deployedX2RootChecks? urs hk vk instanceCommitment ps ch batches).isSome := by
    apply finForallOption_isSome_of
    intro idx
    apply (szBadSetAvoidance?_isSome_iff _ _).2
    rw [deployedX2RootPolynomialData_eq]
    intro hbad
    apply hgood
    refine ⟨(deployedAllPointList vk instanceCommitment ps ch)[idx], ?_, hbad⟩
    exact (mem_deployedAllPointList_iff vk instanceCommitment ps ch _).1
      (List.get_mem _ idx)
  obtain ⟨certificates, hcertificates⟩ := Option.isSome_iff_exists.mp hchecks
  simp [deployedX2RootAvoidance?, hcertificates]

/-- The finite executable `x₁` checks before packaging their proof. -/
def deployedX1RootChecks? [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW) :
    Option (∀ i : Fin (deployedX4PairCount vk instanceCommitment ps ch),
      ∀ idx : Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD
        (i : Nat) ([], [], 0)).1.length,
      PLift (ch.x1 ∉ szBadSet
        (deployedX1RootPolynomialData urs hk vk instanceCommitment ps ch
          batches i i.isLt idx))) :=
  finForallOption fun i =>
    finForallOption fun idx => szBadSetAvoidance?
      (deployedX1RootPolynomialData urs hk vk instanceCommitment ps ch
        batches i i.isLt idx) ch.x1

theorem deployedX1RootGood_of_checks [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (hgood : ∀ i : Fin (deployedX4PairCount vk instanceCommitment ps ch),
      ∀ idx : Fin ((deployedSetsForEval vk instanceCommitment ps ch).getD
        (i : Nat) ([], [], 0)).1.length,
      PLift (ch.x1 ∉ szBadSet
        (deployedX1RootPolynomialData urs hk vk instanceCommitment ps ch
          batches i i.isLt idx))) :
    ch.x1 ∉ deployedX1AllRootSet urs hk vk instanceCommitment ps ch batches := by
  rintro ⟨i, hbad⟩
  rw [deployedX1RootSet] at hbad
  split at hbad
  next hi =>
    obtain ⟨idx, _, hidx⟩ := hbad
    apply (hgood ⟨i, hi⟩ idx).down
    simpa only [deployedX1RootPolynomialData_eq] using hidx
  next hi => simp at hbad

/-- Compute every deployed `x₁` set/member certificate. -/
def deployedX1RootAvoidance? [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW) :
    Option (PLift (ch.x1 ∉
      deployedX1AllRootSet urs hk vk instanceCommitment ps ch batches)) :=
  match deployedX1RootChecks? urs hk vk instanceCommitment ps ch batches with
  | none => none
  | some hgood => some ⟨deployedX1RootGood_of_checks
      urs hk vk instanceCommitment ps ch batches hgood⟩

theorem deployedX1RootAvoidance?_isSome_of [DecidableEq G] [Inhabited G]
    {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {aggregate : Fin (2 ^ urs.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches urs hk vk instanceCommitment ps ch
      aggregate aggregateU aggregateW)
    (hgood : ch.x1 ∉ deployedX1AllRootSet urs hk vk instanceCommitment ps ch batches) :
    (deployedX1RootAvoidance? urs hk vk instanceCommitment ps ch batches).isSome := by
  have hchecks : (deployedX1RootChecks? urs hk vk instanceCommitment ps ch batches).isSome := by
    apply finForallOption_isSome_of
    intro i
    apply finForallOption_isSome_of
    intro idx
    apply (szBadSetAvoidance?_isSome_iff _ _).2
    rw [deployedX1RootPolynomialData_eq]
    intro hbad
    apply hgood
    apply mem_deployedX1AllRootSet_of_mem urs hk vk instanceCommitment ps ch batches
      i i.isLt
    rw [deployedX1RootSet, dif_pos i.isLt]
    exact ⟨idx, Finset.mem_univ _, hbad⟩
  obtain ⟨certificates, hcertificates⟩ := Option.isSome_iff_exists.mp hchecks
  simp [deployedX1RootAvoidance?, hcertificates]

/-- Compute avoidance of the `ξ` shift-recovery root. -/
def deployedXiRootAvoidance? (delta sEval xi : Fp) :
    Option (PLift (xi ∉ szBadSet (ipaShiftXiPolynomial delta sEval))) :=
  match szBadSetAvoidance? (ipaShiftXiPolynomialData delta sEval) xi with
  | none => none
  | some hgood => some ⟨by simpa only [ipaShiftXiPolynomialData_eq] using hgood.down⟩

theorem deployedXiRootAvoidance?_isSome_of (delta sEval xi : Fp)
    (hgood : xi ∉ szBadSet (ipaShiftXiPolynomial delta sEval)) :
    (deployedXiRootAvoidance? delta sEval xi).isSome := by
  have hdata : xi ∉ szBadSet (ipaShiftXiPolynomialData delta sEval) := by
    simpa only [ipaShiftXiPolynomialData_eq] using hgood
  obtain ⟨certificate, hcertificate⟩ := Option.isSome_iff_exists.mp
    ((szBadSetAvoidance?_isSome_iff _ _).2 hdata)
  simp [deployedXiRootAvoidance?, hcertificate]

/-- Compute avoidance of the `z` shift-recovery root. -/
def deployedZRootAvoidance? (delta pU sU sEval xi z : Fp) :
    Option (PLift (z ∉ szBadSet (ipaShiftZPolynomial delta pU sU sEval xi))) :=
  match szBadSetAvoidance? (ipaShiftZPolynomialData delta pU sU sEval xi) z with
  | none => none
  | some hgood => some ⟨by simpa only [ipaShiftZPolynomialData_eq] using hgood.down⟩

theorem deployedZRootAvoidance?_isSome_of (delta pU sU sEval xi z : Fp)
    (hgood : z ∉ szBadSet (ipaShiftZPolynomial delta pU sU sEval xi)) :
    (deployedZRootAvoidance? delta pU sU sEval xi z).isSome := by
  have hdata : z ∉ szBadSet (ipaShiftZPolynomialData delta pU sU sEval xi) := by
    simpa only [ipaShiftZPolynomialData_eq] using hgood
  obtain ⟨certificate, hcertificate⟩ := Option.isSome_iff_exists.mp
    ((szBadSetAvoidance?_isSome_iff _ _).2 hdata)
  simp [deployedZRootAvoidance?, hcertificate]

namespace ComputedAdaptiveOnlineAGMFSFamily

variable {shape : Shape}

local instance vestaInhabitedExecutableDeployedRoots : Inhabited VestaG := ⟨0⟩

/-- Run all six finite deployed-root checks on the successful adaptive batch witness. -/
def adaptiveDeployedGoodRoots?
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O)) :
    Option (PLift (family.AdaptiveDeployedGoodRoots basis O witness)) :=
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let ch := wrappedPreIpaRecord pnu
  let urs := ursOfAugmentedBasis shape.k basis
  let delta := commitGen (evalVector shape.k ch.x3)
      (pnu.1.aMulti (wrappedPreIpaReads pnu)) -
    multiopenValue (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1 ch
  let sEval := commitGen (evalVector shape.k ch.x3) pnu.1.s
  match deployedX1RootAvoidance? urs rfl (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches with
  | none => none
  | some hx1 =>
      match deployedX2RootAvoidance? urs rfl (family.vk basis)
          (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches with
      | none => none
      | some hx2 =>
          match deployedX3RootAvoidance? urs rfl (family.vk basis)
              (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches with
          | none => none
          | some hx3 =>
              match deployedX4RootAvoidance? urs rfl (family.vk basis)
                  (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches with
              | none => none
              | some hx4 =>
                  match deployedXiRootAvoidance? delta sEval ch.xi with
                  | none => none
                  | some hxi =>
                      match deployedZRootAvoidance? delta
                          (pnu.1.multiU (wrappedPreIpaReads pnu)) pnu.1.sU
                          sEval ch.xi ch.z with
                      | none => none
                      | some hz => some ⟨{
                          x1 := by
                            simpa only [AdaptiveDeployedX1Good] using hx1.down
                          x2 := by
                            simpa only [AdaptiveDeployedX2Good] using hx2.down
                          x3 := by
                            simpa only [AdaptiveDeployedX3Good] using hx3.down
                          x4 := by
                            simpa only [AdaptiveDeployedX4Good] using hx4.down
                          xi := by
                            simpa only [AdaptiveDeployedXiGood] using hxi.down
                          z := by
                            simpa only [AdaptiveDeployedZGood] using hz.down }⟩

theorem adaptiveDeployedGoodRoots?_isSome_of
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O))
    (hgood : family.AdaptiveDeployedGoodRoots basis O witness) :
    (family.adaptiveDeployedGoodRoots? basis O witness).isSome := by
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let ch := wrappedPreIpaRecord pnu
  let urs := ursOfAugmentedBasis shape.k basis
  let delta := commitGen (evalVector shape.k ch.x3)
      (pnu.1.aMulti (wrappedPreIpaReads pnu)) -
    multiopenValue (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1 ch
  let sEval := commitGen (evalVector shape.k ch.x3) pnu.1.s
  have hx1Some := deployedX1RootAvoidance?_isSome_of urs rfl (family.vk basis)
    (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches (by
      simpa only [AdaptiveDeployedX1Good, pnu, ch, urs] using hgood.x1)
  have hx2Some := deployedX2RootAvoidance?_isSome_of urs rfl (family.vk basis)
    (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches (by
      simpa only [AdaptiveDeployedX2Good, pnu, ch, urs] using hgood.x2)
  have hx3Some := deployedX3RootAvoidance?_isSome_of urs rfl (family.vk basis)
    (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches (by
      simpa only [AdaptiveDeployedX3Good, pnu, ch, urs] using hgood.x3)
  have hx4Some := deployedX4RootAvoidance?_isSome_of urs rfl (family.vk basis)
    (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches (by
      simpa only [AdaptiveDeployedX4Good, pnu, ch, urs] using hgood.x4)
  have hxiSome := deployedXiRootAvoidance?_isSome_of delta sEval ch.xi (by
    simpa only [AdaptiveDeployedXiGood, pnu, ch, delta, sEval] using hgood.xi)
  have hzSome := deployedZRootAvoidance?_isSome_of delta
    (pnu.1.multiU (wrappedPreIpaReads pnu)) pnu.1.sU sEval ch.xi ch.z (by
      simpa only [AdaptiveDeployedZGood, pnu, ch, delta, sEval] using hgood.z)
  obtain ⟨hx1, hhx1⟩ := Option.isSome_iff_exists.mp hx1Some
  obtain ⟨hx2, hhx2⟩ := Option.isSome_iff_exists.mp hx2Some
  obtain ⟨hx3, hhx3⟩ := Option.isSome_iff_exists.mp hx3Some
  obtain ⟨hx4, hhx4⟩ := Option.isSome_iff_exists.mp hx4Some
  obtain ⟨hxi, hhxi⟩ := Option.isSome_iff_exists.mp hxiSome
  obtain ⟨hz, hhz⟩ := Option.isSome_iff_exists.mp hzSome
  unfold adaptiveDeployedGoodRoots?
  dsimp only
  rw [hhx1, hhx2, hhx3, hhx4, hhxi, hhz]
  rfl

end ComputedAdaptiveOnlineAGMFSFamily

end Zcash.Snark
