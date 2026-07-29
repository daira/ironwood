import Zcash.Circuits.Integration.AdaptiveActionTerminal
import Zcash.Circuits.Integration.StraightLineActionBudgets
import Zcash.Snark.Soundness.AGM.AdaptiveSurfaces

/-!
# Action semantic surfaces for arbitrary adaptive online-AGM adversaries

The first five deployed squeezes are `theta`, `beta`, `gamma`, `y`, and `x`.  At each point an
online-AGM annotation fixes exactly the prover commitments already absorbed into that prefix.
This file records those stage-local representation lists before constructing the corresponding
finite bad sets.
-/

namespace Zcash.Snark

open Classical
open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open scoped ENNReal

variable {shape : Shape}

local instance vestaInhabitedAdaptiveActionSurfaces : Inhabited VestaG := ⟨0⟩

/-- Prover-emitted AGM representations available at one of the five Action semantic squeezes.
The definition follows the deployed transcript order literally. -/
def AlgebraicProofString.actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5) :
    List (AlgebraicPoint (F := Fp) basis) :=
  let advice :=
    (List.ofFn fun p => List.ofFn fun i => aps.adviceCommitments p i).flatten
  let lookupPermuted :=
    (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedInput p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedTable p i).flatten
  let products :=
    (List.ofFn fun p => List.ofFn fun i => aps.permutationProduct p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => aps.lookupProduct p i).flatten ++
      [aps.vanishingRandom]
  if (n : Nat) = 0 then advice
  else if (n : Nat) < 3 then advice ++ lookupPermuted
  else if (n : Nat) = 3 then advice ++ lookupPermuted ++ products
  else advice ++ lookupPermuted ++ products ++ List.ofFn aps.hPieces

/-- Coordinate-free counterpart of `actionRepresentationsBefore`. -/
def ProofString.actionCommitmentPointsBefore {G : Type*}
    (ps : ProofString shape Fp G) (n : Fin 5) : List G :=
  let advice :=
    (List.ofFn fun p => List.ofFn fun i => ps.adviceCommitments p i).flatten
  let lookupPermuted :=
    (List.ofFn fun p => List.ofFn fun i => ps.lookupPermutedInput p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => ps.lookupPermutedTable p i).flatten
  let products :=
    (List.ofFn fun p => List.ofFn fun i => ps.permutationProduct p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => ps.lookupProduct p i).flatten ++
      [ps.vanishingRandom]
  if (n : Nat) = 0 then advice
  else if (n : Nat) < 3 then advice ++ lookupPermuted
  else if (n : Nat) = 3 then advice ++ lookupPermuted ++ products
  else advice ++ lookupPermuted ++ products ++ List.ofFn ps.hPieces

@[simp] theorem AlgebraicProofString.actionRepresentationsBefore_points
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5) :
    (aps.actionRepresentationsBefore n).map AlgebraicPoint.point =
      aps.erase.actionCommitmentPointsBefore n := by
  fin_cases n <;>
    simp [AlgebraicProofString.actionRepresentationsBefore,
      ProofString.actionCommitmentPointsBefore, AlgebraicProofString.erase,
      Function.comp_def, List.map_flatten]

/-- Every stage-local prover representation is already present in that stage's actual query
transcript. -/
theorem AlgebraicProofString.actionRepresentationsBefore_covered
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (aps : AlgebraicProofString shape basis) (hwf : PsWellFormed aps.erase) (n : Fin 5)
    (ap : AlgebraicPoint (F := Fp) basis)
    (hap : ap ∈ aps.actionRepresentationsBefore n) :
    ap.point ∈ transcriptGroupPoints
      (preIpaSqueezePoints init aps.erase (Fin.castLE (by omega) n)) := by
  have lift {P : VestaG} {i j : Fin 11} (hij : (i : Nat) ≤ (j : Nat))
      (hmem : TranscriptElt.point P ∈ preIpaSqueezePoints init aps.erase i) :
      P ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase j) := by
    apply (transcriptGroupPoints_prefix
      (preIpaSqueezePoints_prefix_of_le init aps.erase hwf i j hij)).mem
    exact mem_transcriptGroupPoints_of_mem_point hmem
  fin_cases n
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 0)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    obtain ⟨p, i, h⟩ := hap
    rw [← h]
    exact mem_transcriptGroupPoints_of_mem_point
      (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 1)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 1) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 2)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 2) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 3)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable | hperm | hlookup | hrandom
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 3) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hperm
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (permutationProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hlookup
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · rw [hrandom]
      exact mem_transcriptGroupPoints_of_mem_point
        (vanishingRandom_mem_preIpaSqueezePoints_three init aps.erase)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 4)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable | hperm | hlookup | hrandom | hpiece
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 4) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hperm
      rw [← h]
      exact lift (i := 3) (j := 4) (by omega)
        (permutationProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hlookup
      rw [← h]
      exact lift (i := 3) (j := 4) (by omega)
        (lookupProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · rw [hrandom]
      exact lift (i := 3) (j := 4) (by omega)
        (vanishingRandom_mem_preIpaSqueezePoints_three init aps.erase)
    · obtain ⟨i, h⟩ := hpiece
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (hPiece_mem_preIpaSqueezePoints_four init aps.erase i)

/-- Ordinary commitment points in the stage view are covered by the same exact prefix. -/
theorem ProofString.actionCommitmentPointsBefore_covered
    (init : List (TranscriptElt Fp VestaG))
    (ps : ProofString shape Fp VestaG) (hwf : PsWellFormed ps) (n : Fin 5)
    (P : VestaG) (hP : P ∈ ps.actionCommitmentPointsBefore n) :
    P ∈ transcriptGroupPoints
      (preIpaSqueezePoints init ps (Fin.castLE (by omega) n)) := by
  have lift {P : VestaG} {i j : Fin 11} (hij : (i : Nat) ≤ (j : Nat))
      (hmem : TranscriptElt.point P ∈ preIpaSqueezePoints init ps i) :
      P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps j) := by
    apply (transcriptGroupPoints_prefix
      (preIpaSqueezePoints_prefix_of_le init ps hwf i j hij)).mem
    exact mem_transcriptGroupPoints_of_mem_point hmem
  fin_cases n
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 0)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    obtain ⟨p, i, rfl⟩ := hP
    exact mem_transcriptGroupPoints_of_mem_point
      (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 1)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 1) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 2)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 2) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 3)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable | hperm | hlookup | hrandom
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 3) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := hperm
      exact mem_transcriptGroupPoints_of_mem_point
        (permutationProduct_mem_preIpaSqueezePoints_three init ps p i)
    · obtain ⟨p, i, rfl⟩ := hlookup
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupProduct_mem_preIpaSqueezePoints_three init ps p i)
    · subst P
      exact mem_transcriptGroupPoints_of_mem_point
        (vanishingRandom_mem_preIpaSqueezePoints_three init ps)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 4)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable | hperm | hlookup | hrandom | hpiece
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 4) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := hperm
      exact lift (i := 3) (j := 4) (by omega)
        (permutationProduct_mem_preIpaSqueezePoints_three init ps p i)
    · obtain ⟨p, i, rfl⟩ := hlookup
      exact lift (i := 3) (j := 4) (by omega)
        (lookupProduct_mem_preIpaSqueezePoints_three init ps p i)
    · subst P
      exact lift (i := 3) (j := 4) (by omega)
        (vanishingRandom_mem_preIpaSqueezePoints_three init ps)
    · obtain ⟨i, rfl⟩ := hpiece
      exact mem_transcriptGroupPoints_of_mem_point
        (hPiece_mem_preIpaSqueezePoints_four init ps i)

/-- Query-local stage source: first pre-answer representations of exactly the Action commitments
already absorbed at this squeeze, followed by verifier-fixed representations. -/
def adaptiveActionQuerySource
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 5)
    {t : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)}
    (decoded : DecodedPreIpaPrefix (shape := shape) init (Fin.castLE (by omega) n) t)
    (query : AlgebraicTranscriptQuery (F := Fp) basis t)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) :
    List (AlgebraicPoint (F := Fp) basis) :=
  query.representationsForPoints
      (decoded.proof.1.actionCommitmentPointsBefore n) (by
        intro P hP
        rw [← decoded.point_eq]
        exact decoded.proof.1.actionCommitmentPointsBefore_covered
          init decoded.proof.2 n P hP) ++ fixed

/-- Canonical polynomial carried by a stage-local AGM source. -/
def adaptiveActionPointPolynomial
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (source : List (AlgebraicPoint (F := Fp) basis)) :
    VestaG → Polynomial Fp :=
  onlinePointPolynomial source

/-- Commitment-ID resolver induced by the stage-local point coordinates.  The quotient slot is
assembled from the explicit piece coordinates already present before `x`. -/
noncomputable def adaptiveActionCommitmentPolynomial
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp) :
    CommitmentId → Polynomial Fp :=
  let vk := ActionTerminal.vkAt pp basis
  let ic := actionCircuit.instanceCommitment pp
    (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs
  let pointPoly := adaptiveActionPointPolynomial source
  fun id =>
    match id with
    | .vanishingH => ComputablePolynomial.zero
    | _ =>
        match assembledCommitment vk ic ps ch id with
        | .point P => pointPoly P
        | .msm _ => ComputablePolynomial.zero

/-- The constraint model determined before `y`/`x` by the commitments already in the transcript. -/
noncomputable def adaptiveActionCommittedModel
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp) :
    ConstraintPolyModel (pp.mergeDerived actionCircuit).numProofs :=
  let urs := ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis
  canonicalConstraintModelOfPermutationResolver
    (ActionTerminal.vkAt pp basis) ch
    (adaptiveActionCommitmentPolynomial pp basis inputs ps source ch)
    (ActionPermutationDomain.blindingFactors_lt pp urs)

/-- One of the five exact Action semantic bad sets, reconstructed only from the stage prefix,
earlier oracle answers, and stage-local AGM coordinates. -/
noncomputable def adaptiveActionSurfaceAt
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (n : Fin 5)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  let nu : Fin 11 → Fp := fun i =>
    if h : (i : Nat) < (n : Nat) then earlier ⟨i, h⟩ else 0
  let ch := chRecord nu (fun _ => 0)
  let urs := ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis
  let vk := ActionTerminal.vkAt pp basis
  let ic := actionCircuit.instanceCommitment pp urs inputs
  let pointPoly := adaptiveActionPointPolynomial source
  let poly := adaptiveActionCommitmentPolynomial pp basis inputs ps source ch
  if h0 : (n : Nat) = 0 then
    ↑(TopLevelLookupCoherence.allTopLevelLookupThetaBadSet
      actionCircuit pp urs poly)
  else if h1 : (n : Nat) = 1 then
    ↑(allResolverPermutationBetaBadSet vk poly actionActiveRows) ∪
      ↑(allResolverLookupBetaBadSet vk (ActionTerminal.semanticChRecord ch.theta 0) poly
        (vk.n - vk.blindingFactors - 2))
  else if h2 : (n : Nat) = 2 then
    ↑(allResolverPermutationGammaBadSet vk
        (ActionTerminal.semanticChRecord ch.theta ch.beta) poly actionActiveRows) ∪
      ↑(allResolverLookupGammaBadSet vk
        (ActionTerminal.semanticChRecord ch.theta ch.beta) poly
          (vk.n - vk.blindingFactors - 2))
  else if h3 : (n : Nat) = 3 then
    let model := adaptiveActionCommittedModel pp basis inputs ps source ch
    ⋃ j, ↑(szBadSet (foldSplitWitness model.constraints vk.n j))
  else
    ↑(szBadSet (committedPreXConstraintDifference pointPoly
      (fun i => onlinePointPolynomial source (ps.hPieces i)) vk ic ps ch))

/-- Equality of one exact semantic prefix pins precisely the ordinary commitment list used by
that stage. -/
theorem actionCommitmentPointsBefore_eq_of_prefix
    (init : List (TranscriptElt Fp VestaG)) (n : Fin 5)
    (ps ps' : ProofString shape Fp VestaG)
    (hprefix : preIpaSqueezePoints init ps (Fin.castLE (by omega) n) =
      preIpaSqueezePoints init ps' (Fin.castLE (by omega) n)) :
    ps.actionCommitmentPointsBefore n = ps'.actionCommitmentPointsBefore n := by
  fin_cases n
  · have h := preThetaSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, h]
  · obtain ⟨ha, hi, ht⟩ := preBetaSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht]
  · obtain ⟨ha, hi, ht⟩ := preGammaSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht]
  · obtain ⟨ha, hi, ht, hp, hl, hr⟩ := preYSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht, hp, hl, hr]
  · obtain ⟨ha, hi, ht, hp, hl, hr, hh⟩ := preXSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht, hp, hl, hr, hh]

theorem adaptiveActionCommitmentPolynomial_column_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps ps' : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (hsource : source = source') (hadvice : ps.adviceCommitments = ps'.adviceCommitments) :
    ∀ id, id.isColumnInput →
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch id =
        adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch id := by
  intro id hid
  subst source'
  cases id <;>
    simp_all [CommitmentId.isColumnInput, adaptiveActionCommitmentPolynomial,
      adaptiveActionPointPolynomial, assembledCommitment, hadvice]

theorem adaptiveActionCommitmentPolynomial_lookup_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps ps' : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (hsource : source = source') (hadvice : ps.adviceCommitments = ps'.adviceCommitments)
    (hinput : ps.lookupPermutedInput = ps'.lookupPermutedInput)
    (htable : ps.lookupPermutedTable = ps'.lookupPermutedTable) :
    ∀ id, id.isLookupInput →
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch id =
        adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch id := by
  intro id hid
  subst source'
  cases id <;>
    simp_all [CommitmentId.isLookupInput, adaptiveActionCommitmentPolynomial,
      adaptiveActionPointPolynomial, assembledCommitment, hadvice, hinput, htable]

theorem adaptiveActionCommitmentPolynomial_permutation_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps ps' : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (hsource : source = source') (hadvice : ps.adviceCommitments = ps'.adviceCommitments) :
    ∀ id, id.isPermutationInput →
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch id =
        adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch id := by
  intro id hid
  subst source'
  cases id <;>
    simp_all [CommitmentId.isPermutationInput, adaptiveActionCommitmentPolynomial,
      adaptiveActionPointPolynomial, assembledCommitment, hadvice]

theorem adaptiveActionCommitmentPolynomial_eq_of_preY_fields
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps ps' : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (hsource : source = source')
    (hadvice : ps.adviceCommitments = ps'.adviceCommitments)
    (hinput : ps.lookupPermutedInput = ps'.lookupPermutedInput)
    (htable : ps.lookupPermutedTable = ps'.lookupPermutedTable)
    (hperm : ps.permutationProduct = ps'.permutationProduct)
    (hlookup : ps.lookupProduct = ps'.lookupProduct)
    (hrandom : ps.vanishingRandom = ps'.vanishingRandom) :
    adaptiveActionCommitmentPolynomial pp basis inputs ps source ch =
      adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch := by
  funext id
  subst source'
  cases id <;>
    simp [adaptiveActionCommitmentPolynomial, adaptiveActionPointPolynomial,
      assembledCommitment, hadvice, hinput, htable, hperm, hlookup, hrandom]

set_option maxHeartbeats 800000 in
/-- Equal exact prefixes and equal stage-local coordinates define the same semantic bad set. -/
theorem adaptiveActionSurfaceAt_congr
    (pp : ProofParams)
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (n : Fin 5)
    (ps ps' : ProofString (pp.mergeDerived actionCircuit) Fp VestaG)
    (hwf : PsWellFormed ps) (hwf' : PsWellFormed ps')
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (n : Nat) → Fp)
    (hprefix : preIpaSqueezePoints init ps
        (Fin.castLE (by omega) n) =
      preIpaSqueezePoints init ps' (Fin.castLE (by omega) n))
    (hsource : source = source') :
    adaptiveActionSurfaceAt pp basis inputs n ps source earlier =
      adaptiveActionSurfaceAt pp basis inputs n ps' source' earlier := by
  subst source'
  let nu : Fin 11 → Fp := fun i =>
    if h : (i : Nat) < (n : Nat) then earlier ⟨i, h⟩ else 0
  let ch : Challenges (pp.mergeDerived actionCircuit).k Fp :=
    chRecord nu (fun _ => 0)
  fin_cases n
  · have ha := preThetaSqueezePoint_inj init hprefix
    have hp := adaptiveActionCommitmentPolynomial_column_eq
      pp basis inputs ps ps' source source ch rfl ha
    have hs := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (TopLevelLookupCoherence.allTopLevelLookupThetaBadSet_congr
        actionCircuit pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) hp)
    simpa [adaptiveActionSurfaceAt, nu, ch] using hs
  · obtain ⟨ha, hi, ht⟩ := preBetaSqueezePoint_inj init hprefix
    have hpPerm := adaptiveActionCommitmentPolynomial_permutation_eq
      pp basis inputs ps ps' source source ch rfl ha
    have hpLookup := adaptiveActionCommitmentPolynomial_lookup_eq
      pp basis inputs ps ps' source source ch rfl ha hi ht
    have hsPerm := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverPermutationBetaBadSet_congr
        (ActionTerminal.vkAt pp basis) actionActiveRows hpPerm)
    have hsLookup := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverLookupBetaBadSet_congr (ActionTerminal.vkAt pp basis)
        ((ActionTerminal.vkAt pp basis).n -
          (ActionTerminal.vkAt pp basis).blindingFactors - 2)
        (ch₁ := ActionTerminal.semanticChRecord ch.theta 0)
        (ch₂ := ActionTerminal.semanticChRecord ch.theta 0) rfl hpLookup)
    simpa [adaptiveActionSurfaceAt, nu, ch] using
      congrArg₂ (fun a b : Set Fp => a ∪ b) hsPerm hsLookup
  · obtain ⟨ha, hi, ht⟩ := preGammaSqueezePoint_inj init hprefix
    have hpPerm := adaptiveActionCommitmentPolynomial_permutation_eq
      pp basis inputs ps ps' source source ch rfl ha
    have hpLookup := adaptiveActionCommitmentPolynomial_lookup_eq
      pp basis inputs ps ps' source source ch rfl ha hi ht
    have hsPerm := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverPermutationGammaBadSet_congr
        (ActionTerminal.vkAt pp basis) actionActiveRows
        (ch₁ := ActionTerminal.semanticChRecord ch.theta ch.beta)
        (ch₂ := ActionTerminal.semanticChRecord ch.theta ch.beta) rfl hpPerm)
    have hsLookup := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverLookupGammaBadSet_congr (ActionTerminal.vkAt pp basis)
        ((ActionTerminal.vkAt pp basis).n -
          (ActionTerminal.vkAt pp basis).blindingFactors - 2)
        (ch₁ := ActionTerminal.semanticChRecord ch.theta ch.beta)
        (ch₂ := ActionTerminal.semanticChRecord ch.theta ch.beta) rfl rfl hpLookup)
    simpa [adaptiveActionSurfaceAt, nu, ch] using
      congrArg₂ (fun a b : Set Fp => a ∪ b) hsPerm hsLookup
  · obtain ⟨ha, hi, ht, hp, hl, hr⟩ := preYSqueezePoint_inj init hprefix
    have hpoly := adaptiveActionCommitmentPolynomial_eq_of_preY_fields
      pp basis inputs ps ps' source source ch rfl ha hi ht hp hl hr
    have hmodel :
        adaptiveActionCommittedModel pp basis inputs ps source ch =
          adaptiveActionCommittedModel pp basis inputs ps' source ch := by
      unfold adaptiveActionCommittedModel
      rw [hpoly]
    have hs := congrArg (fun model : ConstraintPolyModel
        (pp.mergeDerived actionCircuit).numProofs =>
      ⋃ j, (↑(szBadSet (foldSplitWitness model.constraints
        (ActionTerminal.vkAt pp basis).n j)) : Set Fp)) hmodel
    simpa [adaptiveActionSurfaceAt, nu, ch] using hs
  · obtain ⟨ha, hi, ht, hp, hl, _hr, hh⟩ := preXSqueezePoint_inj init hprefix
    have hdifference :
        committedPreXConstraintDifference (onlinePointPolynomial source)
            (fun i => onlinePointPolynomial source (ps.hPieces i))
            (ActionTerminal.vkAt pp basis)
            (actionCircuit.instanceCommitment pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
            ps ch =
          committedPreXConstraintDifference (onlinePointPolynomial source)
            (fun i => onlinePointPolynomial source (ps'.hPieces i))
            (ActionTerminal.vkAt pp basis)
            (actionCircuit.instanceCommitment pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
            ps' ch := by
      rw [← hh]
      apply committedPreXConstraintDifference_ps_congr
        (onlinePointPolynomial source) (fun i => onlinePointPolynomial source (ps.hPieces i))
        _ _ ch
      · intro q
        exact congrFun ha q
      · intro q s
        exact congrFun (congrFun hp q) s
      · exact hwf
      · exact hwf'
      · intro q l
        exact congrFun (congrFun hl q) l
      · intro q l
        exact congrFun (congrFun hi q) l
      · intro q l
        exact congrFun (congrFun ht q) l
    have hs := congrArg
      (fun polynomial : Polynomial Fp => (↑(szBadSet polynomial) : Set Fp)) hdifference
    simpa [adaptiveActionSurfaceAt, adaptiveActionPointPolynomial, nu, ch] using hs

/-- On a queried prefix with no provenance relation, the query-time stage source is literally
the final stage source. -/
theorem adaptiveActionQuerySource_eq_of_pinned
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 5)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (decoded : DecodedPreIpaPrefix (shape := shape) family.init
      (Fin.castLE (by omega) n)
      (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O).toAlgebraicWfProof (Fin.castLE (by omega) n)))
    (pinned : SelectedQueryRepresentationPinned
      (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O).toAlgebraicWfProof (Fin.castLE (by omega) n))
      (family.adversary basis) O
      (((family.adversary basis).run O).algebraicProof.actionRepresentationsBefore n)) :
    adaptiveActionQuerySource family.init basis n decoded pinned.query
        (family.fixedRepresentations basis) =
      ((family.adversary basis).run O).algebraicProof.actionRepresentationsBefore n ++
        family.fixedRepresentations basis := by
  let data := (family.adversary basis).run O
  let final := data.algebraicProof.actionRepresentationsBefore n
  have hprefixBounded : fullPrefixesPre family.init decoded.proof (Fin.castLE (by omega) n) =
      fullPrefixesPre family.init data.toAlgebraicWfProof.proof
        (Fin.castLE (by omega) n) := decoded.point_eq
  have hprefix : preIpaSqueezePoints family.init decoded.proof.1
      (Fin.castLE (by omega) n) =
      preIpaSqueezePoints family.init data.algebraicProof.erase
        (Fin.castLE (by omega) n) := congrArg Subtype.val hprefixBounded
  have hordinary : decoded.proof.1.actionCommitmentPointsBefore n =
      data.algebraicProof.erase.actionCommitmentPointsBefore n :=
    actionCommitmentPointsBefore_eq_of_prefix family.init n _ _ hprefix
  have hselected : pinned.query.representationsFor final pinned.covered = final :=
    algebraicPointList_eq_of_maps_eq
      (pinned.query.representationsFor_points final pinned.covered)
      pinned.coefficients_eq
  let decodedCovered : ∀ P ∈ decoded.proof.1.actionCommitmentPointsBefore n,
      P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (Fin.castLE (by omega) n)).val := by
    intro P hP
    rw [← decoded.point_eq]
    exact decoded.proof.1.actionCommitmentPointsBefore_covered family.init
      decoded.proof.2 n P hP
  unfold adaptiveActionQuerySource
  change pinned.query.representationsForPoints
      (decoded.proof.1.actionCommitmentPointsBefore n) decodedCovered ++
        family.fixedRepresentations basis = _
  have hordinaryFinal : decoded.proof.1.actionCommitmentPointsBefore n =
      final.map AlgebraicPoint.point :=
    hordinary.trans (data.algebraicProof.actionRepresentationsBefore_points n).symm
  let finalCoveredPoints : ∀ P ∈ final.map AlgebraicPoint.point,
      P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (Fin.castLE (by omega) n)).val := by
    intro P hP
    obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hP
    exact pinned.covered ap hap
  have representationsForPoints_congr
      (points points' : List VestaG)
      (hcovered : ∀ P ∈ points, P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (Fin.castLE (by omega) n)).val)
      (hcovered' : ∀ P ∈ points', P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (Fin.castLE (by omega) n)).val)
      (hpoints : points = points') :
      pinned.query.representationsForPoints points hcovered =
        pinned.query.representationsForPoints points' hcovered' := by
    subst points'
    rfl
  have hqueryPoints : pinned.query.representationsForPoints
      (decoded.proof.1.actionCommitmentPointsBefore n) decodedCovered =
      pinned.query.representationsForPoints
        (final.map AlgebraicPoint.point) finalCoveredPoints := by
    exact representationsForPoints_congr _ _ decodedCovered finalCoveredPoints hordinaryFinal
  rw [hqueryPoints,
    ← pinned.query.representationsFor_eq_representationsForPoints final pinned.covered]
  exact congrArg (fun source => source ++ family.fixedRepresentations basis) hselected

/-- Query-time Action surface reconstructed from the exact ordinary prefix and its pre-answer AGM
annotation. -/
noncomputable def adaptiveQueriedActionSurface
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (pp.mergeDerived actionCircuit))
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (n : Fin 5)
    (t : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10 +
        3 * (pp.mergeDerived actionCircuit).k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  let n11 : Fin 11 := ⟨n, by omega⟩
  match decodePreIpaPrefix? (shape := pp.mergeDerived actionCircuit) family.init n11 t with
  | none => ∅
  | some decoded =>
      adaptiveActionSurfaceAt pp basis inputs n decoded.proof.1
        (adaptiveActionQuerySource family.init basis n decoded label
          (family.fixedRepresentations basis)) earlier

/-- Fresh-prefix fallback reconstructed from the final output's own stage-local AGM
representations. -/
noncomputable def adaptiveFallbackActionSurface
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (pp.mergeDerived actionCircuit))
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (n : Fin 5)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (_t : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10 +
        3 * (pp.mergeDerived actionCircuit).k))
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  adaptiveActionSurfaceAt pp basis inputs n data.algebraicProof.erase
    (data.algebraicProof.actionRepresentationsBefore n ++ family.fixedRepresentations basis)
    earlier

namespace ComputedAdaptiveOnlineAGMFSFamily

/-- Compare the final stage-local Action commitments with the first online-AGM annotation at the
actual semantic squeeze.  Any coefficient mismatch is returned as explicit relation data. -/
def adaptiveActionRepresentationRelationAt?
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (n : Fin 5) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let p := data.toAlgebraicWfProof
  let n11 : Fin 11 := Fin.castLE (by omega) n
  let t := algebraicFullPrefixesPre family.init p n11
  selectedQueryRepresentationRelation? t (family.adversary basis) O
    (data.algebraicProof.actionRepresentationsBefore n) (by
      intro ap hap
      change ap.point ∈ transcriptGroupPoints
        (preIpaSqueezePoints family.init data.algebraicProof.erase n11)
      exact data.algebraicProof.actionRepresentationsBefore_covered
        family.init data.wellFormed n ap hap)

/-- One shared run checks provenance at `theta`, `beta`, `gamma`, `y`, and `x`. -/
def adaptiveActionRepresentationRelationFinder
    (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    let data := (family.adversary basis).run O
    firstAdaptiveRelation? (List.ofFn fun n =>
      family.adaptiveActionRepresentationRelationAt? basis O data n)

/-- No aggregate semantic-provenance relation means every stage-local comparison was empty. -/
theorem adaptiveActionRepresentationRelationFinder_none_at
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (n : Fin 5) :
    let data := (family.adversary basis).run O
    family.adaptiveActionRepresentationRelationAt? basis O data n = none := by
  dsimp only
  have hall := (firstAdaptiveRelation?_eq_none_iff _).1 (by
    simpa only [adaptiveActionRepresentationRelationFinder] using hnone)
  apply hall
  exact List.mem_ofFn.mpr ⟨n, rfl⟩

end ComputedAdaptiveOnlineAGMFSFamily

end Zcash.Snark
