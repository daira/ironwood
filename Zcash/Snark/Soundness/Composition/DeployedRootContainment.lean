import Zcash.Snark.Soundness.AGM.DeployedPinnedRoots
import Zcash.Snark.Soundness.AGM.DeployedConstraintSupply
import Zcash.Snark.Soundness.Composition.RootContainment
import Zcash.Snark.Soundness.Composition.PrefixedSqueeze

/-!
# Concrete containment for rewind-free deployed AGM decoding

This module closes the deterministic seam beneath the prefix-pinned root bound.  On a run with a
clean recursive-IPA opening, either the opening disagrees with the canonical aggregate coordinates
and exposes a binding relation, or avoiding the six explicit root sets yields every deployed
member value.  Thus failure of this concrete extraction endpoint is contained in the root-family
landing event; no accepting multiopen rewind is used.
-/

namespace Zcash.Snark

open Classical
open ComputedAlgebraicFSFamily
open ComputedDeployedRootFSFamily
open scoped ENNReal

local instance vestaInhabitedDeployedRootContainment : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- All deployed member-polynomial values decoded from the AGM coordinates at the run's own
record. -/
def deployedRootDecoded (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (coins : family.toFamily.Coins) : Prop :=
  let pnu := (wrappedAdversary family.toFamily basis).run coins.1
  Nonempty (DeployedAlgebraicDecode (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
    (wrappedPreIpaRecord pnu)
    (pnu.1.aMulti (wrappedPreIpaReads pnu))
    (pnu.1.multiU (wrappedPreIpaReads pnu))
    (pnu.1.multiBlind (wrappedPreIpaReads pnu)))

/-- The exact pre-`x` good-challenge event consumed by the deterministic constraint supply. -/
noncomputable def deployedConstraintGoodX (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (coins : family.toFamily.Coins) : Prop :=
  let pnu := (wrappedAdversary family.toFamily basis).run coins.1
  let urs := ursOfAugmentedBasis shape.k basis
  let ch := wrappedPreIpaRecord pnu
  ch.x ∉ szBadSet
    (deployedPreXConstraintDifference urs (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch)

/-- The concrete constraint witness produced after rewind-free deployed decoding.  The witness is
the current aggregate AGM coordinate vector, and all constraint carriers are existentially
produced by the deterministic supply. -/
def deployedConstraintSatisfied (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (coins : family.toFamily.Coins) : Prop :=
  let pnu := (wrappedAdversary family.toFamily basis).run coins.1
  let urs := ursOfAugmentedBasis shape.k basis
  let ch := wrappedPreIpaRecord pnu
  ∃ (fixedF : Nat -> Polynomial Fp)
    (adviceF instanceF : Fin shape.numProofs -> Nat -> Polynomial Fp)
    (setsC : Fin shape.numProofs -> List (PermSetEval (Polynomial Fp)))
    (chunksC : Fin shape.numProofs ->
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookupsC : Fin shape.numProofs ->
      List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpolyP : Polynomial Fp),
    SnarkRelation urs
      (deployedCommitment urs rfl (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 ch -
        pnu.1.multiU (wrappedPreIpaReads pnu) • urs.u -
        pnu.1.multiBlind (wrappedPreIpaReads pnu) • urs.w)
      (evalVector shape.k ch.x3) (multiopenValue (family.vk basis)
        (family.instanceCommitment basis) pnu.1.proof.1 ch)
      (circuitSatViaConstraints fixedF (fun _ => adviceF) (fun _ => instanceF)
        (family.vk basis).gates setsC chunksC lookupsC ch.beta ch.gamma
        (family.vk basis).delta ch.theta ch.y (family.vk basis).chunkLen
        l0P lLastP lBlindP hpolyP (family.vk basis).n)
      (pnu.1.aMulti (wrappedPreIpaReads pnu))

/-- The family-level deterministic adapter required by the prefixed capstone.  Deployed
acceptance, the rewind-free AGM decode, and the exact pre-`x` good event produce the concrete
constraint witness, unless the two augmented representations expose a binding relation. -/
theorem deployedRootDecoded_constraintSatisfied_or_relation
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (coins : family.toFamily.Coins)
    (hdecoded : deployedRootDecoded family basis coins)
    (checks : DeployedConstraintChecks (family.vk basis) (family.instanceCommitment basis)
      ((wrappedAdversary family.toFamily basis).run coins.1).1.proof.1
      (wrappedPreIpaRecord ((wrappedAdversary family.toFamily basis).run coins.1)))
    (hAdvLen : shape.numAdviceQueries ≤ (family.vk basis).adviceQueryLayout.length)
    (hInstLen : shape.numInstanceQueries ≤ (family.vk basis).instanceQueryLayout.length)
    (hFixedLen : shape.numFixedQueries ≤ (family.vk basis).fixedQueryLayout.length)
    (homega : (family.vk basis).omega ^ (family.vk basis).n = 1)
    (hn : ((family.vk basis).n : Fp) ≠ 0)
    (hgood : deployedConstraintGoodX family basis coins) :
    deployedConstraintSatisfied family basis coins ∨
      HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w := by
  let pnu := (wrappedAdversary family.toFamily basis).run coins.1
  let urs := ursOfAugmentedBasis shape.k basis
  let ch := wrappedPreIpaRecord pnu
  rcases hdecoded with ⟨decoded⟩
  have hpieces : ∀ i : Fin shape.numQuotientPieces,
      ∃ x : (Fin (2 ^ urs.k) -> Fp) × Fp × Fp,
        commit urs x.1 + x.2.1 • urs.u + x.2.2 • urs.w = pnu.1.proof.1.hPieces i := by
    intro i
    let P := pnu.1.algebraicProof.hPieces i
    refine ⟨(P.gPart, P.coeffs AugmentedIndex.u, P.coeffs AugmentedIndex.w), ?_⟩
    simpa [P, pnu, AlgebraicWfProof.proof, AlgebraicProofString.erase] using
      (AlgebraicPoint.point_eq_components P).symm
  obtain ⟨fixedF, adviceF, instanceF, setsC, chunksC, lookupsC,
      l0P, lLastP, lBlindP, hpolyP, hfinish⟩ :=
    constraints_supply_of_deployedAlgebraicDecode urs rfl (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch
      decoded hpieces checks hAdvLen hInstLen hFixedLen homega hn
  exact hfinish hgood (fun hrelation => by
    refine ⟨fixedF, adviceF, instanceF, setsC, chunksC, lookupsC,
      l0P, lLastP, lBlindP, hpolyP, ?_⟩
    simpa [pnu, urs, ch, deployedConstraintSatisfied] using hrelation)

/-- The concrete output delivered by the rewind-free multiopen layer: either a binding relation or
all deployed member-polynomial values. -/
def deployedRootExtracted (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (coins : family.toFamily.Coins) : Prop :=
  HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w ∨
    deployedRootDecoded family basis coins

/-- A clean accepting run that does not deliver the concrete AGM decode must hit one of the six
explicit, prefix-pinned root sets. -/
theorem deployedRootFailure_subset_landing
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    {coins : family.toFamily.Coins |
        fsWinsFull (family.adversary basis)
          (fullAlgebraicAcceptDeployed basis (family.vk basis)
            (family.instanceCommitment basis))
          (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 ∧
        family.hasCleanOpening basis coins ∧ ¬ deployedRootExtracted family basis coins} <=
      {coins : family.toFamily.Coins | (family.pinnedRoots basis).Landing coins.1} := by
  intro coins hfailure
  rcases hfailure with ⟨_hwin, hclean, hnex⟩
  let O := coins.1
  let pnu := (wrappedAdversary family.toFamily basis).run O
  cases hout : family.outcome basis O with
  | inr relation =>
      exfalso
      apply hnex
      exact Or.inl (HasNontrivialRelation.of_nontrivialRelation relation)
  | inl witness =>
      by_contra hlanding
      have hgood := family.goodRoots_of_not_landing basis O witness hout hlanding
      obtain ⟨cert, hz, hvalid, _houtInstance, opening, _hrun⟩ :=
        cleanOpening_provenance_run family.toFamily basis coins hclean
      let nu := wrappedPreIpaReads pnu
      let ch := wrappedPreIpaRecord pnu
      by_cases hae : opening.1 = pnu.1.aMulti nu
      · have hz' : ch.z ≠ 0 := by
          simpa [pnu, nu, ch, wrappedPreIpaRecord, wrappedPreIpaReads_run,
            wrappedRecord_run, runRecord] using hz
        have hshifted : commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) =
            multiopenValue (family.vk basis) (family.instanceCommitment basis)
              pnu.1.proof.1 ch +
              ch.z⁻¹ * (pnu.1.multiU nu + ch.xi * pnu.1.sU) -
                ch.xi * commitGen (evalVector shape.k ch.x3) pnu.1.s := by
          rw [<- hae]
          simpa [pnu, nu, ch, wrappedPreIpaRecord, wrappedAdversary_run_fst,
            wrappedPreIpaReads_run, wrappedRecord_run, runRecord, commitGen, innerProduct] using
              opening.2.2
        have hgoodXi : ch.xi ∉ szBadSet
            (ipaShiftXiPolynomial
              (commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) -
                multiopenValue (family.vk basis) (family.instanceCommitment basis)
                  pnu.1.proof.1 ch)
              (commitGen (evalVector shape.k ch.x3) pnu.1.s)) := by
          simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.xi
        have hgoodZ : ch.z ∉ szBadSet
            (ipaShiftZPolynomial
              (commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) -
                multiopenValue (family.vk basis) (family.instanceCommitment basis)
                  pnu.1.proof.1 ch)
              (pnu.1.multiU nu) pnu.1.sU
              (commitGen (evalVector shape.k ch.x3) pnu.1.s) ch.xi) := by
          simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.z
        have hvalue : commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) =
            multiopenValue (family.vk basis) (family.instanceCommitment basis)
              pnu.1.proof.1 ch :=
          rawValue_of_shiftedValue_of_good _ _ _ _ _ _ _ hz' hshifted hgoodXi hgoodZ
        have hgood4 : ch.x4 ∉ deployedX4RootSet
            (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
              (family.instanceCommitment basis) pnu.1.proof.1 ch
              witness.batches := by
          simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.x4
        have hgood3 : ch.x3 ∉ deployedX3RootSet
            (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
              (family.instanceCommitment basis) pnu.1.proof.1 ch
              witness.batches := by
          simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.x3
        have hgood2 : ch.x2 ∉ deployedX2RootSet
            (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
              (family.instanceCommitment basis) pnu.1.proof.1 ch
              witness.batches := by
          simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.x2
        have hgood1All : ch.x1 ∉ deployedX1AllRootSet
            (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
              (family.instanceCommitment basis) pnu.1.proof.1 ch
              witness.batches := by
          simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.x1
        have hgood1 := not_mem_deployedX1RootSet_of_not_mem_all
          (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
            (family.instanceCommitment basis) pnu.1.proof.1 ch
            witness.batches hgood1All
        let decoded := deployedAlgebraicDecode_of_good_roots
          (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
            (family.instanceCommitment basis) pnu.1.proof.1 ch
          witness.batches hvalue hgood4 hgood3 hgood2 hgood1
        exfalso
        apply hnex
        exact Or.inr (by
          simpa [deployedRootExtracted, deployedRootDecoded, pnu, nu, ch] using
            (show Nonempty (DeployedAlgebraicDecode (ursOfAugmentedBasis shape.k basis) rfl
              (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1 ch
                (pnu.1.aMulti nu) (pnu.1.multiU nu)
                (pnu.1.multiBlind nu)) from ⟨decoded⟩))
      · exfalso
        apply hnex
        apply Or.inl
        exact hasNontrivialRelation_of_two_openings (ursOfAugmentedBasis shape.k basis) hae
          (by simpa [pnu, nu, wrappedAdversary_run_fst, wrappedPreIpaReads_run] using opening.2.1)

/-- Any deterministic constraint endpoint fed by the decoded member values inherits the same
root-event containment.  This is the adapter used by the concrete `constraintsBadAccept` path:
the remaining premise is purely deterministic (`decoded member values -> S`), not another
multiopen probability or rewinding premise. -/
theorem deployedConstraintFailure_subset_landing
    (family : ComputedDeployedRootFSFamily shape)
    (S : (AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins -> Prop)
    (hdecode : forall basis coins,
      fsWinsFull (family.adversary basis)
        (fullAlgebraicAcceptDeployed basis (family.vk basis)
          (family.instanceCommitment basis))
        (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 ->
      deployedRootDecoded family basis coins ->
      S basis coins ∨
        HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    {coins : family.toFamily.Coins |
        fsWinsFull (family.adversary basis)
          (fullAlgebraicAcceptDeployed basis (family.vk basis)
            (family.instanceCommitment basis))
          (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 ∧
        family.hasCleanOpening basis coins ∧
        ¬ (S basis coins ∨
          HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
            (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)} <=
      {coins : family.toFamily.Coins | (family.pinnedRoots basis).Landing coins.1} := by
  intro coins hfailure
  apply deployedRootFailure_subset_landing family basis
  refine ⟨hfailure.1, hfailure.2.1, ?_⟩
  intro hextracted
  rcases hextracted with hrelation | hdecoded
  · exact hfailure.2.2 (Or.inr hrelation)
  · exact hfailure.2.2 (hdecode basis coins hfailure.1 hdecoded)

/-- The DLOG-based deployed capstone with the concrete rewind-free decode endpoint and an additive
root-set term. -/
theorem snarkExtractionDeployed_prob_le_via_deployed_roots
    {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T') (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily
            (deployedRootExtracted family))
      <= ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound)
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k := by
  exact snarkExtractionDeployed_prob_le_via_wrapped_pinned_roots B hB query hquery
    family.toFamily hDL (deployedRootExtracted family) (family.pinnedRoots)
      (family.pinnedRoots_budget_le) (deployedRootFailure_subset_landing family)

/-- The same additive DLOG-based capstone for a concrete constraint relation `S`, once the
deterministic circuit layer consumes the decoded deployed member values. -/
theorem snarkExtractionDeployed_prob_le_via_deployed_roots_constraints
    {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T') (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (S : (AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins -> Prop)
    (hdecode : forall basis coins,
      fsWinsFull (family.adversary basis)
        (fullAlgebraicAcceptDeployed basis (family.vk basis)
          (family.instanceCommitment basis))
        (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 ->
      deployedRootDecoded family basis coins ->
      S basis coins ∨
        HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily
            (fun basis coins => S basis coins ∨
              HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
                (ursOfAugmentedBasis shape.k basis).u
                (ursOfAugmentedBasis shape.k basis).w))
      <= ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound)
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k := by
  exact snarkExtractionDeployed_prob_le_via_wrapped_pinned_roots B hB query hquery
    family.toFamily hDL (fun basis coins => S basis coins ∨
      HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w)
    (family.pinnedRoots) (family.pinnedRoots_budget_le)
    (deployedConstraintFailure_subset_landing family S hdecode)

/-- Full concrete composition with the pre-`x` circuit-goodness squeeze kept separate.  The
multiopen term is the additive prefix-pinned root budget; the independent quotient/circuit term
remains `(Q+1) * epsilonX`, as in the existing PR #96 composition. -/
theorem snarkExtractionDeployed_prob_le_via_deployed_roots_prefixed
    {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T') (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (S goodX : (AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins -> Prop)
    (hdecode : forall basis coins,
      fsWinsFull (family.adversary basis)
        (fullAlgebraicAcceptDeployed basis (family.vk basis)
          (family.instanceCommitment basis))
        (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 ->
      deployedRootDecoded family basis coins -> goodX basis coins ->
      S basis coins ∨
        HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)
    (badF : (AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) ->
      (Fin 4 -> Fp) -> Set Fp)
    (hstab : forall basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (v : Fp),
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 4) v)) 4 =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4)
    {epsilonX : ENNReal}
    (hbad : forall basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badF basis t nu) <= epsilonX)
    (hcontX : forall basis, {coins : family.toFamily.Coins | ¬ goodX basis coins} <=
      {coins : family.toFamily.Coins |
        coins.1 (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run coins.1) 4) ∈
          badF basis (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins.1) 4)
            (fun i : Fin 4 => coins.1 (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins.1) (i.castLE (by omega))))}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily
            (fun basis coins =>
              (S basis coins ∨
                HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
                  (ursOfAugmentedBasis shape.k basis).u
                  (ursOfAugmentedBasis shape.k basis).w) ∧ goodX basis coins))
      <= (((family.Q + shape.k) * (3 / Fintype.card Fp) +
            (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
            Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound)
          + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k)
        + (family.Q + 1 : Nat) * epsilonX := by
  let rootExtracted := fun basis coins =>
    (goodX basis coins ->
      S basis coins ∨
        HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) ∨
      HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w
  have hsplit : snarkExtractionFailureEventDeployed family.toFamily
      (fun basis coins =>
        (S basis coins ∨
          HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
            (ursOfAugmentedBasis shape.k basis).u
            (ursOfAugmentedBasis shape.k basis).w) ∧ goodX basis coins) <=
      snarkExtractionFailureEventDeployed family.toFamily rootExtracted ∪
        {q : (AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins |
          ¬ goodX q.1 q.2} := by
    rintro ⟨basis, coins⟩ ⟨haccept, hnex⟩
    by_cases hgood : goodX basis coins
    · apply Or.inl
      refine ⟨haccept, ?_⟩
      intro hextracted
      rcases hextracted with hS | hrelation
      · exact hnex ⟨hS hgood, hgood⟩
      · exact hnex ⟨Or.inr hrelation, hgood⟩
    · exact Or.inr hgood
  refine le_trans ((independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure.mono
      (Set.preimage_mono hsplit)) ?_
  refine le_trans (le_of_eq (congrArg
    (fun event => (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure event)
      Set.preimage_union)) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (snarkExtractionDeployed_prob_le_via_deployed_roots_constraints B hB query hquery
      family hDL (fun basis coins => goodX basis coins ->
        S basis coins ∨
          HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
            (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w)
      (fun basis coins hwin hdecoded => Or.inl (hdecode basis coins hwin hdecoded)))
    (badX_le_via_squeeze_prefixed query family.toFamily goodX badF hstab hbad hcontX)

/-- The concrete deployed constraint capstone.  Its deterministic decode premise is fully
discharged: deployed acceptance supplies the verifier checks, prefix-pinned AGM decoding supplies
the individual member polynomials, and the exact pre-`x` good event supplies the quotient
identity.  The only remaining probabilistic input at `x` is the explicit `badF` squeeze bound. -/
theorem snarkExtractionDeployed_prob_le_via_deployed_constraints
    {T' : Type*} [DecidableEq T']
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T') (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.snarkRelationFinder bound)
    (hAdvLen : forall basis,
      shape.numAdviceQueries ≤ (family.vk basis).adviceQueryLayout.length)
    (hInstLen : forall basis,
      shape.numInstanceQueries ≤ (family.vk basis).instanceQueryLayout.length)
    (hFixedLen : forall basis,
      shape.numFixedQueries ≤ (family.vk basis).fixedQueryLayout.length)
    (homega : forall basis, (family.vk basis).omega ^ (family.vk basis).n = 1)
    (hn : forall basis, (((family.vk basis).n : Nat) : Fp) ≠ 0)
    (badF : (AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) ->
      (Fin 4 -> Fp) -> Set Fp)
    (hstab : forall basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (v : Fp),
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 4) v)) 4 =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4)
    {epsilonX : ENNReal}
    (hbad : forall basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badF basis t nu) ≤ epsilonX)
    (hcontX : forall basis,
      {coins : family.toFamily.Coins | ¬ deployedConstraintGoodX family basis coins} <=
      {coins : family.toFamily.Coins |
        coins.1 (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run coins.1) 4) ∈
          badF basis (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins.1) 4)
            (fun i : Fin 4 => coins.1 (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins.1) (i.castLE (by omega))))}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily
            (fun basis coins =>
              (deployedConstraintSatisfied family basis coins ∨
                HasNontrivialRelation (F := Fp) (ursOfAugmentedBasis shape.k basis).g
                  (ursOfAugmentedBasis shape.k basis).u
                  (ursOfAugmentedBasis shape.k basis).w) ∧
              deployedConstraintGoodX family basis coins))
      ≤ (((family.Q + shape.k) * (3 / Fintype.card Fp) +
            (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
            Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound)
          + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k)
        + (family.Q + 1 : Nat) * epsilonX := by
  apply snarkExtractionDeployed_prob_le_via_deployed_roots_prefixed B hB query hquery
    family hDL (deployedConstraintSatisfied family) (deployedConstraintGoodX family)
    ?_ badF hstab hbad hcontX
  intro basis coins hwin hdecoded hgood
  let pnu := (wrappedAdversary family.toFamily basis).run coins.1
  have hacc := deployedAccepts_of_fsWinsFull family.toFamily basis coins.1 hwin
  have checks : DeployedConstraintChecks (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1
      (wrappedPreIpaRecord pnu) := by
    have hpre := DeployedConstraintChecks.of_accepts_chRecord
      (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis) (runProof family.toFamily basis coins.1).proof.1
      (runReads family.toFamily basis coins.1) (runRounds family.toFamily basis coins.1) hacc
    simpa [pnu, wrappedPreIpaRecord, wrappedPreIpaReads_run,
      wrappedAdversary_run_fst, runProof] using hpre
  exact deployedRootDecoded_constraintSatisfied_or_relation family basis coins hdecoded
    checks
    (hAdvLen basis) (hInstLen basis) (hFixedLen basis) (homega basis) (hn basis) hgood

end Zcash.Snark
