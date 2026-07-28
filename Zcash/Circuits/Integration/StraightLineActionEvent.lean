import Zcash.Circuits.Integration.StraightLineActionTerminal

/-!
# The Action bundle statement as a priced straight-line event

`StraightLineActionTerminal` reaches the Action bundle statement from one decoding run, leaving
the challenge exclusions open.  This module prices that gap: the runs where the statement fails
are contained in the compressed constraint failure event plus four per-challenge exclusion
events, so the semantic endpoint bounds the probability that an accepting run carries neither
the bundle statement nor a nontrivial relation.

- `actionStatementDecoded` — the semantic target: the bundle statement or a relation exists.
- `actionXYFailureEvent`, `actionBetaFailureEvent`, `actionGammaFailureEvent`,
  `actionThetaFailureEvent` — a decoding run whose `x`/`y`, `β`, `γ`, or `θ` challenge lands in
  the terminal's exclusion set.  The `x` event is charged here at the terminal's own constraint
  difference rather than aligned with the decode-level difference the compressed event already
  prices: the alignment is a deep pipeline equality, and the extra charge is one more
  per-challenge term.
- `actionSemanticUpgradeContained` — the containment, proved from the terminal bridge.
- `actionBundleStatementFailure_prob_le_of_compressed_bound` — the endpoint.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)
open scoped ENNReal

local instance vestaInhabitedStraightLineActionEvent : Inhabited VestaG := ⟨0⟩

variable (pp : ProofParams)
  (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
  (static : DeployedConstraintStaticChecks family.toRootFamily)
  (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)

/-- **The semantic target.**  *Either* the Action bundle statement holds *or* a nontrivial
relation over the run's basis is exhibited — the conclusion of the terminal, as a proposition. -/
def actionStatementDecoded :
    (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) → Prop :=
  fun basis _ =>
    Nonempty (BundleStatement inputs ⊕'
      NontrivialRelation (F := Fp)
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis).g
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis).u
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis).w)

variable
  (hvk : ∀ basis, family.vk basis =
    actionCircuit.toVerifierKey pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
  (hI : ∀ basis, family.instanceCommitment basis =
    actionCircuit.instanceCommitment pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
  (hchar : ∀ basis O, deployedX4PairCount
    (actionCircuit.toVerifierKey pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (actionCircuit.instanceCommitment pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (straightLineRunOutput family basis O).1.proof.1
    (straightLineRunRecord family basis O) < scalarFieldOrder)

/-- The accepted constraint model at the run's own decode. -/
noncomputable abbrev actionRunModel
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi =>
      (actionRunDecode pp family static basis O inputs (hvk basis) (hI basis) h).toMemberDecode
        (hchar basis O) i hi)
    (hblinding := ActionPermutationDomain.blindingFactors_lt pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (actionRunAccepts pp family static basis O inputs (hvk basis) (hI basis) h)

/-- The accepted member polynomial at the run's own decode. -/
noncomputable abbrev actionRunPolynomial
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi =>
      (actionRunDecode pp family static basis O inputs (hvk basis) (hI basis) h).toMemberDecode
        (hchar basis O) i hi)
    (actionRunAccepts pp family static basis O inputs (hvk basis) (hI basis) h)

/-- Decoding runs whose `x` or `y` challenge lands in the terminal's constraint-fold exclusion
sets: `x` in the combined-constraint difference roots, `y` in a fold-split witness. -/
noncomputable def actionXYFailureEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬(((straightLineRunRecord family q.1 q.2).x ∉ szBadSet
        (combineConstraints
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).fixedCols
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).adviceCols
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).instanceCols
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).gates
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).sets
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).chunks
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).lookups
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).beta
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).gamma
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).delta
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).theta
          (straightLineRunRecord family q.1 q.2).y
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).chunkLen
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).l0
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).lLast
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).lBlind -
          actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h
              CommitmentId.vanishingH *
            (X ^ (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)).n - 1))) ∧
      ∀ j, (straightLineRunRecord family q.1 q.2).y ∉ szBadSet
        (foldSplitWitness
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).constraints
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)).n j))}

/-- Decoding runs whose `β` challenge lands in a permutation or lookup resolver exclusion set. -/
noncomputable def actionBetaFailureEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬(((straightLineRunRecord family q.1 q.2).beta ∉ allResolverPermutationBetaBadSet
        (actionCircuit.toVerifierKey pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1))
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h)
        actionActiveRows) ∧
      (straightLineRunRecord family q.1 q.2).beta ∉ allResolverLookupBetaBadSet
        (actionCircuit.toVerifierKey pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1))
        (straightLineRunRecord family q.1 q.2)
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h)
        ((actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)).n -
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)).blindingFactors - 2))}

/-- Decoding runs whose `γ` challenge lands in a permutation or lookup resolver exclusion set. -/
noncomputable def actionGammaFailureEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬(((straightLineRunRecord family q.1 q.2).gamma ∉ allResolverPermutationGammaBadSet
        (actionCircuit.toVerifierKey pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1))
        (straightLineRunRecord family q.1 q.2)
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h)
        actionActiveRows) ∧
      (straightLineRunRecord family q.1 q.2).gamma ∉ allResolverLookupGammaBadSet
        (actionCircuit.toVerifierKey pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1))
        (straightLineRunRecord family q.1 q.2)
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h)
        ((actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)).n -
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)).blindingFactors - 2))}

/-- Decoding runs whose `θ` challenge lands in the top-level lookup exclusion set. -/
noncomputable def actionThetaFailureEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬((straightLineRunRecord family q.1 q.2).theta ∉
      TopLevelLookupCoherence.allTopLevelLookupThetaBadSet actionCircuit pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h))}

/-- **The containment behind the fusion.**  A decoding run without the bundle statement or a
relation must have a challenge in one of the terminal's exclusion sets: otherwise the terminal
bridge produces the statement.  Stepped through in the body. -/
theorem actionSemanticUpgradeContained :
    family.StraightLineConstraintSemanticUpgradeContained static
      (actionStatementDecoded pp family inputs)
      (actionXYFailureEvent pp family static inputs hvk hI hchar)
      (actionBetaFailureEvent pp family static inputs hvk hI hchar)
      (actionGammaFailureEvent pp family static inputs hvk hI hchar)
      (actionThetaFailureEvent pp family static inputs hvk hI hchar) := by
  intro q hq
  obtain ⟨hdecoded, hsem⟩ := hq
  by_contra hnot
  simp only [Set.mem_union, not_or] at hnot
  obtain ⟨hXY, hBeta, hGamma, hTheta⟩ := hnot
  -- Non-membership in each event gives the corresponding exclusion at the run's own decode.
  have hxy := not_exists.mp hXY hdecoded
  rw [not_not] at hxy
  have hbeta := not_exists.mp hBeta hdecoded
  rw [not_not] at hbeta
  have hgamma := not_exists.mp hGamma hdecoded
  rw [not_not] at hgamma
  have htheta := not_exists.mp hTheta hdecoded
  rw [not_not] at htheta
  -- The terminal bridge assembles the exclusions into the statement.
  exact hsem ⟨action_bundleStatement_or_relation_of_straightLineDecoded pp family static
    q.1 q.2 inputs (hvk q.1) (hI q.1) hdecoded (hchar q.1 q.2)
    hxy.1 hxy.2 ⟨hgamma.1, hbeta.1⟩ ⟨hgamma.2, hbeta.2, htheta⟩⟩

/-- **The Action bundle statement, priced.**  The probability that an accepting straight-line
run carries neither the bundle statement nor a nontrivial relation is at most the compressed
constraint failure bound plus the four per-challenge exclusion bounds. -/
theorem actionBundleStatementFailure_prob_le_of_compressed_bound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → T)
    {compressedBound xyBound betaBound gammaBound thetaBound : ENNReal}
    (hcompressed : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) ≤ compressedBound)
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionXYFailureEvent pp family static inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionBetaFailureEvent pp family static inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionGammaFailureEvent pp family static inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionThetaFailureEvent pp family static inputs hvk hI hchar) ≤ thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintSemanticFailureEvent
            (actionStatementDecoded pp family inputs))
      ≤ compressedBound + (xyBound + (betaBound + (gammaBound + thetaBound))) :=
  family.straightLineConstraintSemanticFailure_prob_le_of_compressed_bound query static
    (actionStatementDecoded pp family inputs)
    (actionXYFailureEvent pp family static inputs hvk hI hchar)
    (actionBetaFailureEvent pp family static inputs hvk hI hchar)
    (actionGammaFailureEvent pp family static inputs hvk hI hchar)
    (actionThetaFailureEvent pp family static inputs hvk hI hchar)
    (actionSemanticUpgradeContained pp family static inputs hvk hI hchar)
    hcompressed hXY hBeta hGamma hTheta

end ActionTerminal

end Zcash.Snark
