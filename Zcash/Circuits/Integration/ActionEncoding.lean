import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Integration.InstanceColumns
import Zcash.Circuits.Integration.QueryLayouts
import Zcash.Circuits.Integration.TopLevelLookups
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Zcash.Circuits.Integration.TopLevelCircuit
import Zcash.Circuits.Integration.TopLevelGates
import Zcash.Circuits.Integration.TopLevelCorrectness
import Zcash.Circuits.Integration.ActionCopyReplay
import Zcash.Circuits.Integration.ActionFixedCoherenceCompute
import Zcash.Circuits.Integration.ActionGateCoherence
import Zcash.Circuits.Integration.ActionLookupSelectorRows
import Zcash.Snark.Keygen.Pipeline

/-!
# Action correctness instantiation

This module packages the representation laws needed to instantiate generic
top-level-circuit correctness for the Orchard Action circuit. It also identifies the
ten rows used by the Action public-input layout. The generic terminal theorem remains
in `Zcash.Snark.Soundness.TopLevelTerminal`.
-/

namespace Zcash.Snark

open Halo2 Polynomial
open Zcash.Circuits
open Zcash.Circuits.Action
open Keygen

set_option maxHeartbeats 20000

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
The canonical polynomial for the Action primary column realizes the public-input
encoding declared by `orchardActionTopLevelCircuit`.
-/
theorem actionPublicInputEncoding_of_instanceRowPolynomial
    {numProofs : ℕ} {proofIndex : Fin numProofs}
    (assignment :
      TopLevelAssignment orchardActionTopLevelCircuit numProofs proofIndex)
    (inputs : PublicInputs Fp)
    (hsize : 10 ≤ 2 ^ orchardActionTopLevelCircuit.domainExponent)
    (hpoly : assignment.polynomial
        (.instanceCol proofIndex
          (Circuit.configure
            Specs.Sinsemilla.orchardGenerators {}).1.primary.index) =
      instanceRowPolynomial
        (2 ^ orchardActionTopLevelCircuit.domainExponent)
        (Zcash.Arithmetic.omegaOf
          orchardActionTopLevelCircuit.domainExponent)
        inputs.rows)
    (hrows : Function.Injective
      fun row : Fin (2 ^ orchardActionTopLevelCircuit.domainExponent) =>
        Zcash.Arithmetic.omegaOf
          orchardActionTopLevelCircuit.domainExponent ^ (row : ℕ)) :
    assignment.PublicInputEncoding inputs := by
  apply assignment.publicInputEncoding_of_rowPolynomials
    inputs (fun _ => inputs.rows)
  · intro index
    change (index : ℕ) <
      2 ^ orchardActionTopLevelCircuit.domainExponent
    exact index.isLt.trans_le hsize
  · intro index
    simpa only [orchardActionTopLevelCircuit_publicInputLayout,
      orchardActionTopLevelCircuit_config, PublicInputs.layout_cells] using hpoly
  · intro index
    simpa only [orchardActionTopLevelCircuit_publicInputLayout,
      orchardActionTopLevelCircuit_config, PublicInputs.layout_cells] using
        PublicInputs.rows_getD inputs index
  · exact hrows

/--
Package the Action circuit's gate, fixed, copy, and lookup representation laws for
one canonical decoded relation.

This is the Action-specific constructor for the generic top-level soundness
interface.  It does not mention the Action statement or its public-input
presentation.
-/
noncomputable def actionTopLevelCircuitCorrectness
    (pp : Keygen.ProofParams) (urs : URS G)
    (hk :
      (pp.mergeDerived orchardActionTopLevelCircuit).k = urs.k)
    (instanceCommitment :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
        ℕ → G)
    (ps : ProofString
      (pp.mergeDerived orchardActionTopLevelCircuit) Fp G)
    (ch : Challenges
      (pp.mergeDerived orchardActionTopLevelCircuit).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk (orchardActionTopLevelCircuit.toVerifierKey pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          (orchardActionTopLevelCircuit.toVerifierKey pp urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          (orchardActionTopLevelCircuit.toVerifierKey pp urs) ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk (orchardActionTopLevelCircuit.toVerifierKey pp urs)
        ps ch batchOpenings i hi)
    (hpoly : Polynomial Fp)
    (relation :
      CanonicalMemberConstraintRelation
        urs hk (orchardActionTopLevelCircuit.toVerifierKey pp urs)
        instanceCommitment ps ch pU pW a batchOpenings memberDecode
        (ActionPermutationDomain.blindingFactors_lt pp urs)
        ch.y hpoly
        (orchardActionTopLevelCircuit.toVerifierKey pp urs).n)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness relation.model.constraints
          (orchardActionTopLevelCircuit.toVerifierKey pp urs).n j))
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        (orchardActionTopLevelCircuit.toVerifierKey pp urs)
        ch relation.polynomial actionActiveRows)
    (lookupExclusions :
      TopLevelLookupCoherence.TopLevelLookupChallengeExclusions
        orchardActionTopLevelCircuit pp urs ch relation.polynomial) :
    TopLevelCircuitCorrectness
      orchardActionTopLevelCircuit pp urs ch relation.polynomial
      (FlatCell actionNumPermCols actionDomainSize)
      (HasNontrivialRelation (F := Fp) urs.g urs.u urs.w) := by
  classical
  let fixedCoherence :
      TopLevelFixedCoherence orchardActionTopLevelCircuit pp urs :=
    ActionFixedCoherence.ofDerived pp urs hk
  have hdomainSize :
      (orchardActionTopLevelCircuit.toVerifierKey pp urs).n = 2 ^ urs.k := by
    change
      2 ^ orchardActionTopLevelCircuit.domainExponent = 2 ^ urs.k
    exact congrArg (2 ^ ·) hk
  have hfixedRows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega ^
          (i : ℕ) :=
    actionRowsInjectiveAtUrs pp urs hk
  refine
    { gates := ActionGateCoherence.topLevelGateCoherence pp urs
      fixedEncoding := ?_
      fixed := ?_
      copies := ?_
      lookups := ?_ }
  · intro proofIndex
    by_cases hrelation :
        HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
    · exact Or.inr hrelation
    · apply Or.inl
      let assignment :
          TopLevelAssignment orchardActionTopLevelCircuit
            (pp.mergeDerived orchardActionTopLevelCircuit).numProofs
            proofIndex :=
        { polynomial := relation.polynomial }
      have hbinding :=
        (relation.fixedColumns_eq_rowPolynomials_or_relation
          orchardActionTopLevelCircuit.pinnedCS.numFixedColumns
          orchardActionTopLevelCircuit.fixedRows
          orchardActionTopLevelCircuit.fixedRows_length
          fixedCoherence.key fixedCoherence.commitment
          fixedCoherence.fixedQueryCount fixedCoherence.queryLayout
          fixedCoherence.queryLayoutBounded hfixedRows).resolve_right
            hrelation
      apply topLevelFixedColumnEncoding_of_binding
        assignment
        (TopLevelAssignment.domainRowsInjective
          (top := orchardActionTopLevelCircuit)
          ActionPermutationDomain.domainExponent_lt)
        (TopLevelAssignment.domainRoot
          (top := orchardActionTopLevelCircuit)
          ActionPermutationDomain.domainExponent_lt)
      intro column
      change
        relation.polynomial (.fixedCol column) =
          instanceRowPolynomial
            (2 ^ orchardActionTopLevelCircuit.domainExponent)
            (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega
            (orchardActionTopLevelCircuit.fixedRows.getD column [])
      have hkTop :
          orchardActionTopLevelCircuit.domainExponent = urs.k :=
        hk
      rw [hkTop]
      exact hbinding column
  · intro proofIndex
    exact relation.topLevelFixedConstraints_or_relation
      rfl fixedCoherence hfixedRows hdomainSize proofIndex
  · intro proofIndex
    simpa only [actionActiveRows] using
      actionCopyReplayWitness_or_relation
        pp urs hk relation hgoodY fixedCoherence
        permutationExclusions proofIndex
  · intro proofIndex
    by_cases hrelation :
        HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
    · exact Or.inr hrelation
    · apply Or.inl
      let lookupCoherence :
          TopLevelLookupCoherence orchardActionTopLevelCircuit :=
        TopLevelLookupCoherence.ofTopLevel
      have hrows : Function.Injective
          fun i : Fin
              (orchardActionTopLevelCircuit.toVerifierKey pp urs).n =>
            (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega ^
              (i : ℕ) := by
        rw [hdomainSize]
        exact hfixedRows
      have hroot :
          (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega ^
            (orchardActionTopLevelCircuit.toVerifierKey pp urs).n = 1 :=
        ActionPermutationDomain.root pp urs
      have hn : (orchardActionTopLevelCircuit.toVerifierKey pp urs).n ≠ 0 := by
        change 2 ^ orchardActionTopLevelCircuit.domainExponent ≠ 0
        positivity
      have hsatisfaction :=
        relation.constraintSatisfaction hn hgoodY
      have lookupSelectorValues : ∀ lookup
          (henabled :
            lookup ∈ operationEnabledLookups
              (orchardActionTopLevelCircuit.operations) 0),
          lookup.InputSelectorValuesRealized
            orchardActionTopLevelCircuit
            (resolverEnvironment
              (orchardActionTopLevelCircuit.toVerifierKey pp urs)
              relation.polynomial proofIndex
              (orchardActionTopLevelCircuit.usableRowsAt
                orchardActionTopLevelCircuit.domainExponent)) := by
        intro lookup henabled
        have hrow :
            orchardActionTopLevelCircuit.placement lookup.region + lookup.row <
              (orchardActionTopLevelCircuit.toVerifierKey pp urs).n :=
          by
            change
              orchardActionTopLevelCircuit.placement lookup.region + lookup.row <
                2 ^ orchardActionTopLevelCircuit.domainExponent
            exact
              (lookup.activationRow_lt_usableRows henabled).trans_le
                (by
                  unfold TopLevelCircuit.usableRowsAt
                  exact (Nat.sub_le _ _).trans (Nat.sub_le _ _))
        have hexact :=
          actionLookupInputSelectorLeafRowsExact
            fixedCoherence lookup henabled
        have hvalues :=
          lookup.inputSelectorValuesRealized_or_bad
            relation.polynomial
            (fun column =>
              orchardActionTopLevelCircuit.fixedRows.getD column [])
            hfixedRows hdomainSize
            (Bad :=
              HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
            (fun column hcolumn =>
              relation.fixedColumn_eq_rowPolynomial_or_relation
                column fixedCoherence.key
                (orchardActionTopLevelCircuit.fixedRows.getD column [])
                (fixedCoherence.commitment column hcolumn)
                hfixedRows
                (by
                  obtain ⟨rotation, hlayout⟩ :=
                    fixedCoherence.queryLayout column hcolumn
                  exact fixedQuery_of_layout
                    (orchardActionTopLevelCircuit.toVerifierKey pp urs)
                    instanceCommitment ps ch column rotation
                    fixedCoherence.fixedQueryCount hlayout))
            proofIndex hrow hexact
        exact hvalues.resolve_right hrelation
      exact
        TopLevelLookupCoherence.TopLevelLookupWitnessConditions.ofChallengeExclusions
          ch relation.polynomial proofIndex
          lookupSelectorValues lookupExclusions

assert_no_sorry actionTopLevelCircuitCorrectness
