import Zcash.Circuits.Action.Statement
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Integration.InstanceColumns
import Zcash.Circuits.Integration.QueryLayouts
import Zcash.Circuits.Integration.TopLevelLookups
import Zcash.Circuits.Integration.ActionStatement
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
# Canonical decoded relation to the Orchard Action statement

This is the Action-specific end of the Clean/Ironwood boundary. The decoded-member
relation and constraint splitting remain verifier-native. The only circuit-specific
steps here are applying the closed Action circuit's soundness theorem and identifying
its ten public instance rows.
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
      fixed := ?_
      copies := ?_
      lookups := ?_ }
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
              (orchardActionTopLevelCircuit.operations 0) 0),
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
              (lookup.activationRow_lt_usableRows
                (ActionGateCoherence.topLevelGateCoherence pp urs)
                henabled).trans_le
                (by
                  unfold TopLevelCircuit.usableRowsAt
                  exact (Nat.sub_le _ _).trans (Nat.sub_le _ _))
        have hexact :=
          actionLookupInputSelectorLeafRowsExact
            fixedCoherence lookup henabled
        have hvalues :=
          lookup.inputSelectorValuesRealized_or_bad
            relation.polynomial fixedCoherence.rows hfixedRows hdomainSize
            (Bad :=
              HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
            (fun column hcolumn =>
              relation.fixedColumn_eq_rowPolynomial_or_relation
                column fixedCoherence.key
                (fixedCoherence.rows column)
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

/--
The canonical bundle-wide decoded relation implies the concrete Orchard Action
bundle statement once the remaining copy and lookup operation families are supplied.

There is no free proposition `S` and no `hencodes` premise. This direct lemma keeps
selector/fixed inputs explicit; the binding-aware wrapper below derives both from
`TopLevelFixedCoherence`.
-/
theorem action_bundleStatement_of_canonicalMemberConstraintRelation
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
    (vk : VerifyingKey
      (pp.mergeDerived orchardActionTopLevelCircuit) Fp G)
    (hvk :
      vk = orchardActionTopLevelCircuit.toVerifierKey pp urs)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi)
    (hbound : orchardActionTopLevelCircuit.domainExponent < 33)
    (hblinding :
      vk.blindingFactors < vk.n)
    (hpoly : Polynomial Fp)
    (relation :
      CanonicalMemberConstraintRelation
        urs hk vk
        instanceCommitment ps ch pU pW a batchOpenings memberDecode
        hblinding ch.y hpoly vk.n)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness relation.model.constraints
          vk.n j))
    (inputs :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
        PublicInputs)
    (hsize :
      10 ≤ 2 ^ orchardActionTopLevelCircuit.domainExponent)
    (hinstance : ∀
      proofIndex :
        Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs,
      relation.polynomial
          (.instanceCol proofIndex
            (Circuit.configure
              Specs.Sinsemilla.orchardGenerators {}).1.primary.index) =
        instanceRowPolynomial
          (2 ^ orchardActionTopLevelCircuit.domainExponent)
          (Zcash.Arithmetic.omegaOf
            orchardActionTopLevelCircuit.domainExponent)
          (inputs proofIndex).rows)
    (gateCoherence :
      TopLevelGateCoherence
        orchardActionTopLevelCircuit pp urs)
    (selectors : ∀ proofIndex,
      SelectorActivationsRealized
        orchardActionTopLevelCircuit.selectorMap
        orchardActionTopLevelCircuit.selectorActivations
        (TopLevelAssignment.environment
          ({ polynomial := relation.polynomial } :
            TopLevelAssignment orchardActionTopLevelCircuit
              (pp.mergeDerived orchardActionTopLevelCircuit).numProofs
              proofIndex)))
    (copies : ∀ proofIndex,
      CircuitConstraintFamily.constraints .copy
        orchardActionTopLevelCircuit.placement
        (TopLevelAssignment.environment
          ({ polynomial := relation.polynomial } :
            TopLevelAssignment orchardActionTopLevelCircuit
              (pp.mergeDerived orchardActionTopLevelCircuit).numProofs
              proofIndex))
        (orchardActionTopLevelCircuit.operations 0) 0)
    (lookups : ∀ proofIndex,
      CircuitConstraintFamily.constraints .lookup
        orchardActionTopLevelCircuit.placement
        (TopLevelAssignment.environment
          ({ polynomial := relation.polynomial } :
            TopLevelAssignment orchardActionTopLevelCircuit
              (pp.mergeDerived orchardActionTopLevelCircuit).numProofs
              proofIndex))
        (orchardActionTopLevelCircuit.operations 0) 0)
    (fixed : ∀ proofIndex,
      CircuitConstraintFamily.constraints .fixed
        orchardActionTopLevelCircuit.placement
        (TopLevelAssignment.environment
          ({ polynomial := relation.polynomial } :
            TopLevelAssignment orchardActionTopLevelCircuit
              (pp.mergeDerived orchardActionTopLevelCircuit).numProofs
              proofIndex))
        (orchardActionTopLevelCircuit.operations 0) 0) :
    BundleStatement Specs.Sinsemilla.orchardGenerators orchardBases inputs := by
  subst vk
  have hn :
      (orchardActionTopLevelCircuit.toVerifierKey pp urs).n ≠ 0 := by
    change 2 ^ orchardActionTopLevelCircuit.domainExponent ≠ 0
    positivity
  have hsatisfaction :=
    relation.constraintSatisfaction hn hgoodY
  have hroot :=
    TopLevelAssignment.domainRoot
      (top := orchardActionTopLevelCircuit) hbound
  intro proofIndex
  let assignment :
      TopLevelAssignment orchardActionTopLevelCircuit
        (pp.mergeDerived orchardActionTopLevelCircuit).numProofs
        proofIndex :=
    { polynomial := relation.polynomial }
  have hconstraints :
      Halo2.Constraints orchardActionTopLevelCircuit.placement
        assignment.environment
        (orchardActionTopLevelCircuit.operations 0) 0 := by
    apply FullCircuitSatisfaction.constraints
    refine
      { gates := ?_
        copies := copies proofIndex
        lookups := lookups proofIndex
        fixed := fixed proofIndex }
    have hdomain : ∀ row : ℕ,
        ((orchardActionTopLevelCircuit.toVerifierKey pp urs).omega ^ row) ^
          (orchardActionTopLevelCircuit.toVerifierKey pp urs).n = 1 := by
      intro row
      change
        (Zcash.Arithmetic.omegaOf
          orchardActionTopLevelCircuit.domainExponent ^ row) ^
            (2 ^ orchardActionTopLevelCircuit.domainExponent) = 1
      rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]
    have hgates :=
      gateCoherence.canonicalConstraints ch relation.polynomial
        hblinding proofIndex hsatisfaction hdomain
        (selectors proofIndex)
    simpa [TopLevelAssignment.environment, resolverEnvironment] using hgates
  have htop :
      orchardActionTopLevelCircuit.Statement 0
        assignment.placedEnvironment := by
    apply orchardActionTopLevelCircuit.soundness
    · exact assignment.synthesisWellFormed hbound
    · exact hconstraints
  have hstatement :=
    statement_of_topLevelStatement
      Specs.Sinsemilla.orchardGenerators orchardBases
      orchardActionTopLevelCircuit rfl 0
      assignment.placedEnvironment htop
  have hpublic :
      PublicInputs.ofEnvironment
          (Circuit.configure
            Specs.Sinsemilla.orchardGenerators {}).1
          assignment.environment =
        inputs proofIndex := by
    apply actionPublicInputs_of_instanceRowPolynomial
      assignment
      (Circuit.configure
        Specs.Sinsemilla.orchardGenerators {}).1
      (inputs proofIndex) hsize
    · exact hinstance proofIndex
    · exact TopLevelAssignment.domainRowsInjective hbound
  change
    Statement Specs.Sinsemilla.orchardGenerators orchardBases
      (PublicInputs.ofEnvironment
        (Circuit.configure
          Specs.Sinsemilla.orchardGenerators {}).1
        assignment.environment) at hstatement
  rwa [hpublic] at hstatement

/--
The binding-aware Action endpoint.

Fixed-column provenance supplies both selector activations and the fixed/table
operation family. A mismatch is returned as the augmented nontrivial-relation event
already used by the deployed extraction stack.
-/
theorem action_bundleStatement_or_relation_of_canonicalMemberConstraintRelation
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
    (vk : VerifyingKey
      (pp.mergeDerived orchardActionTopLevelCircuit) Fp G)
    (hvk :
      vk = orchardActionTopLevelCircuit.toVerifierKey pp urs)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi)
    (hbound : orchardActionTopLevelCircuit.domainExponent < 33)
    (hblinding :
      vk.blindingFactors < vk.n)
    (hpoly : Polynomial Fp)
    (relation :
      CanonicalMemberConstraintRelation
        urs hk vk
        instanceCommitment ps ch pU pW a batchOpenings memberDecode
        hblinding ch.y hpoly vk.n)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness relation.model.constraints
          vk.n j))
    (inputs :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
        PublicInputs)
    (hsize :
      10 ≤ 2 ^ orchardActionTopLevelCircuit.domainExponent)
    (instanceKey :
      LagrangeCommitmentKey urs
        (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega)
    (hinstanceCommitment : ∀
      proofIndex :
        Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs,
      instanceCommitment proofIndex
          (Circuit.configure
            Specs.Sinsemilla.orchardGenerators {}).1.primary.index =
        instanceKey.commitInstance (inputs proofIndex).rows 1)
    (hinstanceRegistered :
      ((Circuit.configure
          Specs.Sinsemilla.orchardGenerators {}).1.primary,
        (0 : Rotation)) ∈
        orchardActionTopLevelCircuit.constraintSystem.instanceQueries)
    (gateCoherence :
      TopLevelGateCoherence
        orchardActionTopLevelCircuit pp urs)
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        (orchardActionTopLevelCircuit.toVerifierKey pp urs)
        ch relation.polynomial actionActiveRows)
    (lookupExclusions :
      TopLevelLookupCoherence.TopLevelLookupChallengeExclusions
        orchardActionTopLevelCircuit pp urs ch relation.polynomial) :
    BundleStatement Specs.Sinsemilla.orchardGenerators orchardBases inputs ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  classical
  subst vk
  have hk' :
      orchardActionTopLevelCircuit.domainExponent = urs.k :=
    hk
  let fixedCoherence :
      TopLevelFixedCoherence
        orchardActionTopLevelCircuit pp urs :=
    ActionFixedCoherence.ofDerived pp urs hk'
  have hfixedRows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega ^
          (i : ℕ) := by
    rw [← hk']
    change Function.Injective
      (fun i : Fin
          (2 ^ orchardActionTopLevelCircuit.domainExponent) =>
        Zcash.Arithmetic.omegaOf
          orchardActionTopLevelCircuit.domainExponent ^ (i : ℕ))
    exact TopLevelAssignment.domainRowsInjective hbound
  have hdomainSize :
      (orchardActionTopLevelCircuit.toVerifierKey pp urs).n =
        2 ^ urs.k := by
    change
      2 ^ orchardActionTopLevelCircuit.domainExponent = 2 ^ urs.k
    rw [hk']
  have hlookupRows : Function.Injective
      fun i : Fin
          (orchardActionTopLevelCircuit.toVerifierKey pp urs).n =>
        (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega ^
          (i : ℕ) := by
    rw [hdomainSize]
    exact hfixedRows
  have hdomainRoot :
      (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega ^
        (orchardActionTopLevelCircuit.toVerifierKey pp urs).n = 1 := by
    change
      Zcash.Arithmetic.omegaOf
          orchardActionTopLevelCircuit.domainExponent ^
        (2 ^ orchardActionTopLevelCircuit.domainExponent) = 1
    exact TopLevelAssignment.domainRoot hbound
  have hnonzero :
      (orchardActionTopLevelCircuit.toVerifierKey pp urs).n ≠ 0 := by
    change 2 ^ orchardActionTopLevelCircuit.domainExponent ≠ 0
    positivity
  have hsatisfaction :=
    relation.constraintSatisfaction hnonzero hgoodY
  by_cases hrelation :
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
  · exact Or.inr hrelation
  · apply Or.inl
    have hinstance : ∀
        proofIndex :
          Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs,
        relation.polynomial
            (.instanceCol proofIndex
              (Circuit.configure
                Specs.Sinsemilla.orchardGenerators {}).1.primary.index) =
          instanceRowPolynomial
            (2 ^ orchardActionTopLevelCircuit.domainExponent)
            (Zcash.Arithmetic.omegaOf
              orchardActionTopLevelCircuit.domainExponent)
            (inputs proofIndex).rows := by
      intro proofIndex
      have hbound :=
        relation.instanceColumn_eq_rowPolynomial_or_relation
          proofIndex
          (Circuit.configure
            Specs.Sinsemilla.orchardGenerators {}).1.primary.index
          instanceKey (inputs proofIndex).rows 1
          (hinstanceCommitment proofIndex) hfixedRows
          (instanceQuery_of_layout
            (orchardActionTopLevelCircuit.toVerifierKey pp urs)
            instanceCommitment ps ch proofIndex
            (Circuit.configure
              Specs.Sinsemilla.orchardGenerators {}).1.primary.index
            0 gateCoherence.instanceQueryCount
            (QueryLayouts.instanceQueryLayout_of_constraintSystem
                orchardActionTopLevelCircuit pp urs
                (Circuit.configure
                  Specs.Sinsemilla.orchardGenerators {}).1.primary
                0 hinstanceRegistered))
      have hrows := hbound.resolve_right hrelation
      change relation.polynomial
          (.instanceCol proofIndex
            (Circuit.configure
              Specs.Sinsemilla.orchardGenerators {}).1.primary.index) =
        instanceRowPolynomial (2 ^ urs.k)
          (Zcash.Arithmetic.omegaOf
            orchardActionTopLevelCircuit.domainExponent)
          (inputs proofIndex).rows at hrows
      simpa only [hk'] using hrows
    apply action_bundleStatement_of_canonicalMemberConstraintRelation
      pp urs hk instanceCommitment ps ch
      (orchardActionTopLevelCircuit.toVerifierKey pp urs) rfl pU pW a
      batchOpenings memberDecode hbound hblinding hpoly relation hgoodY
      inputs hsize hinstance gateCoherence
    · intro proofIndex
      have hfixed :=
        relation.topLevelFixedConstraints_or_relation
          rfl fixedCoherence hfixedRows hdomainSize proofIndex
      have hclean := hfixed.resolve_right hrelation
      change SelectorActivationsRealized
        orchardActionTopLevelCircuit.selectorMap
        orchardActionTopLevelCircuit.selectorActivations
        (resolverEnvironment
          (orchardActionTopLevelCircuit.toVerifierKey pp urs)
          relation.polynomial proofIndex
          (orchardActionTopLevelCircuit.usableRowsAt
            orchardActionTopLevelCircuit.domainExponent))
      exact hclean.1
    · intro proofIndex
      have hcopy :=
        actionCopyReplayWitness_or_relation
          pp urs hk relation hgoodY fixedCoherence
          permutationExclusions proofIndex
      obtain ⟨copy⟩ := hcopy.resolve_right hrelation
      simpa only [actionActiveRows] using
        copy.constraints_or_bad.resolve_right hrelation
    · intro proofIndex
      let lookupCoherence :
          TopLevelLookupCoherence orchardActionTopLevelCircuit :=
        TopLevelLookupCoherence.ofTopLevel
      have lookupSelectorValues : ∀ lookup
          (henabled :
            lookup ∈ operationEnabledLookups
              (orchardActionTopLevelCircuit.operations 0) 0),
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
              (orchardActionTopLevelCircuit.toVerifierKey pp urs).n := by
          exact
            (lookup.activationRow_lt_usableRows
              gateCoherence henabled).trans_le
              (by
                change
                  orchardActionTopLevelCircuit.usableRowsAt
                      orchardActionTopLevelCircuit.domainExponent ≤
                    2 ^ orchardActionTopLevelCircuit.domainExponent
                unfold TopLevelCircuit.usableRowsAt
                omega)
        have hexact :=
          actionLookupInputSelectorLeafRowsExact
            fixedCoherence lookup henabled
        have hvalues :=
          lookup.inputSelectorValuesRealized_or_bad
            relation.polynomial fixedCoherence.rows
            hfixedRows hdomainSize
            (Bad :=
              HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
            (fun column hcolumn =>
              relation.fixedColumn_eq_rowPolynomial_or_relation
                column fixedCoherence.key
                (fixedCoherence.rows column)
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
      let conditions :=
        TopLevelLookupCoherence.TopLevelLookupWitnessConditions.ofChallengeExclusions
          ch relation.polynomial proofIndex
          lookupSelectorValues lookupExclusions
      exact lookupCoherence.constraints
        gateCoherence
        ch relation.polynomial proofIndex hblinding hsatisfaction
        hlookupRows hdomainRoot conditions
    · intro proofIndex
      have hfixed :=
        relation.topLevelFixedConstraints_or_relation
          rfl fixedCoherence hfixedRows hdomainSize proofIndex
      have hclean := hfixed.resolve_right hrelation
      change CircuitConstraintFamily.constraints .fixed
        orchardActionTopLevelCircuit.placement
        (resolverEnvironment
          (orchardActionTopLevelCircuit.toVerifierKey pp urs)
          relation.polynomial proofIndex
          (orchardActionTopLevelCircuit.usableRowsAt
            orchardActionTopLevelCircuit.domainExponent))
        (orchardActionTopLevelCircuit.operations 0) 0
      exact hclean.2
