import Zcash.Snark.Soundness.AGM.BindingSignature
import Zcash.Snark.Soundness.AGM.Capstone
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Zcash.Snark.Soundness.Forking.Adversary
import Zcash.Snark.Soundness.Composition.Bridge
import Zcash.Snark.Soundness.Multiopen.BudgetedExtraction
import Zcash.Snark.Soundness.VestaBudget
import Zcash.Snark.Soundness.FoldSplit
import Zcash.Snark.Soundness.ConstraintSatisfaction
import Zcash.Snark.Soundness.LookupRows
import Zcash.Snark.Soundness.LookupInstantiation
import Zcash.Snark.Soundness.Multiopen.ConstraintResolver
import Zcash.Snark.Soundness.GrandProductBridge
import Zcash.Snark.Soundness.LookupAssembly
import Zcash.Snark.Soundness.PermutationRows
import Zcash.Snark.Soundness.PermutationInstantiation
import Zcash.Snark.Soundness.PermutationSemantics
import Zcash.Snark.Soundness.CircuitSatisfaction
import Zcash.Snark.Soundness.OperationCopies
import Zcash.Snark.Soundness.Composition.Decomposition
import Zcash.Snark.Soundness.Composition.Residual
import Zcash.Snark.Soundness.Composition.Prefixes
import Zcash.Snark.Soundness.Composition.Completeness
import Zcash.Meta.AxiomCheck
import Mathlib.Util.AssertNoSorry

/-!
# AGM trust-boundary checks

The AGM kernels compute representations, openings, relations, certificates, and deployed instances
as data. `assert_no_sorry` checks the executable producer and consumer path; the guarded reports
record its proof dependencies. The reach-set and split-family producers (`globalReachSet` /
`splitFamilyRand`) are held at the stronger `assert_computable +choice` tier: plain defs, with
`Classical.choice` entering only through erased `Prop` positions.
-/

open Zcash.Snark

assert_no_sorry discreteLogOfBasis_of_relation
assert_no_sorry DLChallengeGame.solveFromRelation
assert_no_sorry fixedSlotExtractOrMiss
assert_no_sorry AugmentedRelationWitness.toAlgebraicRelationWitness
assert_no_sorry relationWitnessOfCollision
assert_no_sorry discreteLogOfAugmentedRelationAtChallenge
assert_no_sorry separateOrRelationWitness
assert_no_sorry relationOfFoldGensWitness
assert_no_sorry deployedLeafPeelWitness
assert_no_sorry deployedToAcceptVWitness
assert_no_sorry algebraicRelationOfDeployedAccept
assert_no_sorry AlgebraicProver.toProver
assert_no_sorry AlgebraicDForkCert.toDForkCert
assert_no_sorry algebraicProverAccept_forkValid
assert_no_sorry deployedAlgebraicForkingRelation
assert_no_sorry deployed_forking_relation_shifted
assert_no_sorry deployedAlgebraicForkingRelation_shifted
assert_no_sorry deployedAlgebraicForkingFixedSlot
assert_no_sorry DeployedAlgebraicForkingInstance.run
assert_no_sorry DeployedAlgebraicForkingInstance.ProducesRelation
assert_no_sorry deployedAlgebraicRelationProduced
assert_no_sorry deployedAlgebraicRelationEvent
assert_no_sorry deployedAlgebraicRelationFinder
assert_no_sorry deployedAlgebraicRelationFinder_isSome_iff
assert_no_sorry deployedAlgebraicRelation
assert_no_sorry deployedAlgebraicRelationWitness
assert_no_sorry orchardDeployedAlgebraicForkingFixedSlot
assert_no_sorry orchardDeployedRelationSet
assert_no_sorry OrchardUniformURSIdentification
assert_no_sorry orchardGeneratorROSetup
assert_no_sorry orchardGeneratorROBasis
assert_no_sorry orchard_uniformURSIdentification_of_generatorRO
assert_no_sorry recursiveAlgebraicForkFrom
assert_no_sorry recursiveAlgebraicForkFrom_realizes
assert_no_sorry algebraicForkCertAttempt
assert_no_sorry algebraicForkCertAttempt_valid
assert_no_sorry computedDeployedAlgebraicInstance
assert_no_sorry computedAlgebraicInstanceFailure_measure_le
assert_no_sorry AlgebraicRelationWitness.augment
assert_no_sorry DeployedAlgebraicForkingInstance.runRelation
assert_no_sorry DeployedAlgebraicForkingInstance.runRelation_isSome_of_mismatch
assert_no_sorry DeployedAlgebraicForkingInstance.runToSnark
assert_no_sorry ComputedAlgebraicFSFamily.relationFinder
assert_no_sorry ComputedAlgebraicFSFamily.relationFinder_isSome_of_bindingWin
assert_no_sorry ComputedAlgebraicFSFamily.snarkRelationFinder
assert_no_sorry ComputedAlgebraicFSFamily.snarkRelation_prob_le_of_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.acceptExtractionFailure_measure_le
assert_no_sorry ComputedAlgebraicFSFamily.snarkNonRelationFailure
assert_no_sorry ComputedAlgebraicFSFamily.snarkNonRelationFailure_measure_le
assert_no_sorry ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL_full
assert_no_sorry ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_uniformURS_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_generatorRO_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.binding_prob_le_of_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.binding_prob_le_of_uniformURS_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.binding_prob_le_of_generatorRO_textbookDL
assert_no_sorry ComputedAlgebraicFSFamily.ReductionEfficient
assert_no_sorry ComputedAlgebraicFSFamily.reductionEfficient_exists
assert_no_sorry ComputedAlgebraicFSFamily.instanceAttempt_runs_eq
assert_no_sorry ComputedAlgebraicFSFamily.reductionEfficient_exponential
assert_no_sorry ComputedAlgebraicFSFamily.DiscreteLogRelationHardFor
assert_no_sorry ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL
assert_no_sorry ComputedAlgebraicFSFamily.binding_under_DL
assert_no_sorry bindingWin_unbounded_measure_le
assert_no_sorry queryCharge
assert_no_sorry queryCharge_sum_mul_le
assert_no_sorry le_queryCharge_of_mem_queries
assert_no_sorry mem_queries_dedup
assert_no_sorry applyUpdates_apply_mem_nodup
assert_no_sorry queryCharge_sum_mul_le_table_budget
assert_no_sorry steeredCharge_context_sum_mul_le
assert_no_sorry steeredCharge_context_sum_mul_le_table_budget
assert_no_sorry steeredCharge_sum_mul_le
assert_no_sorry scanCandidate_self
assert_no_sorry self_mem_goodChallenges_iff
assert_no_sorry scanRank_insert_erase
assert_no_sorry scanRank_insert_eq_filter
assert_no_sorry goodChallengesAt
assert_no_sorry OracleComp.queries_queryList
assert_no_sorry recursiveAlgebraicForkFrom_node_runs_le_gated
assert_no_sorry OracleComp.queries_bind
assert_no_sorry OracleComp.mem_queries_completing
assert_no_sorry scanCandidateAt
assert_no_sorry scanCandidateAt_fork
assert_no_sorry scanCandidateAt_update
assert_no_sorry goodChallengesAt_fork
assert_no_sorry goodChallengesAt_update
assert_no_sorry sum_card_scanRank_erase_lt_le
assert_no_sorry OracleComp.restrictSum
assert_no_sorry fsWinsFull_restrictSum_le
assert_no_sorry ComputedAlgebraicFSFamilyRand.determinize
assert_no_sorry ComputedAlgebraicFSFamilyRand.binding_prob_le_of_textbookDL_rand
assert_no_sorry ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_textbookDL_rand
assert_no_sorry ComputedAlgebraicFSFamily.snarkFailureEvent
assert_no_sorry ComputedAlgebraicFSFamilyRand.foldedRelationFinder
assert_no_sorry ComputedAlgebraicFSFamilyRand.binding_prob_le_of_foldedTextbookDL_rand
assert_no_sorry ComputedAlgebraicFSFamilyRand.foldedSnarkRelationFinder
assert_no_sorry ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_foldedTextbookDL_rand
assert_computable ComputedAlgebraicFSFamilyUnbounded.globalReachSet +choice
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.reachSet_subset_globalReachSet
assert_computable ComputedAlgebraicFSFamilyUnbounded.splitFamilyRand +choice
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.run_splitFamilyRand_adversary
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_foldedTextbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_foldedTextbookDL
assert_no_sorry uniformURS_basis_transfer
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.snarkFailureEventUnbounded
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_uniformURS_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_generatorRO_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.bindingEventUnbounded
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_uniformURS_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_generatorRO_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.determinize
assert_computable ComputedAlgebraicFSFamilyUnboundedRand.globalReachSet +choice
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.reachSet_subset_globalReachSet
assert_computable ComputedAlgebraicFSFamilyUnboundedRand.splitFamilyRand +choice
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.run_splitFamilyRand_adversary
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_foldedTextbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_foldedTextbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.snarkFailureEventUnboundedRand
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_uniformURS_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_generatorRO_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.bindingEventUnboundedRand
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_uniformURS_textbookDL
assert_no_sorry ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_generatorRO_textbookDL
assert_no_sorry recursiveAlgebraicForkFrom_node_runs_le
assert_no_sorry recursiveAlgebraicFork_sum_runs_le_unconditional
assert_no_sorry recursiveAlgebraicFork_oracle_tape_sum_runs_le_unconditional
assert_no_sorry recursiveAlgebraicForkFrom_sum_runs_le_of_forkSpread
assert_no_sorry recursiveAlgebraicFork_sum_runs_le_of_forkSpread
assert_no_sorry AlgebraicPoint.point_eq_components
assert_no_sorry Msm.eval_repr
assert_no_sorry RepresentedMultiopen.ofCoveredList
assert_no_sorry AlgebraicWfProof.ofRepresented
assert_no_sorry assembleQueries_points_mem
assert_no_sorry constructIntermediateSets_ref_mem
assert_no_sorry multiopenMsm_points_mem
assert_no_sorry AlgebraicWfProof.ofStandard
assert_no_sorry OracleComp.reachSet
assert_no_sorry OracleComp.run_congr_reachSet
assert_no_sorry OracleComp.restrictTo
assert_no_sorry OracleComp.splitDomain
assert_no_sorry finite_domain_restriction
assert_no_sorry fsWinsFull_mapDomain_measure_eq
assert_no_sorry fsWinsFull_splitDomain
assert_no_sorry fsWinsFull_unbounded_measure_le
assert_no_sorry truncateTranscript
assert_no_sorry Zcash.Security.BindingSignature.NontrivialRelation.toAlgebraicRelationWitness
assert_no_sorry Zcash.Security.BindingSignature.NontrivialRelation.toDiscreteLog
assert_no_sorry Zcash.Security.BindingSignature.orchardImbalanceToDiscreteLog
assert_no_sorry Zcash.Security.BindingSignature.saplingImbalanceToDiscreteLog

/-- info: 'Zcash.Snark.eval_combineConstraints_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eval_combineConstraints_deployed

/-- info: 'Zcash.Snark.hfold_of_constraint_polys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hfold_of_constraint_polys

/-- info: 'Zcash.Snark.discreteLogOfBasis_of_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms discreteLogOfBasis_of_relation

/-- info: 'Zcash.Snark.DLChallengeGame.solveFromRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DLChallengeGame.solveFromRelation

/-- info: 'Zcash.Snark.fixedSlotExtractOrMiss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedSlotExtractOrMiss

/-- info: 'Zcash.Snark.AugmentedRelationWitness.toAlgebraicRelationWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AugmentedRelationWitness.toAlgebraicRelationWitness

/-- info: 'Zcash.Snark.relationWitnessOfCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relationWitnessOfCollision

/-- info: 'Zcash.Snark.discreteLogOfAugmentedRelationAtChallenge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms discreteLogOfAugmentedRelationAtChallenge

/-- info: 'Zcash.Snark.separateOrRelationWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms separateOrRelationWitness

/-- info: 'Zcash.Snark.relationOfFoldGensWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relationOfFoldGensWitness

/-- info: 'Zcash.Snark.deployedLeafPeelWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedLeafPeelWitness

/-- info: 'Zcash.Snark.deployedToAcceptVWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedToAcceptVWitness

/-- info: 'Zcash.Snark.algebraicRelationOfDeployedAccept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms algebraicRelationOfDeployedAccept

/-- info: 'Zcash.Snark.deployedAlgebraicForkingRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicForkingRelation

/-- info: 'Zcash.Snark.deployedAlgebraicForkingFixedSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicForkingFixedSlot

/-- info: 'Zcash.Snark.deployedAlgebraicRelationFinder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicRelationFinder

/-- info: 'Zcash.Snark.deployedAlgebraicRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicRelation

/-- info: 'Zcash.Snark.deployedAlgebraicRelationWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployedAlgebraicRelationWitness

/-- info: 'Zcash.Security.BindingSignature.NontrivialRelation.toAlgebraicRelationWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Security.BindingSignature.NontrivialRelation.toAlgebraicRelationWitness

/-- info: 'Zcash.Security.BindingSignature.NontrivialRelation.toDiscreteLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Zcash.Security.BindingSignature.NontrivialRelation.toDiscreteLog

/-! The probability layer contains theorems rather than data-producing definitions. The checks below
pin its proof dependencies. -/

assert_no_sorry hitProb_ge_inv_card
assert_no_sorry relSet_card_le_succSet_card
assert_no_sorry reduction_advantage_ge
assert_no_sorry relation_prob_le_of_DL
assert_no_sorry winSet_card
assert_no_sorry textbook_winProb_eq_succProb
assert_no_sorry relation_prob_le_of_textbookDL
assert_no_sorry orchard_relation_prob_le_of_DL
assert_no_sorry orchard_reduction_advantage_ge
assert_no_sorry orchard_relation_prob_le_of_textbookDL
assert_no_sorry commitment_binding_prob_le_of_textbookDL
assert_no_sorry orchard_deployed_reduction_advantage_ge
assert_no_sorry orchard_deployed_relation_prob_le_of_textbookDL
assert_no_sorry orchard_deployed_relation_set_eq_relSet
assert_no_sorry orchard_deployed_relation_event_prob_le_of_textbookDL
assert_no_sorry orchard_deployed_relation_prob_eq_of_uniformURS
assert_no_sorry orchard_deployed_relation_prob_le_of_uniformURS_textbookDL
assert_no_sorry orchard_deployed_relation_prob_le_of_generatorRO_textbookDL

-- The multiopen value-check chain: the deployed value check derived from the nested
-- forking floors, the x₁ member un-batch on top of it, and the terminal with `hadvice`/`hinstance`
-- produced rather than assumed (`Soundness.Multiopen.NodeBinding`, `Soundness.Vesta`).
assert_no_sorry deployed_value_check_node_binding
assert_no_sorry deployed_member_node_binding
assert_no_sorry orchard_verifier_vesta_member_constraint_derived

-- The forking-extraction ∘ decoded-capstone composition (`Soundness.Composition.Bridge`): the algebraic
-- clean opening identified with the deployed capstone's shape (`ipaRelation_deployed_of_instance`),
-- the witness-tie composition (`member_snark_of_instance`), and the computed-path soundness
-- endpoint (`orchard_verifier_sound_vesta_computed`) that concludes the plain `SnarkRelation` with
-- NO `ExtractableFromAcceptance` hypothesis. On the witness tie the opened-value shift is derived
-- (`shift_eq_zero_of_openings_agree`), so `hshift` survives only on the standalone single-opening
-- bridge. `snarkExtraction_prob_le_of_generatorRO_textbookDL` is the CONDITIONAL knowledge-error
-- bound: the SNARK-extraction failure is contained in the clean-opening failure and inherits its
-- `(Q+k)·3/|Fp| + (Q+1)/|Fp| + |basis|·ε` bound, conditional on `hExtract` (clean opening ⟹
-- extraction). Discharging `hExtract` — coupling the AGM family's coin measure to the multiopen
-- budget below — is the remaining reconciliation.
assert_no_sorry ipaRelation_deployed_of_instance
assert_no_sorry member_snark_of_instance
assert_no_sorry snarkRelation_of_memberColumns
assert_no_sorry orchard_verifier_sound_vesta_computed
assert_no_sorry snarkExtraction_prob_le_of_generatorRO_textbookDL
assert_no_sorry instanceAttempt_provenance
assert_no_sorry ipaRelation_deployed_of_openings_agree
assert_no_sorry shift_eq_zero_of_openings_agree

-- The budgeted multiopen extraction (`Soundness.Multiopen.FloorBudget`,
-- `Soundness.Multiopen.BudgetedExtraction`): the heavy-fiber Markov descent
-- (`uniformOfFintype_heavy_fiber_lt`) replaces the `∀`-over-runs squeeze floors of the value-check
-- and member cores with a single joint accept floor at honest-base thresholds, the runs pinned by
-- the canonical selectors; `deployed_member_budget` is the combined soundness budget — the joint
-- accept measure sits within the four-threshold budget, or every decoded member column takes its
-- claimed evaluation (or a computed relation exists).
assert_no_sorry uniformOfFintype_heavy_fiber_lt
assert_no_sorry deployed_value_check_node_binding_budgeted
assert_no_sorry deployed_member_node_binding_budgeted
assert_no_sorry deployed_member_budget

-- The decode layer (`Soundness.Multiopen.Decode`/`Deployed`): the Vandermonde recovery of the
-- column witnesses, the deployed x4 collapse proved to be a flat power batch, and the two-level
-- binding of the extracted witness to the member commitments.
assert_no_sorry decodedColumnFamily_of_batch_openings
assert_no_sorry deployedCommitment_x4_batch
assert_no_sorry multiopenValue_x4_batch
assert_no_sorry x1_batch_open_soundV
assert_no_sorry member_binding_of_x1_samples
assert_no_sorry deployed_witness_member_binding
assert_no_sorry deployed_witness_two_level
assert_no_sorry node_binding_of_samples
-- The good-challenge production (`Soundness.GoodChallenge`): the Schwartz-Zippel exclusion budget
-- and the pigeonhole that produces an accepting challenge outside the bad set.
assert_no_sorry uniformChallenge_szBadSet
assert_no_sorry uniformChallenge_szGoodSet
assert_no_sorry uniformChallenge_quotient_szBadSet
assert_no_sorry uniformChallenge_szBadSet_union
assert_no_sorry exists_accepting_good_challenge
assert_no_sorry exists_accepting_good_challenge_quotient
-- The deployed Vesta capstone family: the decoded-column rungs and the terminal, alongside the
-- derived capstone already pinned below.
assert_no_sorry orchard_verifier_vesta_decoded_constraint_of_forked_x4
assert_no_sorry orchard_verifier_vesta_forking_constraint_deployed_x4
assert_no_sorry orchard_verifier_vesta_member_constraint_deployed_x4
assert_no_sorry orchard_verifier_vesta_member_constraint_deployed_terminal

-- The budgeted capstone and computed path (`Soundness.VestaBudget`): the derived deployed member
-- capstone with the run-quantified floors replaced by the joint accept floor, and the computed-path
-- endpoint with the member decode constructed and `hquot` derived — no extraction-data hypothesis.
assert_no_sorry deployed_member_node_binding_at_point_budgeted
assert_no_sorry orchard_verifier_vesta_member_constraint_budgeted
assert_no_sorry member_relation_or_dlr_of_instance_budgeted
assert_no_sorry member_snark_of_instance_budgeted
assert_no_sorry orchard_verifier_sound_vesta_budgeted
assert_no_sorry cleanOpening_provenance
assert_no_sorry snarkExtraction_prob_le_of_generatorRO_textbookDL_budgeted
-- The `hfold` surface: the grouping's eval faithfulness at the vanishing slot is proven, not
-- assumed, so the derivation reads the verifier-computed `expectedHEval` off the routed member.
assert_no_sorry vanishing_query_mem_assembleQueries
assert_no_sorry assembleQueries_vanishingH_unique
assert_no_sorry constructIntermediateSets_unique_comm_routed
assert_no_sorry vanishing_slot_routed
assert_no_sorry hfold_of_expectedHEval_binding
assert_no_sorry hfold_of_vanishing_slot_binding
-- The root-of-unity exclusion is derived from acceptance (`assemble?` rejects at `xⁿ = 1`), and the
-- budget's good branch supplies `hbind` at the routed vanishing slot — so `hfold` now stands on the
-- fingerprint premise alone.
assert_no_sorry deployedAccepts_xn_ne_one
assert_no_sorry hfold_of_member_budget
-- The permutation and lookup arguments folded into the constraint model: the verifier's expression
-- list is the generic builder run on its own claimed evaluations, the same builder over column
-- polynomials evaluates back onto it, and the fold equation therefore needs no fingerprint premise.
assert_no_sorry permutationExpressions_map
assert_no_sorry lookupExpressions_map
assert_no_sorry subProofConstraints_map
assert_no_sorry allConstraints_map
assert_no_sorry subProofExpressions_eq
assert_no_sorry allExpressions_eq
assert_no_sorry eval_constraintPolys
assert_no_sorry eval_combineConstraints
assert_no_sorry eval_combineConstraints_deployed
assert_no_sorry hfold_of_constraint_polys
assert_no_sorry ConstraintPolyModel.constraints_eq_constraintPolys
assert_no_sorry ConstraintPolyModel.gate_mem_constraints
assert_no_sorry ConstraintPolyModel.permutation_mem_constraints
assert_no_sorry ConstraintPolyModel.lookup_mem_constraints
assert_no_sorry ConstraintPolyModel.lookupExpression_mem_lookupConstraints
assert_no_sorry ConstraintSatisfaction.of_all
assert_no_sorry ConstraintSatisfaction.lookupExpression
assert_no_sorry permutation_start_mem
assert_no_sorry permutation_end_mem
assert_no_sorry permutation_chain_mem
assert_no_sorry permutation_step_mem
assert_no_sorry lookup_start_mem
assert_no_sorry lookup_end_mem
assert_no_sorry lookup_product_step_mem
assert_no_sorry lookup_run_start_mem
assert_no_sorry lookup_run_step_mem
assert_no_sorry ConstraintSatisfaction.lookupStart
assert_no_sorry ConstraintSatisfaction.lookupEnd
assert_no_sorry ConstraintSatisfaction.lookupProductStep
assert_no_sorry ConstraintSatisfaction.lookupRunStart
assert_no_sorry ConstraintSatisfaction.lookupRunStep
-- The permutation and lookup arguments closed from the verifier's own row checks: the combined
-- check splits into its parts, the running product telescopes across the rows, two challenge root
-- counts turn the product into a multiset identity, and the existing structural theorems turn that
-- into the copy constraints and the lookup inclusion.
assert_no_sorry constraints_dvd_of_good_y
assert_no_sorry telescope_running_product
assert_no_sorry grandProduct_eq_or_cell_eq_zero
assert_no_sorry multiset_pair_eq_of_prod_eval_eq
assert_no_sorry cellPairs_eq_of_running_product
assert_no_sorry perm_copy_constraints_of_running_product
assert_no_sorry prod_map_chunkedCellPairs
assert_no_sorry chunkedCellPairs_eq_of_running_product
assert_no_sorry perm_copy_constraints_of_chunked_running_product
assert_no_sorry telescope_chunks
assert_no_sorry telescope_chunks_variable_width
assert_no_sorry chunkedGrandProduct_eq_or_cell_eq_zero
assert_no_sorry lookup_multisets_of_prod_eval_eq
assert_no_sorry lookup_multisets_of_diff_eq_zero
assert_no_sorry lookup_subset_of_components
assert_no_sorry lookup_subset_of_prod_eval_eq
assert_no_sorry eval_lookupEvalPolys_productNextEval
assert_no_sorry eval_lookupEvalPolys_permutedInputInvEval_succ
assert_no_sorry lookup_product_row_recurrence
assert_no_sorry lookup_run_start_of_dvd
assert_no_sorry lookup_run_step_of_dvd
assert_no_sorry lookup_run_structure_of_dvd
assert_no_sorry lookup_product_eq_or_factor_eq_zero
assert_no_sorry deployed_lookup_subset
assert_no_sorry mem_assembleQueries_of_mem_subProofLookupQueries
assert_no_sorry constraintModelOfResolver_lookups
assert_no_sorry lookupEntry_mem_lookupEntriesOfResolver
assert_no_sorry lookupEntry_mem_constraintModelOfResolver
assert_no_sorry eval_lookupEntriesOfResolver
assert_no_sorry eval_lookupEntriesOfResolver_of_assembleQueries
assert_no_sorry eval_constraintModelOfResolver_lookups
assert_no_sorry eval_constraintModelOfResolver_lookups_of_assembleQueries
assert_no_sorry ConstraintSatisfaction.lookupConstraintsDvdOfResolver
assert_no_sorry query_eq_of_noDuplicateCommitmentPoint
assert_no_sorry constructIntermediateSets_query_routed
assert_no_sorry constructIntermediateSets_query_eval
assert_no_sorry assembledQueryMemberRoute
assert_no_sorry assembledQueryMemberRoute_faithful
assert_no_sorry assembledQueryRoutingConditions_of_assemble?_eq_some
assert_no_sorry decodedPolynomialResolver_opens_or_relation
assert_no_sorry eval_lookupEntriesOfDecodedResolver_or_relation
-- The deployed row reading: the step rule's folds are running products, the boundary rules pin the
-- product at the first and last rows, and the cell names separate. These are theorems about
-- `permChunkExpression` itself, so the chain above starts at the verifier's own constraint list.
assert_no_sorry permChunk_left_eq_prod
assert_no_sorry permChunk_right_eq_prod
assert_no_sorry permChunkExpression_eq
assert_no_sorry eval_eq_zero_of_dvd_vanishing
assert_no_sorry perm_row_recurrence
assert_no_sorry running_product_start
assert_no_sorry running_product_end
assert_no_sorry running_product_chain
assert_no_sorry name_injective_of_coset
assert_no_sorry deployed_perm_copy_constraints
assert_no_sorry deployed_perm_copy_constraints_all_chunks
assert_no_sorry permutationLastEval_isSome
assert_no_sorry eval_permutationSetsOfResolver
assert_no_sorry eval_permutationColumnPolynomialOfResolver
assert_no_sorry eval_permutationCommonPolynomialOfResolver
assert_no_sorry eval_permutationChunkPairsOfResolver
assert_no_sorry eval_permutationChunksOfResolver
assert_no_sorry ConstraintSatisfaction.resolverPermutationConstraints
assert_no_sorry flattenPermutationChunkCell_injective
assert_no_sorry chunkRowName_injective_of_coset
assert_no_sorry replayKeygenPermutation_pair_linked
assert_no_sorry replayKeygenPermutation_sameCycle_iff
assert_no_sorry chunkPermutationOfFlat_apply
assert_no_sorry keygenSigmaColumn_eval
assert_no_sorry keygenSigmaColumn_natDegree_lt
assert_no_sorry ResolverPermutationCycle.ofKeygenColumns
assert_no_sorry mem_additiveZeroBadSet_iff
assert_no_sorry uniformChallenge_additiveZeroBadSet
assert_no_sorry mem_resolverPermutationZeroFactorBadSet_iff
assert_no_sorry uniformChallenge_resolverPermutationGammaBadSet
assert_no_sorry ConstraintSatisfaction.resolverPermutationCopyConstraints
assert_no_sorry CircuitConstraintFamily.operations_constraints_iff
assert_no_sorry FullCircuitSatisfaction.iff_constraints
assert_no_sorry FullCircuitSatisfaction.of_components_or_bad
assert_no_sorry CircuitConstraintFamily.copy_constraints_iff_declaredCopies
assert_no_sorry copy_constraints_or_bad_of_replay
assert_no_sorry permutationLastEvalsWellFormed_of_assemble?_eq_some
assert_no_sorry eval_permutationDataOfDecodedResolver_or_relation
assert_no_sorry hgood_failure_priced
assert_no_sorry hgood_of_good_challenge
-- The UNCONDITIONAL decomposition: `hExtract` removed, the residual quantified as the
-- clean-but-not-extracted measure term (bounded by the multiopen budget under the coupling
-- documented in `Composition.Decomposition`, not assumed here).
assert_no_sorry ComputedAlgebraicFSFamily.snarkExtractionFailureEvent_subset_union
assert_no_sorry snarkExtraction_prob_le_of_generatorRO_textbookDL_decomposed
-- The forking reduction: the residual closed to the multiopen budget `t` by the fibered single-slot
-- counting bound, transported along the challenge-uniformity coupling. The coupling `hcouple` and the
-- accept containment `hcont` are the isolated non-circular premises (documented in `Composition.Residual`);
-- the reduction itself is proven.
assert_no_sorry fibered_accept_below_threshold_le
assert_no_sorry residual_le_of_coupling_containment
assert_no_sorry snarkExtraction_prob_le_of_generatorRO_textbookDL_unconditional
-- The adaptive-coupling ladder (`Soundness.Composition.Assembly`): the residual bounded through the
-- honest random-oracle query loss instead of the over-idealised exact pushforward. Its two inputs
-- are the family `PeelDecode` and the honest-completeness containment `hcont`.
assert_no_sorry independentProductPMF_fiber_bound
assert_no_sorry residual_le_via_ladder
assert_no_sorry snarkExtraction_prob_le_of_generatorRO_textbookDL_ladder
-- The ladder at the concrete multiopen prefixes (`Soundness.Composition.Prefixes`): the four `x₁`–`x₄`
-- squeeze points, the decode's chain half discharged outright, and its state half reduced to the
-- level-0 factorisation of the accept event (`exists_multiopenStateAt_iff`, an iff — so the
-- factorisation is exactly the standing decode-side input, not a convenient sufficient condition).
assert_no_sorry multiopenPrefixReads_eq
assert_no_sorry multiopenLen_lt
assert_no_sorry multiopenChainAt_prefixes
assert_no_sorry multiopenLevelOf_prefixes
assert_no_sorry multiopenChainAt_ne
assert_no_sorry exists_multiopenStateAt_iff
assert_no_sorry multiopenPeelDecode_of_factors
assert_no_sorry snarkExtraction_prob_le_of_generatorRO_textbookDL_multiopen
-- The honest-completeness half of `hcont` (`Soundness.Composition.Completeness`): the bad event priced
-- unconditionally, and the landing side reduced to the AGM-completeness supply, itself built from a
-- clean opening's forked transcript.
assert_no_sorry memberBadEvent_measure_le
assert_no_sorry memberBadEvent_of_supply
assert_no_sorry honestCompletenessSupply_of_forkedTranscript
assert_no_sorry forkedTranscript_nonempty_of_instanceOpening
assert_no_sorry honestCompletenessSupply_of_instanceOpening
-- The supply's own inputs, discharged: the three IPA fold challenges are exhibited in `Fp`, deployed
-- acceptance is reduced to the family's accept predicate, and the value shift is forced by the
-- witness tie. What is left in `honestCompletenessSupply_of_cleanOpening` is the tie itself.
assert_no_sorry exists_ipaFoldChallenges
assert_no_sorry deployedAccepts_of_verifierEq
assert_no_sorry honestCompletenessSupply_of_openings_agree
assert_no_sorry honestCompletenessSupply_of_cleanOpening
-- The witness tie is no longer a premise: the clean opening and the batch witness commit to the
-- same element, so either they agree (supply) or they collide (relation).
assert_no_sorry honestCompletenessSupply_or_relation
-- Acceptance through `assemble?`: the deployed decision excludes the verifier's rejection paths,
-- which `DeployedIpaVerifierEq` does not, so the supply carries no `assemble? = some m` premise.
assert_no_sorry fullAlgebraicAcceptDeployed
assert_no_sorry fullAlgebraicAccept_of_deployed
assert_no_sorry honestCompletenessSupply_of_cleanOpening_deployed
assert_no_sorry snarkExtractionFailureEventDeployed
assert_no_sorry snarkExtractionFailureEventDeployed_subset
assert_no_sorry snarkExtractionFailureEventDeployed_measure_le
-- The adaptive coupling (`Forking.AdaptiveCoupling`): escapes blind by overwriting rather than by
-- decoding, the per-level averaging bound, and the ladder logic separated from the weights.
assert_no_sorry updEsc
assert_no_sorry updEsc_blind
assert_no_sorry card_heavy_mul_le
assert_no_sorry updEsc_measure_le
assert_no_sorry updEsc_escapesDuringC_measure_le
assert_no_sorry adaptEsc
assert_no_sorry adapt_decomposition
assert_no_sorry adaptEsc_measure_le

/-- info: 'Zcash.Snark.orchard_verifier_vesta_member_constraint_budgeted' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_verifier_vesta_member_constraint_budgeted

/-- info: 'Zcash.Snark.orchard_verifier_sound_vesta_budgeted' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_verifier_sound_vesta_budgeted

/-- info: 'Zcash.Snark.uniformOfFintype_heavy_fiber_lt' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformOfFintype_heavy_fiber_lt

/-- info: 'Zcash.Snark.deployed_member_node_binding_budgeted' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployed_member_node_binding_budgeted

/-- info: 'Zcash.Snark.deployed_member_budget' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployed_member_budget

/-- info: 'Zcash.Snark.ipaRelation_deployed_of_openings_agree' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ipaRelation_deployed_of_openings_agree

/-- info: 'Zcash.Snark.shift_eq_zero_of_openings_agree' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms shift_eq_zero_of_openings_agree

/-- info: 'Zcash.Snark.relation_prob_le_of_textbookDL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relation_prob_le_of_textbookDL

/-! The Vesta endpoints also depend on CompElliptic's `native_decide` point-count axiom through the
`Module Fp VestaG` instance. The checks below record that extra dependency. -/

/-- info: 'Zcash.Snark.orchard_relation_prob_le_of_textbookDL' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_relation_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.commitment_binding_prob_le_of_textbookDL' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms commitment_binding_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.orchard_deployed_relation_prob_le_of_textbookDL' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_deployed_relation_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.orchard_deployed_relation_prob_le_of_uniformURS_textbookDL' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_deployed_relation_prob_le_of_uniformURS_textbookDL

/-- info: 'Zcash.Snark.orchard_uniformURSIdentification_of_generatorRO' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_uniformURSIdentification_of_generatorRO

/-- info: 'Zcash.Snark.orchard_deployed_relation_prob_le_of_generatorRO_textbookDL' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orchard_deployed_relation_prob_le_of_generatorRO_textbookDL

/-! The adversary bounds charge query loss, `z = 0`, and fixed-slot DL. Vesta inherits
CompElliptic's point-count axiom. A polynomial AFK call bound is unproved; PPT time is external. -/

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.binding_prob_le_of_textbookDL' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.binding_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.binding_prob_le_of_uniformURS_textbookDL' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.binding_prob_le_of_uniformURS_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.binding_prob_le_of_generatorRO_textbookDL' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.binding_prob_le_of_generatorRO_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyRand.binding_prob_le_of_textbookDL_rand' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamilyRand.binding_prob_le_of_textbookDL_rand

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyRand.binding_prob_le_of_foldedTextbookDL_rand' depends
on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamilyRand.binding_prob_le_of_foldedTextbookDL_rand

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_foldedTextbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_foldedTextbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_foldedTextbookDL_rand'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_foldedTextbookDL_rand

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_foldedTextbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_foldedTextbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_generatorRO_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_generatorRO_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_generatorRO_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_generatorRO_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_generatorRO_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_generatorRO_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_generatorRO_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_generatorRO_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_uniformURS_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_uniformURS_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_uniformURS_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_uniformURS_textbookDL

/-- info: 'Zcash.Snark.recursiveAlgebraicFork_oracle_tape_sum_runs_le_unconditional' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recursiveAlgebraicFork_oracle_tape_sum_runs_le_unconditional

/-- info: 'Zcash.Snark.recursiveAlgebraicFork_sum_runs_le_of_forkSpread' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recursiveAlgebraicFork_sum_runs_le_of_forkSpread

/-- info: 'Zcash.Snark.bindingWin_unbounded_measure_le' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms bindingWin_unbounded_measure_le

/-! The executable producer returns the deployed `S ⊕' relation` dichotomy. -/

/-- info: 'Zcash.Snark.DeployedAlgebraicForkingInstance.runToSnark' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms DeployedAlgebraicForkingInstance.runToSnark

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.snarkRelation_prob_le_of_textbookDL' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.snarkRelation_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL_full' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL_full

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_generatorRO_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_generatorRO_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.snarkNonRelationFailure_measure_le' depends on
axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.snarkNonRelationFailure_measure_le

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.reductionEfficient_exists' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.reductionEfficient_exists

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.reductionEfficient_exponential' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.reductionEfficient_exponential

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.binding_under_DL' depends on axioms: [propext,
Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.binding_under_DL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_uniformURS_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_uniformURS_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_textbookDL_rand'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_textbookDL_rand

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_uniformURS_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_uniformURS_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_uniformURS_textbookDL'
depends on axioms: [propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms
  ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_uniformURS_textbookDL

/-- info: 'Zcash.Snark.ComputedAlgebraicFSFamily.instanceAttempt_runs_eq' depends on axioms:
[propext, Classical.choice, Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms ComputedAlgebraicFSFamily.instanceAttempt_runs_eq

/-- info: 'Zcash.Snark.uniformURS_basis_transfer' depends on axioms: [propext, Classical.choice,
Quot.sound, CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms uniformURS_basis_transfer

/-- info: 'Zcash.Snark.recursiveAlgebraicFork_sum_runs_le_unconditional' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recursiveAlgebraicFork_sum_runs_le_unconditional

/-- info: 'Zcash.Snark.queryCharge_sum_mul_le_table_budget' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms queryCharge_sum_mul_le_table_budget

/-- info: 'Zcash.Snark.steeredCharge_context_sum_mul_le_table_budget' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms steeredCharge_context_sum_mul_le_table_budget

/-- info: 'Zcash.Snark.sum_card_scanRank_erase_lt_le' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_card_scanRank_erase_lt_le

/-- info: 'Zcash.Snark.recursiveAlgebraicForkFrom_node_runs_le_gated' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recursiveAlgebraicForkFrom_node_runs_le_gated
