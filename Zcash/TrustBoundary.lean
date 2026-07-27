import Zcash.Circuits.Action.RealBases
import Zcash.Security.Ledger.Bridge
import Zcash.Security.Ledger.SinsemillaDLR
import Zcash.Arithmetic.FastMsm
import Zcash.Security.KeyBinding.Instance
import Zcash.Security.KeyBinding.Probability
import Zcash.Security.Ledger.Balance
import Zcash.Security.Ledger.Spendability
import Zcash.Security.Ledger.SpendAuthority
import Zcash.Security.Common.Birthday
import Zcash.Security.BindingSignature.Orchard
import Zcash.Security.BindingSignature.Sapling
import Zcash.Meta.AxiomCheck
import Zcash.Snark.Soundness.CommitFold
import Zcash.Snark.Soundness.Vesta
import Zcash.Snark.Soundness.Deployed.ConcreteBounds
import Zcash.Snark.Soundness.AGM.BindingSignature
import Zcash.Snark.Soundness.AGM.Capstone
import Zcash.Snark.Soundness.AGM.DeployedConstraintSupply
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Zcash.Snark.Soundness.Forking.Adversary
import Zcash.Snark.Soundness.Composition.Bridge
import Zcash.Snark.Soundness.Composition.Decomposition
import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment
import Zcash.Snark.Soundness.Composition.DeployedRootContainment
import Zcash.Snark.Soundness.Composition.PrefixedSqueeze
import Zcash.Snark.Soundness.FoldSplit
import Zcash.Snark.Soundness.GrandProductBridge
import Zcash.Snark.Soundness.LookupAssembly
import Zcash.Snark.Soundness.PermutationRows
import Zcash.Snark.Soundness.ConstraintRelations
import Zcash.Snark.Soundness.ChallengePricing
import Zcash.Snark.Soundness.DegreeWalk
import Zcash.Snark.Soundness.Composition.ScheduleBudget
import Zcash.Snark.Soundness.AGM.PinnedRootWitness
import Zcash.Snark.Soundness.AGM.DirectX4Columns

/-!
# Trust boundary, build-checked

The library-wide census that makes the trust claims build-time checks rather than prose: a change
that widens a declaration's trusted base — a `sorry` reached through some dependency, an unexpected
axiom, or `native_decide` where none was permitted — fails this file rather than passing silently.

Two commands from `Zcash.Meta.AxiomCheck`, per the breaks-as-computed-data discipline (see
`Zcash.Security.RandomOracle`):

* **Computed break reductions** get `assert_computable`: the declaration is a plain `def` — not a
  theorem, not marked `noncomputable` — with axioms bounded by `propext` / `Quot.sound`.
  `+choice` additionally permits `Classical.choice`; with the plain-`def` check this asserts
  choice enters only through erased `Prop` certificate fields, so the break data cannot have been
  conjured from mere propositional existence.
* **Theorems** get `assert_axioms`, an upper bound at the standard tier
  (`propext` / `Classical.choice` / `Quot.sound`). Both commands reject `sorryAx`.
-/

open Zcash.Security.KeyBinding Zcash.Security.RandomOracle Zcash.Security.Birthday
open Zcash.Security.Ledger Zcash.Security.Ledger.Model Zcash.Security.BindingSignature
open Zcash.Meta

/-! ## Key binding — computed break reductions -/

assert_computable Zcash.Security.RandomOracle.CollisionUpToSign.ofOpeningBreak +choice
assert_computable Zcash.Security.RandomOracle.CollisionUpToSign.ofBreak +choice

/-! ## Key binding — theorems -/

assert_axioms Zcash.Security.KeyBinding.Extractor.card_ivk_ge
assert_axioms Zcash.Security.KeyBinding.commit_scalar_pm
assert_axioms Zcash.Security.KeyBinding.rivk_eq_finalOracle
assert_axioms Zcash.Security.KeyBinding.sameIvk_finalOracle_pm
assert_axioms Zcash.Security.KeyBinding.openingBreak_finalOracle_pm
assert_axioms Zcash.Security.KeyBinding.break_finalOracle_pm
assert_axioms Zcash.Security.KeyBinding.residual_of_finalQuery_eq
assert_axioms Zcash.Security.KeyBinding.nk_pinned
assert_axioms Zcash.Security.KeyBinding.ak_pinned
assert_axioms Zcash.Security.KeyBinding.qk_or_sk_pinned
assert_axioms Zcash.Security.KeyBinding.collision_mem_shifted_pm
assert_axioms Zcash.Security.KeyBinding.toInterface

/-! ## Birthday bound -/

assert_axioms Zcash.Security.Birthday.card_shifted_pm_collision_le
assert_axioms Zcash.Security.Birthday.shifted_pm_collision_fraction_le
assert_axioms Zcash.Security.Birthday.birthday_closed_form

/-! ## Key binding — whole-table random-oracle model -/

assert_computable Zcash.Security.KeyBinding.finalQueryEquiv
assert_axioms Zcash.Security.KeyBinding.eval_restrict
assert_axioms Zcash.Security.KeyBinding.pair_shifted_collision_measure_le
assert_axioms Zcash.Security.KeyBinding.finset_shifted_collision_measure_le
assert_axioms Zcash.Security.KeyBinding.ofBreak_queries
assert_axioms Zcash.Security.KeyBinding.break_measure_le
assert_computable Zcash.Security.KeyBinding.badList
assert_axioms Zcash.Security.KeyBinding.mem_badList
assert_axioms Zcash.Security.KeyBinding.badList_measure_le
assert_axioms Zcash.Security.KeyBinding.escapesWithHistory
assert_axioms Zcash.Security.KeyBinding.escapesWithHistory_measure_le
assert_axioms Zcash.Security.KeyBinding.CollidesDuring
assert_axioms Zcash.Security.KeyBinding.CollidesDuring.of_pair
assert_axioms Zcash.Security.KeyBinding.sum_two_mul_add
assert_axioms Zcash.Security.KeyBinding.collidesDuring_measure_le
assert_axioms Zcash.Security.KeyBinding.queries_pair_collision_measure_le
assert_computable Zcash.Security.KeyBinding.derivQueries
assert_axioms Zcash.Security.KeyBinding.break_measure_le_adaptive
assert_axioms Zcash.Security.KeyBinding.break_measure_le_of_queryBound
assert_axioms Zcash.Security.KeyBinding.toOuterMeasure_bind_le
assert_axioms Zcash.Security.KeyBinding.break_measure_le_mixture
assert_axioms Zcash.Security.KeyBinding.uniformOfFintype_prod
assert_computable Zcash.Security.KeyBinding.evalEquiv
assert_axioms Zcash.Security.KeyBinding.uniform_triple_eval
assert_axioms Zcash.Security.KeyBinding.break_measure_le_product
assert_axioms Zcash.Security.toInterface_break_measure_le

/-! ## Ledger-layer break reductions

These data-producing reductions rest on `propext` and `Quot.sound` only — no `Classical.choice`
even in erased positions, which is the strict (flagless) `assert_computable` tier. -/

assert_computable Collision.upToSign
assert_computable Merkle.collisionOfWrongLeaf
assert_computable noteCommitBreakOfNe
assert_computable Zcash.Security.Ledger.nfOldEqOrBreak +choice

/-! ## Statement-layer pinning theorems

The statement layer's exported pinning guarantees: an address `(g_d, pk_d)` determines
`ivk`, and hence `nk` is determined up to an exhibited key-binding break. -/

assert_axioms ivk_pinned
assert_axioms nk_eq_or_break

/-! ## Ledger model

The ledger-model definitions are plain computable data over public ledger contents; the
theorems are deterministic list facts. -/

assert_computable posVal
assert_computable Merkle.subRoot
assert_computable Merkle.authChildren
assert_axioms Merkle.Path.compress_isSome
assert_axioms Merkle.path_of_root
assert_computable leafList
assert_computable leafFun
assert_computable rootAfter
assert_computable nullifiers
assert_computable transparentPoolBalance
assert_computable outputActions
assert_computable outputOpenings
assert_computable positionedOutputs
assert_computable nonZeroSpends
assert_computable poolValueBalance
assert_axioms posVal_lt
assert_axioms rootAfter_prefix
assert_axioms output_rho_eq_nullifiers
assert_axioms output_rho_nodup
assert_axioms leafList_eq_map
assert_axioms outputOpenings_length

/-! ## Balance-subset

The capstone and the per-spend pinning are computable reductions; `findPair` and the
anchor search (`Nat.find`, itself axiom-free) keep the branch decisions decidable.
`+choice` on the three reductions is the erased-positions tier: choice enters only
through Mathlib proof terms in `Prop` positions (e.g. `List.getD_eq_getElem`'s proof),
never the data path. -/

assert_computable findPair
assert_axioms findPair_spec
assert_axioms findPair_none
assert_axioms flatMap_sublist
assert_axioms outputActions_prefix
assert_axioms nullifiers_prefix
assert_axioms take_prefix_take
assert_axioms spendActions_map_nf_sublist
assert_axioms length_leafList
assert_axioms length_positionedOutputs
assert_axioms positionedOutputs_getElem
assert_computable noteCommitBreakOfOutputNe
assert_axioms satisfied_of_spendMem
assert_axioms anchor_of_spendMem
assert_computable spendPinnedOrBreak +choice
assert_computable allPinnedOrBreak +choice
assert_computable balanceSubsetOrBreak +choice

/-! ## Balance-value (conservation form)

`+choice` on the two endpoints is again the erased-positions tier: choice arrives with
the `ring`/`omega` proof terms in their `Prop` fields, never the data path. -/

assert_computable txNetValue
assert_computable issuanceTotal
assert_axioms transparentPoolBalance_eq
assert_axioms positionedOutputs_value_sum
assert_axioms nonZeroSpends_value_sum
assert_axioms poolValueBalance_eq_neg
assert_computable allValueOrBreak
assert_computable valueConservationOrBreak +choice
assert_computable balanceValueOrBreak +choice

/-! ## Spendability

The Faerie-Gold core and the roadblock inversion are computable reductions at the strict
flagless tier; the nullifier split and the persistence theorem are deterministic list
facts. -/

assert_axioms nullifiers_append
assert_computable faerieGoldCore
assert_computable respendOrBreak
assert_axioms validLedger_append

/-! ## Spend Authority

The per-action core and the valid-ledger capstone are computable reductions; the
receivability pinning is a deterministic module-algebra theorem. `+choice` on the two
reductions is the erased-positions tier: choice arrives with `smul_eq_zero`'s Mathlib
proof inside the receivability pinning, consumed only in `Prop` positions — never the
data path. -/

assert_axioms ivk_eq_of_receivable
assert_computable spendAuthForgeryOrBreak +choice
assert_computable spendAuthorityOrBreak +choice

/-! ## Binding-signature relation reductions

Unlike the ledger break reductions, these depend on `Classical.choice` (`+choice`). It enters
only through erased `Prop` certificate fields (the arithmetic side proofs); the relation
coefficients themselves are direct terms of the inputs, and the plain-`def` check means the data
cannot have been conjured from mere propositional existence. -/

assert_computable NontrivialRelation.ofImbalance +choice
assert_computable NontrivialRelation.ofBundleModImbalance +choice
assert_computable NontrivialRelation.ofBundleIntImbalance +choice
assert_computable NontrivialRelation.ofOrchardImbalance +choice
assert_computable NontrivialRelation.ofSaplingImbalance +choice

/-!
## SNARK soundness stack

The census also carries the SNARK binding and knowledge-soundness reductions, consolidated here
from the former per-directory files and, like the key-binding and ledger sections above, expressed
through the `Zcash.Meta.AxiomCheck` macros rather than the older `assert_no_sorry` +
`#guard_msgs`-pinned `#print axioms` idiom:

* **Computed break reductions** — the data-producing `def`s that extract a discrete-log relation
  from a collision, fold, peel, or fork — get `assert_computable`: a plain `def`, not marked
  `noncomputable`. `Classical.choice` enters only through erased `Prop` certificate fields
  (`+choice`); the relation coefficients are direct terms of the inputs, so the break data cannot
  have been conjured from mere propositional existence. Vesta-instantiated producers additionally
  inherit CompElliptic's `native_decide` curve point-count axiom (`+native`).
* **Theorems** — the probability-layer bounds, the knowledge-soundness and binding endpoints across
  all adversary models, the DL capstones, and the run-time/query-charge lemmas — get
  `assert_axioms`, bounding the trusted base at the standard tier (`propext` / `Classical.choice` /
  `Quot.sound`), with `+native` on the Vesta-instantiated endpoints.
-/

open Zcash.Snark

/-! ### Binding reductions from IPA/CommitFold collisions -/

assert_computable NontrivialDLRelation.ofCollision +choice
assert_computable NontrivialDLRelation.ofIpaOpenings +choice

/-! ### Verifier-soundness capstones -/

assert_axioms deployedAccepts_verifierEq
assert_axioms orchard_verifier_deployed_opening_of_forked
assert_axioms orchard_verifier_deployed_constraint_of_forked
assert_axioms orchard_verifier_vesta_constraint_of_forked +native

/-! ### Deployed binding-reduction breaks

The binding reductions return computed data (plain `def`s); the same treatment covers the forking
reductions `ipa_extractV`, `ipaRelation_extract`, `produceDeployed`, `deployed_forking_tree`, and
`deployed_forking_relation`, each computing its witness from an explicit certificate. -/

assert_computable NontrivialRelation.ofCombinationCollision +choice
assert_computable NontrivialRelation.ofFoldedGens +choice
assert_computable NontrivialRelation.ofLeafPeel +choice
assert_computable NontrivialRelation.ofDeployedTree +choice
assert_computable NontrivialRelation.ofUnopenedFork +choice
assert_computable NontrivialRelation.ofUnopenedForkVesta +choice +native
assert_computable ipa_extractV +choice
assert_computable ipaRelation_extract +choice
assert_computable produceDeployed +choice
assert_computable deployed_forking_tree +choice
assert_computable deployed_forking_relation +choice

/-! ### AGM / Fiat–Shamir soundness

The AGM kernels compute representations, openings, relations, certificates, and deployed instances
as data (`assert_computable`); the probability layer, the knowledge-soundness and binding endpoints,
and the run-time bounds are theorems (`assert_axioms`). -/

assert_computable discreteLogOfBasis_of_relation +choice
assert_computable discreteLogOfChallenge_of_relation +choice
assert_computable programmedExtractOrMiss +choice
assert_computable AugmentedRelationWitness.toAlgebraicRelationWitness +choice
assert_computable relationWitnessOfCollision +choice
assert_computable discreteLogOfAugmentedRelationAtChallenge +choice
assert_computable separateOrRelationWitness +choice
assert_computable algebraicPowerBatchWithSourceOrRelation +choice
assert_computable finForallOrRelationWitness +choice
assert_computable constructIntermediateSets_comm_route +choice
assert_computable deployed_slot_route_of_checks +choice
assert_computable deployedRouteSelectorOfSpecs +choice
assert_computable deployedX4InterpolationDataOfCapacity +choice +native
assert_computable deployedConstraintQuotientAgreementOrRelation +choice +native
assert_computable deployedConstraintQuotientFinder +choice +native
assert_computable decodedQuotientEqReassembledOrRelationWitness +choice
assert_computable DeployedAlgebraicDecode.quotientEvalEqCommittedPreXOrRelationWitness +choice
assert_computable ComputedDeployedRootFSFamily.deployedRelationFinder +choice +native
assert_computable deployedConstraintFinderOfOutcome +choice +native
assert_computable deployedConstraintRelationFinder +choice +native
assert_computable relationOfFoldGensWitness +choice
assert_computable deployedLeafPeelWitness +choice
assert_computable deployedToAcceptVWitness +choice
assert_computable algebraicRelationOfDeployedAccept +choice
assert_axioms AlgebraicProver.toProver
assert_axioms AlgebraicDForkCert.toDForkCert
assert_axioms algebraicProverAccept_forkValid
assert_computable deployedAlgebraicForkingRelation +choice
assert_axioms deployed_forking_relation_shifted
assert_axioms deployedAlgebraicForkingRelation_shifted
assert_computable deployedAlgebraicForkingProgrammed +choice
assert_axioms DeployedAlgebraicForkingInstance.run
assert_axioms DeployedAlgebraicForkingInstance.ProducesRelation
assert_axioms deployedAlgebraicRelationProduced
assert_axioms deployedAlgebraicRelationEvent
assert_computable deployedAlgebraicRelationFinder +choice
assert_axioms deployedAlgebraicRelationFinder_isSome_iff
assert_computable deployedAlgebraicRelation +choice
assert_computable deployedAlgebraicRelationWitness +choice
assert_axioms orchardDeployedAlgebraicForkingProgrammed +native
assert_axioms orchardDeployedRelationSet +native
assert_axioms OrchardUniformURSIdentification +native
assert_axioms orchardGeneratorROSetup
assert_axioms orchardGeneratorROBasis
assert_axioms orchard_uniformURSIdentification_of_generatorRO +native
assert_axioms recursiveAlgebraicForkFrom
assert_axioms recursiveAlgebraicForkFrom_realizes
assert_axioms algebraicForkCertAttempt +native
assert_axioms algebraicForkCertAttempt_valid +native
assert_axioms computedDeployedAlgebraicInstance +native
assert_axioms computedAlgebraicInstanceFailure_measure_le +native
assert_axioms AlgebraicRelationWitness.augment
assert_axioms DeployedAlgebraicForkingInstance.runRelation
assert_axioms DeployedAlgebraicForkingInstance.runRelation_isSome_of_mismatch
assert_computable DeployedAlgebraicForkingInstance.runToSnark +choice +native
assert_axioms ComputedAlgebraicFSFamily.relationFinder +native
assert_axioms ComputedAlgebraicFSFamily.relationFinder_isSome_of_bindingWin +native
assert_axioms ComputedAlgebraicFSFamily.snarkRelationFinder +native
assert_axioms ComputedAlgebraicFSFamily.snarkRelation_prob_le_of_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.acceptExtractionFailure_measure_le +native
assert_axioms ComputedAlgebraicFSFamily.snarkNonRelationFailure +native
assert_axioms ComputedAlgebraicFSFamily.snarkNonRelationFailure_measure_le +native
assert_axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_textbookDL_full +native
assert_axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_uniformURS_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.snarkFailure_prob_le_of_generatorRO_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.binding_prob_le_of_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.binding_prob_le_of_uniformURS_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.binding_prob_le_of_generatorRO_textbookDL +native
assert_axioms ComputedAlgebraicFSFamily.ReductionEfficient +native
assert_axioms ComputedAlgebraicFSFamily.reductionEfficient_exists +native
assert_axioms ComputedAlgebraicFSFamily.instanceAttempt_runs_eq +native
assert_axioms ComputedAlgebraicFSFamily.reductionEfficient_exponential +native
assert_axioms ComputedAlgebraicFSFamily.DiscreteLogRelationHardFor +native
assert_axioms ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL +native
assert_axioms ComputedAlgebraicFSFamily.binding_under_DL +native
assert_axioms bindingWin_unbounded_measure_le +native
assert_axioms queryCharge
assert_axioms queryCharge_sum_mul_le
assert_axioms le_queryCharge_of_mem_queries
assert_axioms mem_queries_dedup
assert_axioms applyUpdates_apply_mem_nodup
assert_axioms queryCharge_sum_mul_le_table_budget
assert_axioms steeredCharge_context_sum_mul_le
assert_axioms steeredCharge_context_sum_mul_le_table_budget
assert_axioms steeredCharge_sum_mul_le
assert_axioms scanCandidate_self
assert_axioms self_mem_goodChallenges_iff
assert_axioms scanRank_insert_erase
assert_axioms scanRank_insert_eq_filter
assert_axioms goodChallengesAt
assert_axioms OracleComp.queries_queryList
assert_axioms recursiveAlgebraicForkFrom_node_runs_le_gated
assert_axioms OracleComp.queries_bind
assert_axioms OracleComp.mem_queries_completing
assert_axioms scanCandidateAt
assert_axioms scanCandidateAt_fork
assert_axioms scanCandidateAt_update
assert_axioms goodChallengesAt_fork
assert_axioms goodChallengesAt_update
assert_axioms sum_card_scanRank_erase_lt_le
assert_axioms OracleComp.restrictSum
assert_axioms fsWinsFull_restrictSum_le
assert_axioms ComputedAlgebraicFSFamilyRand.determinize
assert_axioms ComputedAlgebraicFSFamilyRand.binding_prob_le_of_textbookDL_rand +native
assert_axioms ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_textbookDL_rand +native
assert_axioms ComputedAlgebraicFSFamily.snarkFailureEvent +native
assert_axioms ComputedAlgebraicFSFamilyRand.foldedRelationFinder +native
assert_axioms ComputedAlgebraicFSFamilyRand.binding_prob_le_of_foldedTextbookDL_rand +native
assert_axioms ComputedAlgebraicFSFamilyRand.foldedSnarkRelationFinder +native
assert_axioms ComputedAlgebraicFSFamilyRand.snarkFailure_prob_le_of_foldedTextbookDL_rand +native
assert_computable ComputedAlgebraicFSFamilyUnbounded.globalReachSet +choice
assert_axioms ComputedAlgebraicFSFamilyUnbounded.reachSet_subset_globalReachSet
assert_computable ComputedAlgebraicFSFamilyUnbounded.splitFamilyRand +choice
assert_axioms ComputedAlgebraicFSFamilyUnbounded.run_splitFamilyRand_adversary
assert_axioms ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_foldedTextbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_foldedTextbookDL +native
assert_axioms uniformURS_basis_transfer +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.snarkFailureEventUnbounded +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_uniformURS_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.snarkFailure_prob_le_of_unbounded_generatorRO_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.bindingEventUnbounded +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_uniformURS_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnbounded.binding_prob_le_of_unbounded_generatorRO_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.determinize
assert_computable ComputedAlgebraicFSFamilyUnboundedRand.globalReachSet +choice
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.reachSet_subset_globalReachSet
assert_computable ComputedAlgebraicFSFamilyUnboundedRand.splitFamilyRand +choice
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.run_splitFamilyRand_adversary
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_foldedTextbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_foldedTextbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.snarkFailureEventUnboundedRand +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_uniformURS_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.snarkFailure_prob_le_of_unboundedRand_generatorRO_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.bindingEventUnboundedRand +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_uniformURS_textbookDL +native
assert_axioms ComputedAlgebraicFSFamilyUnboundedRand.binding_prob_le_of_unboundedRand_generatorRO_textbookDL +native
assert_axioms recursiveAlgebraicForkFrom_node_runs_le
assert_axioms recursiveAlgebraicFork_sum_runs_le_unconditional
assert_axioms recursiveAlgebraicFork_oracle_tape_sum_runs_le_unconditional
assert_axioms recursiveAlgebraicForkFrom_sum_runs_le_of_forkSpread
assert_axioms recursiveAlgebraicFork_sum_runs_le_of_forkSpread
assert_axioms AlgebraicPoint.point_eq_components +native
assert_axioms Msm.eval_repr +native
assert_axioms RepresentedMultiopen.ofCoveredList +native
assert_axioms AlgebraicWfProof.ofRepresented +native
assert_axioms assembleQueries_points_mem
assert_axioms constructIntermediateSets_ref_mem
assert_axioms multiopenMsm_points_mem
assert_axioms AlgebraicWfProof.ofStandard +native
assert_axioms OracleComp.reachSet
assert_axioms OracleComp.run_congr_reachSet
assert_axioms OracleComp.restrictTo
assert_axioms OracleComp.splitDomain
assert_axioms finite_domain_restriction
assert_axioms fsWinsFull_mapDomain_measure_eq
assert_axioms fsWinsFull_splitDomain
assert_axioms fsWinsFull_unbounded_measure_le
assert_axioms truncateTranscript
assert_computable Zcash.Security.BindingSignature.NontrivialRelation.toAlgebraicRelationWitness +choice
assert_computable Zcash.Security.BindingSignature.NontrivialRelation.toDiscreteLog +choice
assert_axioms Zcash.Security.BindingSignature.orchardImbalanceToDiscreteLog
assert_axioms Zcash.Security.BindingSignature.saplingImbalanceToDiscreteLog
assert_axioms programmedRelSet_card
assert_axioms programmedRelSet_subset_win_union_miss
assert_axioms missSet_card_le
assert_axioms relation_prob_le_of_textbookDL
assert_axioms programmedRelSetWithCoins_card
assert_axioms programmedRelSetWithCoins_subset_win_union_miss
assert_axioms missSetWithCoins_card_le
assert_axioms relationWithCoins_prob_le_of_textbookDL
assert_axioms orchard_relation_prob_le_of_textbookDL +native
assert_axioms commitment_binding_prob_le_of_textbookDL +native
assert_axioms orchard_deployed_relation_prob_le_of_textbookDL +native
assert_axioms orchard_deployed_relation_set_eq_relSet +native
assert_axioms orchard_deployed_relation_event_prob_le_of_textbookDL +native
assert_axioms orchard_deployed_relation_prob_eq_of_uniformURS +native
assert_axioms orchard_deployed_relation_prob_le_of_uniformURS_textbookDL +native
assert_axioms orchard_deployed_relation_prob_le_of_generatorRO_textbookDL +native

/-! ### Fork-tree knowledge error

The closed form of the fork-tree knowledge error and its evaluation over the deployed Orchard
parameters. All theorems, so `assert_axioms`: the arithmetic runs on `Nat`/`ℝ≥0∞` and the deployed
field cardinality comes from `ZMod.card`, so no compiler trust enters here. -/

assert_axioms kerr_mul_card
assert_axioms kerr_eq
assert_axioms kerr_div_card
assert_axioms deployed_forking_knowledge_error
assert_axioms deployed_forking_knowledge_error_captured

/-! ### Multiopen decode and forking composition

The decode layer's surviving surface: the Vandermonde column recovery, the `x₄` flat-power-batch
collapse, and the forking-extraction composition. The rewind-based compatibility layer that once
sat here — the propositional binding disjunct and the accept-event ladders it fed — has been
removed, so every break the deployed route charges to DLOG is computed relation data, censused
below through explicit `PSum` outcomes and computable finders. Theorems throughout, so
`assert_axioms`, with `+native` on the Vesta-instantiated endpoints. -/

-- The forking-extraction ∘ decoded-capstone composition (`Soundness.Composition.Bridge`): the algebraic
-- clean opening identified with the deployed capstone's shape (`ipaRelation_deployed_of_instance`).
-- On the witness tie the opened-value shift is derived
-- (`shift_eq_zero_of_openings_agree`), so `hshift` survives only on the standalone single-opening
-- bridge. `snarkExtraction_prob_le_of_generatorRO_textbookDL` is the CONDITIONAL knowledge-error
-- bound: the SNARK-extraction failure is contained in the clean-opening failure and inherits its
-- `(Q+k)·3/|Fp| + (Q+1)/|Fp| + ε + 1/|Fp|` bound, conditional on `hExtract` (clean opening ⟹
-- extraction). Discharging `hExtract` — coupling the AGM family's coin measure to the multiopen
-- budget below — is the remaining reconciliation. This stack is not consumed by the rewind-free
-- constraint capstone below.
assert_axioms ipaRelation_deployed_of_instance +native
assert_axioms snarkExtraction_prob_le_of_generatorRO_textbookDL +native
assert_axioms instanceAttempt_provenance +native
assert_axioms ipaRelation_deployed_of_openings_agree +native
assert_axioms shift_eq_zero_of_openings_agree +native

-- The decode layer (`Soundness.Multiopen.Decode`/`Deployed`): the Vandermonde recovery of the
-- column witnesses, the deployed x4 collapse proved to be a flat power batch, and the two-level
-- binding of the extracted witness to the member commitments.
assert_axioms decodedColumnFamily_of_batch_openings
assert_axioms deployedCommitment_x4_batch
assert_axioms multiopenValue_x4_batch
assert_axioms member_binding_of_x1_samples
assert_axioms node_binding_of_samples
-- The multiopen support modules, pinned directly rather than transitively through the capstones
-- above. `Opened` holds the rewind accept events and the three `Classical.choose` witness
-- extractors; `RPoly` the interpolation/power-form algebra; `Compat` the Msm-evaluation and
-- two-openings binding lemmas; `Claimed` the counting cores; `ValueCheckDeployed` the deployed
-- point sets. A stray axiom here would surface at a capstone, but only these pins name the
-- declaration that introduced it.
assert_axioms vandermonde_decode_map
assert_axioms vandermonde_reconstruct_map
assert_axioms openedColumnDecode
assert_axioms openedDecodedCols
assert_axioms openedDecodedCols_eval_x3
assert_axioms openedDecodedCols_top_eval_x3
assert_axioms openedX4Batch_of_witnessFamily
assert_axioms OpenedX4Accept
assert_axioms OpenedX3Accept
assert_axioms OpenedX2Accept
assert_axioms openedX4Rewind_of_x4Prob
assert_axioms openedX4Rewind_of_x4Prob_forked
assert_axioms opened_constraint_of_relation_and_batch
assert_axioms x1DecodeComp
assert_axioms opened_witness_member_binding
assert_axioms OpenedX1Accept
assert_axioms openedMemberDecode_of_x1Prob
assert_axioms rotatedFeed
assert_axioms member_constraint_of_relation_and_batch
assert_axioms poly_eq_of_agree_on_family
assert_axioms foldl_range_add_eq_sum
assert_axioms foldl_range_guardProd_eq_prod
assert_axioms guardProd_eq_prod_erase
assert_axioms lagrangePoly
assert_axioms lagrangePoly_eval_node
assert_axioms lagrangePoly_eval
assert_axioms foldl_mul_inv_eq_prod
assert_axioms multiopenEval_powerForm
assert_axioms coeffs_zero_of_power_sum_vanishes
assert_axioms multiopenEval_perSet_zero_of_samples
assert_axioms lagrangePoly_natDegree_lt
assert_axioms col_eq_lagrangePoly_of_samples
assert_axioms col_eval_node_eq_claimed
assert_axioms Msm.eval_zero
assert_axioms Msm.eval_scale
assert_axioms Msm.eval_add
assert_axioms claimedEval_of_x3Prob
assert_axioms gateGood_of_xProb
assert_axioms deployedSetPts
assert_axioms deployedAllPts
assert_axioms deployedSetPts_subset
assert_axioms deployed_query_point_mem
-- The avoidance-strengthened forking count (`Soundness.Forking.Probability`): the counting lemma
-- that buys the multiopen grid's interpolation samples off the opened set points, so the value
-- check takes no sample-avoidance hypothesis.
assert_axioms exists_injective_accepting_avoiding_of_measure
-- The good-challenge production (`Soundness.GoodChallenge`): the Schwartz-Zippel exclusion budget
-- and the pigeonhole that produces an accepting challenge outside the bad set.
assert_axioms uniformChallenge_szBadSet
assert_axioms uniformChallenge_szGoodSet
assert_axioms uniformChallenge_quotient_szBadSet
assert_axioms uniformChallenge_szBadSet_union
assert_axioms exists_accepting_good_challenge
assert_axioms exists_accepting_good_challenge_quotient
-- The deployed Vesta capstone family: the decoded-column rungs and the terminal, alongside the
-- derived capstone already pinned below.
assert_axioms orchard_verifier_vesta_member_constraint_deployed_x4 +native

-- Deterministic verifier routing used by the rewind-free deployed constraint decoder.
assert_axioms vanishing_query_mem_assembleQueries
assert_axioms assembleQueries_vanishingH_unique
assert_axioms constructIntermediateSets_unique_comm_routed
assert_axioms vanishing_slot_routed
assert_axioms hfold_of_expectedHEval_binding
assert_axioms hfold_of_vanishing_slot_binding
assert_axioms deployedAccepts_xn_ne_one
assert_axioms deployedAccepts_pipeline
assert_axioms deployed_member_commitment_eq_assembled
assert_axioms lagrangeBasisPoly_eval
assert_axioms lagrange_bind_derived
-- The permutation and lookup arguments folded into the constraint model: the verifier's expression
-- list is the generic builder run on its own claimed evaluations, the same builder over column
-- polynomials evaluates back onto it, and the fold equation therefore needs no fingerprint premise.
assert_axioms permutationExpressions_map
assert_axioms lookupExpressions_map
assert_axioms subProofConstraints_map
assert_axioms allConstraints_map
assert_axioms subProofExpressions_eq
assert_axioms allExpressions_eq
assert_axioms eval_constraintPolys
assert_axioms eval_combineConstraints
assert_axioms eval_combineConstraints_deployed
assert_axioms hfold_of_constraint_polys_of_xn_ne_direct
assert_axioms constraints_supply_of_deployedAlgebraicDecode
-- The permutation and lookup arguments closed from the verifier's own row checks: the combined
-- check splits into its parts, the running product telescopes across the rows, two challenge root
-- counts turn the product into a multiset identity, and the existing structural theorems turn that
-- into the copy constraints and the lookup inclusion.
assert_axioms constraints_dvd_of_good_y
assert_axioms telescope_running_product
assert_axioms grandProduct_eq_or_cell_eq_zero
assert_axioms multiset_pair_eq_of_prod_eval_eq
assert_axioms cellPairs_eq_of_running_product
assert_axioms perm_copy_constraints_of_running_product
assert_axioms lookup_multisets_of_prod_eval_eq
assert_axioms lookup_multisets_of_diff_eq_zero
assert_axioms lookup_subset_of_components
assert_axioms lookup_subset_of_prod_eval_eq
-- The deployed row reading: the step rule's folds are running products, the boundary rules pin the
-- product at the first and last rows, and the cell names separate. These are theorems about
-- `permChunkExpression` itself, so the chain above starts at the verifier's own constraint list.
assert_axioms permChunk_left_eq_prod
assert_axioms permChunk_right_eq_prod
assert_axioms permChunkExpression_eq
assert_axioms eval_eq_zero_of_dvd_vanishing
assert_axioms perm_row_recurrence
assert_axioms running_product_start
assert_axioms running_product_end
assert_axioms name_injective_of_coset
assert_axioms deployed_perm_copy_constraints
-- Locating a single rule inside the verifier's flat constraint list, fixing the permutation sets to
-- committed running products, and chaining the two: the copy constraints now follow from the
-- polynomial constraint identity itself, with no hypothesis about the shape of the checks.
assert_axioms permChunkExpression_mem_permutationExpressions
assert_axioms start_mem_permutationExpressions
assert_axioms end_mem_permutationExpressions
assert_axioms mem_subProofConstraints_of_mem_permutationExpressions
assert_axioms mem_allConstraints_of_mem_subProofConstraints
assert_axioms mem_constraintPolys_of_mem_permutationExpressions
assert_axioms head?_deployedPermSets
assert_axioms getLast?_deployedPermSets
assert_axioms deployed_copy_constraints_of_identity
-- The same for the lookup argument: its five rules located in the list, read row by row, and
-- chained to the inclusion.
assert_axioms lookupExpressions_eq
assert_axioms mem_subProofConstraints_of_mem_lookupExpressions
assert_axioms mem_constraintPolys_of_mem_lookupExpressions
assert_axioms running_product_end_flipped
assert_axioms lookup_row_recurrence
assert_axioms lookup_row_zero
assert_axioms lookup_row_step
assert_axioms lookup_rules_dvd_of_identity
assert_axioms deployed_lookup_subset_of_identity
assert_axioms deployed_lookup_relation_of_identity
-- Decompression: the θ-compressed membership becomes membership of whole rows, since the
-- compression is the fold polynomial of the row's values and a good θ separates distinct tuples.
assert_axioms foldPoly_sub
assert_axioms tuple_eq_of_foldPoly_eval_eq
assert_axioms compress_eval_eq_foldPoly
assert_axioms deployed_lookup_tuple_of_identity
-- Every new challenge surface priced the way `hgood` is: a uniform-challenge measure bound per
-- root-set event — the fold split's `y`, the bridge's `β` and `γ`, the vanishing-factor escapes,
-- and the decompression's pairwise `θ`. Sequential conditioning across the squeezes is the same
-- coupling hook `hgood` carries, documented with the `hfold`/`hgood` surfaces.
assert_axioms uniformChallenge_szBadSet_iUnion_le
assert_axioms goodY_failure_measure_le
assert_axioms perm_gamma_failure_measure_le
assert_axioms perm_beta_failure_measure_le
assert_axioms escape_measure_le
assert_axioms theta_failure_measure_le
-- The last links: the point check lifted to the polynomial identity, the permutation taken to be the
-- one keygen builds from the circuit's copy constraints, the cells of every chunk covered at once,
-- and circuit satisfaction defined by the whole constraint list rather than the gates alone.
assert_axioms constraint_identity_of_hfold
assert_axioms declared_equalities_of_running_product
assert_axioms deployed_declared_equalities_of_identity
assert_axioms prod_map_chunkCellPairs
assert_axioms perm_copy_constraints_of_chunk_products
assert_axioms chunkName_injective_of_coset
assert_axioms deployed_declared_equalities_of_identity_chunks
assert_axioms circuitSatViaConstraints_of_check
-- Closing the loop: the capstone hands over an opening paired with satisfaction of the whole
-- constraint list, and the two arguments' relations are read back out of that same predicate.
assert_axioms snarkRelation_constraints
assert_axioms declared_equalities_of_circuitSat
assert_axioms lookup_relation_of_circuitSat
assert_axioms lookup_tuple_of_circuitSat
-- Several permutation chunks, not one: the chaining rule located in the list, read at row zero, and
-- the chunks flattened into a single running product so the permutation acts on every cell.
assert_axioms chain_mem_permutationExpressions
assert_axioms running_product_chain
assert_axioms deployed_copy_constraints_of_identity_chunks
assert_axioms hgood_of_good_challenge
-- The UNCONDITIONAL decomposition: `hExtract` removed, the residual quantified as the
-- clean-but-not-extracted measure term (bounded by the multiopen budget under the coupling
-- documented in `Composition.Decomposition`, not assumed here).
assert_axioms ComputedAlgebraicFSFamily.snarkExtractionFailureEvent_subset_union +native
assert_axioms snarkExtraction_prob_le_of_generatorRO_textbookDL_decomposed +native
-- Product-measure lifting, now used by the direct pinned-root composition.
assert_axioms independentProductPMF_fiber_bound
-- Acceptance through `assemble?`, isolated from the historical completeness ladder.
assert_axioms fullAlgebraicAcceptDeployed +native
assert_axioms fullAlgebraicAccept_of_deployed +native
assert_axioms snarkExtractionFailureEventDeployed +native
assert_axioms snarkExtractionFailureEventDeployed_subset_union +native

-- Rewind-free AGM unbatching and its direct additive root pricing.
assert_axioms algebraicBatchErrorPolynomial_eval
assert_axioms algebraicBatchErrorPolynomial_natDegree_le
assert_axioms algebraicBatch_values_of_errorPolynomial_eq_zero
assert_axioms algebraicBatch_badSet_measure_le
assert_axioms deployedX4AlgebraicValues_of_good
assert_axioms deployedClearedQuotientIdentity_of_good_x3
assert_axioms deployedAggregateNodeBinding_of_good_x2
assert_axioms deployedMemberNodeBinding_of_good_x1
assert_axioms deployedMemberNodeBinding_of_good_challenges
assert_axioms xEscTable_measure_le
assert_axioms xEscAtPoint_measure_le
assert_axioms PinnedRootEvent.landing_measure_le
assert_axioms PinnedRootFamily.landing_measure_le
assert_axioms deployedRootBad_measure_le +native
assert_axioms DeployedRootSqueezeInvariance +native
assert_axioms tableReadingPinnedRootEvent
assert_axioms tableReadingPinnedRootEvent_landing_measure_le
assert_axioms deployedRootEventBudget_sum_le
assert_axioms badX_le_via_squeeze_prefixed +native
-- The stability input derived from Fiat–Shamir prefix-determinism: the `x` squeeze point reads
-- only answers at strictly shorter transcripts, so resampling at the point itself moves nothing.
assert_axioms hstab_of_xPrefixDetermined +native
-- Prefix injectivity at the multiopen squeeze points (`Forking.Adversary.PreIpa`): each point
-- pins every field absorbed before it — the toolkit for the deployed squeeze-invariance
-- schedules, which need each root-set datum emitted strictly before its own squeeze.
assert_axioms preXSqueezePoint_inj
assert_axioms preX1SqueezePoint_inj
assert_axioms preX2SqueezePoint_inj
assert_axioms preX3SqueezePoint_inj
assert_axioms preX4SqueezePoint_inj
-- The degree walk (`Soundness.DegreeWalk`): every constraint family's polynomial stays under an
-- explicit cap — gates by `Expr.degreeBound`, permutation chunks by width, lookups by their
-- compressed expressions — the combined bound the `x`-squeeze schedule's `epsilonX` prices.
assert_axioms natDegree_combineConstraints_le
-- The schedule, priced (`Composition.ScheduleBudget`): the committed carriers stay under the
-- walk's caps, root witnesses at one table share the family's own outcome so the root set
-- collapses across fork tapes, and the schedule constructor discharges `measure_le` outright —
-- `pinned` stays the named causal premise.
assert_axioms natDegree_committedPreXConstraintDifference_le
assert_axioms natDegree_deployedConstraintDifferenceOfRoot_le +native
assert_axioms deployedConstraintDifference_witness_congr +native
assert_axioms deployedConstraintXBadSet_measure_le +native
assert_axioms deployedConstraintXSqueezeSchedule_of_pinned +native
-- The pinned-root witness family (`AGM.PinnedRootWitness`): the zero data over the degenerate
-- shape, whose assembled multiopen commitment is the zero point for every basis and record —
-- the evaluations the satisfiability pin of `DeployedRootSqueezeInvariance` consumes.
assert_axioms multiopenCommitment_witness_zero +native
assert_axioms witnessProof +native
assert_axioms witnessFamily +native
-- The premise itself, discharged: the constant family's root sets are empty except at `x₃`,
-- where the set is the deployed point set — and the assembly never reads `x₃`, so reprogramming
-- an event's own squeeze answer moves nothing. `DeployedRootSqueezeInvariance` is satisfiable.
assert_axioms witnessFamily_reads_update +native
assert_axioms deployedRootBad_witness +native
assert_axioms deployedAllPts_x3_blind
assert_axioms deployedRootSqueezeInvariance_witness +native
-- The direct route (`AGM.DirectX4Columns`): the `x₄` columns are read off the online coverage —
-- a column below the pair count is its set's `x₁` power sum, the last is the prover's `q′` — so
-- the batch-or-relation decision needs no offline interpolation and no field-capacity premise.
assert_axioms x4BatchCommitments_eq_memberPowerSum
assert_axioms deployedX4ColumnRepresentationsOfCovered +native
assert_axioms aggregate_opens_deployedCommitment +native
assert_axioms deployedX4BatchOfCoveredOrRelation +native
assert_axioms deployedRootOutcomeOfCovered +native
assert_axioms ComputedDeployedRootFSFamily.ofCovered +native
assert_axioms snarkExtractionDeployed_prob_le_via_wrapped_pinned_roots +native
assert_axioms ComputedDeployedRootFSFamily.deployedRelation_prob_le_of_generatorRO_textbookDL +native
assert_axioms deployedRootFailure_subset_landing +native
assert_axioms deployedDecodeFailure_subset_union +native
assert_axioms deployedNonRelationFailure_prob_le_of_generatorRO +native
assert_axioms snarkExtractionDeployed_prob_le_via_deployed_roots +native

-- Online-source constraint composition.  All disagreement branches retain concrete relation
-- coefficients and are charged through the same single-instance textbook-DLOG finder.
assert_axioms deployedConstraint_memberPoly_eq_online +native
assert_axioms deployedOnlineConstraintOutcomeOfDecode +native
assert_axioms deployedConstraintFailure_subset_union +native
assert_axioms deployedConstraintRelation_prob_le_of_generatorRO_textbookDL +native
assert_axioms snarkConstraintsDeployed_prob_le_via_deployed_roots +native
assert_axioms snarkConstraintsDeployed_prob_le_of_online_outcome +native
assert_axioms deployedConstraintUpgradeContained_of_root +native
assert_axioms deployedConstraintOutcomeOfRoot_relation_eq_online +native
assert_axioms deployedConstraintBadX_subset_landing +native
assert_axioms deployedConstraintBadX_prob_le +native
assert_axioms snarkConstraintsDeployed_prob_le_of_root_schedule +native

/-! ## The Action circuit — the halo2-native soundness trust surface

The circuit-layer soundness theorems live at the `native_decide` tier: they consume
`native_decide` certificates only — the six fixed-base window tables, small `interval_cases`
facts, and CompElliptic's Pallas point-count witness (`pallas_natCard`). These assertions pin
exactly that budget for the generic soundness theorems and for the fully-instantiated deployed
bundle — a `sorry` or any further axiom reached anywhere in the Action stack fails the build
here. -/

assert_axioms Zcash.Circuits.Action.Circuit.soundness +native
assert_axioms Zcash.Circuits.Action.Circuit.soundnessPost +native
assert_axioms Zcash.Circuits.Action.orchardActionCircuit +native

/-! ## The circuit → ledger bridge — exported refinement theorems

The end-to-end refinement from a satisfying Action assignment to the games-facing ledger
statement (`ActionBreak … ∨ ∃ inst w, …`), together with the two correctness directions of the
break classifier `classifyAction`: an escape it returns is a break of the witness's own hash
query, and a `none` return — no escape at any of the four sites — means every Sinsemilla query
of the witness is defined. `actionBreak_iff_classify_isSome` packages both directions as the
consumer-boundary equivalence. Same budget as the circuit layer above: standard tier plus
`native_decide` certificates (including the Pallas point-count witness). -/

assert_axioms Zcash.Security.Ledger.Bridge.specPost_to_ledger +native
assert_axioms Zcash.Security.Ledger.Bridge.circuit_soundness_to_ledger +native
assert_axioms Zcash.Security.Ledger.Bridge.actionBreak_of_classify +native
assert_axioms Zcash.Security.Ledger.Bridge.classify_none_defined +native
assert_axioms Zcash.Security.Ledger.Bridge.actionBreak_iff_classify_isSome +native

/-! ## The Sinsemilla discrete-log-relation reduction

The onward step from a classified Action escape to the games-facing relation object, which
the census above stops short of: the escaped chain is turned into an explicit generator
combination (`ofPoint_hashToPoint`), the coefficient vector is computed from the break data
(`breakCoeffs`, with its relation and nontriviality facts), and the two headline reductions
package that as a `NontrivialRelationOne` at the escaped site's domain point.

`relationOfBreakData` and `classifyRelation` are asserted computable, per the
breaks-as-computed-data convention. `+native` covers the deployed bases' on-curve certificates
carried in their erased `Prop` fields; `+choice` is the same erased-positions tier the classifier
itself sits at.

`ofPoint_hashToPoint` and `breakCoeffs_nontrivial` stay at the standard tier: the chain
combination reasons in `ℕ`-multiples of the lifted table, and nontriviality only in the scalar
field. `breakCoeffs_relation` needs `+native` because it scales group elements by field
elements, and the `Module Fq PallasGroup` instance is built from the Pallas point count. That
is the same witness the circuit layer above carries, reaching this file through the group's
scalar action rather than a certificate check. -/

assert_computable Zcash.Security.Ledger.Bridge.breakCoeffs +choice
assert_computable Zcash.Security.Ledger.Bridge.relationOfBreakData +choice +native
assert_computable Zcash.Security.Ledger.Bridge.classifyRelation +choice +native
assert_axioms Zcash.Security.Ledger.Bridge.ofPoint_hashToPoint
assert_axioms Zcash.Security.Ledger.Bridge.breakCoeffs_relation +native
assert_axioms Zcash.Security.Ledger.Bridge.breakCoeffs_nontrivial
assert_axioms Zcash.Security.Ledger.Bridge.classify_query_inr +native
assert_axioms Zcash.Security.Ledger.Bridge.classifyRelation_isSome_iff +native
assert_axioms Zcash.Security.Ledger.Bridge.classifyRelation_site +native

/-! ## `@[csimp]` replacement lemmas

Every `@[csimp]` lemma gets an axiom check here. The compiler applies the
substitution in all downstream compiled code, but the axioms of the lemma's own
proof are not propagated into downstream `native_decide` axiom tracking (
[lean4#7463](https://github.com/leanprover/lean4/issues/7463)), so a csimp lemma
whose proof smuggled `sorryAx` or a project axiom would be invisible to every
consumer's census entry. Checking the lemma itself closes that hole. -/

assert_axioms Zcash.Arithmetic.Msm.evalNat_eq_evalNatFast
