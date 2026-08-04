import Zcash.Snark.Soundness.Action.AdaptiveStatementKnowledge
import Zcash.Snark.Soundness.Action.AdaptiveStatementProfile

/-!
# Oracle-access certificates for the adaptive-statement reduction

The traversal formulas `adaptiveStatementDlogRandomOracleQueries` and
`adaptiveStatementKnowledgeExtractorRandomOracleQueries` are conservative counts.  This module
connects them to the executable code.  `relationFinderReads` is the concrete set of table points
the combined relation finder can consult — the adversary's own query log plus the selected
statement's canonical challenge prefixes.  `relationFinderReads_card_le` bounds its size by
`Q + (11 + k)`, and the locality theorems prove the finder and the knowledge extractor read
nothing else: two tables agreeing on the read set produce the same relation result and the same
extraction verdict.  The traversal formulas then dominate the certified count
(`relationFinderReads_card_le_dlogQueries` and its extractor counterpart), which is the missing
link between the resource arithmetic and the code it prices.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)

local instance adaptiveStatementReadsVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

variable {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
  (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)

/-- Every table point the combined relation finder can consult: the adversary's query log and
the selected statement's canonical pre-IPA and IPA-round prefixes. -/
def relationFinderReads (O : family.Coins) :
    Finset (AdaptiveActionStatementTranscript pp) :=
  ((family.adversary basis).queries O).toFinset ∪
    (Finset.univ.image fun i : Fin 11 =>
      (family.runOutput basis O).prefixesPre (family.vkTranscriptRepr basis) i) ∪
    (Finset.univ.image fun j : Fin (AdaptiveActionStatementShape pp).k =>
      (family.runOutput basis O).prefixes (family.vkTranscriptRepr basis) j)

/-- The certified read count: one adversary run plus one canonical challenge sweep. -/
theorem relationFinderReads_card_le (O : family.Coins) :
    (family.relationFinderReads basis O).card ≤
      family.Q + (11 + (AdaptiveActionStatementShape pp).k) := by
  refine le_trans (Finset.card_union_le _ _) ?_
  refine le_trans (Nat.add_le_add_right (Finset.card_union_le _ _) _) ?_
  have hq : ((family.adversary basis).queries O).toFinset.card ≤ family.Q :=
    le_trans (List.toFinset_card_le _)
      (OracleComp.queries_length_le (family.queryBound basis) O)
  have hpre : (Finset.univ.image fun i : Fin 11 =>
      (family.runOutput basis O).prefixesPre (family.vkTranscriptRepr basis) i).card ≤ 11 :=
    le_trans Finset.card_image_le (by simp)
  have hipa : (Finset.univ.image fun j : Fin (AdaptiveActionStatementShape pp).k =>
      (family.runOutput basis O).prefixes (family.vkTranscriptRepr basis) j).card ≤
        (AdaptiveActionStatementShape pp).k :=
    le_trans Finset.card_image_le (by simp)
  omega

/-- The certified count is below the conservative four-traversal solver formula. -/
theorem relationFinderReads_card_le_dlogQueries (O : family.Coins) :
    (family.relationFinderReads basis O).card ≤
      adaptiveStatementDlogRandomOracleQueries family := by
  refine le_trans (family.relationFinderReads_card_le basis O) ?_
  unfold adaptiveStatementDlogRandomOracleQueries adaptiveStatementDlogTraversalSlots
  omega

/-- The certified count is below the conservative five-traversal extractor formula. -/
theorem relationFinderReads_card_le_knowledgeExtractorQueries (O : family.Coins) :
    (family.relationFinderReads basis O).card ≤
      adaptiveStatementKnowledgeExtractorRandomOracleQueries family := by
  refine le_trans (family.relationFinderReads_card_le basis O) ?_
  unfold adaptiveStatementKnowledgeExtractorRandomOracleQueries
    adaptiveStatementKnowledgeExtractorTraversalSlots
  omega

/-! ## Locality of the run primitives

Every finder stage consults the table only through the primitives below, so agreement on the
read set propagates from the retained execution to the whole reduction. -/

variable {family basis}

/-- Agreement on the read set reproduces the retained execution. -/
theorem cachedExecution_eq_of_agree {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    family.cachedExecution basis O' = family.cachedExecution basis O :=
  LabeledOracleComp.runWithAnnotations_eq_of_agree fun t ht =>
    h t (by
      unfold relationFinderReads
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr ht)))

/-- Agreement on the read set reproduces the selected statement and proof. -/
theorem runOutput_eq_of_agree {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    family.runOutput basis O' = family.runOutput basis O := by
  have hcached := cachedExecution_eq_of_agree h
  have h1 := congrArg Prod.fst hcached
  simpa [cachedExecution_output_eq] using h1

/-- Agreement on the read set reproduces the retained annotation log. -/
theorem annotations_eq_of_agree {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    (family.adversary basis).annotations O' = (family.adversary basis).annotations O := by
  have hcached := cachedExecution_eq_of_agree h
  have h2 := congrArg Prod.snd hcached
  simpa [cachedExecution, LabeledOracleComp.runWithAnnotations_snd] using h2

/-- Agreement on the read set reproduces the eleven pre-IPA challenge reads. -/
theorem runPreIpaReads_eq_of_agree {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    family.runPreIpaReads basis O' = family.runPreIpaReads basis O := by
  have houtput := runOutput_eq_of_agree h
  funext i
  show O' ((family.runOutput basis O').prefixesPre (family.vkTranscriptRepr basis) i) =
    O ((family.runOutput basis O).prefixesPre (family.vkTranscriptRepr basis) i)
  rw [houtput]
  exact h _ (by
    unfold relationFinderReads
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)))

/-- Agreement on the read set reproduces the IPA-round challenge reads. -/
theorem runIpaReads_eq_of_agree {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    family.runIpaReads basis O' = family.runIpaReads basis O := by
  have houtput := runOutput_eq_of_agree h
  funext j
  show O' ((family.runOutput basis O').prefixes (family.vkTranscriptRepr basis) j) =
    O ((family.runOutput basis O).prefixes (family.vkTranscriptRepr basis) j)
  rw [houtput]
  exact h _ (by
    unfold relationFinderReads
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))

/-- Agreement on the read set reproduces the complete verifier challenge record. -/
theorem runRecord_eq_of_agree {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    family.runRecord basis O' = family.runRecord basis O := by
  rw [family.runRecord_eq_chRecord basis O', family.runRecord_eq_chRecord basis O,
    runPreIpaReads_eq_of_agree h]
  exact congrArg _ (runIpaReads_eq_of_agree h)

/-! ## Locality of the finder stages

The whole stage chain is indexed by the run view — the selected output and the two
challenge-read vectors — with the table-indexed forms recovered as abbreviations at `runView`.
The provenance stage consults the table only through the retained execution, so its locality is
one rewrite, and every other stage is a view-level function whose remaining arguments are the
source-mismatch verdict and proposition-valued certificates.  Full finder and extractor
locality therefore reduce to `runView_eq_of_agree` plus one congruence per stage, closed by
proof irrelevance. -/

/-- Agreement on the read set reproduces the whole run view. -/
theorem runView_eq_of_agree {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    runView family basis O' = runView family basis O := by
  unfold runView
  rw [runOutput_eq_of_agree h, runPreIpaReads_eq_of_agree h, runIpaReads_eq_of_agree h]

/-- Agreement on the read set reproduces the provenance stage. -/
theorem provenanceRelationFinder_eq_of_agree {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    family.provenanceRelationFinder basis O' = family.provenanceRelationFinder basis O := by
  unfold provenanceRelationFinder
  rw [cachedExecution_eq_of_agree h]

/-- Agreement on the read set reproduces the acceptance verdict. -/
theorem accepts_iff_of_agree {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    (family.accepts basis O' ↔ family.accepts basis O) := by
  unfold accepts
  rw [runOutput_eq_of_agree h, runRecord_eq_of_agree h]

/-- Agreement on the read set reproduces the executable acceptance check's verdict. -/
theorem accepts?_isSome_eq_of_agree {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    (family.accepts? basis O').isSome = (family.accepts? basis O).isSome := by
  have hiff := accepts_iff_of_agree h
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hsome
    exact family.accepts?_isSome_of basis O
      (hiff.mp ((family.accepts? basis O').get hsome).down)
  · intro hsome
    exact family.accepts?_isSome_of basis O'
      (hiff.mpr ((family.accepts? basis O).get hsome).down)

/-- Agreement on the read set reproduces the source-mismatch verdict. -/
theorem semanticSourceMismatchRelationFinder_eq_of_agree {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    family.semanticSourceMismatchRelationFinder basis O' =
      family.semanticSourceMismatchRelationFinder basis O := by
  rw [← family.semanticSourceMismatchRelationFinderOfOutput_eq basis O',
    ← family.semanticSourceMismatchRelationFinderOfOutput_eq basis O,
    runOutput_eq_of_agree h]

/-- Agreement on the read set reproduces the quotient stage. -/
theorem statementQuotientRelationFinder_eq_of_agree {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    family.statementQuotientRelationFinder basis O' =
      family.statementQuotientRelationFinder basis O :=
  congrArg (family.statementQuotientRelationFinderV basis) (runView_eq_of_agree h)

/-- Equal views and finder inputs give equal identity-branch results; the certificate
arguments are propositions and never steer the computation. -/
theorem identityRelationFinderV_congr {view view' : RunView pp family basis}
    (hview : view' = view)
    {source source' : Option (AlgebraicRelationWitness (F := Fp) basis)}
    (hsource : source' = source)
    (hchar' : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view'.output.inputs)
      view'.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view'.pre view'.rounds) <
        scalarFieldOrder)
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        scalarFieldOrder)
    (hfacts' : source' = none → family.SemanticStageFacts basis view')
    (hfacts : source = none → family.SemanticStageFacts basis view) :
    family.identityRelationFinderV basis view' hchar' source' hfacts' =
      family.identityRelationFinderV basis view hchar source hfacts := by
  subst hview
  subst hsource
  rfl

/-- Agreement on the read set reproduces the identity branch. -/
theorem identityRelationFinder_eq_of_agree
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    family.identityRelationFinder hchar basis O' =
      family.identityRelationFinder hchar basis O :=
  family.identityRelationFinderV_congr (runView_eq_of_agree h)
    (semanticSourceMismatchRelationFinder_eq_of_agree h) _ _ _ _

/-- Equal views give equal terminal results, for any character certificates. -/
theorem terminalRelationFinderV_congr {view view' : RunView pp family basis}
    (hview : view' = view)
    (hchar' : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view'.output.inputs)
      view'.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view'.pre view'.rounds) <
        scalarFieldOrder)
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        scalarFieldOrder) :
    family.terminalRelationFinderV basis view' hchar' =
      family.terminalRelationFinderV basis view hchar := by
  subst hview
  rfl

/-- Agreement on the read set reproduces the decoded Action terminal. -/
theorem terminalRelationFinder_eq_of_agree
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    family.terminalRelationFinder hchar basis O' =
      family.terminalRelationFinder hchar basis O :=
  family.terminalRelationFinderV_congr (runView_eq_of_agree h) _ _

/-- **Complete finder locality.**  Agreement on the certified read set reproduces the combined
relation finder: every stage consults the table only through the run view, the retained
execution, and the source-mismatch verdict, each of which the read set determines. -/
theorem relationFinder_eq_of_agree
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    family.relationFinder hchar basis O' = family.relationFinder hchar basis O := by
  unfold relationFinder
  rw [provenanceRelationFinder_eq_of_agree h,
    statementQuotientRelationFinder_eq_of_agree h,
    identityRelationFinder_eq_of_agree hchar h,
    terminalRelationFinder_eq_of_agree hchar h]

/-- Equal views and finder results give the same extraction verdict. -/
theorem adaptiveStatementKnowledgeExtractorV_isSome_congr
    {view view' : RunView pp family basis} (hview : view' = view)
    {fr fr' : Option (AlgebraicRelationWitness (F := Fp) basis)} (hfr : fr' = fr)
    (hchar' : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view'.output.inputs)
      view'.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view'.pre view'.rounds) <
        scalarFieldOrder)
    (hchar : deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis view.output.inputs)
      view.output.toAlgebraicWfProof.proof.1
      (chRecord (k := (AdaptiveActionStatementShape pp).k) view.pre view.rounds) <
        scalarFieldOrder)
    (hfacts' : fr' = none → family.SemanticStageFacts basis view')
    (hfacts : fr = none → family.SemanticStageFacts basis view) :
    (family.adaptiveStatementKnowledgeExtractorV basis view' hchar' fr' hfacts').isSome =
      (family.adaptiveStatementKnowledgeExtractorV basis view hchar fr hfacts).isSome := by
  subst hview
  subst hfr
  rfl

/-- **Complete extractor locality.**  Agreement on the certified read set reproduces the
knowledge extractor's verdict. -/
theorem adaptiveStatementKnowledgeExtractor_isSome_eq_of_agree
    (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
      (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
      (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
    {O O' : family.Coins}
    (h : ∀ t ∈ family.relationFinderReads basis O, O' t = O t) :
    (family.adaptiveStatementKnowledgeExtractor hchar basis O').isSome =
      (family.adaptiveStatementKnowledgeExtractor hchar basis O).isSome :=
  family.adaptiveStatementKnowledgeExtractorV_isSome_congr (runView_eq_of_agree h)
    (relationFinder_eq_of_agree hchar h) _ _ _ _

end ComputedAdaptiveActionStatementFSFamily

end Zcash.Snark
