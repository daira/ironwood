import Zcash.Snark.Soundness.AGM.OnlineMembers

/-!
# Arbitrary adaptive online-AGM random-oracle adversaries

`OracleComp` records the transcript point at each random-oracle query, but an online AGM also has
to expose algebraic representations of the group elements already present in that point.  Keeping
those representations only in the final proof output is too weak: a malicious adaptive adversary
may change them after learning the query answer, and no pre-squeeze chronology can then be derived.

`LabeledOracleComp` adds proof-irrelevant query data while still consulting the ordinary oracle at
the ordinary query point.  `AlgebraicTranscriptQuery` is the Halo2 instantiation: every group point
in the queried transcript carries coefficients over the sampled augmented basis.  The resulting
`ComputedAdaptiveOnlineAGMFSFamily` is the bare bounded adversary model intended by the public
soundness endpoint.  It permits arbitrary query order and arbitrary adaptive continuations; it
does not require root, IPA, constraint-`x`, or semantic phase objects.
-/

namespace Zcash.Snark

/-- An adaptive oracle computation whose query nodes carry data not passed to the oracle.  The
oracle still receives only `t : T`, so different labels at the same `t` share one oracle answer. -/
inductive LabeledOracleComp (T F : Type*) (Label : T → Type*) (α : Type*) where
  | pure (a : α)
  | query (t : T) (label : Label t) (k : F → LabeledOracleComp T F Label α)

namespace LabeledOracleComp

variable {T F α β : Type*} {Label : T → Type*}

/-- Forget query annotations, preserving the exact adaptive query tree seen by the random oracle. -/
def erase : LabeledOracleComp T F Label α → OracleComp T F α
  | .pure a => .pure a
  | .query t _ k => .query t (fun u => (k u).erase)

/-- Run a labeled computation against an ordinary oracle table. -/
def run (A : LabeledOracleComp T F Label α) (O : T → F) : α := A.erase.run O

/-- The ordinary query log of a labeled computation. -/
def queries (A : LabeledOracleComp T F Label α) (O : T → F) : List T := A.erase.queries O

/-- The annotation attached to each query on one concrete run.  Answers are deliberately omitted:
they remain available from the oracle table, while this log records exactly the data fixed before
each answer was read. -/
structure QueryAnnotation (T : Type*) (Label : T → Type*) where
  point : T
  label : Label point

/-- Query annotations along the adaptive path selected by `O`. -/
def annotations (A : LabeledOracleComp T F Label α) (O : T → F) :
    List (QueryAnnotation T Label) :=
  match A with
  | .pure _ => []
  | .query t label k => ⟨t, label⟩ :: (k (O t)).annotations O

/-- Retrieve the first annotation at `t`, if the computation queried `t`. -/
def findLabel [DecidableEq T] (A : LabeledOracleComp T F Label α) (O : T → F)
    (t : T) : Option (Label t) :=
  match A with
  | .pure _ => none
  | .query q label k =>
      if h : q = t then some (h ▸ label) else (k (O q)).findLabel O t

/-- A labeled computation is query-bounded exactly when its erased computation is. -/
abbrev QueryBound (A : LabeledOracleComp T F Label α) (Q : ℕ) : Prop := A.erase.QueryBound Q

/-- Sequence two labeled computations. -/
def bind : LabeledOracleComp T F Label α →
    (α → LabeledOracleComp T F Label β) → LabeledOracleComp T F Label β
  | .pure a, f => f a
  | .query t label k, f => .query t label (fun u => (k u).bind f)

@[simp] theorem erase_pure (a : α) :
    (pure a : LabeledOracleComp T F Label α).erase = .pure a := rfl

@[simp] theorem erase_query (t : T) (label : Label t)
    (k : F → LabeledOracleComp T F Label α) :
    (query t label k).erase = .query t (fun u => (k u).erase) := rfl

@[simp] theorem erase_bind (A : LabeledOracleComp T F Label α)
    (f : α → LabeledOracleComp T F Label β) :
    (A.bind f).erase = A.erase.bind (fun a => (f a).erase) := by
  induction A with
  | pure a => rfl
  | query t label k ih =>
      simp only [bind, erase, OracleComp.bind]
      congr
      funext u
      exact ih u

@[simp] theorem run_pure (a : α) (O : T → F) :
    (pure a : LabeledOracleComp T F Label α).run O = a := rfl

@[simp] theorem run_query (t : T) (label : Label t)
    (k : F → LabeledOracleComp T F Label α) (O : T → F) :
    (query t label k).run O = (k (O t)).run O := rfl

@[simp] theorem run_bind (A : LabeledOracleComp T F Label α)
    (f : α → LabeledOracleComp T F Label β) (O : T → F) :
    (A.bind f).run O = (f (A.run O)).run O := by
  simp only [run, erase_bind, OracleComp.run_bind]

@[simp] theorem annotations_pure (a : α) (O : T → F) :
    (pure a : LabeledOracleComp T F Label α).annotations O = [] := rfl

@[simp] theorem annotations_query (t : T) (label : Label t)
    (k : F → LabeledOracleComp T F Label α) (O : T → F) :
    (query t label k).annotations O =
      ⟨t, label⟩ :: (k (O t)).annotations O := rfl

/-- Erasing annotations gives the ordinary query log. -/
theorem queries_eq_map_annotations (A : LabeledOracleComp T F Label α) (O : T → F) :
    A.queries O = (A.annotations O).map QueryAnnotation.point := by
  induction A with
  | pure a => rfl
  | query t label k ih =>
      simp only [queries, erase, OracleComp.queries, annotations, List.map_cons]
      exact congrArg (List.cons t) (ih (O t))

@[simp] theorem findLabel_isSome_iff [DecidableEq T]
    (A : LabeledOracleComp T F Label α) (O : T → F) (t : T) :
    (A.findLabel O t).isSome ↔ t ∈ A.queries O := by
  induction A with
  | pure a => simp [findLabel, queries, erase, OracleComp.queries]
  | query q label k ih =>
      by_cases h : q = t
      · subst t
        simp [findLabel, queries, erase, OracleComp.queries]
      · simpa [findLabel, h, queries, erase, OracleComp.queries, Ne.symm h] using ih (O q)

/-- If no query-time annotation exists at `t`, reprogramming `t` cannot change the result. -/
theorem run_update_of_findLabel_eq_none [DecidableEq T]
    (A : LabeledOracleComp T F Label α) (O : T → F) (t : T) (v : F)
    (hfresh : A.findLabel O t = none) :
    A.run (Function.update O t v) = A.run O := by
  apply OracleComp.run_update_of_not_mem_queries
  intro hmem
  have : (A.findLabel O t).isSome := (findLabel_isSome_iff A O t).2 hmem
  simp [hfresh] at this

/-- The first annotation at a point is fixed before that point's answer is read. -/
theorem findLabel_update_self [DecidableEq T]
    (A : LabeledOracleComp T F Label α) (O : T → F) (t : T) (v : F) :
    A.findLabel (Function.update O t v) t = A.findLabel O t := by
  induction A with
  | pure a => rfl
  | query q label k ih =>
      by_cases h : q = t
      · subst t
        simp [findLabel]
      · simp [findLabel, h, ih (O q)]

/-- The bad set selected at `t`: use the first query-time annotation when it exists, otherwise
use a set computed from the final output.  The fallback is safe because `findLabel = none` means
reprogramming `t` cannot change that output. -/
def firstLabelOrFallbackBad [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (t : T) (O : T → F) : Set F :=
  match A.findLabel O t with
  | some label => bad t label O
  | none => fallback (A.run O) t O

/-- `firstLabelOrFallbackBad` is blind to the answer at the point it prices. -/
theorem firstLabelOrFallbackBad_update_self [DecidableEq T]
    (A : LabeledOracleComp T F Label α)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (hbadBlind : ∀ t label O v,
      bad t label (Function.update O t v) = bad t label O)
    (hfallbackBlind : ∀ a t O v,
      fallback a t (Function.update O t v) = fallback a t O)
    (t : T) (O : T → F) (v : F) :
    firstLabelOrFallbackBad A bad fallback t (Function.update O t v) =
      firstLabelOrFallbackBad A bad fallback t O := by
  rw [firstLabelOrFallbackBad, firstLabelOrFallbackBad, A.findLabel_update_self O t v]
  cases hfound : A.findLabel O t with
  | some label => exact hbadBlind t label O v
  | none =>
    rw [A.run_update_of_findLabel_eq_none O t v hfound]
    exact hfallbackBlind (A.run O) t O v

/-- **Arbitrary adaptive labeled squeeze.**  Complete the adversary with the verifier's selected
query.  Its answer lands in the first pre-answer annotation's bad set, or in the fresh fallback
set, with probability at most `(Q+1)·ε`.  No phase ordering or prefix-determinism premise is
required. -/
theorem firstLabelOrFallbackBad_measure_le
    [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    (A : LabeledOracleComp T F Label α) (xpt : α → T)
    (bad : (t : T) → Label t → (T → F) → Set F)
    (fallback : α → T → (T → F) → Set F)
    (hbadBlind : ∀ t label O v,
      bad t label (Function.update O t v) = bad t label O)
    (hfallbackBlind : ∀ a t O v,
      fallback a t (Function.update O t v) = fallback a t O)
    {epsilon : ENNReal}
    (hbad : ∀ t label O,
      (PMF.uniformOfFintype F).toOuterMeasure (bad t label O) ≤ epsilon)
    (hfallback : ∀ a t O,
      (PMF.uniformOfFintype F).toOuterMeasure (fallback a t O) ≤ epsilon)
    {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | O (xpt (A.run O)) ∈
        firstLabelOrFallbackBad A bad fallback (xpt (A.run O)) O} ≤
      (Q + 1 : ℕ) * epsilon := by
  let esc : T → (T → F) → Set F := firstLabelOrFallbackBad A bad fallback
  have hsub : {O : T → F | O (xpt (A.run O)) ∈ esc (xpt (A.run O)) O} ⊆
      {O : T → F | (A.erase.completing (fun a (_ : Fin 1) => xpt a)).escapesDuringC esc O} := by
    intro O hO
    exact OracleComp.escapesDuringC_completing esc
      (fun a (_ : Fin 1) => xpt a) (j := 0) hO
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  apply escapesDuringC_measure_le' esc
  · exact firstLabelOrFallbackBad_update_self A bad fallback hbadBlind hfallbackBlind
  · intro t O
    unfold esc firstLabelOrFallbackBad
    cases A.findLabel O t with
    | some label => exact hbad t label O
    | none => exact hfallback (A.run O) t O
  · exact OracleComp.queryBound_completing (fun a (_ : Fin 1) => xpt a) hQ

end LabeledOracleComp

/-- Extract the group elements, in order, from a Fiat--Shamir transcript. -/
def transcriptGroupPoints {F G : Type*} : List (TranscriptElt F G) → List G
  | [] => []
  | .point P :: rest => P :: transcriptGroupPoints rest
  | _ :: rest => transcriptGroupPoints rest

/-- Online AGM data attached to one random-oracle query.  The represented points are exactly the
group elements already absorbed into the queried transcript, in transcript order. -/
structure AlgebraicTranscriptQuery {F G ι : Type*} [Field F] [AddCommGroup G] [Module F G]
    [Fintype ι]
    (basis : ι → G) {L : ℕ} (t : BTranscript F G L) where
  representedPoints : List (AlgebraicPoint (F := F) basis)
  points_eq : representedPoints.map AlgebraicPoint.point = transcriptGroupPoints t.val

namespace AlgebraicTranscriptQuery

/-- Recover the first query-time representation of a point occurring in the transcript. -/
def representationOfPoint {F G ι : Type*} [Field F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} {t : BTranscript F G L}
    (query : AlgebraicTranscriptQuery (F := F) basis t) (P : G)
    (hP : P ∈ transcriptGroupPoints t.val) : AlgebraicPoint (F := F) basis := by
  have H : (query.representedPoints.find? (fun ap => ap.point = P)).isSome := by
    rw [List.find?_isSome]
    have hP' : P ∈ query.representedPoints.map AlgebraicPoint.point := by
      rw [query.points_eq]
      exact hP
    obtain ⟨ap, hap, hpoint⟩ := List.mem_map.mp hP'
    exact ⟨ap, hap, by simpa using hpoint⟩
  exact (query.representedPoints.find? (fun ap => ap.point = P)).get H

@[simp] theorem representationOfPoint_point {F G ι : Type*} [Field F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} {t : BTranscript F G L}
    (query : AlgebraicTranscriptQuery (F := F) basis t) (P : G)
    (hP : P ∈ transcriptGroupPoints t.val) :
    (query.representationOfPoint P hP).point = P := by
  unfold representationOfPoint
  let H : (query.representedPoints.find? (fun ap => ap.point = P)).isSome := by
    rw [List.find?_isSome]
    have hP' : P ∈ query.representedPoints.map AlgebraicPoint.point := by
      rw [query.points_eq]
      exact hP
    obtain ⟨ap, hap, hpoint⟩ := List.mem_map.mp hP'
    exact ⟨ap, hap, by simpa using hpoint⟩
  have hsome := List.find?_some (Option.some_get H).symm
  simpa using hsome

/-- Select query-time representations for a final list of points known to occur in the queried
transcript. -/
def representationsFor {F G ι : Type*} [Field F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} {t : BTranscript F G L}
    (query : AlgebraicTranscriptQuery (F := F) basis t) :
    (final : List (AlgebraicPoint (F := F) basis)) →
      (∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val) →
      List (AlgebraicPoint (F := F) basis)
  | [], _ => []
  | ap :: rest, hcovered =>
      query.representationOfPoint ap.point (hcovered ap (by simp)) ::
        query.representationsFor rest (fun candidate hmem =>
          hcovered candidate (by simp [hmem]))

/-- Selection preserves the final list's group points exactly. -/
theorem representationsFor_points {F G ι : Type*} [Field F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} {t : BTranscript F G L}
    (query : AlgebraicTranscriptQuery (F := F) basis t)
    (final : List (AlgebraicPoint (F := F) basis))
    (hcovered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val) :
    (query.representationsFor final hcovered).map AlgebraicPoint.point =
      final.map AlgebraicPoint.point := by
  induction final with
  | nil => rfl
  | cons ap rest ih =>
      simp only [representationsFor, List.map_cons, representationOfPoint_point,
        List.cons.injEq, true_and]
      exact ih (fun candidate hmem => hcovered candidate (by simp [hmem]))

end AlgebraicTranscriptQuery

/-- Compare two valid representations of the same point.  A coefficient mismatch computes an
explicit relation over the public basis; equality returns no relation. -/
def representationMismatchRelation? {F G ι : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} (P Q : AlgebraicPoint (F := F) basis) (hpoint : P.point = Q.point) :
    Option (AlgebraicRelationWitness (F := F) basis) :=
  if hcoeff : P.coeffs = Q.coeffs then none else
    some
      { coeffs := P.coeffs - Q.coeffs
        nontrivial := sub_ne_zero.mpr hcoeff
        relation := by
          calc
            representationEval basis (P.coeffs - Q.coeffs) =
                representationEval basis P.coeffs - representationEval basis Q.coeffs := by
              simp only [representationEval, Pi.sub_apply, sub_smul,
                Finset.sum_sub_distrib]
            _ = P.point - Q.point := by rw [P.hEq, Q.hEq]
            _ = 0 := by rw [hpoint, sub_self] }

@[simp] theorem representationMismatchRelation?_eq_none_iff
    {F G ι : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} (P Q : AlgebraicPoint (F := F) basis) (hpoint : P.point = Q.point) :
    representationMismatchRelation? P Q hpoint = none ↔ P.coeffs = Q.coeffs := by
  simp [representationMismatchRelation?]

/-- Compare two pointwise-equal representation lists.  Either every coefficient vector agrees or
the first mismatch is returned as an explicit relation.  This is executable: the only branching
is equality of finite coefficient vectors. -/
def representationListsEqualOrRelation
    {F G ι : Type*} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} (left right : List (AlgebraicPoint (F := F) basis))
    (hpoints : left.map AlgebraicPoint.point = right.map AlgebraicPoint.point) :
    (left.map AlgebraicPoint.coeffs = right.map AlgebraicPoint.coeffs) ⊕'
      AlgebraicRelationWitness (F := F) basis := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact PSum.inl rfl
      | cons Q qs => simp at hpoints
  | cons P ps ih =>
      cases right with
      | nil => simp at hpoints
      | cons Q qs =>
          have hpoint : P.point = Q.point := by simpa using congrArg List.head? hpoints
          have htail : ps.map AlgebraicPoint.point = qs.map AlgebraicPoint.point := by
            simpa using congrArg List.tail hpoints
          cases hrel : representationMismatchRelation? P Q hpoint with
          | some relation => exact PSum.inr relation
          | none =>
              have hcoeff := (representationMismatchRelation?_eq_none_iff P Q hpoint).1 hrel
              match ih qs htail with
              | PSum.inr relation => exact PSum.inr relation
              | PSum.inl hrest => exact PSum.inl (by simp [hcoeff, hrest])

/-- Evidence that the representations used at a completed transcript were fixed by an actual
query annotation before the oracle answer was read. -/
structure QueryRepresentationPinned {F G ι : Type*} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [Fintype ι] {α : Type*}
    {basis : ι → G} {L : ℕ} (t : BTranscript F G L)
    (A : LabeledOracleComp (BTranscript F G L) F
      (AlgebraicTranscriptQuery (F := F) basis) α) (O : BTranscript F G L → F)
    (final : List (AlgebraicPoint (F := F) basis)) where
  query : AlgebraicTranscriptQuery (F := F) basis t
  found : A.findLabel O t = some query
  coefficients_eq : query.representedPoints.map AlgebraicPoint.coeffs =
    final.map AlgebraicPoint.coeffs

/-- At any completed transcript, either the adversary never queried it, its final coefficients
equal the pre-answer annotation, or the discrepancy is an explicit DLOG relation. -/
def queryRepresentationProvenanceOrRelation
    {F G ι α : Type*} [Field F] [DecidableEq F] [DecidableEq G]
    [AddCommGroup G] [Module F G]
    [Fintype ι] {basis : ι → G} {L : ℕ} (t : BTranscript F G L)
    (A : LabeledOracleComp (BTranscript F G L) F
      (AlgebraicTranscriptQuery (F := F) basis) α) (O : BTranscript F G L → F)
    (final : List (AlgebraicPoint (F := F) basis))
    (hfinal : final.map AlgebraicPoint.point = transcriptGroupPoints t.val) :
    (A.findLabel O t = none ⊕' QueryRepresentationPinned t A O final) ⊕'
      AlgebraicRelationWitness (F := F) basis := by
  match hfound : A.findLabel O t with
  | none => exact PSum.inl (PSum.inl rfl)
  | some query =>
      have hpoints : query.representedPoints.map AlgebraicPoint.point =
          final.map AlgebraicPoint.point := query.points_eq.trans hfinal.symm
      match representationListsEqualOrRelation query.representedPoints final hpoints with
      | PSum.inr relation => exact PSum.inr relation
      | PSum.inl hcoeff =>
          exact PSum.inl (PSum.inr
            { query := query
              found := hfound
              coefficients_eq := hcoeff })

/-- Query-time provenance for only the represented points relevant to one soundness check.  This
avoids requiring verifier-fixed points in the transcript to be duplicated in a final proof list. -/
structure SelectedQueryRepresentationPinned
    {F G ι : Type*} [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [Fintype ι] {α : Type*}
    {basis : ι → G} {L : ℕ} (t : BTranscript F G L)
    (A : LabeledOracleComp (BTranscript F G L) F
      (AlgebraicTranscriptQuery (F := F) basis) α) (O : BTranscript F G L → F)
    (final : List (AlgebraicPoint (F := F) basis)) where
  query : AlgebraicTranscriptQuery (F := F) basis t
  found : A.findLabel O t = some query
  covered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val
  coefficients_eq :
    (query.representationsFor final covered).map AlgebraicPoint.coeffs =
      final.map AlgebraicPoint.coeffs

/-- For any selected final points already absorbed at `t`, either `t` was never queried, their
coefficients equal the first pre-answer query annotations, or a mismatch computes a relation. -/
def selectedQueryRepresentationProvenanceOrRelation
    {F G ι α : Type*} [Field F] [DecidableEq F] [DecidableEq G]
    [AddCommGroup G] [Module F G] [Fintype ι]
    {basis : ι → G} {L : ℕ} (t : BTranscript F G L)
    (A : LabeledOracleComp (BTranscript F G L) F
      (AlgebraicTranscriptQuery (F := F) basis) α) (O : BTranscript F G L → F)
    (final : List (AlgebraicPoint (F := F) basis))
    (hcovered : ∀ ap ∈ final, ap.point ∈ transcriptGroupPoints t.val) :
    (A.findLabel O t = none ⊕' SelectedQueryRepresentationPinned t A O final) ⊕'
      AlgebraicRelationWitness (F := F) basis := by
  match hfound : A.findLabel O t with
  | none => exact PSum.inl (PSum.inl rfl)
  | some query =>
      let selected := query.representationsFor final hcovered
      have hpoints : selected.map AlgebraicPoint.point = final.map AlgebraicPoint.point :=
        query.representationsFor_points final hcovered
      match representationListsEqualOrRelation selected final hpoints with
      | PSum.inr relation => exact PSum.inr relation
      | PSum.inl hcoeff =>
          exact PSum.inl (PSum.inr
            { query := query
              found := hfound
              covered := hcovered
              coefficients_eq := hcoeff })

/-- A malicious adaptive online-AGM computation over the Halo2 transcript domain. -/
abbrev AdaptiveOnlineAGMComp {shape : Shape}
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (α : Type*) :=
  LabeledOracleComp
    (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
    (AlgebraicTranscriptQuery (F := Fp) basis) α

/-- The bare bounded adaptive online-AGM family.  No execution cuts or freshness proofs are fields:
the adversary may make arbitrary malicious random-oracle queries, and every query carries the AGM
representations fixed at that query. -/
structure ComputedAdaptiveOnlineAGMFSFamily (shape : Shape) where
  init : List (TranscriptElt Fp VestaG)
  vk : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → VerifyingKey shape Fp VestaG
  instanceCommitment : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
    Fin shape.numProofs → ℕ → VestaG
  fixedRepresentations : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
    List (AlgebraicPoint (F := Fp) basis)
  adversary : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
    AdaptiveOnlineAGMComp init basis
      (OnlineMemberProofData (vk := vk basis)
        (instanceCommitment := instanceCommitment basis) basis (fixedRepresentations basis))
  Q : ℕ
  queryBound : ∀ basis, (adversary basis).QueryBound Q

namespace ComputedAdaptiveOnlineAGMFSFamily

variable {shape : Shape}

/-- Forget only the per-query AGM annotations and assemble the canonical online-member family.
The erased random-oracle computation has definitionally the same outputs and query budget. -/
noncomputable def toOnlineMemberFamily (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    ComputedOnlineMemberFSFamily shape :=
  ComputedOnlineMemberFSFamily.ofProofData family.init family.vk family.instanceCommitment
    family.fixedRepresentations (fun basis => (family.adversary basis).erase) family.Q
    family.queryBound

/-- Forget member coverage as well, yielding the existing arbitrary-query algebraic family. -/
noncomputable abbrev toFamily (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    ComputedAlgebraicFSFamily shape := family.toOnlineMemberFamily.toFamily

@[simp] theorem toOnlineMemberFamily_Q (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    family.toOnlineMemberFamily.Q = family.Q := rfl

@[simp] theorem toFamily_Q (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    family.toFamily.Q = family.Q := rfl

end ComputedAdaptiveOnlineAGMFSFamily

end Zcash.Snark
