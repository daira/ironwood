import Zcash.Snark.Soundness.Composition.ActionBudget

/-!
# Group-operation cost of the assembled fingerprint MSM

`DirectPathCost` prices the decode's field operations; this module prices the group operations
of the acceptance check itself.  Evaluating an `Msm` costs the fixed `2 ^ k + 2` generator sweep
plus one operation per accumulated term, so the cost of one deployed acceptance check is
determined by the term count of the MSM `assemble?` produces.  `deployedAssembleGroupOps` reads
that count off the actual assembled MSM, and `deployedAssembleGroupOps_le` bounds it by the
shape-level `assembleGroupOpsBudget`: the query terms routed through the multiopen grouping
(each at most one term, except the vanishing `h` reference at one per quotient piece), the
quotient commitment, and the IPA fold's per-round and blinding terms.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

/-- Group terms a commitment reference contributes when accumulated into an MSM. -/
def CommitmentRef.termCount {k : ℕ} {F G : Type*} : CommitmentRef k F G → ℕ
  | .point _ => 1
  | .msm m => m.other.length

@[simp] theorem CommitmentRef.termCount_point {k : ℕ} {F G : Type*} (P : G) :
    (CommitmentRef.point (k := k) (F := F) P).termCount = 1 := rfl

@[simp] theorem CommitmentRef.termCount_msm {k : ℕ} {F G : Type*} (m : Msm k F G) :
    (CommitmentRef.msm m).termCount = m.other.length := rfl

/-- Total term count of one grouped multiopen input. -/
def MultiopenGrouped.termCount {k : ℕ} {F G : Type*} (grouped : MultiopenGrouped k F G) : ℕ :=
  (grouped.sets.map fun s => (s.map fun m => m.1.termCount).sum).sum

private theorem foldl_scale_appendTerm_other_length {k : ℕ} {F G : Type*} [Field F] (xn : F)
    (l : List G) :
    ∀ acc : Msm k F G,
      (l.foldl (fun acc c => (acc.scale xn).appendTerm (1 : F) c) acc).other.length
        = acc.other.length + l.length := by
  induction l with
  | nil => intro acc; simp
  | cons c t ih =>
      intro acc
      rw [List.foldl_cons, ih]
      simp
      omega

/-- The vanishing `h` fold carries one term per quotient piece. -/
theorem vanishingHCommitment_other_length {k : ℕ} {F G : Type*} [Field F] (xn : F)
    (hPieces : List G) :
    (vanishingHCommitment k xn hPieces).other.length = hPieces.length := by
  rw [vanishingHCommitment]
  have h := foldl_scale_appendTerm_other_length (k := k) xn hPieces.reverse (Msm.zero k F G)
  simpa using h

/-- Accumulating one commitment reference adds exactly its term count. -/
theorem accumulateCommitment_other_length {k : ℕ} {F G : Type*} [Field F] (pow : F)
    (c : CommitmentRef k F G) (acc : Msm k F G) :
    (accumulateCommitment pow c acc).other.length = acc.other.length + c.termCount := by
  cases c <;> simp [accumulateCommitment]

private theorem compressSet_fold_other_length {k : ℕ} {F G : Type*} [Field F] (x1 : F)
    (sq : List (CommitmentRef k F G × List F)) :
    ∀ st : Msm k F G × List F × F,
      ((sq.foldl (fun (st : Msm k F G × List F × F) qc =>
          (accumulateCommitment st.2.2 qc.1 st.1,
           (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
           st.2.2 * x1)) st).1).other.length
        = st.1.other.length + (sq.map fun qc => qc.1.termCount).sum := by
  induction sq with
  | nil => intro st; simp
  | cons qc t ih =>
      intro st
      rw [List.foldl_cons, ih]
      simp [accumulateCommitment_other_length]
      omega

/-- One compressed point set carries exactly its members' term counts. -/
theorem compressSet_other_length {k : ℕ} {F G : Type*} [Field F] (x1 : F)
    (sq : List (CommitmentRef k F G × List F)) (numPoints : ℕ) :
    (compressSet x1 sq numPoints).1.other.length = (sq.map fun qc => qc.1.termCount).sum := by
  rw [compressSet]
  have h := compressSet_fold_other_length x1 sq
    (Msm.zero k F G, List.replicate numPoints (0 : F), (1 : F))
  simpa using h

private theorem combine_fold_other_length_le {k : ℕ} {F G : Type*} [Field F] (x4 : F)
    (qs : List (Msm k F G)) :
    ∀ (u : List F) (st : Msm k F G × F),
      (((qs.zip u).foldl (fun (st : Msm k F G × F) p =>
          ((st.1.scale x4).add p.1, st.2 * x4 + p.2)) st).1).other.length
        ≤ st.1.other.length + (qs.map fun m => m.other.length).sum := by
  induction qs with
  | nil => intro u st; simp
  | cons q t ih =>
      intro u st
      cases u with
      | nil => simp
      | cons a u' =>
          rw [List.zip_cons_cons, List.foldl_cons]
          refine le_trans (ih u' _) ?_
          simp
          omega

/-- The `x₄` collapse spends the quotient commitment plus every compressed set's terms. -/
theorem multiopenCombine_other_length_le {k : ℕ} {F G : Type*} [Field F] (x4 : F) (qPrime : G)
    (qs : List (Msm k F G)) (u : List F) (ev : F) (incoming : Msm k F G) :
    (multiopenCombine x4 qPrime qs u ev incoming).1.other.length
      ≤ incoming.other.length + 1 + (qs.map fun m => m.other.length).sum := by
  rw [multiopenCombine]
  refine le_trans (combine_fold_other_length_le x4 qs u _) ?_
  simp

private theorem zip_compress_termCount_le {k : ℕ} {F G : Type*} [Field F] (x1 : F)
    (sets : List (List (CommitmentRef k F G × List F))) :
    ∀ points : List (List F),
      (((sets.zip points).map fun sp => compressSet x1 sp.1 sp.2.length).map
          fun m => m.1.other.length).sum
        ≤ (sets.map fun s => (s.map fun m => m.1.termCount).sum).sum := by
  induction sets with
  | nil => intro points; simp
  | cons s t ih =>
      intro points
      cases points with
      | nil => simp
      | cons p ps' =>
          rw [List.zip_cons_cons]
          simp only [List.map_cons, List.sum_cons]
          exact Nat.add_le_add (le_of_eq (compressSet_other_length x1 s p.length)) (ih ps')

/-- The multiopen opening spends the quotient commitment plus the grouped term count. -/
theorem assembleOpening_other_length_le {k : ℕ} {F G : Type*} [Field F] (x1 x2 x3 x4 : F)
    (qPrime : G) (u : List F) (grouped : MultiopenGrouped k F G) (incoming : Msm k F G) :
    (assembleOpening x1 x2 x3 x4 qPrime u grouped incoming).1.other.length
      ≤ incoming.other.length + 1 + grouped.termCount := by
  rw [assembleOpening]
  refine le_trans (multiopenCombine_other_length_le x4 qPrime _ _ _ incoming) ?_
  rw [MultiopenGrouped.termCount, List.map_map]
  exact Nat.add_le_add_left (zip_compress_termCount_le x1 grouped.sets grouped.points) _

private theorem ipaFold_rounds_fold_other_length_le {k : ℕ} {F G : Type*} [Field F]
    (l : List ((G × G) × F)) :
    ∀ m : Msm k F G,
      ((l.foldl (fun acc p => (acc.appendTerm p.2⁻¹ p.1.1).appendTerm p.2 p.1.2) m)).other.length
        ≤ m.other.length + 2 * l.length := by
  induction l with
  | nil => intro m; simp
  | cons a t ih =>
      intro m
      rw [List.foldl_cons]
      refine le_trans (ih _) ?_
      simp
      omega

/-- The IPA fold adds the blinding term plus two terms per round. -/
theorem ipaFold_other_length_le {k : ℕ} {F G : Type*} [Field F] (x v c f xi z : F) (u : List F)
    (S : G) (rounds : List (G × G)) (m : Msm k F G) :
    (ipaFold x v c f xi z u S rounds m).other.length
      ≤ m.other.length + 1 + 2 * rounds.length := by
  rw [ipaFold]
  simp only [Msm.other_addToGScalars, Msm.other_addToUScalar, Msm.other_addToWScalar]
  refine le_trans (ipaFold_rounds_fold_other_length_le _ _) ?_
  simp only [Msm.other_length_appendTerm, Msm.other_addToGScalars]
  have hzip : (rounds.zip u).length ≤ rounds.length := by
    rw [List.length_zip]
    exact min_le_left _ _
  omega

/-- The checked final MSM's terms fit the grouped term count plus the IPA tail. -/
theorem assembleFinalMsm?_other_length_le {shape : Shape} {F G : Type*} [Field F]
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (grouped : MultiopenGrouped shape.k F G) {msm : Msm shape.k F G}
    (h : assembleFinalMsm? ps ch grouped = some msm) :
    msm.other.length ≤ grouped.termCount + 2 * shape.k + 2 := by
  rw [assembleFinalMsm?] at h
  split at h
  case h_1 opened hop =>
      cases h
      rw [assembleOpening?] at hop
      split at hop
      case isTrue =>
          cases hop
          refine le_trans (ipaFold_other_length_le ..) ?_
          have hopen := assembleOpening_other_length_le ch.x1 ch.x2 ch.x3 ch.x4
            ps.multiopenQPrime (List.ofFn ps.multiopenU) grouped (Msm.zero shape.k F G)
          simp only [Msm.other_zero, List.length_nil, List.length_ofFn] at hopen ⊢
          omega
      case isFalse => cases hop
  case h_2 => cases h

/-- Every routed member's commitment reference originates from a flat query. -/
theorem constructIntermediateSets_sets_getD_commitment_mem {k : ℕ} {F G : Type*}
    [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G)) (si : ℕ)
    {member : CommitmentRef k F G × List F}
    (hmem : member ∈ (constructIntermediateSets queries).sets.getD si []) :
    ∃ q ∈ queries, member.1 = q.commitment := by
  classical
  rcases lt_or_ge si (constructIntermediateSets queries).sets.length with hlt | hge
  · rw [List.getD_eq_getElem _ _ hlt] at hmem
    have hsets : (constructIntermediateSets queries).sets
        = (List.range (cisSetList queries).length).map fun si' =>
            (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2) := rfl
    have hlt' : si < ((List.range (cisSetList queries).length).map fun si' =>
        (cisRouted queries si').map fun cd => (cd.2.1, cd.2.2.2)).length := by
      rw [← hsets]; exact hlt
    rw [List.getElem_of_eq hsets hlt, List.getElem_map, List.getElem_range] at hmem
    obtain ⟨cd, hcd, rfl⟩ := List.mem_map.mp hmem
    have hcdData : cd ∈ cisData queries := by
      rw [cisRouted] at hcd
      exact List.mem_reverse.mp (List.mem_filter.mp hcd).1
    rw [cisData] at hcdData
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcdData
    rcases cisComms_fold_prov queries [] hc with hnil | ⟨q, hq, rfl⟩
    · exact absurd hnil List.not_mem_nil
    · exact ⟨q, hq, rfl⟩
  · rw [List.getD_eq_default _ _ hge] at hmem
    exact absurd hmem List.not_mem_nil

private theorem foldl_growth_length_le {α β : Type*} (f : List β → α → List β)
    (hf : ∀ acc a, (f acc a).length ≤ acc.length + 1) (l : List α) :
    ∀ init : List β, (l.foldl f init).length ≤ init.length + l.length := by
  induction l with
  | nil => intro init; simp
  | cons a t ih =>
      intro init
      rw [List.foldl_cons]
      refine le_trans (ih _) ?_
      have := hf init a
      rw [List.length_cons]
      omega

/-- The grouping produces at most one point set per flat query. -/
theorem constructIntermediateSets_sets_length_le {k : ℕ} {F G : Type*}
    [DecidableEq F] [DecidableEq G] (queries : List (VerifierQuery k F G)) :
    (constructIntermediateSets queries).sets.length ≤ queries.length := by
  classical
  show ((List.range (cisSetList queries).length).map fun si =>
    (cisRouted queries si).map fun cd => (cd.2.1, cd.2.2.2)).length ≤ _
  rw [List.length_map, List.length_range]
  have hset : (cisSetList queries).length ≤ (cisData queries).length := by
    rw [cisSetList]
    refine le_trans (foldl_growth_length_le _ (fun acc cd => ?_) (cisData queries) []) (by simp)
    split
    · omega
    · rw [List.length_append, List.length_singleton]
  have hdata : (cisData queries).length = (cisComms queries).length := by
    rw [cisData, List.length_map]
  have hcomms : (cisComms queries).length ≤ queries.length := by
    have h := cisComms_fold_length_le queries []
    rw [List.length_nil, Nat.zero_add] at h
    rw [cisComms]
    exact h
  omega

private theorem columnQueries_commitment_termCount {k : ℕ} {F G' : Type*} [Field F]
    {omega x : F} {commitment : ℕ → G'} {mkId : ℕ → CommitmentId}
    {layout : List (ℕ × ℤ)} {evals : List F} {q : VerifierQuery k F G'}
    (hq : q ∈ columnQueries omega x commitment mkId layout evals) :
    q.commitment.termCount = 1 := by
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hq
  rfl

private theorem permutationQueries_commitment_termCount {k : ℕ} {F G' : Type*} [Field F]
    {x xNext xLast : F} {mkId : ℕ → CommitmentId} {sets : List (G' × PermSetEval F)}
    {q : VerifierQuery k F G'}
    (hq : q ∈ permutationQueries x xNext xLast mkId sets) :
    q.commitment.termCount = 1 := by
  rw [permutationQueries] at hq
  rcases List.mem_append.mp hq with h | h
  · obtain ⟨s, -, hmem⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rfl
  · obtain ⟨s, -, hsome⟩ := List.mem_filterMap.mp h
    cases hle : s.1.2.lastEval with
    | none => rw [hle] at hsome; exact absurd hsome (by simp)
    | some le =>
        rw [hle, Option.map_some] at hsome
        cases hsome
        rfl

private theorem lookupQueries_commitment_termCount {k : ℕ} {F G' : Type*} [Field F]
    {x xInv xNext : F} {mkProduct mkInput mkTable : ℕ → CommitmentId}
    {lookups : List (LookupCommitments G' × LookupEval F)} {q : VerifierQuery k F G'}
    (hq : q ∈ lookupQueries x xInv xNext mkProduct mkInput mkTable lookups) :
    q.commitment.termCount = 1 := by
  rw [lookupQueries] at hq
  obtain ⟨l, -, hmem⟩ := List.mem_flatMap.mp hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem permutationCommonQueries_commitment_termCount {k : ℕ} {F G' : Type*} [Field F]
    {x : F} {mkId : ℕ → CommitmentId} {commsEvals : List (G' × F)} {q : VerifierQuery k F G'}
    (hq : q ∈ permutationCommonQueries x mkId commsEvals) :
    q.commitment.termCount = 1 := by
  obtain ⟨ce, -, rfl⟩ := List.mem_map.mp hq
  rfl

/-- Every deployed query's reference carries at most one term per quotient piece plus one:
all references are single points except the vanishing `h` MSM. -/
theorem assembleQueries_commitment_termCount_le {shape : Shape} {F G' : Type*} [Field F]
    [Inhabited G'] (vk : VerifyingKey shape F G') (ic : Fin shape.numProofs → ℕ → G')
    (ps : ProofString shape F G') (ch : Challenges shape.k F)
    {q : VerifierQuery shape.k F G'} (hq : q ∈ assembleQueries vk ic ps ch) :
    q.commitment.termCount ≤ shape.numQuotientPieces + 1 := by
  simp only [assembleQueries, List.mem_append] at hq
  rcases hq with ((hq | hq) | hq) | hq
  · obtain ⟨l, hl, hql⟩ := List.mem_flatten.mp hq
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hl
    simp only [List.mem_append] at hql
    rcases hql with ((h | h) | h) | h
    · rw [columnQueries_commitment_termCount h]; omega
    · rw [columnQueries_commitment_termCount h]; omega
    · rw [permutationQueries_commitment_termCount h]; omega
    · rw [lookupQueries_commitment_termCount h]; omega
  · rw [columnQueries_commitment_termCount hq]; omega
  · rw [permutationCommonQueries_commitment_termCount hq]; omega
  · simp only [vanishingQueries, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · show (CommitmentRef.msm _).termCount ≤ _
      rw [CommitmentRef.termCount_msm, vanishingHCommitment_other_length, List.length_ofFn]
      omega
    · show (CommitmentRef.point _).termCount ≤ _
      rw [CommitmentRef.termCount_point]
      omega

variable {G : Type*} [DecidableEq G] [Inhabited G]

/-- The grouped term count of the deployed queries fits the shape budget: at most one set per
query, at most one member per query per set, at most one term per quotient piece plus one per
member. -/
theorem constructIntermediateSets_termCount_le {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ic : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    (constructIntermediateSets (assembleQueries vk ic ps ch)).termCount
      ≤ queryBudget shape * (queryBudget shape * (shape.numQuotientPieces + 1)) := by
  classical
  have hqlen := assembleQueries_length_le vk ic ps ch
  rw [MultiopenGrouped.termCount]
  refine le_trans (List.sum_le_card_nsmul _
    (queryBudget shape * (shape.numQuotientPieces + 1)) ?_) ?_
  · intro n hn
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hn
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
    have hgetD : (constructIntermediateSets (assembleQueries vk ic ps ch)).sets.getD i []
        = (constructIntermediateSets (assembleQueries vk ic ps ch)).sets[i] :=
      List.getD_eq_getElem _ _ hi
    refine le_trans (List.sum_le_card_nsmul _ (shape.numQuotientPieces + 1) ?_) ?_
    · intro t ht
      obtain ⟨member, hmember, rfl⟩ := List.mem_map.mp ht
      obtain ⟨q, hq, hqc⟩ := constructIntermediateSets_sets_getD_commitment_mem
        (assembleQueries vk ic ps ch) i (by rw [hgetD]; exact hmember)
      rw [hqc]
      exact assembleQueries_commitment_termCount_le vk ic ps ch hq
    · rw [List.length_map, smul_eq_mul]
      refine Nat.mul_le_mul_right _ ?_
      calc (constructIntermediateSets (assembleQueries vk ic ps ch)).sets[i].length
          = ((constructIntermediateSets (assembleQueries vk ic ps ch)).sets.getD i []).length :=
            by rw [hgetD]
        _ ≤ (assembleQueries vk ic ps ch).length :=
            constructIntermediateSets_sets_getD_length_le _ i
        _ ≤ queryBudget shape := hqlen
  · rw [List.length_map, smul_eq_mul]
    exact Nat.mul_le_mul_right _
      (le_trans (constructIntermediateSets_sets_length_le _) hqlen)

/-- Modeled group-operation cost of one deployed acceptance check: evaluating the assembled
fingerprint MSM sweeps the `2 ^ k + 2` fixed generators and each accumulated term.  A rejected
assembly evaluates nothing. -/
def deployedAssembleGroupOps {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ic : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) : ℕ :=
  match assemble? vk ic ps ch with
  | some msm => 2 ^ shape.k + 2 + msm.other.length
  | none => 0

/-- Shape-level envelope for one acceptance evaluation: the generator sweep, the grouped query
terms, and the quotient and IPA tail. -/
def assembleGroupOpsBudget (shape : Shape) : ℕ :=
  2 ^ shape.k + 2 +
    (queryBudget shape * (queryBudget shape * (shape.numQuotientPieces + 1)) +
      2 * shape.k + 2)

/-- **One acceptance evaluation fits the shape budget.**  The bound holds per run at the actual
assembled MSM, with no adversary-dependent quantity. -/
theorem deployedAssembleGroupOps_le {shape : Shape}
    (vk : VerifyingKey shape Fp G) (ic : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    deployedAssembleGroupOps vk ic ps ch ≤ assembleGroupOpsBudget shape := by
  rw [deployedAssembleGroupOps]
  split
  case h_2 => exact Nat.zero_le _
  case h_1 msm hmsm =>
      rw [assemble?] at hmsm
      split at hmsm
      case isFalse => exact absurd hmsm (by simp)
      case isTrue =>
        split at hmsm
        case isTrue => exact absurd hmsm (by simp)
        case isFalse =>
          split at hmsm
          case h_2 => exact absurd hmsm (by simp)
          case h_1 grouped hgrouped =>
              split at hmsm
              case isFalse => exact absurd hmsm (by simp)
              case isTrue =>
                  rw [constructIntermediateSets?] at hgrouped
                  split at hgrouped
                  case isTrue => exact absurd hgrouped (by simp)
                  case isFalse =>
                      cases hgrouped
                      have hlen := assembleFinalMsm?_other_length_le ps ch _ hmsm
                      have hterm := constructIntermediateSets_termCount_le vk ic ps ch
                      rw [assembleGroupOpsBudget]
                      omega

end Zcash.Snark
