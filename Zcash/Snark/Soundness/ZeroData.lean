import Zcash.Snark.Soundness.Deployed.Verification

/-!
# Zero-data multiopen assembly

The multiopen commitment is an MSM assembled from commitment references.  When every referenced
group element is zero — a zero proof string, zero instance commitments, and a verifying key whose
two group-valued commitment families are zero — the assembled MSM evaluates to the zero point for
*every* challenge record and every basis, whatever the (real, nonzero) scalar layout data says.
The layouts choose *which* zero point each query references; they never introduce a nonzero one.

This is the keystone a constant zero-data prover family needs at a non-degenerate shape: its
`multiopen_repr` obligation becomes `0 = 0`.  The proof is structural — a zero-data invariant
carried through `assembleQueries`, `constructIntermediateSets`, `compressSet`, and
`multiopenCombine` — so no literal layout list is ever unfolded.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm URS)

variable {k : ℕ} {F G : Type*}

/-! ## The MSM invariant -/

/-- An MSM whose basis scalars vanish and whose appended points are all the zero point.  Such an
MSM evaluates to zero against every URS. -/
def MsmZeroData [Zero F] [Zero G] (m : Msm k F G) : Prop :=
  (∀ i, m.gScalars i = 0) ∧ m.wScalar = 0 ∧ m.uScalar = 0 ∧ ∀ t ∈ m.other, t.2 = (0 : G)

theorem msmZeroData_zero [Zero F] [Zero G] : MsmZeroData (Msm.zero k F G) :=
  ⟨fun _ => rfl, rfl, rfl, fun _t ht => absurd ht List.not_mem_nil⟩

theorem msmZeroData_appendTerm [Zero F] [Zero G] {m : Msm k F G}
    (h : MsmZeroData m) (c : F) :
    MsmZeroData (m.appendTerm c (0 : G)) := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro t ht
  rcases List.mem_cons.mp ht with h0 | hmem
  · rw [h0]
  · exact h.2.2.2 t hmem

theorem msmZeroData_scale [MulZeroClass F] [Zero G] {m : Msm k F G}
    (h : MsmZeroData m) (c : F) :
    MsmZeroData (m.scale c) := by
  refine ⟨fun i => ?_, ?_, ?_, ?_⟩
  · show c * m.gScalars i = 0
    rw [h.1 i, mul_zero]
  · show c * m.wScalar = 0
    rw [h.2.1, mul_zero]
  · show c * m.uScalar = 0
    rw [h.2.2.1, mul_zero]
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact h.2.2.2 s hs

theorem msmZeroData_add [AddZeroClass F] [Zero G] {m₁ m₂ : Msm k F G}
    (h₁ : MsmZeroData m₁) (h₂ : MsmZeroData m₂) :
    MsmZeroData (m₁.add m₂) := by
  refine ⟨fun i => ?_, ?_, ?_, ?_⟩
  · show m₁.gScalars i + m₂.gScalars i = 0
    rw [h₁.1 i, h₂.1 i, add_zero]
  · show m₁.wScalar + m₂.wScalar = 0
    rw [h₁.2.1, h₂.2.1, add_zero]
  · show m₁.uScalar + m₂.uScalar = 0
    rw [h₁.2.2.1, h₂.2.2.1, add_zero]
  · intro t ht
    rcases List.mem_append.mp ht with hmem | hmem
    · exact h₁.2.2.2 t hmem
    · exact h₂.2.2.2 t hmem

/-- A zero-data MSM evaluates to the zero point against every URS. -/
theorem msmZeroData_eval [Field F] [AddCommGroup G] [Module F G] {urs : URS G}
    {m : Msm urs.k F G} (h : MsmZeroData m) : m.eval urs = 0 := by
  unfold Msm.eval
  rw [Finset.sum_congr rfl (fun i _ => by rw [h.1 i, zero_smul]), Finset.sum_const_zero,
    h.2.1, h.2.2.1, zero_smul, zero_smul, List.sum_eq_zero]
  · simp
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    rw [h.2.2.2 t ht, smul_zero]

/-! ## The commitment-reference invariant -/

/-- A commitment reference whose group content is zero: a zero point, or a zero-data MSM. -/
def refZeroData [Zero F] [Zero G] : CommitmentRef k F G → Prop
  | .point p => p = 0
  | .msm m => MsmZeroData m

/-- A zero-data reference contributes the zero point to the MSM. -/
theorem refZeroData_eval [Field F] [AddCommGroup G] [Module F G] {urs : URS G}
    {ref : CommitmentRef urs.k F G} (h : refZeroData ref) :
    ref.eval urs = 0 := by
  cases ref with
  | point p => exact h
  | msm m => exact msmZeroData_eval h

theorem refZeroData_accumulate [Field F] [Zero G] {c : CommitmentRef k F G}
    (hc : refZeroData c) {acc : Msm k F G} (hacc : MsmZeroData acc) (pow : F) :
    MsmZeroData (accumulateCommitment pow c acc) := by
  cases c with
  | point p =>
      show MsmZeroData (acc.appendTerm pow p)
      have hp : p = 0 := hc
      rw [hp]
      exact msmZeroData_appendTerm hacc pow
  | msm m =>
      exact msmZeroData_add hacc (msmZeroData_scale hc pow)

/-- The folded `h` commitment over zero pieces is a zero-data MSM. -/
theorem msmZeroData_vanishingHCommitment [Field F] [Zero G] (xn : F)
    (hPieces : List G) (hzero : ∀ p ∈ hPieces, p = (0 : G)) :
    MsmZeroData (vanishingHCommitment k xn hPieces) := by
  unfold vanishingHCommitment
  have hgen : ∀ (l : List G), (∀ p ∈ l, p = (0 : G)) → ∀ (acc : Msm k F G), MsmZeroData acc →
      MsmZeroData (l.foldl (fun acc c => (acc.scale xn).appendTerm (1 : F) c) acc) := by
    intro l
    induction l with
    | nil => exact fun _ acc h => h
    | cons p l ih =>
        intro hl acc hacc
        rw [List.foldl_cons]
        refine ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ ?_
        rw [hl p List.mem_cons_self]
        exact msmZeroData_appendTerm (msmZeroData_scale hacc xn) 1
  exact hgen _ (fun p hp => hzero p (List.mem_reverse.mp hp)) _ msmZeroData_zero

/-! ## The zero proof string -/

/-- The all-zero proof string, at any shape.  The permutation `lastEval` options follow the
deployed schedule — `some 0` for every set except the last — so the string is well-formed at
shapes with real permutation sets, not only at the degenerate witness shape. -/
def zeroProofString (shape : Shape) (F G : Type*) [Zero F] [Zero G] : ProofString shape F G :=
  { adviceCommitments := fun _ _ => 0, lookupPermutedInput := fun _ _ => 0,
    lookupPermutedTable := fun _ _ => 0, permutationProduct := fun _ _ => 0,
    lookupProduct := fun _ _ => 0, vanishingRandom := 0, hPieces := fun _ => 0,
    instanceEvals := fun _ _ => 0, adviceEvals := fun _ _ => 0,
    fixedEvals := fun _ => 0, vanishingRandomEval := 0,
    permutationCommonEvals := fun _ => 0,
    permutationSetEvals := fun _ s =>
      ⟨0, 0, if (s : ℕ) + 1 < shape.numPermutationSets then some 0 else none⟩,
    lookupEvals := fun _ _ => ⟨0, 0, 0, 0, 0⟩, multiopenQPrime := 0,
    multiopenU := fun _ => 0, ipaS := 0, ipaRounds := fun _ => (0, 0),
    ipaC := 0, ipaF := 0 }


/-! ## Every assembled query references zero group content -/

/-- Column queries over a zero commitment family reference only zero points. -/
theorem columnQueries_refZeroData [Field F] [Zero G] (omega x : F)
    (commitment : ℕ → G) (hcomm : ∀ i, commitment i = 0)
    (mkId : ℕ → CommitmentId) (layout : List (ℕ × ℤ)) (evals : List F) :
    ∀ q ∈ columnQueries (k := k) omega x commitment mkId layout evals,
      refZeroData q.commitment := by
  intro q hq
  obtain ⟨e, _he, rfl⟩ := List.mem_map.mp hq
  exact hcomm e.1.1

/-- `finFnG` of the zero family is zero everywhere once the default is zero. -/
theorem finFnG_zero [Inhabited G] [Zero G] (hdefault : (default : G) = 0) {n : ℕ} (i : ℕ) :
    finFnG (fun _ : Fin n => (0 : G)) i = 0 := by
  unfold finFnG
  split
  · rfl
  · exact hdefault

/-- Every query assembled from zero data references zero group content, whatever the layouts. -/
theorem assembleQueries_refZeroData {shape : Shape} [Field F] [Inhabited G] [Zero G]
    (hdefault : (default : G) = 0)
    (vk : VerifyingKey shape F G)
    (hfixed : ∀ i, vk.fixedCommitment i = 0)
    (hperm : ∀ i, vk.permutationCommonCommitment i = 0)
    (ic : Fin shape.numProofs → ℕ → G) (hic : ∀ p i, ic p i = 0)
    (ch : Challenges shape.k F) :
    ∀ q ∈ assembleQueries vk ic (zeroProofString shape F G) ch,
      refZeroData q.commitment := by
  intro q hq
  simp only [assembleQueries] at hq
  rcases List.mem_append.mp hq with hq | hq
  · rcases List.mem_append.mp hq with hq | hq
    · rcases List.mem_append.mp hq with hq | hq
      · -- per-proof queries
        obtain ⟨lqs, hlqs, hqmem⟩ := List.mem_flatten.mp hq
        obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hlqs
        rcases List.mem_append.mp hqmem with hqm | hqm
        · rcases List.mem_append.mp hqm with hqm | hqm
          · rcases List.mem_append.mp hqm with hqm | hqm
            · -- instance-column queries
              exact columnQueries_refZeroData _ _ _ (hic p) _ _ _ q hqm
            · -- advice-column queries through `finFnG`
              exact columnQueries_refZeroData _ _ _ (finFnG_zero hdefault) _ _ _ q hqm
          · -- permutation product queries: zero product commitments
            rcases List.mem_append.mp hqm with hqm | hqm
            · obtain ⟨s, hs, hqm⟩ := List.mem_flatMap.mp hqm
              obtain ⟨hzip, -⟩ := List.of_mem_zip hs
              obtain ⟨j, hj⟩ := List.mem_ofFn.mp hzip
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hqm
              rcases hqm with h0 | h0 <;>
                (rw [h0]; show s.1.1 = 0; rw [← hj]; rfl)
            · -- the `xLast` block also references only the zero product commitments
              obtain ⟨s, hs, hsome⟩ := List.mem_filterMap.mp hqm
              have hsmem := List.mem_reverse.mp (List.mem_of_mem_drop hs)
              obtain ⟨hzip, -⟩ := List.of_mem_zip hsmem
              obtain ⟨j, hj⟩ := List.mem_ofFn.mp hzip
              obtain ⟨le, -, hq⟩ := Option.map_eq_some_iff.mp hsome
              rw [← hq]
              show s.1.1 = 0
              rw [← hj]; rfl
        · -- lookup queries: all three commitments are the zero point
          obtain ⟨l, hl, hqm⟩ := List.mem_flatMap.mp hqm
          obtain ⟨hlmem, -⟩ := List.of_mem_zip hl
          obtain ⟨j, hj⟩ := List.mem_ofFn.mp hlmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hqm
          rcases hqm with h0 | h0 | h0 | h0 | h0 <;>
            first
            | (rw [h0]; show l.1.1.product = 0; rw [← hj]; rfl)
            | (rw [h0]; show l.1.1.permutedInput = 0; rw [← hj]; rfl)
            | (rw [h0]; show l.1.1.permutedTable = 0; rw [← hj]; rfl)
      · -- fixed-column queries: zero key commitments
        exact columnQueries_refZeroData _ _ _ hfixed _ _ _ q hq
    · -- common permutation queries: zero key commitments
      obtain ⟨ce, hce, rfl⟩ := List.mem_map.mp hq
      obtain ⟨hmem, -⟩ := List.of_mem_zip hce
      obtain ⟨c, hc⟩ := List.mem_ofFn.mp hmem
      show ce.1.1 = 0
      rw [← hc]
      exact hperm c

  · -- vanishing queries: the folded `h` MSM over zero pieces, and the zero random point
    rcases List.mem_cons.mp hq with h0 | hq
    · rw [h0]
      show MsmZeroData _
      refine msmZeroData_vanishingHCommitment _ _ ?_
      intro p hp
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      rfl
    · rcases List.mem_cons.mp hq with h0 | hq
      · rw [h0]; rfl
      · exact absurd hq List.not_mem_nil

/-! ## Provenance through the grouping -/

/-- Elements of a conditional-append fold come from the seed or are images of list elements. -/
private theorem mem_foldl_collect {α β : Type*} (g : α → β) (c : List β → α → Bool) :
    ∀ (l : List α) (init : List β) (b : β),
      b ∈ l.foldl (fun acc a => if c acc a then acc else acc ++ [g a]) init →
      b ∈ init ∨ ∃ a ∈ l, b = g a
  | [], _init, _b, hb => Or.inl hb
  | a :: l, init, b, hb => by
      rw [List.foldl_cons] at hb
      rcases mem_foldl_collect g c l _ b hb with hstep | ⟨a', ha', rfl⟩
      · by_cases hc : c init a
        · rw [if_pos hc] at hstep
          exact Or.inl hstep
        · rw [if_neg hc] at hstep
          rcases List.mem_append.mp hstep with h | h
          · exact Or.inl h
          · exact Or.inr ⟨a, List.mem_cons_self, List.mem_singleton.mp h⟩
      · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', rfl⟩

/-- Every commitment reference routed into a point set is the commitment of one of the assembled
queries: the grouping reorders and deduplicates, but never invents a reference. -/
theorem constructIntermediateSets_sets_ref_provenance [DecidableEq F] [DecidableEq G]
    (queries : List (VerifierQuery k F G))
    {set : List (CommitmentRef k F G × List F)}
    (hset : set ∈ (constructIntermediateSets queries).sets)
    {qc : CommitmentRef k F G × List F} (hqc : qc ∈ set) :
    ∃ q ∈ queries, qc.1 = q.commitment := by
  simp only [constructIntermediateSets] at hset
  obtain ⟨si, _hsi, rfl⟩ := List.mem_map.mp hset
  obtain ⟨cd, hcd, rfl⟩ := List.mem_map.mp hqc
  have hcd' := List.mem_reverse.mp (List.mem_of_mem_filter hcd)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcd'
  rcases mem_foldl_collect (fun q : VerifierQuery k F G => (q.commId, q.commitment)) _
      queries [] c hc with h | ⟨q, hq, rfl⟩
  · exact absurd h List.not_mem_nil
  · exact ⟨q, hq, rfl⟩

/-! ## Compression and combination preserve the invariant -/

/-- Compressing a point set whose member references all carry zero group content yields a
zero-data MSM. -/
theorem compressSet_fst_zeroData [Field F] [Zero G] (x1 : F)
    (setQueries : List (CommitmentRef k F G × List F)) (numPoints : ℕ)
    (hzero : ∀ qc ∈ setQueries, refZeroData qc.1) :
    MsmZeroData (compressSet x1 setQueries numPoints).1 := by
  unfold compressSet
  have hgen : ∀ (l : List (CommitmentRef k F G × List F)),
      (∀ qc ∈ l, refZeroData qc.1) → ∀ (st : Msm k F G × List F × F), MsmZeroData st.1 →
      MsmZeroData (l.foldl (fun (st : Msm k F G × List F × F) qc =>
        (accumulateCommitment st.2.2 qc.1 st.1,
         (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
         st.2.2 * x1)) st).1 := by
    intro l
    induction l with
    | nil => exact fun _ _st h => h
    | cons qc l ih =>
        intro hl st hst
        rw [List.foldl_cons]
        exact ih (fun qc' hqc' => hl qc' (List.mem_cons_of_mem _ hqc')) _
          (refZeroData_accumulate (hl qc List.mem_cons_self) hst st.2.2)
  exact hgen _ hzero _ msmZeroData_zero

/-- The `x₄` collapse of zero-data compressed commitments against a zero `q′` stays zero-data. -/
theorem multiopenCombine_fst_zeroData [Field F] [Zero G] (x4 : F) {qPrime : G}
    (hqPrime : qPrime = 0) (qCommitments : List (Msm k F G)) (u : List F) (msmEval : F)
    (hzero : ∀ m ∈ qCommitments, MsmZeroData m) :
    MsmZeroData (multiopenCombine x4 qPrime qCommitments u msmEval (Msm.zero k F G)).1 := by
  unfold multiopenCombine
  have hgen : ∀ (l : List (Msm k F G × F)),
      (∀ p ∈ l, MsmZeroData p.1) → ∀ (st : Msm k F G × F), MsmZeroData st.1 →
      MsmZeroData (l.foldl
        (fun (st : Msm k F G × F) p => ((st.1.scale x4).add p.1, st.2 * x4 + p.2)) st).1 := by
    intro l
    induction l with
    | nil => exact fun _ _st h => h
    | cons p l ih =>
        intro hl st hst
        rw [List.foldl_cons]
        exact ih (fun p' hp' => hl p' (List.mem_cons_of_mem _ hp')) _
          (msmZeroData_add (msmZeroData_scale hst x4) (hl p List.mem_cons_self))
  refine hgen _ ?_ _ ?_
  · intro p hp
    exact hzero p.1 (List.of_mem_zip hp).1
  · rw [hqPrime]
    exact msmZeroData_appendTerm msmZeroData_zero 1

/-! ## The keystone -/

/-- **The assembled multiopen MSM of zero data is zero-data, at every shape.**  A verifying key
whose two group-valued commitment families are zero, zero instance commitments, and the zero proof
string assemble — through whatever scalar layouts the key carries — an MSM whose basis scalars
vanish and whose every appended point is the zero point. -/
theorem assembledMsm_zeroData {shape : Shape} [Field F] [DecidableEq F]
    [DecidableEq G] [Inhabited G] [Zero G]
    (hdefault : (default : G) = 0)
    (vk : VerifyingKey shape F G)
    (hfixed : ∀ i, vk.fixedCommitment i = 0)
    (hperm : ∀ i, vk.permutationCommonCommitment i = 0)
    (ic : Fin shape.numProofs → ℕ → G) (hic : ∀ p i, ic p i = 0)
    (ch : Challenges shape.k F) :
    MsmZeroData (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4
      (zeroProofString shape F G).multiopenQPrime
      (List.ofFn (zeroProofString shape F G).multiopenU)
      (constructIntermediateSets
        (assembleQueries vk ic (zeroProofString shape F G) ch))
      (Msm.zero shape.k F G)).1 := by
  unfold assembleOpening
  refine multiopenCombine_fst_zeroData _ rfl _ _ _ ?_
  intro m hm
  obtain ⟨msm, hmsm, rfl⟩ := List.mem_map.mp hm
  obtain ⟨sp, hsp, rfl⟩ := List.mem_map.mp hmsm
  refine compressSet_fst_zeroData _ _ _ ?_
  intro qc hqc
  obtain ⟨q, hq, hEq⟩ := constructIntermediateSets_sets_ref_provenance _
    (List.of_mem_zip hsp).1 hqc
  rw [hEq]
  exact assembleQueries_refZeroData hdefault vk hfixed hperm ic hic ch q hq

/-- **The multiopen commitment of zero data is the zero point, at every shape**, for every basis
and every challenge record. -/
theorem multiopenCommitment_zeroData {shape : Shape} [Field F] [DecidableEq F]
    [AddCommGroup G] [Module F G] [DecidableEq G] [Inhabited G]
    (hdefault : (default : G) = 0)
    (g : Fin (2 ^ shape.k) → G) (w u : G)
    (vk : VerifyingKey shape F G)
    (hfixed : ∀ i, vk.fixedCommitment i = 0)
    (hperm : ∀ i, vk.permutationCommonCommitment i = 0)
    (ic : Fin shape.numProofs → ℕ → G) (hic : ∀ p i, ic p i = 0)
    (ch : Challenges shape.k F) :
    multiopenCommitment g w u vk ic (zeroProofString shape F G) ch = 0 := by
  unfold multiopenCommitment
  exact msmZeroData_eval (assembledMsm_zeroData hdefault vk hfixed hperm ic hic ch)

end Zcash.Snark
