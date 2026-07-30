import Mathlib.Tactic
import Zcash.Snark.Fingerprint.Rational.QueryTable
import Zcash.Snark.Fingerprint.Rational.QueryWalk
import Zcash.Snark.Fingerprint.Rational.IpaWalk
import Zcash.Snark.Fingerprint.Rational.OpeningWalk
import Zcash.Snark.Fingerprint.Epsilon
import Zcash.Snark.Soundness.Deployed.Verification

/-!
# The capstone: the assembled coefficient family

The final leg of the walk. The scalar coordinates of the assembled MSM are represented by the IPA
walk (`Rational/IpaWalk.lean`, fed the opening value from `Rational/OpeningWalk.lean`); what
remains is the `other` term list, **positionally** — `Msm.coeffAt (.term t)` reads position `t`
of the coefficient stream, so the ε theorem needs one fixed function per position, not a
permutation-quotient view.

* The generic stream lemmas compute `other` through every assembly stage: `ipaFold` prepends the
  round pairs and `ξ`, `multiopenCombine` scales the accumulated stream by `x₄` and appends each
  compressed set, `compressSet` prepends a point member's `x₁`-power and appends the vanishing
  member's `h`-piece block, and `vanishingHCommitment` carries the `xⁿ`-powers.
* On the good event the grouping is the fixed reference structure
  (`Rational/QueryTable.lean`), and every member's commitment constructor is fixed data
  (`refKind`): the one `.msm` member is the vanishing `h` commitment
  (`assembleQueries_commitment_char`). The mirrors (`mirrorPointFns`/`mirrorMsmFns`/
  `mirrorBlocks`/`ipaPrefixFns`) rebuild the stream as one fixed list of represented functions,
  and `assembleAt_other_map_fst` is the positional closed form.
* `assembleCoeffFamily` packages everything into the `RationalCoeffFamily`
  (`Fingerprint/Epsilon.lean`) the ε theorem consumes: per coefficient coordinate a numerator
  over `openDen` (`g`-block), the trivial denominator (`w`/`u`), or the IPA product denominator
  `ipaDen` (`other` terms — the round coefficients `uⱼ⁻¹` are the one denominator-bearing term
  family), all under the single degree cap `msmDegreeBudget`.
-/

namespace Zcash.Snark

open MvPolynomial
open Zcash.Arithmetic (Msm)

/-! ## `other`-projections of the MSM operations -/

section StreamOps

variable {k : ℕ} {F G : Type*}

@[simp] theorem appendTerm_other (c : F) (P : G) (m : Msm k F G) :
    (m.appendTerm c P).other = (c, P) :: m.other := rfl

@[simp] theorem scale_other [Mul F] (c : F) (m : Msm k F G) :
    (Msm.scale c m).other = m.other.map fun t => (c * t.1, t.2) := rfl

@[simp] theorem add_other [Add F] (m₁ m₂ : Msm k F G) :
    (m₁.add m₂).other = m₁.other ++ m₂.other := rfl

@[simp] theorem addToGScalars_other [Add F] [Zero F] (l : List F) (m : Msm k F G) :
    (m.addToGScalars l).other = m.other := rfl

@[simp] theorem addToUScalar_other [Add F] (c : F) (m : Msm k F G) :
    (m.addToUScalar c).other = m.other := rfl

@[simp] theorem addToWScalar_other [Add F] (c : F) (m : Msm k F G) :
    (m.addToWScalar c).other = m.other := rfl

/-- Scaling's coefficient stream is the scaled coefficient stream. -/
theorem scale_other_map_fst [Mul F] (c : F) (m : Msm k F G) :
    ((Msm.scale c m).other.map Prod.fst) = m.other.map fun t => c * t.1 := by
  simp [List.map_map, Function.comp_def]

end StreamOps

/-! ## The `other` list through the assembly stages -/

section StreamLemmas

variable {k : ℕ} {F G : Type*} [Field F]

/-- The per-round fold prepends `(uⱼ, Rⱼ), (uⱼ⁻¹, Lⱼ)` in reverse round order. -/
theorem foldl_appendTerm_pair_other (l : List ((G × G) × F)) :
    ∀ m : Msm k F G,
      (l.foldl (fun acc p => (acc.appendTerm p.2⁻¹ p.1.1).appendTerm p.2 p.1.2) m).other
        = (l.reverse.flatMap fun p => [(p.2, p.1.2), (p.2⁻¹, p.1.1)]) ++ m.other := by
  induction l with
  | nil => intro m; simp
  | cons a t ih =>
    intro m
    rw [List.foldl_cons, ih, List.reverse_cons, List.flatMap_append]
    simp [List.append_assoc]

/-- The IPA fold's term list: the round pairs in reverse order, the blinding term, then the
incoming multiopen terms. -/
theorem ipaFold_other (x v c f xi z : F) (u : List F) (S : G) (rounds : List (G × G))
    (m : Msm k F G) :
    (ipaFold x v c f xi z u S rounds m).other
      = ((rounds.zip u).reverse.flatMap fun p => [(p.2, p.1.2), (p.2⁻¹, p.1.1)])
        ++ (xi, S) :: m.other := by
  simp only [ipaFold, addToGScalars_other, addToUScalar_other, addToWScalar_other,
    foldl_appendTerm_pair_other, appendTerm_other]

/-- The vanishing `h` commitment's coefficient stream: the `xⁿ`-powers, ascending. -/
theorem scaleAppend_fold_other_map_fst (xn : F) (l : List G) :
    ∀ acc : Msm k F G,
      ((l.foldl (fun acc c => (acc.scale xn).appendTerm 1 c) acc).other.map Prod.fst)
        = (List.range l.length).map (fun i => xn ^ i)
          ++ (acc.other.map Prod.fst).map (fun c => xn ^ l.length * c) := by
  induction l with
  | nil =>
    intro acc
    simp
  | cons a t ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp only [appendTerm_other, List.map_cons, scale_other, List.map_map, List.length_cons,
      List.range_succ, List.map_append, List.append_assoc, mul_one]
    congr 1
    congr 1
    refine List.map_congr_left fun t' _ => ?_
    simp only [Function.comp_apply]
    rw [pow_succ]
    ring

/-- `vanishingHCommitment`'s coefficient stream is `[xn⁰, …, xn^(P−1)]`. -/
theorem vanishingHCommitment_other_map_fst (xn : F) (hs : List G) :
    ((vanishingHCommitment k xn hs).other.map Prod.fst)
      = (List.range hs.length).map (fun i => xn ^ i) := by
  rw [vanishingHCommitment]
  rw [scaleAppend_fold_other_map_fst]
  simp [Msm.zero]

/-- The point-member coefficients of one set's compression, in processing order: the running
`x₁`-power at each `.point` member. -/
def pointCoeffs (x1 : F) : List (CommitmentRef k F G × List F) → F → List F
  | [], _ => []
  | (c, _) :: rest, pow =>
    match c with
    | .point _ => pow :: pointCoeffs x1 rest (pow * x1)
    | .msm _ => pointCoeffs x1 rest (pow * x1)

/-- The MSM-member coefficient blocks of one set's compression: each `.msm` member's stream,
scaled by the running `x₁`-power, in processing order. -/
def msmCoeffs (x1 : F) : List (CommitmentRef k F G × List F) → F → List F
  | [], _ => []
  | (c, _) :: rest, pow =>
    match c with
    | .point _ => msmCoeffs x1 rest (pow * x1)
    | .msm mm => (mm.other.map fun t => pow * t.1) ++ msmCoeffs x1 rest (pow * x1)

/-- The compression fold's coefficient stream: reversed point coefficients, then the incoming
stream, then the MSM blocks. -/
theorem compress_fold_other_map_fst (x1 : F) (mems : List (CommitmentRef k F G × List F)) :
    ∀ (m : Msm k F G) (evs : List F) (pow : F),
      ((mems.foldl (fun (st : Msm k F G × List F × F) qc =>
          (accumulateCommitment st.2.2 qc.1 st.1,
           (st.2.1.zip qc.2).map (fun e => e.1 + e.2 * st.2.2),
           st.2.2 * x1)) (m, evs, pow)).1.other.map Prod.fst)
        = (pointCoeffs x1 mems pow).reverse ++ (m.other.map Prod.fst)
          ++ msmCoeffs x1 mems pow := by
  induction mems with
  | nil =>
    intro m evs pow
    simp [pointCoeffs, msmCoeffs]
  | cons qc rest ih =>
    intro m evs pow
    obtain ⟨c, evsQ⟩ := qc
    rw [List.foldl_cons]
    cases c with
    | point p =>
      rw [ih]
      simp only [accumulateCommitment, appendTerm_other, List.map_cons, pointCoeffs, msmCoeffs,
        List.reverse_cons, List.append_assoc, List.singleton_append]
    | msm mm =>
      rw [ih]
      simp only [accumulateCommitment, add_other, List.map_append, scale_other_map_fst,
        pointCoeffs, msmCoeffs, List.append_assoc]

/-- One compressed set's coefficient stream. -/
theorem compressSet_fst_other_map_fst (x1 : F) (mems : List (CommitmentRef k F G × List F))
    (numPoints : ℕ) :
    ((compressSet x1 mems numPoints).1.other.map Prod.fst)
      = (pointCoeffs x1 mems 1).reverse ++ msmCoeffs x1 mems 1 := by
  rw [compressSet]
  have h := compress_fold_other_map_fst x1 mems (Msm.zero k F G)
    (List.replicate numPoints (0 : F)) 1
  simpa [Msm.zero] using h

/-- The `x₄`-collapse's appended blocks: each set's terms, scaled by the power of `x₄` matching
its distance from the end. -/
def combineBlocks (x4 : F) : List (Msm k F G) → List (F × G)
  | [] => []
  | qc :: rest => (qc.other.map fun t => (x4 ^ rest.length * t.1, t.2)) ++ combineBlocks x4 rest

/-- The `x₄`-collapse fold's term list: the seed scaled by the full `x₄`-power, then the blocks. -/
theorem combine_fold_fst_other (x4 : F) (l : List (Msm k F G × F)) :
    ∀ (m : Msm k F G) (e : F),
      ((l.foldl (fun (st : Msm k F G × F) p => ((st.1.scale x4).add p.1, st.2 * x4 + p.2))
          (m, e)).1).other
        = (m.other.map fun t => (x4 ^ l.length * t.1, t.2))
          ++ combineBlocks x4 (l.map Prod.fst) := by
  induction l with
  | nil =>
    intro m e
    simp [combineBlocks]
  | cons a t ih =>
    intro m e
    rw [List.foldl_cons, ih]
    simp only [add_other, scale_other, List.map_append, List.map_map, List.map_cons,
      combineBlocks, List.length_cons, List.length_map, List.append_assoc]
    congr 1
    refine List.map_congr_left fun t' _ => ?_
    simp only [Function.comp_apply]
    rw [pow_succ]
    ring_nf

end StreamLemmas

/-! ## Which member is the MSM: the commitment characterization -/

section CommitmentChar

variable {shape : Shape} {G : Type*} [Inhabited G]

/-- Every assembled query either is the vanishing member — slot identity `.vanishingH`,
commitment the folded `h` MSM — or is a plain point commitment with a different identity. -/
theorem assembleQueries_commitment_char (vk : VerifyingKey shape Fp G)
    (ic : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) :
    ∀ q ∈ assembleQueries vk ic ps ch,
      (q.commId = .vanishingH
          ∧ q.commitment = .msm (vanishingHCommitment shape.k (ch.x ^ vk.n)
              (List.ofFn ps.hPieces)))
        ∨ (q.commId ≠ .vanishingH ∧ ∃ g, q.commitment = .point g) := by
  intro q hq
  rw [assembleQueries] at hq
  simp only [List.mem_append] at hq
  rcases hq with ((hq | hq) | hq) | hq
  · -- the per-proof blocks: four point-commitment builders
    obtain ⟨l, hl, hql⟩ := List.mem_flatten.mp hq
    obtain ⟨p, -, rfl⟩ := List.mem_ofFn.mp hl
    simp only [List.mem_append] at hql
    rcases hql with ((hql | hql) | hql) | hql
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hql
      exact Or.inr ⟨by simp, _, rfl⟩
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hql
      exact Or.inr ⟨by simp, _, rfl⟩
    · rw [permutationQueries] at hql
      simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_filterMap] at hql
      rcases hql with ⟨s, -, rfl | rfl⟩ | ⟨s, -, hmap⟩
      · exact Or.inr ⟨by simp, _, rfl⟩
      · exact Or.inr ⟨by simp, _, rfl⟩
      · obtain ⟨le, -, rfl⟩ := Option.map_eq_some_iff.mp hmap
        exact Or.inr ⟨by simp, _, rfl⟩
    · rw [lookupQueries] at hql
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hql
      obtain ⟨l', -, hq5⟩ := hql
      rcases hq5 with rfl | rfl | rfl | rfl | rfl <;> exact Or.inr ⟨by simp, _, rfl⟩
  · -- the fixed columns
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hq
    exact Or.inr ⟨by simp, _, rfl⟩
  · -- the common permutation columns
    rw [permutationCommonQueries] at hq
    obtain ⟨ce, -, rfl⟩ := List.mem_map.mp hq
    exact Or.inr ⟨by simp, _, rfl⟩
  · -- the vanishing block: the `h` MSM, then the random-poly point
    rw [vanishingQueries] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨by simp, _, rfl⟩

end CommitmentChar

/-! ## The fixed mirrors of the `other` stream -/

section Mirrors

variable (shape : Shape) {G : Type*} (vk : VerifyingKey shape Fp G)

/-- Whether a reference member decodes to the vanishing `h` MSM: its flat position carries the
`.vanishingH` slot identity. Out-of-range positions read the `.randomPoly` default, so the kind
is `false` there. -/
def refKind : CommitmentRef shape.k ℕ ℕ → Bool
  | .point n => decide ((queryCommIds shape vk).getD n .randomPoly = .vanishingH)
  | .msm _ => false

/-- The mirror of `pointCoeffs` over the fixed reference members: the running `x₁`-power
functions at the point members. -/
def mirrorPointFns : List (CommitmentRef shape.k ℕ ℕ × List ℕ) → (Point shape → Fp)
    → List (Point shape → Fp)
  | [], _ => []
  | (c, _) :: rest, powf =>
    if refKind shape vk c then
      mirrorPointFns rest (fun pt => powf pt * pt ScalarSlot.x1)
    else
      powf :: mirrorPointFns rest (fun pt => powf pt * pt ScalarSlot.x1)

/-- The mirror of `msmCoeffs`: the vanishing member's `xⁿ`-power block times the running
`x₁`-power. -/
def mirrorMsmFns : List (CommitmentRef shape.k ℕ ℕ × List ℕ) → (Point shape → Fp)
    → List (Point shape → Fp)
  | [], _ => []
  | (c, _) :: rest, powf =>
    if refKind shape vk c then
      (List.range shape.numQuotientPieces).map
          (fun i => fun pt => powf pt * (pt ScalarSlot.x ^ vk.n) ^ i)
        ++ mirrorMsmFns rest (fun pt => powf pt * pt ScalarSlot.x1)
    else
      mirrorMsmFns rest (fun pt => powf pt * pt ScalarSlot.x1)

/-- One reference set's compressed coefficient stream, mirrored. -/
def setFns (si : ℕ) : List (Point shape → Fp) :=
  (mirrorPointFns shape vk ((refSetsL shape vk).getD si []) (fun _ => 1)).reverse
    ++ mirrorMsmFns shape vk ((refSetsL shape vk).getD si []) (fun _ => 1)

/-- The mirror of `combineBlocks`: each set's functions scaled by its `x₄`-power. -/
def mirrorBlocks : List (List (Point shape → Fp)) → List (Point shape → Fp)
  | [] => []
  | fns :: rest =>
    fns.map (fun f => fun pt => pt ScalarSlot.x4 ^ rest.length * f pt) ++ mirrorBlocks rest

/-- The IPA prefix: per round, in reverse order, the challenge and its inverse. -/
def ipaPrefixFns : List (Point shape → Fp) :=
  (List.finRange shape.k).reverse.flatMap
    (fun j => [fun pt => pt (ScalarSlot.ipaRound j), fun pt => (pt (ScalarSlot.ipaRound j))⁻¹])

/-- The collapsed `q'` coefficient: the full `x₄`-power on the seed term. -/
def qPrimeCoeffFn : Point shape → Fp := fun pt => pt ScalarSlot.x4 ^ numSetsD shape vk * 1

/-- **The fixed coefficient-function list of the assembled `other` terms**, positionally: the
IPA prefix, the blinding coefficient `ξ`, the collapsed `q'` coefficient, then the per-set
blocks. On the good event the assembled coefficient stream is exactly this list evaluated at the
sample point (`assembleAt_other_map_fst`). -/
def otherCoeffFns : List (Point shape → Fp) :=
  ipaPrefixFns shape ++ [fun pt => pt ScalarSlot.xi] ++ [qPrimeCoeffFn shape vk]
    ++ mirrorBlocks shape ((List.range (numSetsD shape vk)).map (setFns shape vk))

/-- The assembled `other` length: the mirror's length, a verifying-key constant. -/
def otherLen : ℕ := (otherCoeffFns shape vk).length

end Mirrors

/-! ## The stream equality on the good event -/

section StreamEq

variable {shape : Shape} {G : Type*} [DecidableEq G] [Inhabited G]
variable (vk : VerifyingKey shape Fp G) (ic : Fin shape.numProofs → ℕ → G)
variable (base : ProofString shape Fp G)

/-- On the good event, the total assembly is the non-rejecting final MSM over the derived
grouping. -/
theorem assembleAt_eq_finalMsm {pt : Point shape} (hf : VkSymbolicFacts shape vk)
    (hgood : GoodEvent vk pt) :
    assembleAt vk ic base pt
      = assembleFinalMsm (Point.toProofString pt base) (Point.toChallenges pt)
          (constructIntermediateSets (assembleQueries vk ic (Point.toProofString pt base)
            (Point.toChallenges pt))) :=
  assemble?_eq_some vk ic _ _ (assembleAt_some vk ic base hf hgood)

omit [DecidableEq G] in
/-- The decoded commitment of a reference member, by kind: the vanishing `h` MSM exactly when
the kind is `true`, a plain point otherwise. -/
theorem decode_commitment_by_kind (pt : Point shape) (c : CommitmentRef shape.k ℕ ℕ)
    (idxs : List ℕ) :
    (if refKind shape vk c then
        (decodeMember (assembleQueries vk ic (Point.toProofString pt base)
          (Point.toChallenges pt)) (c, idxs)).1
          = .msm (vanishingHCommitment shape.k (pt ScalarSlot.x ^ vk.n)
              (List.ofFn base.hPieces))
      else
        ∃ g, (decodeMember (assembleQueries vk ic (Point.toProofString pt base)
          (Point.toChallenges pt)) (c, idxs)).1 = .point g) := by
  set qs := assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt) with hqs
  have hchar := assembleQueries_commitment_char vk ic (Point.toProofString pt base)
    (Point.toChallenges pt)
  have hlen : qs.length = (queryCommIds shape vk).length := by
    have := assembleQueries_map_commId vk ic pt base
    rw [hqs, ← this, List.length_map]
  cases c with
  | msm mm =>
    rw [refKind, if_neg (by simp)]
    exact ⟨default, rfl⟩
  | point n =>
    rcases lt_or_ge n qs.length with hn | hn
    · have hmem : qs.getD n default ∈ qs := by
        rw [List.getD_eq_getElem _ _ hn]
        exact List.getElem_mem hn
      have hid : (qs.getD n default).commId = (queryCommIds shape vk).getD n .randomPoly := by
        exact map_getD_eq (assembleQueries_map_commId vk ic pt base) hn default .randomPoly
      rcases hchar _ hmem with ⟨hvan, hcomm⟩ | ⟨hvan, g, hcomm⟩
      · rw [refKind, if_pos (by rw [decide_eq_true_iff, ← hid]; exact hvan)]
        rw [decodeMember, hcomm]
        simp
      · rw [refKind, if_neg (by rw [decide_eq_true_iff, ← hid]; exact hvan)]
        exact ⟨g, hcomm⟩
    · have hkind : refKind shape vk (.point n) = false := by
        rw [refKind, decide_eq_false_iff_not]
        rw [List.getD_eq_default _ _ (by omega)]
        simp
      rw [hkind, if_neg (by simp)]
      refine ⟨default, ?_⟩
      rw [decodeMember, List.getD_eq_default _ _ hn]
      rfl

omit [DecidableEq G] [Inhabited G] in
/-- The vanishing member's coefficient stream at a sample point. -/
theorem hComm_stream (pt : Point shape) :
    ((vanishingHCommitment shape.k (pt ScalarSlot.x ^ vk.n)
        (List.ofFn base.hPieces)).other.map Prod.fst)
      = (List.range shape.numQuotientPieces).map
          (fun i => (pt ScalarSlot.x ^ vk.n) ^ i) := by
  rw [vanishingHCommitment_other_map_fst, List.length_ofFn]

omit [DecidableEq G] in
/-- Decoding one reference member list's point coefficients yields the mirror at the sample
point. -/
theorem pointCoeffs_decode (pt : Point shape)
    (mems : List (CommitmentRef shape.k ℕ ℕ × List ℕ)) :
    ∀ powf : Point shape → Fp,
      pointCoeffs (pt ScalarSlot.x1)
          (mems.map (decodeMember (assembleQueries vk ic (Point.toProofString pt base)
            (Point.toChallenges pt)))) (powf pt)
        = (mirrorPointFns shape vk mems powf).map (· pt) := by
  induction mems with
  | nil => intro powf; rfl
  | cons mem rest ih =>
    intro powf
    obtain ⟨c, idxs⟩ := mem
    have hdec := decode_commitment_by_kind vk ic base pt c idxs
    rw [List.map_cons, mirrorPointFns]
    have hpair : decodeMember (assembleQueries vk ic (Point.toProofString pt base)
        (Point.toChallenges pt)) (c, idxs)
        = ((decodeMember (assembleQueries vk ic (Point.toProofString pt base)
            (Point.toChallenges pt)) (c, idxs)).1,
          (decodeMember (assembleQueries vk ic (Point.toProofString pt base)
            (Point.toChallenges pt)) (c, idxs)).2) := rfl
    by_cases hk : refKind shape vk c
    · rw [if_pos hk] at hdec ⊢
      rw [hpair, hdec]
      simp only [pointCoeffs]
      exact ih (fun pt' => powf pt' * pt' ScalarSlot.x1)
    · rw [if_neg hk] at hdec ⊢
      obtain ⟨g, hg⟩ := hdec
      rw [hpair, hg]
      simp only [pointCoeffs, List.map_cons]
      exact congrArg (powf pt :: ·) (ih (fun pt' => powf pt' * pt' ScalarSlot.x1))

omit [DecidableEq G] in
/-- Decoding one reference member list's MSM blocks yields the mirror at the sample point. -/
theorem msmCoeffs_decode (pt : Point shape)
    (mems : List (CommitmentRef shape.k ℕ ℕ × List ℕ)) :
    ∀ powf : Point shape → Fp,
      msmCoeffs (pt ScalarSlot.x1)
          (mems.map (decodeMember (assembleQueries vk ic (Point.toProofString pt base)
            (Point.toChallenges pt)))) (powf pt)
        = (mirrorMsmFns shape vk mems powf).map (· pt) := by
  induction mems with
  | nil => intro powf; rfl
  | cons mem rest ih =>
    intro powf
    obtain ⟨c, idxs⟩ := mem
    have hdec := decode_commitment_by_kind vk ic base pt c idxs
    rw [List.map_cons, mirrorMsmFns]
    have hpair : decodeMember (assembleQueries vk ic (Point.toProofString pt base)
        (Point.toChallenges pt)) (c, idxs)
        = ((decodeMember (assembleQueries vk ic (Point.toProofString pt base)
            (Point.toChallenges pt)) (c, idxs)).1,
          (decodeMember (assembleQueries vk ic (Point.toProofString pt base)
            (Point.toChallenges pt)) (c, idxs)).2) := rfl
    by_cases hk : refKind shape vk c
    · rw [if_pos hk] at hdec ⊢
      rw [hpair, hdec]
      simp only [msmCoeffs, List.map_append]
      congr 1
      · have hstr := hComm_stream vk base pt
        calc ((vanishingHCommitment shape.k (pt ScalarSlot.x ^ vk.n)
              (List.ofFn base.hPieces)).other.map fun t => powf pt * t.1)
            = ((vanishingHCommitment shape.k (pt ScalarSlot.x ^ vk.n)
                (List.ofFn base.hPieces)).other.map Prod.fst).map (fun c' => powf pt * c') := by
              rw [List.map_map]; rfl
          _ = ((List.range shape.numQuotientPieces).map
                (fun i => (pt ScalarSlot.x ^ vk.n) ^ i)).map (fun c' => powf pt * c') := by
              rw [hstr]
          _ = ((List.range shape.numQuotientPieces).map
                (fun i => fun pt' => powf pt' * (pt' ScalarSlot.x ^ vk.n) ^ i)).map (· pt) := by
              rw [List.map_map, List.map_map]; rfl
      · exact ih (fun pt' => powf pt' * pt' ScalarSlot.x1)
    · rw [if_neg hk] at hdec ⊢
      obtain ⟨g, hg⟩ := hdec
      rw [hpair, hg]
      simp only [msmCoeffs]
      exact ih (fun pt' => powf pt' * pt' ScalarSlot.x1)

omit [DecidableEq G] in
set_option maxHeartbeats 800000 in
/-- One decoded set's compressed coefficient stream is the mirrored set functions at the
point. -/
theorem setStream_decode (pt : Point shape) (si : ℕ) (numPoints : ℕ) :
    ((compressSet (pt ScalarSlot.x1)
        (((refSetsL shape vk).getD si []).map (decodeMember
          (assembleQueries vk ic (Point.toProofString pt base) (Point.toChallenges pt))))
        numPoints).1.other.map Prod.fst)
      = (setFns shape vk si).map (· pt) := by
  rw [compressSet_fst_other_map_fst, setFns, List.map_append, List.map_reverse]
  congr 1
  · exact congrArg List.reverse
      (pointCoeffs_decode vk ic base pt ((refSetsL shape vk).getD si []) (fun _ => 1))
  · exact msmCoeffs_decode vk ic base pt ((refSetsL shape vk).getD si []) (fun _ => 1)

omit [DecidableEq G] [Inhabited G] in
/-- The `x₄`-blocks of a list of value MSMs with mirrored streams are the mirrored blocks. -/
theorem combineBlocks_stream {α : Type*} (pt : Point shape) (l : List α)
    (valF : α → Msm shape.k Fp G) (mirF : α → List (Point shape → Fp))
    (h : ∀ s ∈ l, ((valF s).other.map Prod.fst) = (mirF s).map (· pt)) :
    ((combineBlocks (pt ScalarSlot.x4) (l.map valF)).map Prod.fst)
      = (mirrorBlocks shape (l.map mirF)).map (· pt) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, combineBlocks, mirrorBlocks, List.map_append, List.length_map]
    rw [ih (fun s hs => h s (List.mem_cons_of_mem _ hs))]
    congr 1
    rw [List.map_map, List.map_map]
    have ha := h a List.mem_cons_self
    calc ((valF a).other.map fun t => pt ScalarSlot.x4 ^ rest.length * t.1)
        = ((valF a).other.map Prod.fst).map (fun c => pt ScalarSlot.x4 ^ rest.length * c) := by
          rw [List.map_map]; rfl
      _ = ((mirF a).map (· pt)).map (fun c => pt ScalarSlot.x4 ^ rest.length * c) := by rw [ha]
      _ = (mirF a).map ((· pt) ∘ fun f => fun pt' => pt' ScalarSlot.x4 ^ rest.length * f pt') := by
          rw [List.map_map]; rfl

set_option maxHeartbeats 1000000 in
/-- **The positional `other` stream.** On the good event, the assembled MSM's coefficient
stream is the fixed mirror evaluated at the sample point. -/
theorem assembleAt_other_map_fst {pt : Point shape} (hf : VkSymbolicFacts shape vk)
    (hgood : GoodEvent vk pt) :
    ((assembleAt vk ic base pt).other.map Prod.fst)
      = (otherCoeffFns shape vk).map (· pt) := by
  classical
  set ps := Point.toProofString pt base with hps
  set ch := Point.toChallenges pt with hch
  set qs := assembleQueries vk ic ps ch with hqs
  have hS : numSetsD shape vk = shape.numPointSets := hf.ref_numSets
  have hPlen : (refPointsL shape vk).length = numSetsD shape vk :=
    (constructIntermediateSets_points_length (refTable shape vk)).symm
  -- normal forms for the grouping and the u-list (the `openingValue_eq` idiom)
  have hsetsR : (constructIntermediateSets qs).sets
      = (List.range (numSetsD shape vk)).map (fun si =>
          ((refSetsL shape vk).getD si []).map (decodeMember qs)) := by
    rw [hqs, hps, hch, grouped_sets_eq vk ic base hf hgood]
    conv_lhs => rw [show (constructIntermediateSets (refTable shape vk)).sets
      = refSetsL shape vk from rfl, self_eq_range_map_getD (refSetsL shape vk)]
    rw [List.map_map]
    rfl
  have hptsR : (constructIntermediateSets qs).points
      = (List.range (numSetsD shape vk)).map (fun si =>
          (classRotsL shape vk si).map (fun r => pt ScalarSlot.x * vk.omega ^ r)) := by
    rw [hqs, hps, hch, grouped_points_eq vk ic base hf hgood]
    conv_lhs => rw [show (constructIntermediateSets (refTable shape vk)).points
      = refPointsL shape vk from rfl, self_eq_range_map_getD (refPointsL shape vk)]
    rw [List.map_map, hPlen]
    refine List.map_congr_left fun si _ => ?_
    exact points_decode vk si pt
  have hu : List.ofFn ps.multiopenU
      = (List.range (numSetsD shape vk)).map (fun si => uAt (shape := shape) si pt) := by
    rw [hps, u_ofFn_eq base pt, hS]
  -- the final MSM and its IPA layer
  rw [assembleAt_eq_finalMsm vk ic base hf hgood, ← hps, ← hch, ← hqs, assembleFinalMsm]
  rw [ipaFold_other, List.map_append, List.map_cons]
  -- the multiopen layer: normalize every list to a map over `range numSetsD`, then read the
  -- collapse fold's term list off `combine_fold_fst_other`
  rw [assembleOpening, multiopenCombine, hsetsR, hptsR, hu]
  simp only [List.map_map, zip_map_same]
  rw [combine_fold_fst_other]
  simp only [List.map_map, appendTerm_other, Msm.zero, List.map_cons, List.map_nil,
    List.length_map, List.length_range, List.singleton_append]
  -- the three content pieces
  have hipa : (((List.ofFn ps.ipaRounds).zip (List.ofFn ch.ipaRound)).reverse.flatMap
        (fun p => [(p.2, p.1.2), (p.2⁻¹, p.1.1)])).map Prod.fst
      = (ipaPrefixFns shape).map (· pt) := by
    rw [hps, hch]
    show (((List.ofFn base.ipaRounds).zip
        (List.ofFn fun j => pt (ScalarSlot.ipaRound j))).reverse.flatMap
          fun p => [(p.2, p.1.2), (p.2⁻¹, p.1.1)]).map Prod.fst
      = (ipaPrefixFns shape).map (· pt)
    rw [List.map_flatMap, List.ofFn_eq_map, List.ofFn_eq_map, zip_map_same,
      ← List.map_reverse, List.flatMap_map, ipaPrefixFns, List.map_flatMap]
    rfl
  have hblocks : ((combineBlocks (pt ScalarSlot.x4) ((List.range (numSetsD shape vk)).map
        (fun si => (compressSet (pt ScalarSlot.x1)
          (((refSetsL shape vk).getD si []).map (decodeMember qs))
          ((classRotsL shape vk si).map (fun r => pt ScalarSlot.x * vk.omega ^ r)).length).1))).map
        Prod.fst)
      = (mirrorBlocks shape ((List.range (numSetsD shape vk)).map (setFns shape vk))).map
          (· pt) :=
    combineBlocks_stream (G := G) pt (List.range (numSetsD shape vk))
      (fun si => (compressSet (pt ScalarSlot.x1)
        (((refSetsL shape vk).getD si []).map (decodeMember qs))
        ((classRotsL shape vk si).map (fun r => pt ScalarSlot.x * vk.omega ^ r)).length).1)
      (setFns shape vk)
      (fun si _ => setStream_decode vk ic base pt si
        ((classRotsL shape vk si).map (fun r => pt ScalarSlot.x * vk.omega ^ r)).length)
  -- assemble
  rw [otherCoeffFns]
  simp only [List.map_append, List.map_cons, List.map_nil, List.singleton_append,
    List.append_assoc]
  rw [← hipa, ← hblocks, hch]
  rfl

/-- The assembled `other` length is the mirror's, on the whole good event. -/
theorem assembleAt_other_length {pt : Point shape} (hf : VkSymbolicFacts shape vk)
    (hgood : GoodEvent vk pt) :
    (assembleAt vk ic base pt).other.length = otherLen shape vk := by
  have h := congrArg List.length (assembleAt_other_map_fst vk ic base hf hgood)
  simpa [otherLen] using h

end StreamEq

/-! ## Representations of the `other` coefficients -/

section OtherReps

variable {shape : Shape} {G : Type*} {vk : VerifyingKey shape Fp G}

/-- The IPA product denominator: every round challenge, once. The one denominator the `other`
coefficients need — the per-round `uⱼ⁻¹` terms sit over their own factor, everything else over
`1`, and all extend to this single product. -/
noncomputable def ipaDen (shape : Shape) : MvPolynomial (ScalarSlot shape) Fp :=
  ∏ j : Fin shape.k, X (ScalarSlot.ipaRound j)

/-- Every round challenge is an enumerated denominator factor. -/
theorem ipaRound_mem_denFactors (j : Fin shape.k) :
    (X (ScalarSlot.ipaRound j) : MvPolynomial (ScalarSlot shape) Fp) ∈ denFactors vk := by
  simp only [denFactors, List.mem_append]
  exact Or.inr (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)

/-- The IPA denominator is a product of enumerated factors. -/
theorem ipaDen_mem :
    ipaDen shape
      ∈ Submonoid.closure {φ : MvPolynomial (ScalarSlot shape) Fp | φ ∈ denFactors vk} := by
  rw [ipaDen]
  exact Submonoid.prod_mem _ fun j _ =>
    Submonoid.subset_closure (ipaRound_mem_denFactors (vk := vk) j)

/-- The IPA denominator's degree is at most the round count. -/
theorem ipaDen_totalDegree_le : (ipaDen shape).totalDegree ≤ shape.k := by
  rw [ipaDen]
  refine le_trans (totalDegree_finsetProd _ _) ?_
  calc (∑ j : Fin shape.k, (X (ScalarSlot.ipaRound j) :
        MvPolynomial (ScalarSlot shape) Fp).totalDegree)
      ≤ ∑ _j : Fin shape.k, 1 := Finset.sum_le_sum fun j _ => by simp [totalDegree_X]
    _ = shape.k := by simp

/-- Lift a trivial-denominator representation to the IPA denominator. -/
theorem NumeratorRep.extendToIpaDen {f : Point shape → Fp} {d : ℕ}
    (h : NumeratorRep vk 1 f d) : NumeratorRep vk (ipaDen shape) f (d + shape.k) := by
  have hext := (h.extend (ipaDen shape)).denCongr (one_mul (ipaDen shape))
  exact hext.mono (Nat.add_le_add le_rfl ipaDen_totalDegree_le)

/-- A round challenge's inverse, over the IPA denominator. -/
theorem ipaInv_rep_ipaDen (j : Fin shape.k) :
    NumeratorRep vk (ipaDen shape) (fun pt => (pt (ScalarSlot.ipaRound j))⁻¹) shape.k := by
  have hbase : NumeratorRep vk (X (ScalarSlot.ipaRound j))
      (fun pt => (pt (ScalarSlot.ipaRound j))⁻¹) 0 :=
    (NumeratorRep.invFactor (vk := vk) (X (ScalarSlot.ipaRound j))
      (ipaRound_mem_denFactors j)).congr_event fun pt _ => by simp
  have hext := hbase.extend (∏ j' ∈ Finset.univ.erase j, X (ScalarSlot.ipaRound j'))
  have hden : X (ScalarSlot.ipaRound j) * ∏ j' ∈ Finset.univ.erase j,
      X (ScalarSlot.ipaRound j') = ipaDen shape := by
    rw [ipaDen]
    exact Finset.mul_prod_erase (Finset.univ : Finset (Fin shape.k))
      (fun j' => (X (ScalarSlot.ipaRound j') : MvPolynomial (ScalarSlot shape) Fp))
      (Finset.mem_univ j)
  refine (hext.denCongr hden).mono ?_
  have hdeg : ((∏ j' ∈ Finset.univ.erase j, X (ScalarSlot.ipaRound j') :
      MvPolynomial (ScalarSlot shape) Fp)).totalDegree ≤ shape.k := by
    refine le_trans (totalDegree_finsetProd _ _) ?_
    calc (∑ j' ∈ Finset.univ.erase j, (X (ScalarSlot.ipaRound j') :
          MvPolynomial (ScalarSlot shape) Fp).totalDegree)
        ≤ ∑ _j' ∈ Finset.univ.erase j, 1 := Finset.sum_le_sum fun j' _ => by simp [totalDegree_X]
      _ = (Finset.univ.erase j).card := by simp
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.erase_subset _ _)
      _ = shape.k := by simp
  omega

/-- Every set's member count stays under the member budget. -/
theorem members_length_le (si : ℕ) :
    ((refSetsL shape vk).getD si []).length ≤ memberBudget vk := by
  rcases lt_or_ge si (refSetsL shape vk).length with hsi | hsi
  · refine le_foldr_max (List.mem_map.mpr ⟨(refSetsL shape vk).getD si [], ?_, rfl⟩)
    rw [List.getD_eq_getElem _ _ hsi]
    exact List.getElem_mem hsi
  · rw [List.getD_eq_default _ _ hsi]
    simp

/-- The mirror entries of one member list are represented over the trivial denominator: the
running power chain costs one degree per member, the vanishing block up to `n` per quotient
piece. -/
theorem mirrorPointMsm_rep (mems : List (CommitmentRef shape.k ℕ ℕ × List ℕ)) :
    ∀ (powf : Point shape → Fp) (d : ℕ), NumeratorRep vk 1 powf d →
      (∀ f ∈ mirrorPointFns shape vk mems powf,
          NumeratorRep vk 1 f (d + mems.length + vk.n * shape.numQuotientPieces))
        ∧ ∀ f ∈ mirrorMsmFns shape vk mems powf,
            NumeratorRep vk 1 f (d + mems.length + vk.n * shape.numQuotientPieces) := by
  induction mems with
  | nil =>
    intro powf d hpow
    exact ⟨fun f hf => absurd hf List.not_mem_nil, fun f hf => absurd hf List.not_mem_nil⟩
  | cons mem rest ih =>
    intro powf d hpow
    obtain ⟨c, idxs⟩ := mem
    have hpow' : NumeratorRep vk 1 (fun pt => powf pt * pt ScalarSlot.x1) (d + 1) :=
      (hpow.mul (NumeratorRep.var ScalarSlot.x1)).denCongr (one_mul 1)
    obtain ⟨ihp, ihm⟩ := ih (fun pt => powf pt * pt ScalarSlot.x1) (d + 1) hpow'
    constructor
    · intro f hf
      rw [mirrorPointFns] at hf
      split at hf
      · exact (ihp f hf).mono (by simp only [List.length_cons]; omega)
      · rcases List.mem_cons.mp hf with rfl | hf'
        · exact hpow.mono (by omega)
        · exact (ihp f hf').mono (by simp only [List.length_cons]; omega)
    · intro f hf
      rw [mirrorMsmFns] at hf
      split at hf
      · rcases List.mem_append.mp hf with hf' | hf'
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf'
          rw [List.mem_range] at hi
          have hxn : NumeratorRep vk 1 (fun pt => (pt ScalarSlot.x ^ vk.n) ^ i)
              (i * (vk.n * 1)) :=
            ((((NumeratorRep.var (vk := vk) ScalarSlot.x).pow vk.n).denCongr
              (one_pow vk.n)).pow i).denCongr (one_pow i)
          refine ((hpow.mul hxn).denCongr (one_mul 1)).mono ?_
          have hile : i * (vk.n * 1) ≤ vk.n * shape.numQuotientPieces := by
            have hip : i ≤ shape.numQuotientPieces := by omega
            calc i * (vk.n * 1) = vk.n * i := by ring
              _ ≤ vk.n * shape.numQuotientPieces := Nat.mul_le_mul_left _ hip
          simp only [List.length_cons]
          omega
        · exact (ihm f hf').mono (by simp only [List.length_cons]; omega)
      · exact (ihm f hf).mono (by simp only [List.length_cons]; omega)

/-- One set's mirrored stream is represented over the trivial denominator. -/
theorem setFns_rep (si : ℕ) :
    ∀ f ∈ setFns shape vk si,
      NumeratorRep vk 1 f (memberBudget vk + vk.n * shape.numQuotientPieces) := by
  intro f hf
  rw [setFns] at hf
  obtain ⟨hp, hm⟩ := mirrorPointMsm_rep (vk := vk) ((refSetsL shape vk).getD si [])
    (fun _ => 1) 0 (NumeratorRep.const 1)
  have hlen := members_length_le (vk := vk) si
  rcases List.mem_append.mp hf with hf' | hf'
  · exact (hp f (List.mem_reverse.mp hf')).mono (by omega)
  · exact (hm f hf').mono (by omega)

/-- The mirrored `x₄`-blocks are represented over the trivial denominator. -/
theorem mirrorBlocks_rep (ls : List (List (Point shape → Fp))) (d : ℕ)
    (h : ∀ fns ∈ ls, ∀ f ∈ fns, NumeratorRep vk 1 f d) :
    ∀ f ∈ mirrorBlocks shape ls, NumeratorRep vk 1 f (d + ls.length) := by
  induction ls with
  | nil => intro f hf; exact absurd hf List.not_mem_nil
  | cons fns rest ih =>
    intro f hf
    rw [mirrorBlocks] at hf
    rcases List.mem_append.mp hf with hf' | hf'
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf'
      have hx4 : NumeratorRep vk 1 (fun pt => pt ScalarSlot.x4 ^ rest.length)
          (rest.length * 1) :=
        ((NumeratorRep.var (vk := vk) ScalarSlot.x4).pow rest.length).denCongr
          (one_pow rest.length)
      refine ((hx4.mul (h fns List.mem_cons_self g hg)).denCongr (one_mul 1)).mono ?_
      simp only [List.length_cons]
      omega
    · exact (ih (fun fns' hf'' => h fns' (List.mem_cons_of_mem _ hf'')) f hf').mono
        (by simp only [List.length_cons]; omega)

/-- Degree budget for one assembled `other` coefficient over `ipaDen`. -/
def otherCoeffBudget (shape : Shape) {G : Type*} (vk : VerifyingKey shape Fp G) : ℕ :=
  memberBudget vk + vk.n * shape.numQuotientPieces + numSetsD shape vk + shape.k + 2

/-- **Every mirrored `other` coefficient is represented over the IPA denominator** at the
`otherCoeffBudget` cap. -/
theorem otherCoeffFns_rep :
    ∀ f ∈ otherCoeffFns shape vk,
      NumeratorRep vk (ipaDen shape) f (otherCoeffBudget shape vk) := by
  intro f hf
  rw [otherCoeffFns] at hf
  rcases List.mem_append.mp hf with hf | hfblocks
  · rcases List.mem_append.mp hf with hf | hfq
    · rcases List.mem_append.mp hf with hfipa | hfxi
      · -- the IPA prefix: challenges and their inverses
        rw [ipaPrefixFns] at hfipa
        obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hfipa
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact ((NumeratorRep.var _).extendToIpaDen).mono (by rw [otherCoeffBudget]; omega)
        · exact (ipaInv_rep_ipaDen j).mono (by rw [otherCoeffBudget]; omega)
      · -- the blinding coefficient
        simp only [List.mem_singleton] at hfxi
        subst hfxi
        exact ((NumeratorRep.var _).extendToIpaDen).mono (by rw [otherCoeffBudget]; omega)
    · -- the collapsed q' coefficient
      simp only [List.mem_singleton] at hfq
      subst hfq
      have hx4 : NumeratorRep vk 1 (fun pt => pt ScalarSlot.x4 ^ numSetsD shape vk)
          (numSetsD shape vk * 1) :=
        ((NumeratorRep.var (vk := vk) ScalarSlot.x4).pow (numSetsD shape vk)).denCongr
          (one_pow _)
      have hq : NumeratorRep vk 1 (qPrimeCoeffFn shape vk) (numSetsD shape vk * 1 + 0) :=
        (hx4.mul (NumeratorRep.const 1)).denCongr (one_mul 1)
      exact hq.extendToIpaDen.mono (by rw [otherCoeffBudget]; omega)
  · -- the per-set blocks
    have hb := mirrorBlocks_rep ((List.range (numSetsD shape vk)).map (setFns shape vk))
      (memberBudget vk + vk.n * shape.numQuotientPieces)
      (fun fns hfns => by
        obtain ⟨si, -, rfl⟩ := List.mem_map.mp hfns
        exact setFns_rep si)
      f hfblocks
    rw [List.length_map, List.length_range] at hb
    exact hb.extendToIpaDen.mono (by rw [otherCoeffBudget]; omega)

end OtherReps

/-! ## The coefficient family -/

section Family

variable {shape : Shape} {G : Type*} [DecidableEq G] [Inhabited G]
variable (vk : VerifyingKey shape Fp G) (ic : Fin shape.numProofs → ℕ → G)
variable (base : ProofString shape Fp G)

/-- The opening value as a function of the sample point — the exact composite
`assembleFinalMsm` computes (`Rational/OpeningWalk.lean` represents it over `openDen`). -/
def openValueFn : Point shape → Fp := fun pt =>
  (assembleOpening (Point.toChallenges pt).x1 (Point.toChallenges pt).x2
      (Point.toChallenges pt).x3 (Point.toChallenges pt).x4
      ((Point.toProofString pt base).multiopenQPrime)
      (List.ofFn ((Point.toProofString pt base).multiopenU))
      (constructIntermediateSets (assembleQueries vk ic (Point.toProofString pt base)
        (Point.toChallenges pt)))
      (Msm.zero shape.k Fp G)).2

/-- The per-coordinate denominators of the assembled coefficient family. -/
noncomputable def coordDen : MsmCoord shape.k (otherLen shape vk)
    → MvPolynomial (ScalarSlot shape) Fp
  | .g _ => openDen shape vk
  | .w => 1
  | .u => 1
  | .term _ => ipaDen shape

/-- The per-coordinate closed-form coefficient functions of the assembled MSM. -/
def coordFn : MsmCoord shape.k (otherLen shape vk) → Point shape → Fp
  | .g i => fun pt =>
      [-(openValueFn vk ic base pt)].getD i.val 0
        + (computeS (List.ofFn fun j => pt (ScalarSlot.ipaRound j))
            (-(pt ScalarSlot.ipaC))).getD i.val 0
  | .w => fun pt => -(pt ScalarSlot.ipaF)
  | .u => fun pt => -(pt ScalarSlot.ipaC)
      * computeB (pt ScalarSlot.x3) (List.ofFn fun j => pt (ScalarSlot.ipaRound j))
      * pt ScalarSlot.z
  | .term t => fun pt => ((otherCoeffFns shape vk).map (· pt)).getD t.val 0

/-- The uniform numerator-degree cap of the assembled coefficient family. -/
def msmDegreeBudget (shape : Shape) {G : Type*} (vk : VerifyingKey shape Fp G) : ℕ :=
  max (max (vBudget vk) (1 + shape.k + openDenBudget shape vk))
    (max (2 ^ shape.k + shape.k + 3) (otherCoeffBudget shape vk))

/-- The uniform denominator-degree cap of the assembled coefficient family. -/
def msmDenBudget (shape : Shape) {G : Type*} (vk : VerifyingKey shape Fp G) : ℕ :=
  max (openDenBudget shape vk) shape.k

/-- Every coordinate function is represented over its coordinate denominator at the uniform
cap. -/
theorem coordFn_rep (hf : VkSymbolicFacts shape vk)
    (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (hchunks : vk.permutationChunks.length = shape.numPermutationSets)
    (hPerm : 1 ≤ shape.numPermutationSets) :
    ∀ c : MsmCoord shape.k (otherLen shape vk),
      NumeratorRep vk (coordDen vk c) (coordFn vk ic base c) (msmDegreeBudget shape vk) := by
  intro c
  cases c with
  | g i =>
    have hv := openingValue_rep vk ic base hf hchunkW hchunks hPerm
    have hg := gScalars_coord_rep (vk := vk) hv (openDen_totalDegree_le shape vk) i
    exact hg.mono (by rw [msmDegreeBudget]; omega)
  | w => exact wScalar_rep.mono (by rw [msmDegreeBudget]; omega)
  | u => exact uScalar_rep.mono (by rw [msmDegreeBudget]; omega)
  | term t =>
    have hl : ListRep vk (ipaDen shape) (fun pt => (otherCoeffFns shape vk).map (· pt))
        (otherCoeffBudget shape vk) :=
      ⟨otherCoeffFns shape vk, fun pt => rfl, otherCoeffFns_rep⟩
    exact (hl.getD t.val).mono (by rw [msmDegreeBudget]; omega)

/-- On the good event, every assembled coefficient is its closed-form coordinate function. -/
theorem coordFn_agrees (hf : VkSymbolicFacts shape vk) {pt : Point shape}
    (hgood : GoodEvent vk pt) :
    ∀ c : MsmCoord shape.k (otherLen shape vk),
      (assembleAt vk ic base pt).coeffAt c = coordFn vk ic base c pt := by
  have heq := assembleAt_eq_finalMsm vk ic base hf hgood
  have hz := assembleQueries_grouped_gwuZero vk ic (Point.toProofString pt base)
    (Point.toChallenges pt)
  intro c
  cases c with
  | g i =>
    show (assembleAt vk ic base pt).gScalars i = _
    rw [heq, assembleFinalMsm_gScalars_of_gwuZero _ _ _ hz i]
    rfl
  | w =>
    show (assembleAt vk ic base pt).wScalar = _
    rw [heq, assembleFinalMsm_wScalar_of_gwuZero _ _ _ hz]
    rfl
  | u =>
    show (assembleAt vk ic base pt).uScalar = _
    rw [heq, assembleFinalMsm_uScalar_of_gwuZero _ _ _ hz]
    rfl
  | term t =>
    show (((assembleAt vk ic base pt).other.map Prod.fst).getD t.val 0) = _
    rw [assembleAt_other_map_fst vk ic base hf hgood]
    rfl

/-- **The assembled coefficient family**: the deployed assembly's coefficients,
as one `RationalCoeffFamily` — polynomial numerators over enumerated-factor denominators at the
`msmDegreeBudget`/`msmDenBudget` caps, agreeing with `assemble?` on the whole good event. This
is the object `competing_coefficient_family_agreement_le` consumes. -/
noncomputable def assembleCoeffFamily (hf : VkSymbolicFacts shape vk)
    (hchunkW : ∀ c ∈ vk.permutationChunks, c.length ≤ vk.chunkLen)
    (hchunks : vk.permutationChunks.length = shape.numPermutationSets)
    (hPerm : 1 ≤ shape.numPermutationSets) :
    RationalCoeffFamily vk ic base (otherLen shape vk) (msmDegreeBudget shape vk)
      (msmDenBudget shape vk) where
  num c := Classical.choose (coordFn_rep vk ic base hf hchunkW hchunks hPerm c)
  den := coordDen vk
  den_mem c := by
    cases c with
    | g i => exact openDen_mem shape vk
    | w => exact Submonoid.one_mem _
    | u => exact Submonoid.one_mem _
    | term t => exact ipaDen_mem
  num_totalDegree_le c :=
    (Classical.choose_spec (coordFn_rep vk ic base hf hchunkW hchunks hPerm c)).1
  den_totalDegree_le c := by
    cases c with
    | g i =>
      exact le_trans (openDen_totalDegree_le shape vk) (le_max_left _ _)
    | w => simp [coordDen, msmDenBudget]
    | u => simp [coordDen, msmDenBudget]
    | term t => exact le_trans ipaDen_totalDegree_le (le_max_right _ _)
  represents pt hgood :=
    ⟨assembleAt vk ic base pt, assembleAt_some vk ic base hf hgood,
      assembleAt_other_length vk ic base hf hgood,
      fun c => by
        rw [coordFn_agrees vk ic base hf hgood c]
        exact (Classical.choose_spec
          (coordFn_rep vk ic base hf hchunkW hchunks hPerm c)).2 pt hgood⟩

end Family

end Zcash.Snark
