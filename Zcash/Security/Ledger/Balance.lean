import Mathlib
import Zcash.Security.Ledger.Effects

/-!
# Balance-subset: every nonzero spend is a committed output

The first Balance theorem, as a computed reduction. For a valid ledger, the nonzero
spends form a sub-multiset of the positioned outputs — each spend is the opening of the
output that created its commitment, at that output's leaf position, and no positioned
opening is spent twice — or the ledger's own data computes a `BalanceBreak`:

* a Merkle `Collision` — one height's compression collided, with both evaluations
  successful — when a spend's authentication path validates a leaf that is not the
  committed one;
* a `NoteCommitBreak`, when a spend's commitment matches an output's but their openings
  differ;
* a key-binding break, when two spends of one note tuple would otherwise have to reveal
  the same nullifier twice.

The shape of the argument (design doc, "The theorems"): the anchor pins each spend's
path to a prefix tree; position binding pins the leaf; `uncommitted_ne` rules out the
padding; the opening comparison pins the output or computes the note-commitment break;
and duplicate spends of one positioned opening are found by `findPair`, whose result is
certified as a two-element *sublist* — carrying "two distinct occurrences" with no index
arithmetic — so `nfOldEqOrBreak` and nullifier uniqueness finish.

Everything is a plain computable `def` per breaks-as-computed-data; the anchor index and
the duplicate pair are found by decidable search, so no data is conjured from the
validity hypothesis's existentials.
-/

namespace Zcash.Security.Ledger.Model

variable {F : Type*}
variable {G : Type*}
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*} {d : ℕ}

/-! ## Finding a duplicate, certified as a sublist -/

/-- Scan for the first two entries with equal images under `f`, returned in list order.
`findPair_spec` certifies them as a two-element sublist — which is what carries "two
distinct occurrences" without any index arithmetic — and `findPair_none` certifies that
a failed scan means the images are pairwise distinct. -/
def findPair {α β : Type*} [DecidableEq β] (f : α → β) : List α → Option (α × α)
  | [] => none
  | a :: t =>
    match t.find? fun b => f b = f a with
    | some b => some (a, b)
    | none => findPair f t

theorem findPair_spec {α β : Type*} [DecidableEq β] (f : α → β) :
    ∀ {l : List α} {a₁ a₂ : α}, findPair f l = some (a₁, a₂) →
      f a₁ = f a₂ ∧ List.Sublist [a₁, a₂] l
  | [], _, _, h => by simp [findPair] at h
  | a :: t, a₁, a₂, h => by
    rw [findPair] at h
    cases hf : t.find? fun b => f b = f a with
    | some b =>
        rw [hf] at h
        obtain ⟨rfl, rfl⟩ : a = a₁ ∧ b = a₂ := by simpa [eq_comm] using h
        refine ⟨?_, ?_⟩
        · have := List.find?_some hf
          simpa [eq_comm] using this
        · exact (List.singleton_sublist.mpr (List.mem_of_find?_eq_some hf)).cons_cons a
    | none =>
        rw [hf] at h
        obtain ⟨hfa, hsub⟩ := findPair_spec f h
        exact ⟨hfa, hsub.trans (List.sublist_cons_self a t)⟩

theorem findPair_none {α β : Type*} [DecidableEq β] (f : α → β) :
    ∀ {l : List α}, findPair f l = none → (l.map f).Nodup
  | [], _ => by simp
  | a :: t, h => by
    rw [findPair] at h
    cases hf : t.find? fun b => f b = f a with
    | some b => rw [hf] at h; exact absurd h (by simp)
    | none =>
        rw [hf] at h
        have hnot : ∀ b ∈ t, ¬ f b = f a := by
          have := List.find?_eq_none.mp hf
          simpa using this
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, findPair_none f h⟩
        obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
        exact hnot b hb hfb

/-! ## List plumbing: sublists and prefixes through the ledger's flat maps -/

/-- A pointwise sublist of chunks is a sublist of the flat maps. -/
theorem flatMap_sublist {α β : Type*} {l : List α} {g g' : α → List β}
    (h : ∀ x ∈ l, List.Sublist (g x) (g' x)) :
    List.Sublist (l.flatMap g) (l.flatMap g') := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.flatMap_cons]
      exact (h a (by simp)).append (ih fun x hx => h x (by simp [hx]))

theorem outputActions_prefix {l₁ l₂ : Ledger KW F G RHO PSI MHASH MENC MSG SIG d}
    (h : l₁ <+: l₂) : outputActions l₁ <+: outputActions l₂ := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨outputActions r, by simp [outputActions, List.flatMap_append]⟩

theorem nullifiers_prefix {l₁ l₂ : Ledger KW F G RHO PSI MHASH MENC MSG SIG d}
    (h : l₁ <+: l₂) : nullifiers l₁ <+: nullifiers l₂ := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨nullifiers r, by simp [nullifiers, List.flatMap_append]⟩

/-- Earlier prefixes of a ledger are prefixes of later ones. -/
theorem take_prefix_take {l : Ledger KW F G RHO PSI MHASH MENC MSG SIG d} {j i : ℕ}
    (h : j ≤ i) : l.take j <+: l.take i := by
  have : l.take j = (l.take i).take j := by
    rw [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact List.take_prefix j (l.take i)

/-- The spends' nullifiers sit inside the ledger's nullifier list, occurrence for
occurrence. -/
theorem spendActions_map_nf_sublist
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) :
    List.Sublist ((spendActions ledger i).map fun a => a.inst.nf_old)
      (nullifiers ledger) := by
  have h1 : List.Sublist ((spendActions ledger i).map fun a => a.inst.nf_old)
      (nullifiers (ledger.take i)) := by
    rw [spendActions, nullifiers, List.map_flatMap]
    exact flatMap_sublist fun tx _ => tx.actions.filter_sublist.map _
  exact h1.trans (nullifiers_prefix (List.take_prefix i ledger)).sublist

/-- Leaves and output actions correspond index for index. -/
theorem length_leafList (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) :
    (leafList ledger).length = (outputActions ledger).length := by
  rw [leafList_eq_map, List.length_map]

/-- A prefix agrees with the longer list at every index it has. -/
private theorem getElem_of_prefix {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) {p : ℕ}
    (hp : p < l₁.length) : l₂[p]'(lt_of_lt_of_le hp h.length_le) = l₁[p] := by
  obtain ⟨r, rfl⟩ := h
  exact List.getElem_append_left hp

@[simp] theorem length_positionedOutputs
    (ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d) (i : ℕ) :
    (positionedOutputs ledger i).length = (outputActions (ledger.take i)).length := by
  simp [positionedOutputs, outputOpenings]

/-- The `p`-th positioned output is the `p`-th output action's opening at position `p`. -/
theorem positionedOutputs_getElem
    {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG d} {i p : ℕ}
    (hp : p < (outputActions (ledger.take i)).length) :
    (positionedOutputs ledger i)[p]'(by simpa using hp)
      = ⟨p, outputOpening ((outputActions (ledger.take i))[p])⟩ := by
  simp [positionedOutputs, outputOpenings]

section Validity

variable [Field F] [AddCommGroup G] [Module F G]
variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- The break data a Balance violation computes: a tree-hash collision at one height, a
note-commitment opening collision, or a key-binding break on the two spends' key
witnesses. -/
inductive BalanceBreak (P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG)
    (kv : KeyBindingInterface KW G IVK NK) where
  | merkle (c : Merkle.Collision P.merkle)
  | noteCommit (b : NoteCommitBreak P)
  | keyBinding (w₁ w₂ : KW) (h : kv.Break w₁ w₂)

/-- A spend whose commitment `extract`-matches an output's, with a different opening,
computes a note-commitment break — `noteCommitBreakOfNe`'s spend-versus-output twin. -/
def noteCommitBreakOfOutputNe {inst₁ inst₂ : ActionInstance G MHASH RHO}
    {w₁ w₂ : ActionWitness KW F G RHO PSI MHASH MENC P.depth}
    (h₁ : ActionSatisfied P kv inst₁ w₁) (h₂ : ActionSatisfied P kv inst₂ w₂)
    (hx : P.extract w₁.cm_old = P.extract w₂.cm_new)
    (hne : (w₁.rcm_old, w₁.note_old) ≠ (w₂.rcm_new, w₂.note_new)) :
    NoteCommitBreak P :=
  ⟨_, _, _, _, _, _, hne, h₁.commit_old, h₂.commit_new, hx⟩

/-- Membership in the spends carries statement satisfaction and nonzero value. -/
theorem satisfied_of_spendMem
    (hval : ValidLedger P kv issuance maxActions ledger) {i : ℕ}
    {a : Action KW F G RHO PSI MHASH MENC SIG P.depth} (ha : a ∈ spendActions ledger i) :
    ActionSatisfied P kv a.inst a.w ∧ a.w.note_old.v ≠ 0 := by
  obtain ⟨tx, htx, hafil⟩ := List.mem_flatMap.mp ha
  have htx' : tx ∈ ledger := (List.take_sublist i ledger).subset htx
  refine ⟨hval.satisfied tx htx' a (List.mem_of_mem_filter hafil), ?_⟩
  simpa using (List.mem_filter.mp hafil).2

/-- A spend's anchor is the root after some prefix within range. -/
theorem anchor_of_spendMem
    (hval : ValidLedger P kv issuance maxActions ledger) {i : ℕ}
    {a : Action KW F G RHO PSI MHASH MENC SIG P.depth} (ha : a ∈ spendActions ledger i) :
    ∃ j, j ≤ i ∧ rootAfter P ledger j = some a.inst.rt := by
  obtain ⟨tx, htx, hafil⟩ := List.mem_flatMap.mp ha
  obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp htx
  have hki : k < i := lt_of_lt_of_le hk (by simp [List.length_take])
  have hkl : k < ledger.length := lt_of_lt_of_le hk (by simp [List.length_take])
  have hget : ledger.get ⟨k, hkl⟩ = tx := by
    rw [List.get_eq_getElem, ← List.getElem_take (h := hk)]
    exact hgetk
  obtain ⟨j, hjk, hrt⟩ := hval.anchor_valid ⟨k, hkl⟩ a
    (by rw [hget]; exact List.mem_of_mem_filter hafil)
  exact ⟨j, le_of_lt (lt_of_le_of_lt hjk hki), hrt⟩

/-- **Per-spend pinning.** A nonzero spend of a valid ledger is the positioned opening
of the output that created its commitment — or the ledger data computes a break. The
anchor prefix is recovered by decidable search (`Nat.find`), so the branches stay
computable. -/
def spendPinnedOrBreak [DecidableEq F] [DecidableEq G] [DecidableEq RHO]
    [DecidableEq PSI] [DecidableEq MHASH] [DecidableEq MENC]
    (hval : ValidLedger P kv issuance maxActions ledger) {i : ℕ}
    {a : Action KW F G RHO PSI MHASH MENC SIG P.depth} (ha : a ∈ spendActions ledger i) :
    (spendRecord a ∈ positionedOutputs ledger i) ⊕' BalanceBreak P kv :=
  have hex : ∃ j, j ≤ i ∧ rootAfter P ledger j = some a.inst.rt := anchor_of_spendMem hval ha
  let j := Nat.find hex
  have hji : j ≤ i := (Nat.find_spec hex).1
  have hpath : Merkle.Path P.merkle (P.extract a.w.cm_old) a.inst.rt a.w.path a.w.side :=
    (satisfied_of_spendMem hval ha).1.merkle_path (satisfied_of_spendMem hval ha).2
  have hroot : Merkle.root P.merkle (leafFun P (leafList (ledger.take j)))
      = some a.inst.rt := (Nat.find_spec hex).2
  if hleaf : P.extract a.w.cm_old = leafFun P (leafList (ledger.take j)) a.w.side then
    if hp : posVal a.w.side < (leafList (ledger.take j)).length then
      have hpa : posVal a.w.side < (outputActions (ledger.take j)).length := by
        rwa [← length_leafList]
      let out := (outputActions (ledger.take j))[posVal a.w.side]
      have hcx : P.extract a.w.cm_old = out.inst.cmx_new := by
        rw [hleaf, leafFun, List.getD_eq_getElem _ _ hp]
        have := leafList_eq_map (ledger.take j)
        simp only [out, this, List.getElem_map]
      have hout_sat : ActionSatisfied P kv out.inst out.w := by
        have hmem : out ∈ outputActions (ledger.take j) := List.getElem_mem hpa
        obtain ⟨tx, htx, hout⟩ := List.mem_flatMap.mp hmem
        exact hval.satisfied tx ((List.take_sublist j ledger).subset htx) out hout
      if hop : (⟨a.w.rcm_old, a.w.note_old⟩ : Opening F G RHO PSI) = outputOpening out then
        .inl (by
          have hpre : outputActions (ledger.take j) <+: outputActions (ledger.take i) :=
            outputActions_prefix (take_prefix_take hji)
          have hpi : posVal a.w.side < (outputActions (ledger.take i)).length :=
            lt_of_lt_of_le hpa hpre.length_le
          refine List.mem_iff_getElem.mpr ⟨posVal a.w.side, by simpa using hpi, ?_⟩
          rw [positionedOutputs_getElem hpi, getElem_of_prefix hpre hpa]
          rw [spendRecord, ← hop])
      else
        .inr (.noteCommit (noteCommitBreakOfOutputNe (satisfied_of_spendMem hval ha).1
          hout_sat (hcx.trans hout_sat.cmx_new_eq)
          (fun hpair => hop (by
            simp only [Prod.mk.injEq] at hpair
            simp [outputOpening, hpair.1, hpair.2]))))
    else
      absurd (by
          rw [hleaf, leafFun, List.getD_eq_default]
          omega) (P.uncommitted_ne a.w.cm_old)
  else
    .inr (.merkle (Merkle.collisionOfWrongLeaf P.merkle hpath hroot hleaf))

/-- Run the per-spend pinning over a list of spends, stopping at the first break. -/
def allPinnedOrBreak [DecidableEq F] [DecidableEq G] [DecidableEq RHO]
    [DecidableEq PSI] [DecidableEq MHASH] [DecidableEq MENC]
    (hval : ValidLedger P kv issuance maxActions ledger) {i : ℕ} :
    (L : List (Action KW F G RHO PSI MHASH MENC SIG P.depth)) →
    (∀ a ∈ L, a ∈ spendActions ledger i) →
    ((∀ a ∈ L, spendRecord a ∈ positionedOutputs ledger i) ⊕' BalanceBreak P kv)
  | [], _ => .inl (by simp)
  | a :: t, hL =>
    match spendPinnedOrBreak hval (hL a (by simp)) with
    | .inr b => .inr b
    | .inl hmem =>
      match allPinnedOrBreak hval t (fun x hx => hL x (by simp [hx])) with
      | .inr b => .inr b
      | .inl hall => .inl (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          exacts [hmem, hall x hx'])

/-- **Balance-subset, as a computed reduction.** For a valid ledger, the nonzero spends
are a sub-multiset of the positioned outputs — or the ledger data computes a
`BalanceBreak`. Duplicate spends are located by `findPair`; sharing a positioned opening
forces sharing a revealed nullifier (`nfOldEqOrBreak`), which nullifier uniqueness
forbids, so the surviving branch is a key-binding break. -/
def balanceSubsetOrBreak [DecidableEq F] [DecidableEq G] [DecidableEq RHO]
    [DecidableEq PSI] [DecidableEq MHASH] [DecidableEq MENC] [DecidableEq NK]
    [NoZeroSMulDivisors F G]
    (hval : ValidLedger P kv issuance maxActions ledger) (i : ℕ) :
    (nonZeroSpends ledger i ≤ ↑(positionedOutputs ledger i)) ⊕' BalanceBreak P kv :=
  match hfp : findPair spendRecord (spendActions ledger i) with
  | some (a₁, a₂) =>
      have hspec := findPair_spec spendRecord hfp
      have h₁ : a₁ ∈ spendActions ledger i := hspec.2.subset (by simp)
      have h₂ : a₂ ∈ spendActions ledger i := hspec.2.subset (by simp)
      have hrcm : a₁.w.rcm_old = a₂.w.rcm_old := by
        have := congrArg (fun r => r.opening.rcm) hspec.1
        simpa [spendRecord] using this
      have hnote : a₁.w.note_old = a₂.w.note_old := by
        have := congrArg (fun r => r.opening.note) hspec.1
        simpa [spendRecord] using this
      match nfOldEqOrBreak (satisfied_of_spendMem hval h₁).1
          (satisfied_of_spendMem hval h₂).1 hrcm hnote with
      | .inr hbr => .inr (.keyBinding a₁.w.kw a₂.w.kw hbr)
      | .inl hnf =>
          -- one nullifier at two distinct occurrences — impossible in a valid ledger
          have hsubnf : List.Sublist [a₁.inst.nf_old, a₂.inst.nf_old] (nullifiers ledger) := by
            have h := (hspec.2.map fun a => a.inst.nf_old).trans
              (spendActions_map_nf_sublist ledger i)
            simpa using h
          have hnd : [a₁.inst.nf_old, a₂.inst.nf_old].Nodup :=
            hval.nf_nodup.sublist hsubnf
          absurd hnf (by simpa using hnd)
  | none =>
      have hnodup : ((spendActions ledger i).map spendRecord).Nodup :=
        findPair_none spendRecord hfp
      match allPinnedOrBreak hval (spendActions ledger i) (fun _ h => h) with
      | .inr b => .inr b
      | .inl hall =>
          .inl (by
            rw [nonZeroSpends]
            refine (Multiset.le_iff_subset (by simpa using hnodup)).mpr ?_
            intro x hx
            obtain ⟨a, haL, rfl⟩ := List.mem_map.mp (by simpa using hx)
            simpa using hall a haL)

end Validity

end Zcash.Security.Ledger.Model
