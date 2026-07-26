import Zcash.Snark.Soundness.VestaBudget
import Zcash.Snark.Verifier.QueryCommitment

/-!
# Deriving the constraint feed bindings from the deployed decode

The constraint terminal (`orchard_verifier_vesta_member_constraints_terminal_derived`,
`Soundness.VestaBudget`) consumes feed and carrier bindings at `ch.x`: the fed columns, the
permutation carriers, the lookups and the Lagrange terms take the values the proof string claims.
This module derives those bindings instead of supplying them.

The route: deployed acceptance runs the rejecting grouping, so every opening query is routed to a
member slot with its claimed evaluation recorded faithfully
(`constructIntermediateSets_comm_routed` + `eq_of_not_hasDuplicateCommitmentPoint`); the member
node binding then pins the decoded member column to that recorded value at the query's point. So
each class's fed polynomial — the decoded column, rotated per the layout — takes the proof
string's own claim at `ch.x`, with the selections *produced* by the routing rather than assumed.

What acceptance supplies for free: the duplicate guard (slot determinism), the `u`-count guard
(the pair count is the set count), and the root-of-unity exclusion. The measure premises are the
same two floors the budgeted capstone carries: the honest-base `x₁` floor and the joint accept
floor.
-/

namespace Zcash.Snark

open Polynomial
open scoped ENNReal
open Classical

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-! ## What acceptance says about the grouping pipeline -/

/-- **The accept pipeline's grouping facts.** Deployed acceptance runs `assemble?`, which rejects
on a duplicate slot-and-point query and on a `u`-count mismatch — so acceptance itself supplies
the duplicate guard and the count identity. -/
theorem deployedAccepts_pipeline [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch) :
    hasDuplicateCommitmentPoint (assembleQueries vk instanceCommitment ps ch) = false ∧
    (List.ofFn ps.multiopenU).length
      = (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.length := by
  unfold DeployedAccepts at hacc
  rcases hasm : assemble? vk instanceCommitment ps ch with _ | m
  · rw [hasm] at hacc; exact hacc.elim
  rw [hasm] at hacc
  unfold assemble? at hasm
  by_cases hwf : proofStringWellFormed ps = true
  swap
  · rw [if_neg hwf] at hasm; exact absurd hasm (by simp)
  rw [if_pos hwf] at hasm
  by_cases hxn : ch.x ^ vk.n = (1 : Fp)
  · rw [if_pos hxn] at hasm; exact absurd hasm (by simp)
  rw [if_neg hxn] at hasm
  rcases hcis : constructIntermediateSets? (assembleQueries vk instanceCommitment ps ch) with _ | grouped
  · rw [hcis] at hasm; exact absurd hasm (by simp)
  simp only [hcis] at hasm
  have hdup : hasDuplicateCommitmentPoint (assembleQueries vk instanceCommitment ps ch) = false := by
    by_contra hd
    rw [Bool.not_eq_false] at hd
    rw [constructIntermediateSets?, if_pos hd] at hcis
    exact absurd hcis (by simp)
  have hgrouped : grouped = constructIntermediateSets (assembleQueries vk instanceCommitment ps ch) := by
    rw [constructIntermediateSets?, if_neg (by rw [hdup]; exact Bool.false_ne_true)] at hcis
    exact (Option.some.inj hcis).symm
  by_cases hx3 : multiopenPointsAvoidX3 ch.x3 grouped = true
  swap
  · rw [if_neg hx3] at hasm; exact absurd hasm (by simp)
  rw [if_pos hx3] at hasm
  unfold assembleFinalMsm? at hasm
  rcases hop : assembleOpening? ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime
      (List.ofFn ps.multiopenU) grouped (Msm.zero shape.k Fp G) with _ | opened
  · simp [hop] at hasm
  unfold assembleOpening? at hop
  by_cases hguard : (List.ofFn ps.multiopenU).length = grouped.sets.length ∧
      grouped.points.length = grouped.sets.length
  · exact ⟨hdup, hgrouped ▸ hguard.1⟩
  · rw [if_neg hguard] at hop; exact absurd hop (by simp)

/-- **Acceptance from the verifier equation, under the guards.** The equation-form acceptance
the algebraic family tests, upgraded to the pipeline form the deployed machinery consumes: with
the proof string well formed, the squeeze off the roots of unity, no duplicate slot-and-point
query, the `x₃` draw off the opened points, and the `u`-count matching, the assembler succeeds
and its MSM's evaluation is the equation's left side. The guards are exactly the priced panic
events (`card_vanishingPanic_le`, `card_multiopenPanic_le`) plus the structural counts. -/
theorem deployedAccepts_of_verifierEq_of_guards [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (heq : DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch)
    (hwf : proofStringWellFormed ps = true)
    (hxn : ch.x ^ vk.n ≠ 1)
    (hdup : hasDuplicateCommitmentPoint (assembleQueries vk instanceCommitment ps ch) = false)
    (hx3 : multiopenPointsAvoidX3 ch.x3
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) = true)
    (hu : (List.ofFn ps.multiopenU).length
        = (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.length ∧
      (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.length
        = (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.length) :
    DeployedAccepts urs hk vk instanceCommitment ps ch := by
  have hcis : constructIntermediateSets? (assembleQueries vk instanceCommitment ps ch)
      = some (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) := by
    rw [constructIntermediateSets?, if_neg (by rw [hdup]; exact Bool.false_ne_true)]
  have hop : assembleOpening? ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime
      (List.ofFn ps.multiopenU) (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch))
      (Msm.zero shape.k Fp G)
      = some (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime
        (List.ofFn ps.multiopenU) (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch))
        (Msm.zero shape.k Fp G)) := by
    rw [assembleOpening?, if_pos hu]
  have hsome : assemble? vk instanceCommitment ps ch
      = some (assembleFinalMsm ps ch
        (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch))) := by
    unfold assemble?
    rw [if_pos hwf, if_neg hxn, hcis]
    show (if multiopenPointsAvoidX3 ch.x3
        (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) = true then
      assembleFinalMsm? ps ch (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch))
      else none) = _
    rw [if_pos hx3]
    unfold assembleFinalMsm?
    rw [hop]
    rfl
  unfold DeployedAccepts
  rw [hsome]
  show (hk ▸ assembleFinalMsm ps ch
    (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) : Msm urs.k Fp G).eval urs = 0
  rw [eval_cast hk, deployed_verification_eq (hk ▸ urs.g) urs.w urs.u ps ch
    (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch))]
  exact heq

/-- **Acceptance pins the pair count to the set count.** The `x₄` pair list zips the per-set
aggregates against the `u` vector, and the accept pipeline's `u`-count guard makes the two
lengths equal — so every routed set index is an `x₄` pair index. -/
theorem deployedX4PairCount_eq_sets_length [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch) :
    deployedX4PairCount vk instanceCommitment ps ch
      = (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.length := by
  obtain ⟨-, hu⟩ := deployedAccepts_pipeline urs hk vk instanceCommitment ps ch hacc
  rw [deployedX4PairCount_eq, deployedX4Pairs, List.length_zip, deployedX4Qs]
  simp only [List.length_map, List.length_zip, hu,
    ← constructIntermediateSets_points_length (assembleQueries vk instanceCommitment ps ch), min_self]

/-! ## The deployed routing of a class query -/

/-- **Deployed slot routing.** Under acceptance, any opening query is routed to a member of an
`x₄`-paired point set: the member's recorded identity is the query's slot, the query's point is
among the set's points, and the recorded evaluation at that point's position is the query's own
claim. The selections every feed binding needs, produced from the run. -/
theorem deployed_query_routed [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch)
    {q : VerifierQuery shape.k Fp G} (hq : q ∈ assembleQueries vk instanceCommitment ps ch) :
    ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
      ∃ hm : 0 < (deployedSetQueries vk instanceCommitment ps ch i).length,
      ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀ = q.commId) ∧
        (∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) d₀).1 = q.commitment) ∧
        q.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
        ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
              q.point) 0
          = q.eval := by
  obtain ⟨hdup, -⟩ := deployedAccepts_pipeline urs hk vk instanceCommitment ps ch hacc
  obtain ⟨i, hi, m, hmlt, hids, hcomm, hpt, hev⟩ :=
    constructIntermediateSets_comm_routed (assembleQueries vk instanceCommitment ps ch) hq
      (fun q' hq' hid hpt =>
        congrArg VerifierQuery.eval (eq_of_not_hasDuplicateCommitmentPoint hdup hq hq' hid hpt))
      (fun q' hq' hid => assembleQueries_commitment_eq_of_commId vk instanceCommitment ps ch hq hq' hid)
  have hmlen : m < (deployedSetQueries vk instanceCommitment ps ch i).length := by
    show m < (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.zip
        (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points).getD i ([], [])).1.length
    rw [constructIntermediateSets_zip_sets_getD]
    exact hmlt
  refine ⟨i, ?_, lt_of_le_of_lt (Nat.zero_le _) hmlen, ⟨m, hmlen⟩, ?_, ?_, ?_, ?_⟩
  · rw [deployedX4PairCount_eq_sets_length urs hk vk instanceCommitment ps ch hacc]
    exact hi
  · intro c₀
    exact hids c₀
  · intro d₀
    show ((((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.zip
        (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points).getD i
          ([], [])).1.getD (m : ℕ) d₀).1 = q.commitment
    rw [constructIntermediateSets_zip_sets_getD]
    exact hcomm d₀
  · rw [deployedSetPts, List.mem_toFinset]
    exact hpt
  · have h := hev (.point 0, []) 0
    show ((((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.zip
        (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points).getD i
          ([], [])).1.getD (m : ℕ) (.point 0, [])).2.getD _ 0 = q.eval
    rw [constructIntermediateSets_zip_sets_getD]
    exact h

/-- **Deployed slot routing, all queries of one slot.** The single-member form of
`deployed_query_routed`: the slot is routed once, and every query on it reads its point and its
recorded claim off that one member — what the multi-rotation carriers consume. -/
theorem deployed_slot_routed_all [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch) {c : CommitmentId}
    {q₀ : VerifierQuery shape.k Fp G} (hq₀ : q₀ ∈ assembleQueries vk instanceCommitment ps ch)
    (hq₀c : q₀.commId = c) :
    ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
      ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀ = c) ∧
        (∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) d₀).1 = q₀.commitment) ∧
        ∀ q ∈ assembleQueries vk instanceCommitment ps ch, q.commId = c →
          q.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
          ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
              (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
                q.point) 0
            = q.eval := by
  obtain ⟨hdup, -⟩ := deployedAccepts_pipeline urs hk vk instanceCommitment ps ch hacc
  obtain ⟨i, hi, m, hmlt, hids, hcomm, hall⟩ :=
    constructIntermediateSets_comm_routed_all (assembleQueries vk instanceCommitment ps ch) hq₀ hq₀c
      (fun q hq q' hq' hid hpt =>
        congrArg VerifierQuery.eval
          (eq_of_not_hasDuplicateCommitmentPoint hdup hq' hq hid hpt))
      (fun q hq hid => assembleQueries_commitment_eq_of_commId vk instanceCommitment ps ch hq₀ hq
        (hid.trans hq₀c.symm))
  have hmlen : m < (deployedSetQueries vk instanceCommitment ps ch i).length := by
    show m < (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.zip
        (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points).getD i ([], [])).1.length
    rw [constructIntermediateSets_zip_sets_getD]
    exact hmlt
  refine ⟨i, ?_, ⟨m, hmlen⟩, hids, ?_, ?_⟩
  · rw [deployedX4PairCount_eq_sets_length urs hk vk instanceCommitment ps ch hacc]
    exact hi
  · intro d₀
    show ((((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.zip
        (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points).getD i
          ([], [])).1.getD (m : ℕ) d₀).1 = q₀.commitment
    rw [constructIntermediateSets_zip_sets_getD]
    exact hcomm d₀
  · intro q hq hqc
    obtain ⟨hpt, hev⟩ := hall q hq hqc
    refine ⟨by rw [deployedSetPts, List.mem_toFinset]; exact hpt, ?_⟩
    have h := hev (.point 0, []) 0
    show ((((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.zip
        (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points).getD i
          ([], [])).1.getD (m : ℕ) (.point 0, [])).2.getD _ 0 = q.eval
    rw [constructIntermediateSets_zip_sets_getD]
    exact h

/-- Canonical-commitment projection of `deployed_query_routed`: the routed member retains the
reference structurally named by the query's slot identity. -/
theorem deployed_query_routed_assembled [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch)
    {q : VerifierQuery shape.k Fp G} (hq : q ∈ assembleQueries vk instanceCommitment ps ch) :
    ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
      ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀ = q.commId) ∧
        (∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) d₀).1 =
          assembledCommitment vk instanceCommitment ps ch q.commId) ∧
        q.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
        ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
              q.point) 0 = q.eval := by
  obtain ⟨i, hi, -, m, hids, hcomm, hpt, hev⟩ :=
    deployed_query_routed urs hk vk instanceCommitment ps ch hacc hq
  have hcanonical := assembleQueries_commitment_eq_assembled vk instanceCommitment ps ch hq
  exact ⟨i, hi, m, hids, fun d₀ => (hcomm d₀).trans hcanonical, hpt, hev⟩

/-- Canonical-commitment projection for a whole multi-rotation slot. -/
theorem deployed_slot_routed_all_assembled [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch) {c : CommitmentId}
    {q₀ : VerifierQuery shape.k Fp G} (hq₀ : q₀ ∈ assembleQueries vk instanceCommitment ps ch)
    (hq₀c : q₀.commId = c) :
    ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
      ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀ = c) ∧
        (∀ d₀, ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) d₀).1 =
          assembledCommitment vk instanceCommitment ps ch c) ∧
        ∀ q ∈ assembleQueries vk instanceCommitment ps ch, q.commId = c →
          q.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
          ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
              (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
                q.point) 0 = q.eval := by
  obtain ⟨i, hi, m, hids, hcomm, hall⟩ :=
    deployed_slot_routed_all urs hk vk instanceCommitment ps ch hacc hq₀ hq₀c
  have hcanonical := assembleQueries_commitment_eq_assembled vk instanceCommitment ps ch hq₀
  exact ⟨i, hi, m, hids, fun d₀ => (hcomm d₀).trans (hcanonical.trans
    (congrArg (assembledCommitment vk instanceCommitment ps ch) hq₀c)), hall⟩

/-- Any selected deployed member is backed by the canonical reference named by its aligned slot
identity.  Unlike the query-routing lemmas, this applies directly to selector functions returned
by the feed builders. -/
theorem deployed_member_commitment_eq_assembled [DecidableEq G] [Inhabited G] {shape : Shape}
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → Nat → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (i : Nat)
    (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) {c : CommitmentId}
    (c0 : CommitmentId)
    (hid : (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : Nat) c0 = c)
    (d0 : CommitmentRef shape.k Fp G × List Fp) :
    ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : Nat) d0).1 =
      assembledCommitment vk instanceCommitment ps ch c := by
  have hm : (m : Nat) <
      ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).sets.getD i []).length := by
    simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using m.isLt
  have h := constructIntermediateSets_member_commitment_eq_of_id
    (assembleQueries vk instanceCommitment ps ch) (assembledCommitment vk instanceCommitment ps ch)
    (fun q hq => assembleQueries_commitment_eq_assembled vk instanceCommitment ps ch hq)
    i (m : Nat) hm c0 (by simpa only [deployedSetCommIds] using hid) d0
  simpa only [deployedSetQueries, constructIntermediateSets_zip_sets_getD] using h

/-! ## The advice feed binding, derived

The terminal's `hadviceBind` — each rotated fed column takes the claimed advice evaluation at
`ch.x` — with the member selections produced by the routing and the decoded column bound by the
member node binding. The out-of-range halves need the verifying key to claim one evaluation per
layout entry (`hAdvLen`), a `decide`-able VK fact. -/

/-- The canonical member selection for one advice query: the routed set and member indices. -/
theorem advice_slot_selected [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch) (pi : Fin shape.numProofs)
    {j : ℕ} (hjl : j < vk.adviceQueryLayout.length) (hje : j < shape.numAdviceQueries) :
    ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
      ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀
          = CommitmentId.adviceCol pi (vk.adviceQueryLayout.getD j (0, 0)).1) ∧
        rotateOmega vk.omega ch.x (vk.adviceQueryLayout.getD j (0, 0)).2
          ∈ deployedSetPts vk instanceCommitment ps ch i ∧
        ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
              (rotateOmega vk.omega ch.x (vk.adviceQueryLayout.getD j (0, 0)).2)) 0
          = finFn (ps.adviceEvals pi) j := by
  obtain ⟨q, hqmem, hqid, hqpt, hqev⟩ :=
    advice_query_mem_assembleQueries_eval vk instanceCommitment ps ch pi hjl hje
  obtain ⟨i, hi, -, m, hids, -, hpt, hev⟩ := deployed_query_routed urs hk vk instanceCommitment ps ch hacc hqmem
  exact ⟨i, hi, m, fun c₀ => (hids c₀).trans hqid, hqpt ▸ hpt, by rw [hqpt, hqev] at hev; exact hev⟩

/-- The instance twin of `advice_slot_selected`. -/
theorem instance_slot_selected [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch) (pi : Fin shape.numProofs)
    {j : ℕ} (hjl : j < vk.instanceQueryLayout.length) (hje : j < shape.numInstanceQueries) :
    ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
      ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀
          = CommitmentId.instanceCol pi (vk.instanceQueryLayout.getD j (0, 0)).1) ∧
        rotateOmega vk.omega ch.x (vk.instanceQueryLayout.getD j (0, 0)).2
          ∈ deployedSetPts vk instanceCommitment ps ch i ∧
        ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
              (rotateOmega vk.omega ch.x (vk.instanceQueryLayout.getD j (0, 0)).2)) 0
          = finFn (ps.instanceEvals pi) j := by
  obtain ⟨q, hqmem, hqid, hqpt, hqev⟩ :=
    instance_query_mem_assembleQueries_eval vk instanceCommitment ps ch pi hjl hje
  obtain ⟨i, hi, -, m, hids, -, hpt, hev⟩ := deployed_query_routed urs hk vk instanceCommitment ps ch hacc hqmem
  exact ⟨i, hi, m, fun c₀ => (hids c₀).trans hqid, hqpt ▸ hpt, by rw [hqpt, hqev] at hev; exact hev⟩

/-- The fixed twin of `advice_slot_selected` (one shared column family, no sub-proof index). -/
theorem fixed_slot_selected [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch)
    {j : ℕ} (hjl : j < vk.fixedQueryLayout.length) (hje : j < shape.numFixedQueries) :
    ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
      ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀
          = CommitmentId.fixedCol (vk.fixedQueryLayout.getD j (0, 0)).1) ∧
        rotateOmega vk.omega ch.x (vk.fixedQueryLayout.getD j (0, 0)).2
          ∈ deployedSetPts vk instanceCommitment ps ch i ∧
        ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
              (rotateOmega vk.omega ch.x (vk.fixedQueryLayout.getD j (0, 0)).2)) 0
          = finFn ps.fixedEvals j := by
  obtain ⟨q, hqmem, hqid, hqpt, hqev⟩ := fixed_query_mem_assembleQueries vk instanceCommitment ps ch hjl hje
  obtain ⟨i, hi, -, m, hids, -, hpt, hev⟩ := deployed_query_routed urs hk vk instanceCommitment ps ch hacc hqmem
  exact ⟨i, hi, m, fun c₀ => (hids c₀).trans hqid, hqpt ▸ hpt, by rw [hqpt, hqev] at hev; exact hev⟩

/-! ## The advice and instance feed bindings, derived -/

open Classical in
/-- **`hadviceBind`, derived.** Member selections for every sub-proof and advice query are
produced by the routing, and the rotated feed of their decoded columns takes the claimed advice
evaluation at `ch.x` at every index — the constraint terminal's `hadviceBind` with nothing
supplied. `hAdvLen` asks the verifying key to carry one layout entry per claimed evaluation, a
`decide`-able VK fact; the measure premises are the budgeted capstone's own two floors. -/
theorem adviceFeed_bind_derived [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk instanceCommitment ps ch b₂f))
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hAdvLen : shape.numAdviceQueries ≤ vk.adviceQueryLayout.length) :
    ∃ (adviceSet : Fin shape.numProofs → Fin shape.numAdviceQueries → ℕ)
      (hadviceSet : ∀ q j, adviceSet q j < deployedX4PairCount vk instanceCommitment ps ch)
      (adviceMem : ∀ (q : Fin shape.numProofs) (j : Fin shape.numAdviceQueries),
        Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet q j)).length),
      (∀ (q : Fin shape.numProofs) (j : Fin shape.numAdviceQueries),
        (deployedSetCommIds vk instanceCommitment ps ch (adviceSet q j)).getD ((adviceMem q j : ℕ))
            CommitmentId.vanishingH
          = CommitmentId.adviceCol q (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1) ∧
      ∀ (q : Fin shape.numProofs) (n : ℕ),
        (rotatedFeed vk.omega vk.adviceQueryLayout
          (fun j : Fin shape.numAdviceQueries =>
            coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet q j)
              (hadviceSet q j) (hlen _ (hadviceSet q j)) (hprob1 _ (hadviceSet q j)) hacc).cols
                (adviceMem q j))) n).eval ch.x
          = finFn (ps.adviceEvals q) n := by
  have hsel : ∀ (q : Fin shape.numProofs) (j : Fin shape.numAdviceQueries),
      ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀
            = CommitmentId.adviceCol q (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1) ∧
          rotateOmega vk.omega ch.x (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).2
            ∈ deployedSetPts vk instanceCommitment ps ch i ∧
          ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
              (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
                (rotateOmega vk.omega ch.x (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).2)) 0
            = finFn (ps.adviceEvals q) (j : ℕ) :=
    fun q j => advice_slot_selected urs hk vk instanceCommitment ps ch hacc q
      (lt_of_lt_of_le j.isLt hAdvLen) j.isLt
  choose iSel hiSel mSel hidsSel hptSel hevSel using hsel
  refine ⟨iSel, hiSel, mSel, fun q j => hidsSel q j CommitmentId.vanishingH, ?_⟩
  intro q n
  by_cases h : n < shape.numAdviceQueries
  · rw [rotatedFeed_eval vk.omega vk.adviceQueryLayout _ h ch.x]
    rcases deployed_member_node_binding_at_point_budgeted urs hk vk instanceCommitment ps ch (iSel q ⟨n, h⟩)
        (hiSel q ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (iSel q ⟨n, h⟩) (hiSel q ⟨n, h⟩)
          (hlen _ (hiSel q ⟨n, h⟩)) (hprob1 _ (hiSel q ⟨n, h⟩)) hacc)
        b₂f (hJ _ (hiSel q ⟨n, h⟩)) (hptSel q ⟨n, h⟩) (mSel q ⟨n, h⟩) with hb | hdlr
    · rw [hb]
      exact hevSel q ⟨n, h⟩
    · exact absurd hdlr hnrel
  · rw [rotatedFeed_eval_of_ge vk.omega vk.adviceQueryLayout _ (Nat.not_lt.mp h) ch.x,
      finFn, dif_neg h]

open Classical in
/-- **`hinstanceBind`, derived** — the instance twin of `adviceFeed_bind_derived`. -/
theorem instanceFeed_bind_derived [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk instanceCommitment ps ch b₂f))
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hInstLen : shape.numInstanceQueries ≤ vk.instanceQueryLayout.length) :
    ∃ (instanceSet : Fin shape.numProofs → Fin shape.numInstanceQueries → ℕ)
      (hinstanceSet : ∀ q j, instanceSet q j < deployedX4PairCount vk instanceCommitment ps ch)
      (instanceMem : ∀ (q : Fin shape.numProofs) (j : Fin shape.numInstanceQueries),
        Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet q j)).length),
      (∀ (q : Fin shape.numProofs) (j : Fin shape.numInstanceQueries),
        (deployedSetCommIds vk instanceCommitment ps ch (instanceSet q j)).getD ((instanceMem q j : ℕ))
            CommitmentId.vanishingH
          = CommitmentId.instanceCol q (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1) ∧
      ∀ (q : Fin shape.numProofs) (n : ℕ),
        (rotatedFeed vk.omega vk.instanceQueryLayout
          (fun j : Fin shape.numInstanceQueries =>
            coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet q j)
              (hinstanceSet q j) (hlen _ (hinstanceSet q j)) (hprob1 _ (hinstanceSet q j))
              hacc).cols (instanceMem q j))) n).eval ch.x
          = finFn (ps.instanceEvals q) n := by
  have hsel : ∀ (q : Fin shape.numProofs) (j : Fin shape.numInstanceQueries),
      ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀
            = CommitmentId.instanceCol q (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1) ∧
          rotateOmega vk.omega ch.x (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).2
            ∈ deployedSetPts vk instanceCommitment ps ch i ∧
          ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
              (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
                (rotateOmega vk.omega ch.x (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).2)) 0
            = finFn (ps.instanceEvals q) (j : ℕ) :=
    fun q j => instance_slot_selected urs hk vk instanceCommitment ps ch hacc q
      (lt_of_lt_of_le j.isLt hInstLen) j.isLt
  choose iSel hiSel mSel hidsSel hptSel hevSel using hsel
  refine ⟨iSel, hiSel, mSel, fun q j => hidsSel q j CommitmentId.vanishingH, ?_⟩
  intro q n
  by_cases h : n < shape.numInstanceQueries
  · rw [rotatedFeed_eval vk.omega vk.instanceQueryLayout _ h ch.x]
    rcases deployed_member_node_binding_at_point_budgeted urs hk vk instanceCommitment ps ch (iSel q ⟨n, h⟩)
        (hiSel q ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (iSel q ⟨n, h⟩) (hiSel q ⟨n, h⟩)
          (hlen _ (hiSel q ⟨n, h⟩)) (hprob1 _ (hiSel q ⟨n, h⟩)) hacc)
        b₂f (hJ _ (hiSel q ⟨n, h⟩)) (hptSel q ⟨n, h⟩) (mSel q ⟨n, h⟩) with hb | hdlr
    · rw [hb]
      exact hevSel q ⟨n, h⟩
    · exact absurd hdlr hnrel
  · rw [rotatedFeed_eval_of_ge vk.omega vk.instanceQueryLayout _ (Nat.not_lt.mp h) ch.x,
      finFn, dif_neg h]

/-! ## The fixed feed and the common permutation columns -/

open Classical in
/-- **`hfixed`, derived** — the fixed-column twin of `adviceFeed_bind_derived`: one shared feed,
bound to the claimed fixed evaluations at every index. -/
theorem fixedFeed_bind_derived [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk instanceCommitment ps ch b₂f))
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hFixedLen : shape.numFixedQueries ≤ vk.fixedQueryLayout.length) :
    ∃ (fixedSet : Fin shape.numFixedQueries → ℕ)
      (hfixedSet : ∀ j, fixedSet j < deployedX4PairCount vk instanceCommitment ps ch)
      (fixedMem : ∀ j : Fin shape.numFixedQueries,
        Fin (deployedSetQueries vk instanceCommitment ps ch (fixedSet j)).length),
      (∀ j : Fin shape.numFixedQueries,
        (deployedSetCommIds vk instanceCommitment ps ch (fixedSet j)).getD ((fixedMem j : ℕ))
            CommitmentId.vanishingH
          = CommitmentId.fixedCol (vk.fixedQueryLayout.getD (j : ℕ) (0, 0)).1) ∧
      ∀ n : ℕ,
        (rotatedFeed vk.omega vk.fixedQueryLayout
          (fun j : Fin shape.numFixedQueries =>
            coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (fixedSet j)
              (hfixedSet j) (hlen _ (hfixedSet j)) (hprob1 _ (hfixedSet j)) hacc).cols
                (fixedMem j))) n).eval ch.x
          = finFn ps.fixedEvals n := by
  have hsel : ∀ j : Fin shape.numFixedQueries,
      ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀
            = CommitmentId.fixedCol (vk.fixedQueryLayout.getD (j : ℕ) (0, 0)).1) ∧
          rotateOmega vk.omega ch.x (vk.fixedQueryLayout.getD (j : ℕ) (0, 0)).2
            ∈ deployedSetPts vk instanceCommitment ps ch i ∧
          ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
              (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
                (rotateOmega vk.omega ch.x (vk.fixedQueryLayout.getD (j : ℕ) (0, 0)).2)) 0
            = finFn ps.fixedEvals (j : ℕ) :=
    fun j => fixed_slot_selected urs hk vk instanceCommitment ps ch hacc
      (lt_of_lt_of_le j.isLt hFixedLen) j.isLt
  choose iSel hiSel mSel hidsSel hptSel hevSel using hsel
  refine ⟨iSel, hiSel, mSel, fun j => hidsSel j CommitmentId.vanishingH, ?_⟩
  intro n
  by_cases h : n < shape.numFixedQueries
  · rw [rotatedFeed_eval vk.omega vk.fixedQueryLayout _ h ch.x]
    rcases deployed_member_node_binding_at_point_budgeted urs hk vk instanceCommitment ps ch (iSel ⟨n, h⟩)
        (hiSel ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (iSel ⟨n, h⟩) (hiSel ⟨n, h⟩)
          (hlen _ (hiSel ⟨n, h⟩)) (hprob1 _ (hiSel ⟨n, h⟩)) hacc)
        b₂f (hJ _ (hiSel ⟨n, h⟩)) (hptSel ⟨n, h⟩) (mSel ⟨n, h⟩) with hb | hdlr
    · rw [hb]
      exact hevSel ⟨n, h⟩
    · exact absurd hdlr hnrel
  · rw [rotatedFeed_eval_of_ge vk.omega vk.fixedQueryLayout _ (Nat.not_lt.mp h) ch.x,
      finFn, dif_neg h]

/-- The permutation-common slot selection: the σ column `c` is routed with its claimed common
evaluation recorded at `ch.x`. -/
theorem permCommon_slot_selected [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch) (c : Fin shape.numPermutationColumns) :
    ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
      ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
        (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀
          = CommitmentId.permCommon c) ∧
        ch.x ∈ deployedSetPts vk instanceCommitment ps ch i ∧
        ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf
              ch.x) 0
          = ps.permutationCommonEvals c := by
  obtain ⟨q, hqmem, hqid, hqpt, hqev⟩ := permCommon_query_mem_assembleQueries vk instanceCommitment ps ch c
  obtain ⟨i, hi, -, m, hids, -, hpt, hev⟩ := deployed_query_routed urs hk vk instanceCommitment ps ch hacc hqmem
  exact ⟨i, hi, m, fun c₀ => (hids c₀).trans hqid, hqpt ▸ hpt, by rw [hqpt, hqev] at hev; exact hev⟩

/-! ## The permutation-set carriers, derived

`hsets` asks the polynomial carriers to take the claimed per-set permutation evaluations at
`ch.x`. Each set's carrier decodes its product commitment *once* — the slot serves all three
openings — and fills the record with that polynomial and its rotations, so evaluation lands on
the claimed `eval`/`nextEval`/`lastEval`. The last set's `lastEval` has no opening
(halo2 skips it), so it is carried as a constant; the permutation expressions never read it. -/

open Classical in
/-- **`hsets`, derived.** One decoded product polynomial per permutation set, rotated per
opening: the carrier list evaluates at `ch.x` to the verifier's own `subProofPermSets`. -/
theorem permSets_bind_derived [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk instanceCommitment ps ch b₂f))
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w) :
    ∃ (permSel : Fin shape.numProofs → Fin shape.numPermutationSets → ℕ)
      (hpermSel : ∀ q s, permSel q s < deployedX4PairCount vk instanceCommitment ps ch)
      (permMem : ∀ (q : Fin shape.numProofs) (s : Fin shape.numPermutationSets),
        Fin (deployedSetQueries vk instanceCommitment ps ch (permSel q s)).length),
      (∀ (q : Fin shape.numProofs) (s : Fin shape.numPermutationSets),
        (deployedSetCommIds vk instanceCommitment ps ch (permSel q s)).getD ((permMem q s : ℕ))
            CommitmentId.vanishingH
          = CommitmentId.permProduct q s) ∧
      ∀ q : Fin shape.numProofs,
        (List.ofFn (fun s : Fin shape.numPermutationSets => PermSetEval.mk
          (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (permSel q s)
            (hpermSel q s) (hlen _ (hpermSel q s)) (hprob1 _ (hpermSel q s)) hacc).cols
              (permMem q s)))
          ((coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (permSel q s)
            (hpermSel q s) (hlen _ (hpermSel q s)) (hprob1 _ (hpermSel q s)) hacc).cols
              (permMem q s))).comp (Polynomial.C (vk.omega ^ (1 : ℤ)) * Polynomial.X))
          ((ps.permutationSetEvals q s).lastEval.map (fun le =>
            if (s : ℕ) + 1 < shape.numPermutationSets then
              (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (permSel q s)
                (hpermSel q s) (hlen _ (hpermSel q s)) (hprob1 _ (hpermSel q s)) hacc).cols
                  (permMem q s))).comp
                (Polynomial.C (vk.omega ^ (-((vk.blindingFactors : ℤ) + 1))) * Polynomial.X)
            else Polynomial.C le)))).map (PermSetEval.map (fun r => r.eval ch.x))
          = subProofPermSets ps q := by
  -- one routed slot per product commitment, serving all its openings
  have hsel : ∀ (q : Fin shape.numProofs) (s : Fin shape.numPermutationSets),
      ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀
            = CommitmentId.permProduct q s) ∧
          ∀ q' ∈ assembleQueries vk instanceCommitment ps ch, q'.commId = CommitmentId.permProduct q s →
            q'.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
            ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
                (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
                  []).idxOf q'.point) 0
              = q'.eval := by
    intro q s
    obtain ⟨q₀, hq₀, hq₀id, -, -⟩ := perm_product_query_mem_assembleQueries vk instanceCommitment ps ch q s
    obtain ⟨i, hi, m, hids, -, hall⟩ :=
      deployed_slot_routed_all urs hk vk instanceCommitment ps ch hacc hq₀ hq₀id
    exact ⟨i, hi, m, hids, hall⟩
  choose iSel hiSel mSel hidsSel hallSel using hsel
  refine ⟨iSel, hiSel, mSel, fun q s => hidsSel q s CommitmentId.vanishingH, ?_⟩
  intro q
  rw [List.map_ofFn, subProofPermSets]
  refine congrArg List.ofFn (funext fun s => ?_)
  -- the decoded product polynomial of this set's slot
  set zdec := coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (iSel q s)
    (hiSel q s) (hlen _ (hiSel q s)) (hprob1 _ (hiSel q s)) hacc).cols (mSel q s)) with hz
  -- the member node binding at any of the slot's points
  have hbindAt : ∀ p ∈ deployedSetPts vk instanceCommitment ps ch (iSel q s),
      zdec.eval p
        = ((deployedSetQueries vk instanceCommitment ps ch (iSel q s)).getD ((mSel q s : ℕ))
            (.point 0, [])).2.getD
          (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD (iSel q s)
            []).idxOf p) 0 := by
    intro p hp
    rcases deployed_member_node_binding_at_point_budgeted urs hk vk instanceCommitment ps ch (iSel q s)
        (hiSel q s)
        (openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (iSel q s) (hiSel q s)
          (hlen _ (hiSel q s)) (hprob1 _ (hiSel q s)) hacc)
        b₂f (hJ _ (hiSel q s)) hp (mSel q s) with hb | hdlr
    · exact hb
    · exact absurd hdlr hnrel
  -- the three openings' bindings
  obtain ⟨qx, hqx, hqxid, hqxpt, hqxev⟩ := perm_product_query_mem_assembleQueries vk instanceCommitment ps ch q s
  obtain ⟨hptx, hevx⟩ := hallSel q s qx hqx hqxid
  have hbx : zdec.eval ch.x = (ps.permutationSetEvals q s).eval := by
    have := hbindAt qx.point hptx
    rw [hqxpt] at this hevx
    rw [this, hevx, hqxev]
  obtain ⟨qn, hqn, hqnid, hqnpt, hqnev⟩ :=
    perm_product_next_query_mem_assembleQueries vk instanceCommitment ps ch q s
  obtain ⟨hptn, hevn⟩ := hallSel q s qn hqn hqnid
  have hbn : zdec.eval (rotateOmega vk.omega ch.x 1)
      = (ps.permutationSetEvals q s).nextEval := by
    have := hbindAt qn.point hptn
    rw [hqnpt] at this hevn
    rw [this, hevn, hqnev]
  -- assemble the record equality, component by component
  have heta : ps.permutationSetEvals q s
      = PermSetEval.mk (ps.permutationSetEvals q s).eval (ps.permutationSetEvals q s).nextEval
          (ps.permutationSetEvals q s).lastEval := rfl
  rw [Function.comp_apply, heta]
  simp only [PermSetEval.map, PermSetEval.mk.injEq]
  refine ⟨hbx, ?_, ?_⟩
  · rw [eval_comp_rotate, ← hbn, rotateOmega, mul_comm]
  · rcases hle : (ps.permutationSetEvals q s).lastEval with _ | le
    · rfl
    · rw [Option.map_map]
      by_cases hlast : (s : ℕ) + 1 < shape.numPermutationSets
      · obtain ⟨ql, hql, hqlid, hqlpt, hqlev⟩ :=
          perm_product_last_query_mem_assembleQueries vk instanceCommitment ps ch q s hlast hle
        obtain ⟨hptl, hevl⟩ := hallSel q s ql hql hqlid
        have hbl : zdec.eval (rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1)))
            = le := by
          have := hbindAt ql.point hptl
          rw [hqlpt] at this hevl
          rw [this, hevl, hqlev]
        simp only [Option.map_some, Function.comp_apply, if_pos hlast]
        rw [eval_comp_rotate, ← hbl, rotateOmega, mul_comm]
      · simp only [Option.map_some, Function.comp_apply, if_neg hlast, Polynomial.eval_C]

/-! ## The lookup carriers, derived

Each lookup decodes three committed polynomials — the product (opened at `x` and `ωx`), the
permuted input (at `x` and `ω⁻¹x`), and the permuted table (at `x`) — each slot routed once and
serving its openings, so the record's five fields evaluate at `ch.x` to the claimed
`LookupEval`. -/

open Classical in
/-- **`hlookups`, derived** — the lookup twin of `permSets_bind_derived`. -/
theorem lookups_bind_derived [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk instanceCommitment ps ch b₂f))
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w) :
    ∃ (prodSel inSel tabSel : Fin shape.numProofs → Fin shape.numLookups → ℕ)
      (hprodSel : ∀ q l, prodSel q l < deployedX4PairCount vk instanceCommitment ps ch)
      (hinSel : ∀ q l, inSel q l < deployedX4PairCount vk instanceCommitment ps ch)
      (htabSel : ∀ q l, tabSel q l < deployedX4PairCount vk instanceCommitment ps ch)
      (prodMem : ∀ (q : Fin shape.numProofs) (l : Fin shape.numLookups),
        Fin (deployedSetQueries vk instanceCommitment ps ch (prodSel q l)).length)
      (inMem : ∀ (q : Fin shape.numProofs) (l : Fin shape.numLookups),
        Fin (deployedSetQueries vk instanceCommitment ps ch (inSel q l)).length)
      (tabMem : ∀ (q : Fin shape.numProofs) (l : Fin shape.numLookups),
        Fin (deployedSetQueries vk instanceCommitment ps ch (tabSel q l)).length),
      (∀ (q : Fin shape.numProofs) (l : Fin shape.numLookups),
        (deployedSetCommIds vk instanceCommitment ps ch (prodSel q l)).getD ((prodMem q l : ℕ))
            CommitmentId.vanishingH = CommitmentId.lookupProduct q l ∧
        (deployedSetCommIds vk instanceCommitment ps ch (inSel q l)).getD ((inMem q l : ℕ))
            CommitmentId.vanishingH = CommitmentId.lookupPermInput q l ∧
        (deployedSetCommIds vk instanceCommitment ps ch (tabSel q l)).getD ((tabMem q l : ℕ))
            CommitmentId.vanishingH = CommitmentId.lookupPermTable q l) ∧
      ∀ q : Fin shape.numProofs,
        (List.ofFn (fun l : Fin shape.numLookups =>
          (LookupEval.mk
            (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (prodSel q l)
              (hprodSel q l) (hlen _ (hprodSel q l)) (hprob1 _ (hprodSel q l)) hacc).cols
                (prodMem q l)))
            ((coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (prodSel q l)
              (hprodSel q l) (hlen _ (hprodSel q l)) (hprob1 _ (hprodSel q l)) hacc).cols
                (prodMem q l))).comp (Polynomial.C (vk.omega ^ (1 : ℤ)) * Polynomial.X))
            (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (inSel q l)
              (hinSel q l) (hlen _ (hinSel q l)) (hprob1 _ (hinSel q l)) hacc).cols
                (inMem q l)))
            ((coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (inSel q l)
              (hinSel q l) (hlen _ (hinSel q l)) (hprob1 _ (hinSel q l)) hacc).cols
                (inMem q l))).comp (Polynomial.C (vk.omega ^ (-1 : ℤ)) * Polynomial.X))
            (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (tabSel q l)
              (htabSel q l) (hlen _ (htabSel q l)) (hprob1 _ (htabSel q l)) hacc).cols
                (tabMem q l))),
          vk.lookupInputExprs l, vk.lookupTableExprs l))).map
            (fun lk => (lk.1.map (fun r => r.eval ch.x), lk.2.1, lk.2.2))
          = subProofLookups vk ps q := by
  have hselP : ∀ (q : Fin shape.numProofs) (l : Fin shape.numLookups),
      ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀
            = CommitmentId.lookupProduct q l) ∧
          ∀ q' ∈ assembleQueries vk instanceCommitment ps ch, q'.commId = CommitmentId.lookupProduct q l →
            q'.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
            ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
                (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
                  []).idxOf q'.point) 0
              = q'.eval := by
    intro q l
    obtain ⟨q₀, hq₀, hq₀id, -, -⟩ := lookup_product_query_mem_assembleQueries vk instanceCommitment ps ch q l
    obtain ⟨i, hi, m, hids, -, hall⟩ :=
      deployed_slot_routed_all urs hk vk instanceCommitment ps ch hacc hq₀ hq₀id
    exact ⟨i, hi, m, hids, hall⟩
  have hselI : ∀ (q : Fin shape.numProofs) (l : Fin shape.numLookups),
      ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀
            = CommitmentId.lookupPermInput q l) ∧
          ∀ q' ∈ assembleQueries vk instanceCommitment ps ch, q'.commId = CommitmentId.lookupPermInput q l →
            q'.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
            ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
                (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
                  []).idxOf q'.point) 0
              = q'.eval := by
    intro q l
    obtain ⟨q₀, hq₀, hq₀id, -, -⟩ := lookup_permInput_query_mem_assembleQueries vk instanceCommitment ps ch q l
    obtain ⟨i, hi, m, hids, -, hall⟩ :=
      deployed_slot_routed_all urs hk vk instanceCommitment ps ch hacc hq₀ hq₀id
    exact ⟨i, hi, m, hids, hall⟩
  have hselT : ∀ (q : Fin shape.numProofs) (l : Fin shape.numLookups),
      ∃ i, i < deployedX4PairCount vk instanceCommitment ps ch ∧
        ∃ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          (∀ c₀, (deployedSetCommIds vk instanceCommitment ps ch i).getD (m : ℕ) c₀
            = CommitmentId.lookupPermTable q l) ∧
          ∀ q' ∈ assembleQueries vk instanceCommitment ps ch, q'.commId = CommitmentId.lookupPermTable q l →
            q'.point ∈ deployedSetPts vk instanceCommitment ps ch i ∧
            ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD
                (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i
                  []).idxOf q'.point) 0
              = q'.eval := by
    intro q l
    obtain ⟨q₀, hq₀, hq₀id, -, -⟩ := lookup_permTable_query_mem_assembleQueries vk instanceCommitment ps ch q l
    obtain ⟨i, hi, m, hids, -, hall⟩ :=
      deployed_slot_routed_all urs hk vk instanceCommitment ps ch hacc hq₀ hq₀id
    exact ⟨i, hi, m, hids, hall⟩
  choose iP hiP mP hidsP hallP using hselP
  choose iI hiI mI hidsI hallI using hselI
  choose iT hiT mT hidsT hallT using hselT
  refine ⟨iP, iI, iT, hiP, hiI, hiT, mP, mI, mT,
    fun q l => ⟨hidsP q l CommitmentId.vanishingH, hidsI q l CommitmentId.vanishingH,
      hidsT q l CommitmentId.vanishingH⟩, ?_⟩
  intro q
  rw [List.map_ofFn, subProofLookups]
  refine congrArg List.ofFn (funext fun l => ?_)
  rw [Function.comp_apply]
  -- the per-slot binding-at-a-point helper
  have hbindAt : ∀ (i : ℕ) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
      (m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length),
      ∀ p ∈ deployedSetPts vk instanceCommitment ps ch i,
      (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch i hi
          (hlen _ hi) (hprob1 _ hi) hacc).cols m)).eval p
        = ((deployedSetQueries vk instanceCommitment ps ch i).getD ((m : ℕ)) (.point 0, [])).2.getD
          (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf p)
          0 := by
    intro i hi m p hp
    rcases deployed_member_node_binding_at_point_budgeted urs hk vk instanceCommitment ps ch i hi
        (openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch i hi (hlen _ hi) (hprob1 _ hi)
          hacc)
        b₂f (hJ _ hi) hp m with hb | hdlr
    · exact hb
    · exact absurd hdlr hnrel
  -- the five bindings
  obtain ⟨q1, hq1, hq1id, hq1pt, hq1ev⟩ := lookup_product_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt1, hev1⟩ := hallP q l q1 hq1 hq1id
  have hb1 : (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (iP q l)
      (hiP q l) (hlen _ (hiP q l)) (hprob1 _ (hiP q l)) hacc).cols (mP q l))).eval ch.x
      = (ps.lookupEvals q l).productEval := by
    have := hbindAt (iP q l) (hiP q l) (mP q l) q1.point hpt1
    rw [hq1pt] at this hev1
    rw [this, hev1, hq1ev]
  obtain ⟨q2, hq2, hq2id, hq2pt, hq2ev⟩ :=
    lookup_product_next_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt2, hev2⟩ := hallP q l q2 hq2 hq2id
  have hb2 : (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (iP q l)
      (hiP q l) (hlen _ (hiP q l)) (hprob1 _ (hiP q l)) hacc).cols
        (mP q l))).eval (rotateOmega vk.omega ch.x 1)
      = (ps.lookupEvals q l).productNextEval := by
    have := hbindAt (iP q l) (hiP q l) (mP q l) q2.point hpt2
    rw [hq2pt] at this hev2
    rw [this, hev2, hq2ev]
  obtain ⟨q3, hq3, hq3id, hq3pt, hq3ev⟩ :=
    lookup_permInput_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt3, hev3⟩ := hallI q l q3 hq3 hq3id
  have hb3 : (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (iI q l)
      (hiI q l) (hlen _ (hiI q l)) (hprob1 _ (hiI q l)) hacc).cols (mI q l))).eval ch.x
      = (ps.lookupEvals q l).permutedInputEval := by
    have := hbindAt (iI q l) (hiI q l) (mI q l) q3.point hpt3
    rw [hq3pt] at this hev3
    rw [this, hev3, hq3ev]
  obtain ⟨q4, hq4, hq4id, hq4pt, hq4ev⟩ :=
    lookup_permInput_inv_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt4, hev4⟩ := hallI q l q4 hq4 hq4id
  have hb4 : (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (iI q l)
      (hiI q l) (hlen _ (hiI q l)) (hprob1 _ (hiI q l)) hacc).cols
        (mI q l))).eval (rotateOmega vk.omega ch.x (-1))
      = (ps.lookupEvals q l).permutedInputInvEval := by
    have := hbindAt (iI q l) (hiI q l) (mI q l) q4.point hpt4
    rw [hq4pt] at this hev4
    rw [this, hev4, hq4ev]
  obtain ⟨q5, hq5, hq5id, hq5pt, hq5ev⟩ :=
    lookup_permTable_query_mem_assembleQueries vk instanceCommitment ps ch q l
  obtain ⟨hpt5, hev5⟩ := hallT q l q5 hq5 hq5id
  have hb5 : (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (iT q l)
      (hiT q l) (hlen _ (hiT q l)) (hprob1 _ (hiT q l)) hacc).cols (mT q l))).eval ch.x
      = (ps.lookupEvals q l).permutedTableEval := by
    have := hbindAt (iT q l) (hiT q l) (mT q l) q5.point hpt5
    rw [hq5pt] at this hev5
    rw [this, hev5, hq5ev]
  -- assemble the tuple
  have heta : ps.lookupEvals q l
      = LookupEval.mk (ps.lookupEvals q l).productEval (ps.lookupEvals q l).productNextEval
          (ps.lookupEvals q l).permutedInputEval (ps.lookupEvals q l).permutedInputInvEval
          (ps.lookupEvals q l).permutedTableEval := rfl
  refine congrArg (fun z => (z, vk.lookupInputExprs l, vk.lookupTableExprs l)) ?_
  rw [heta]
  simp only [LookupEval.map, LookupEval.mk.injEq]
  refine ⟨hb1, ?_, hb3, ?_, hb5⟩
  · rw [eval_comp_rotate, ← hb2, rotateOmega, mul_comm]
  · rw [eval_comp_rotate, ← hb4, rotateOmega, mul_comm]

/-! ## The common permutation feed and the chunk carriers -/

open Classical in
/-- **The σ-column feed, derived**: entry `c` decodes the `permCommon c` slot, bound at `ch.x` to
the claimed common evaluation; `0` out of range, where the claim is `0` too. -/
theorem permCommonFeed_bind_derived [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk instanceCommitment ps ch b₂f))
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w) :
    ∃ commonF : ℕ → Polynomial Fp,
      ∀ n : ℕ, (commonF n).eval ch.x = finFn ps.permutationCommonEvals n := by
  have hsel := fun c : Fin shape.numPermutationColumns =>
    permCommon_slot_selected urs hk vk instanceCommitment ps ch hacc c
  choose iSel hiSel mSel hidsSel hptSel hevSel using hsel
  refine ⟨fun n => if h : n < shape.numPermutationColumns then
    coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (iSel ⟨n, h⟩)
      (hiSel ⟨n, h⟩) (hlen _ (hiSel ⟨n, h⟩)) (hprob1 _ (hiSel ⟨n, h⟩)) hacc).cols
        (mSel ⟨n, h⟩))
    else 0, ?_⟩
  intro n
  dsimp only
  by_cases h : n < shape.numPermutationColumns
  · rw [dif_pos h, finFn, dif_pos h]
    rcases deployed_member_node_binding_at_point_budgeted urs hk vk instanceCommitment ps ch (iSel ⟨n, h⟩)
        (hiSel ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (iSel ⟨n, h⟩) (hiSel ⟨n, h⟩)
          (hlen _ (hiSel ⟨n, h⟩)) (hprob1 _ (hiSel ⟨n, h⟩)) hacc)
        b₂f (hJ _ (hiSel ⟨n, h⟩)) (hptSel ⟨n, h⟩) (mSel ⟨n, h⟩) with hb | hdlr
    · rw [hb]
      exact hevSel ⟨n, h⟩
    · exact absurd hdlr hnrel
  · rw [dif_neg h, finFn, dif_neg h, Polynomial.eval_zero]

/-- **`hchunks` from the feeds.** With the set carriers matching `subProofPermSets` at `ch.x`
(`hsets`) and per-class feed polynomials bound to the claimed evaluations, the chunk carriers —
each set paired with its columns' `(resolved feed, σ feed)` pairs — evaluate at `ch.x` to
`subProofPermChunks`. Pure list algebra over the bindings; no new probabilistic input. -/
theorem permChunks_bind_of_feeds {shape : Shape} {G' : Type*}
    (vk : VerifyingKey shape Fp G') (ps : ProofString shape Fp G') (ch : Challenges shape.k Fp)
    (q : Fin shape.numProofs)
    (setCarriers : List (PermSetEval (Polynomial Fp)))
    (hsets : setCarriers.map (PermSetEval.map (fun r => r.eval ch.x)) = subProofPermSets ps q)
    (fixedF adviceF instanceF commonF : ℕ → Polynomial Fp)
    (hfixedF : ∀ n, (fixedF n).eval ch.x = finFn ps.fixedEvals n)
    (hadviceF : ∀ n, (adviceF n).eval ch.x = finFn (ps.adviceEvals q) n)
    (hinstanceF : ∀ n, (instanceF n).eval ch.x = finFn (ps.instanceEvals q) n)
    (hcommonF : ∀ n, (commonF n).eval ch.x = finFn ps.permutationCommonEvals n) :
    ((setCarriers.zip vk.permutationChunks).map (fun sc => (sc.1, sc.2.map (fun cr =>
        ((match cr.1 with
          | .advice i => adviceF i
          | .fixed i => fixedF i
          | .instance i => instanceF i), commonF cr.2))))).map
      (fun c => (c.1.map (fun r => r.eval ch.x),
        c.2.map (fun r => (r.1.eval ch.x, r.2.eval ch.x))))
      = subProofPermChunks vk ps q := by
  rw [subProofPermChunks, ← hsets, List.zip_map_left, List.map_map, List.map_map]
  refine List.map_congr_left fun sc _ => ?_
  simp only [Function.comp_apply]
  refine congrArg (Prod.mk _) ?_
  rw [List.map_map]
  refine List.map_congr_left fun cr _ => ?_
  simp only [Function.comp_apply]
  refine congrArg₂ Prod.mk ?_ (hcommonF cr.2)
  rcases cr.1 with i | i | i
  · exact hadviceF i
  · exact hfixedF i
  · exact hinstanceF i

/-! ## The Lagrange polynomials

`hl0`/`hlLast`/`hlBlind` ask for polynomials whose values at `ch.x` are the verifier's computed
Lagrange basis values. The basis polynomial is public domain data — a geometric sum — and its
closed-form value holds at every point off the roots of unity, which acceptance excludes. -/

/-- The `i`-th Lagrange basis polynomial of the size-`n` domain:
`(ω^i / n) · Σ_{k<n} (ω^i)^{n−1−k} Xᵏ`. Off the roots of unity its value is halo2's
`lagrangeBasisValue` formula `(xⁿ − 1)·ωⁱ / (n·(x − ωⁱ))`. -/
noncomputable def lagrangeBasisPoly (omega : Fp) (n : ℕ) (i : ℤ) : Polynomial Fp :=
  Polynomial.C (omega ^ i / (n : Fp)) *
    ∑ k ∈ Finset.range n, Polynomial.C ((omega ^ i) ^ (n - 1 - k)) * Polynomial.X ^ k

/-- **The closed form.** At any `x` with `xⁿ ≠ 1`, the basis polynomial takes the verifier's
`lagrangeBasisValue`: the geometric sum clears `(x − ωⁱ)` into `xⁿ − 1`. -/
theorem lagrangeBasisPoly_eval (omega : Fp) (n : ℕ) (i : ℤ) (x : Fp)
    (hω : omega ^ n = 1) (hn : (n : Fp) ≠ 0) (hx : x ^ n ≠ 1) :
    (lagrangeBasisPoly omega n i).eval x = lagrangeBasisValue omega n (x ^ n) x i := by
  have hω0 : omega ≠ 0 := by
    intro h0
    rw [h0] at hω
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact hn (by norm_num)
    · rw [zero_pow hpos.ne'] at hω
      exact one_ne_zero hω.symm
  have han : (omega ^ i) ^ n = 1 := by
    rw [← zpow_natCast (omega ^ i) n, ← zpow_mul, mul_comm i (n : ℤ), zpow_mul,
      zpow_natCast, hω, one_zpow]
  have hxa : x ≠ omega ^ i := by
    intro hxe
    rw [hxe] at hx
    exact hx han
  have hgeom : (∑ k ∈ Finset.range n, (omega ^ i) ^ (n - 1 - k) * x ^ k) * (x - omega ^ i)
      = x ^ n - 1 := by
    have h := geom_sum₂_mul x (omega ^ i) n
    calc (∑ k ∈ Finset.range n, (omega ^ i) ^ (n - 1 - k) * x ^ k) * (x - omega ^ i)
        = (∑ k ∈ Finset.range n, x ^ k * (omega ^ i) ^ (n - 1 - k)) * (x - omega ^ i) := by
          congr 1
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ = x ^ n - (omega ^ i) ^ n := h
      _ = x ^ n - 1 := by rw [han]
  have heval : (lagrangeBasisPoly omega n i).eval x
      = (omega ^ i / (n : Fp)) * ∑ k ∈ Finset.range n, (omega ^ i) ^ (n - 1 - k) * x ^ k := by
    simp [lagrangeBasisPoly, Polynomial.eval_finsetSum]
  have hsub : x - omega ^ i ≠ 0 := sub_ne_zero.mpr hxa
  have hS : (∑ k ∈ Finset.range n, (omega ^ i) ^ (n - 1 - k) * x ^ k)
      = (x ^ n - 1) / (x - omega ^ i) := by
    rw [eq_div_iff hsub]
    exact hgeom
  rw [heval, lagrangeBasisValue, hS]
  field_simp

/-- Evaluation commutes with the `foldl (+)` the verifier's `lBlind` uses. -/
theorem eval_foldl_add (x : Fp) (acc : Polynomial Fp) (ps : List (Polynomial Fp)) :
    (ps.foldl (· + ·) acc).eval x
      = (ps.map (fun p => p.eval x)).foldl (· + ·) (acc.eval x) := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih => simpa using ih (acc + p)

/-- **The three Lagrange bindings, derived.** Polynomial carriers for `l₀`, `l_last` and
`l_blind` whose values at any `x` off the roots of unity are the verifier's `lagrangeBasis`
triple — acceptance supplies the exclusion. -/
theorem lagrange_bind_derived (omega : Fp) (n blinding : ℕ) (x : Fp)
    (hω : omega ^ n = 1) (hn : (n : Fp) ≠ 0) (hx : x ^ n ≠ 1) :
    (lagrangeBasisPoly omega n 0).eval x = (lagrangeBasis omega n blinding (x ^ n) x).1 ∧
    (lagrangeBasisPoly omega n (-((blinding : ℤ) + 1))).eval x
      = (lagrangeBasis omega n blinding (x ^ n) x).2.1 ∧
    (((List.range blinding).map
        (fun j => lagrangeBasisPoly omega n (-((j : ℤ) + 1)))).foldl (· + ·) 0).eval x
      = (lagrangeBasis omega n blinding (x ^ n) x).2.2 := by
  refine ⟨lagrangeBasisPoly_eval omega n 0 x hω hn hx,
    lagrangeBasisPoly_eval omega n _ x hω hn hx, ?_⟩
  show _ = ((List.range blinding).map
      (fun j => lagrangeBasisValue omega n (x ^ n) x (-((j : ℤ) + 1)))).foldl (· + ·) 0
  rw [eval_foldl_add, Polynomial.eval_zero, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  exact lagrangeBasisPoly_eval omega n _ x hω hn hx

/-! ## The supplied constraint terminal

Everything assembles: from the batch, the two floors, and acceptance, the whole constraint supply
is *produced* — feeds, carriers, Lagrange terms, and the committed quotient, each bound to the
proof string's claims — and the conclusion consumes only the good squeeze (priced downstream) and
the encoding of the member relation into the final statement. -/

open Polynomial in
open Classical in
/-- **The constraint supply, produced from the run.** Either a nontrivial `(g, u, w)` relation is
at hand, or there exist concrete feeds, permutation and lookup carriers, Lagrange terms, and a
committed quotient — all decoded from the run and bound to its claims — such that for any good
squeeze (`ch.x` off the constraint difference's bad set) and any encoding of the member relation,
the deployed `SnarkRelation` at `circuitSatViaConstraints` follows. The two receivers are the two
priced/semantic surfaces that remain open; nothing else is supplied. -/
theorem constraints_supply_derived [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → Nat → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (pU pW : Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk instanceCommitment ps ch b₂f))
    (hacc : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hAdvLen : shape.numAdviceQueries ≤ vk.adviceQueryLayout.length)
    (hInstLen : shape.numInstanceQueries ≤ vk.instanceQueryLayout.length)
    (hFixedLen : shape.numFixedQueries ≤ vk.fixedQueryLayout.length)
    (hω : vk.omega ^ vk.n = 1) (hn : (vk.n : Fp) ≠ 0) :
    HasNontrivialRelation (F := Fp) urs.g urs.u urs.w ∨
    ∃ (fixedF : ℕ → Polynomial Fp)
      (adviceF instanceF : Fin shape.numProofs → ℕ → Polynomial Fp)
      (setsC : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)))
      (chunksC : Fin shape.numProofs →
        List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
      (lookupsC : Fin shape.numProofs →
        List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
      (l0P lLastP lBlindP hpolyP : Polynomial Fp),
      ∀ {S : Prop},
        ch.x ∉ szBadSet (combineConstraints fixedF adviceF instanceF vk.gates setsC chunksC
          lookupsC ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen l0P lLastP lBlindP
          - hpolyP * (X ^ vk.n - 1)) →
        (∀ a, SnarkRelation urs
          (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
          (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch)
          (circuitSatViaConstraints fixedF (fun _ => adviceF) (fun _ => instanceF) vk.gates
            setsC chunksC lookupsC ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen
            l0P lLastP lBlindP hpolyP vk.n) a → S) →
        S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  by_cases hnrel : HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
  · exact Or.inl hnrel
  refine Or.inr ?_
  have hxn : ch.x ^ vk.n ≠ 1 := deployedAccepts_xn_ne_one urs hk vk instanceCommitment ps ch hacc
  -- the derived feeds and carriers
  obtain ⟨aSet, haSet, aMem, haLayout, haBind⟩ := adviceFeed_bind_derived urs hk vk instanceCommitment ps ch
    pbatch hlen hprob1 b₂f hJ hacc hnrel hAdvLen
  obtain ⟨iSet, hiSet, iMem, hiLayout, hiBind⟩ := instanceFeed_bind_derived urs hk vk instanceCommitment ps ch
    pbatch hlen hprob1 b₂f hJ hacc hnrel hInstLen
  obtain ⟨fSet, hfSet, fMem, hfLayout, hfBind⟩ := fixedFeed_bind_derived urs hk vk instanceCommitment ps ch
    pbatch hlen hprob1 b₂f hJ hacc hnrel hFixedLen
  obtain ⟨pSet, hpSet, pMem, hpLayout, hpBind⟩ := permSets_bind_derived urs hk vk instanceCommitment ps ch
    pbatch hlen hprob1 b₂f hJ hacc hnrel
  obtain ⟨commonF, hcommonF⟩ := permCommonFeed_bind_derived urs hk vk instanceCommitment ps ch
    pbatch hlen hprob1 b₂f hJ hacc hnrel
  obtain ⟨lpSel, liSel, ltSel, hlpSel, hliSel, hltSel, lpMem, liMem, ltMem, hlLayout, hlBind⟩ :=
    lookups_bind_derived urs hk vk instanceCommitment ps ch pbatch hlen hprob1 b₂f hJ hacc hnrel
  obtain ⟨hl0, hlLast, hlBlind⟩ :=
    lagrange_bind_derived vk.omega vk.n vk.blindingFactors ch.x hω hn hxn
  -- the routed vanishing slot and the decoded quotient
  obtain ⟨iV, hiVsets, hroute, mV, hmV, hidsV, hevalsV⟩ := vanishing_slot_routed vk instanceCommitment ps ch
  have hiV : iV < deployedX4PairCount vk instanceCommitment ps ch := by
    rw [deployedX4PairCount_eq_sets_length urs hk vk instanceCommitment ps ch hacc]
    exact hiVsets
  set mdecV := openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch iV hiV
    (hlen _ hiV) (hprob1 _ hiV) hacc with hmdecV
  set adviceF : Fin shape.numProofs → ℕ → Polynomial Fp := fun q =>
    rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin shape.numAdviceQueries =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (aSet q j)
        (haSet q j) (hlen _ (haSet q j)) (hprob1 _ (haSet q j)) hacc).cols (aMem q j)))
    with hadviceF
  set instanceF : Fin shape.numProofs → ℕ → Polynomial Fp := fun q =>
    rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin shape.numInstanceQueries =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (iSet q j)
        (hiSet q j) (hlen _ (hiSet q j)) (hprob1 _ (hiSet q j)) hacc).cols (iMem q j)))
    with hinstanceF
  set fixedF : ℕ → Polynomial Fp :=
    rotatedFeed vk.omega vk.fixedQueryLayout (fun j : Fin shape.numFixedQueries =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (fSet j)
        (hfSet j) (hlen _ (hfSet j)) (hprob1 _ (hfSet j)) hacc).cols (fMem j)))
    with hfixedF
  set setsC : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)) := fun q =>
    List.ofFn (fun s : Fin shape.numPermutationSets => PermSetEval.mk
      (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (pSet q s)
        (hpSet q s) (hlen _ (hpSet q s)) (hprob1 _ (hpSet q s)) hacc).cols (pMem q s)))
      ((coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (pSet q s)
        (hpSet q s) (hlen _ (hpSet q s)) (hprob1 _ (hpSet q s)) hacc).cols
          (pMem q s))).comp (Polynomial.C (vk.omega ^ (1 : ℤ)) * Polynomial.X))
      ((ps.permutationSetEvals q s).lastEval.map (fun le =>
        if (s : ℕ) + 1 < shape.numPermutationSets then
          (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (pSet q s)
            (hpSet q s) (hlen _ (hpSet q s)) (hprob1 _ (hpSet q s)) hacc).cols
              (pMem q s))).comp
            (Polynomial.C (vk.omega ^ (-((vk.blindingFactors : ℤ) + 1))) * Polynomial.X)
        else Polynomial.C le))) with hsetsC
  set chunksC : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)) := fun q =>
    ((setsC q).zip vk.permutationChunks).map (fun sc => (sc.1, sc.2.map (fun cr =>
      ((match cr.1 with
        | .advice i => adviceF q i
        | .fixed i => fixedF i
        | .instance i => instanceF q i), commonF cr.2)))) with hchunksC
  set lookupsC : Fin shape.numProofs →
      List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)) := fun q =>
    List.ofFn (fun l : Fin shape.numLookups =>
      (LookupEval.mk
        (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (lpSel q l)
          (hlpSel q l) (hlen _ (hlpSel q l)) (hprob1 _ (hlpSel q l)) hacc).cols (lpMem q l)))
        ((coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (lpSel q l)
          (hlpSel q l) (hlen _ (hlpSel q l)) (hprob1 _ (hlpSel q l)) hacc).cols
            (lpMem q l))).comp (Polynomial.C (vk.omega ^ (1 : ℤ)) * Polynomial.X))
        (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (liSel q l)
          (hliSel q l) (hlen _ (hliSel q l)) (hprob1 _ (hliSel q l)) hacc).cols (liMem q l)))
        ((coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (liSel q l)
          (hliSel q l) (hlen _ (hliSel q l)) (hprob1 _ (hliSel q l)) hacc).cols
            (liMem q l))).comp (Polynomial.C (vk.omega ^ (-1 : ℤ)) * Polynomial.X))
        (coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (ltSel q l)
          (hltSel q l) (hlen _ (hltSel q l)) (hprob1 _ (hltSel q l)) hacc).cols (ltMem q l))),
      vk.lookupInputExprs l, vk.lookupTableExprs l)) with hlookupsC
  refine ⟨fixedF, adviceF, instanceF, setsC, chunksC, lookupsC,
    lagrangeBasisPoly vk.omega vk.n 0,
    lagrangeBasisPoly vk.omega vk.n (-((vk.blindingFactors : ℤ) + 1)),
    ((List.range vk.blindingFactors).map
      (fun j => lagrangeBasisPoly vk.omega vk.n (-((j : ℤ) + 1)))).foldl (· + ·) 0,
    coeffsToPoly (mdecV.cols ⟨mV, hmV⟩), ?_⟩
  intro S hxgood hencodes
  rcases hfold_of_constraint_polys urs hk vk instanceCommitment ps ch fixedF adviceF instanceF setsC chunksC
      lookupsC _ _ _ (coeffsToPoly (mdecV.cols ⟨mV, hmV⟩)) iV mV hmV
      (fun m₀ => coeffsToPoly (mdecV.cols m₀))
      (fun idx m₀ => deployed_member_node_binding_budgeted urs hk vk instanceCommitment ps ch iV hiV mdecV b₂f
        (hJ _ hiV) (deployedSetQueries_eval_length vk instanceCommitment ps ch iV) idx m₀)
      rfl hroute hevalsV hacc hfBind haBind hiBind hpBind
      (fun q => permChunks_bind_of_feeds vk ps ch q (setsC q) (hpBind q) fixedF (adviceF q)
        (instanceF q) commonF hfBind (haBind q) (hiBind q) hcommonF)
      hlBind hl0 hlLast hlBlind
    with hfold | hrel
  · exact Or.inl (hencodes a₀ ⟨pbatch.ipaRelation_of_x4Current hξcur,
      circuitSatViaConstraints_of_check fixedF (fun _ => adviceF) (fun _ => instanceF) vk.gates
        setsC chunksC lookupsC ch.beta ch.gamma vk.delta ch.theta ch.y vk.chunkLen _ _ _
        (coeffsToPoly (mdecV.cols ⟨mV, hmV⟩)) vk.n a₀ ch.x hfold
        (hgood_of_good_challenge _ (coeffsToPoly (mdecV.cols ⟨mV, hmV⟩)) vk.n hxgood)⟩)
  · exact Or.inr hrel

end Zcash.Snark
