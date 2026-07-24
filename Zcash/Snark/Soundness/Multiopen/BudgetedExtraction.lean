import Zcash.Snark.Soundness.Multiopen.NodeBinding
import Zcash.Snark.Soundness.Multiopen.FloorBudget

/-!
# The budgeted multiopen extraction (single-path member terminal)

The extraction cores of `Multiopen.NodeBinding` consume their squeeze floors quantified over every
splice run. This module re-proves the nested extraction with a single measure premise — one joint
accept floor `t₁ + t₂ + t₃ + t₄ < μ(J)` over the joint draw of the four fresh challenges — using
canonical run selectors (`Classical.choose` fixes each level's accepting run before any probability
statement) and heavy-fiber Markov descent (each level peels its own threshold off the joint floor,
`uniformOfFintype_heavy_fiber_lt`, and forks the heavy set into the sample family the next level
consumes).

The endpoint `deployed_member_budget` is the combined budget: *either* the joint accept measure
sits within `Σtᵢ`, *or* every decoded member column takes its claimed evaluation (or a computed
`(g, U, W)`-relation exists). The `∀`-over-runs cores remain alongside.

There are no side hypotheses beyond the floor: `t₃` carries a `+ |allPts|` collision summand on top
of the interpolation degree bound, which buys the `x₃` samples off the opened set points outright
(`exists_injective_accepting_avoiding_of_measure`) rather than assuming they miss them. That matters
because acceptance does not imply it — a colliding `χ` makes the verifier's `(x₃ − p)⁻¹` equal
`0⁻¹ = 0`, degenerating the multiopen check instead of failing it — so the avoidance has to be paid
for, and `t₃` is where it is paid.
-/

namespace Zcash.Snark

-- The deployed grouping definitions appear inside index types, so a defeq check on an index can
-- pull the whole `constructIntermediateSets (assembleQueries …)` computation through `whnf`.
-- Sealing them keeps those checks syntactic; the proofs below use their equation lemmas.
attribute [local irreducible] deployedSetQueries deployedSetCommIds deployedX4PairCount
  x4BatchCommitments x4BatchEvals

open Polynomial
open scoped ENNReal
open Classical

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-! ## Canonical run selectors

Each `OpenedX*Accept` event is an existential over its splice run. The *run-accept payload*
definitions below name the body of that existential, so `OpenedX*Accept … = ∃ r, X*RunAccepts … r`
definitionally; the canonical selector is `Classical.choose` on that existential when the event
holds (the honest run otherwise), and its spec lemma returns the payload at the canonical run. -/

/-- The body of `OpenedX2Accept`'s run existential: run `r` accepts the set-separation rewind at
challenge `χ` with a clean forked transcript on its opened commitment. -/
def X2RunAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (χ : Fp) (r : X2Run shape G) : Prop :=
  ∃ (z blind : Fp)
    (fs : ForkedTranscript urs hk vk instanceCommitment (r.spliced ps) (r.challenges ch χ) b z blind)
    (t : IpaTreeV Fp G urs.k),
    IpaAcceptV urs.g b fs.openedCommitment
      (multiopenValue vk instanceCommitment (r.spliced ps) (r.challenges ch χ)) t

/-- The canonical accepting `x₂` splice run at challenge `χ`: `Classical.choose` on the accept
event's run existential when it holds, the honest run otherwise. A *function of the challenge*,
fixed before any probability statement — the joint accept event and the budgeted extraction
reference the same run by construction. -/
noncomputable def canonicalX2Run [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (χ : Fp) : X2Run shape G :=
  if _ : X2RunAccepts urs hk vk instanceCommitment ps ch b χ (honestX2Run ps ch) then honestX2Run ps ch
  else if h : OpenedX2Accept urs hk vk instanceCommitment ps ch b χ then
    (show ∃ r : X2Run shape G, X2RunAccepts urs hk vk instanceCommitment ps ch b χ r from h).choose
  else honestX2Run ps ch

/-- The canonical `x₂` run carries the accept payload whenever the event holds. -/
theorem canonicalX2Run_accepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) {χ : Fp}
    (h : OpenedX2Accept urs hk vk instanceCommitment ps ch b χ) :
    X2RunAccepts urs hk vk instanceCommitment ps ch b χ (canonicalX2Run urs hk vk instanceCommitment ps ch b χ) := by
  rw [canonicalX2Run]
  by_cases hh : X2RunAccepts urs hk vk instanceCommitment ps ch b χ (honestX2Run ps ch)
  · rw [dif_pos hh]; exact hh
  · rw [dif_neg hh, dif_pos h]
    exact (show ∃ r : X2Run shape G, X2RunAccepts urs hk vk instanceCommitment ps ch b χ r from h).choose_spec

/-- **Honest-preferring collapse (`x₂`).** When the honest run witnesses the accept event, the
canonical `x₂` run *is* the honest run — so at the honest tuple its splice is the identity and the
inner base collapses to the honest transcript. -/
theorem canonicalX2Run_honest [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) {χ : Fp}
    (hh : X2RunAccepts urs hk vk instanceCommitment ps ch b χ (honestX2Run ps ch)) :
    canonicalX2Run urs hk vk instanceCommitment ps ch b χ = honestX2Run ps ch := by
  rw [canonicalX2Run, dif_pos hh]

/-- The body of `OpenedX3Accept`'s run existential. -/
def X3RunAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (χ : Fp) (r : X3Run shape G) : Prop :=
  ∃ (z blind : Fp)
    (fs : ForkedTranscript urs hk vk instanceCommitment (r.spliced ps) (r.challenges ch χ) b z blind)
    (t : IpaTreeV Fp G urs.k),
    IpaAcceptV urs.g b fs.openedCommitment
      (multiopenValue vk instanceCommitment (r.spliced ps) (r.challenges ch χ)) t

/-- The canonical accepting `x₃` splice run at challenge `χ`, as `canonicalX2Run`. -/
noncomputable def canonicalX3Run [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (χ : Fp) : X3Run shape G :=
  if _ : X3RunAccepts urs hk vk instanceCommitment ps ch b χ (honestX3Run ps ch) then honestX3Run ps ch
  else if h : OpenedX3Accept urs hk vk instanceCommitment ps ch b χ then
    (show ∃ r : X3Run shape G, X3RunAccepts urs hk vk instanceCommitment ps ch b χ r from h).choose
  else honestX3Run ps ch

/-- The canonical `x₃` run carries the accept payload whenever the event holds. -/
theorem canonicalX3Run_accepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) {χ : Fp}
    (h : OpenedX3Accept urs hk vk instanceCommitment ps ch b χ) :
    X3RunAccepts urs hk vk instanceCommitment ps ch b χ (canonicalX3Run urs hk vk instanceCommitment ps ch b χ) := by
  rw [canonicalX3Run]
  by_cases hh : X3RunAccepts urs hk vk instanceCommitment ps ch b χ (honestX3Run ps ch)
  · rw [dif_pos hh]; exact hh
  · rw [dif_neg hh, dif_pos h]
    exact (show ∃ r : X3Run shape G, X3RunAccepts urs hk vk instanceCommitment ps ch b χ r from h).choose_spec

/-- **Honest-preferring collapse (`x₃`).** -/
theorem canonicalX3Run_honest [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) {χ : Fp}
    (hh : X3RunAccepts urs hk vk instanceCommitment ps ch b χ (honestX3Run ps ch)) :
    canonicalX3Run urs hk vk instanceCommitment ps ch b χ = honestX3Run ps ch := by
  rw [canonicalX3Run, dif_pos hh]

/-- The body of `OpenedX1PinnedAccept`'s run existential: run `run` accepts the deployed verifier
at compression challenge `χv` and carries an opened `x₄` batch at its own interpolation base. -/
def X1PinnedRunAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (χv : Fp) (run : X1Run shape G) : Prop :=
  ∃ (aR : Fin (2 ^ urs.k) → Fp) (pUR pWR : Fp),
    DeployedAccepts urs hk vk instanceCommitment (run.spliced ps) (run.challenges ch χv) ∧
    Nonempty (OpenedBatchOpenings urs (evalVector urs.k ((run.challenges ch χv).x3))
      (x4BatchCommitments urs hk vk instanceCommitment (run.spliced ps) (run.challenges ch χv))
      (x4BatchEvals vk instanceCommitment (run.spliced ps) (run.challenges ch χv)) aR pUR pWR)

/-- The canonical accepting pinned `x₁` splice run at challenge `χv`, as `canonicalX2Run`. -/
noncomputable def canonicalX1Run [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (χv : Fp) : X1Run shape G :=
  if _ : X1PinnedRunAccepts urs hk vk instanceCommitment ps ch χv (honestX1Run ps ch) then honestX1Run ps ch
  else if h : OpenedX1PinnedAccept urs hk vk instanceCommitment ps ch χv then
    (show ∃ run : X1Run shape G, X1PinnedRunAccepts urs hk vk instanceCommitment ps ch χv run from h).choose
  else honestX1Run ps ch

/-- The canonical pinned `x₁` run carries the accept payload whenever the event holds. -/
theorem canonicalX1Run_accepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {χv : Fp} (h : OpenedX1PinnedAccept urs hk vk instanceCommitment ps ch χv) :
    X1PinnedRunAccepts urs hk vk instanceCommitment ps ch χv (canonicalX1Run urs hk vk instanceCommitment ps ch χv) := by
  rw [canonicalX1Run]
  by_cases hh : X1PinnedRunAccepts urs hk vk instanceCommitment ps ch χv (honestX1Run ps ch)
  · rw [dif_pos hh]; exact hh
  · rw [dif_neg hh, dif_pos h]
    exact (show ∃ run : X1Run shape G, X1PinnedRunAccepts urs hk vk instanceCommitment ps ch χv run from h).choose_spec

/-- **Honest-preferring collapse (`x₁`).** -/
theorem canonicalX1Run_honest [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {χv : Fp}
    (hh : X1PinnedRunAccepts urs hk vk instanceCommitment ps ch χv (honestX1Run ps ch)) :
    canonicalX1Run urs hk vk instanceCommitment ps ch χv = honestX1Run ps ch := by
  rw [canonicalX1Run, dif_pos hh]

/-! ## The canonical-run grid extraction -/

/-- **`openedX3_rewound_batch_eval` at the canonical run.** The single-slot `x₄` floor at the
*canonical* `x₃` run's base — exactly what the joint floor's heavy fiber supplies — replaces the
`∀`-over-`X3Run` floor family: the accept event's run is the canonical one by construction, so the
floor is spent at precisely the run the extraction opens. Same conclusion: one batch whose decoded
column at every slot evaluates at `χ` to the slot's claimed evaluation. -/
theorem openedX3_rewound_batch_eval_canonical [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {χ : Fp}
    (hprob4 : (deployedX4PairCount vk instanceCommitment
          ((canonicalX3Run urs hk vk instanceCommitment ps ch (evalVector urs.k χ) χ).spliced ps)
          ((canonicalX3Run urs hk vk instanceCommitment ps ch (evalVector urs.k χ) χ).challenges ch χ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk instanceCommitment
              ((canonicalX3Run urs hk vk instanceCommitment ps ch (evalVector urs.k χ) χ).spliced ps)
              ((canonicalX3Run urs hk vk instanceCommitment ps ch (evalVector urs.k χ) χ).challenges ch χ)
              (evalVector urs.k χ))))
    (hacc : OpenedX3Accept urs hk vk instanceCommitment ps ch (evalVector urs.k χ) χ) :
    ∃ (r : X3Run shape G) (a : Fin (2 ^ urs.k) → Fp) (pU pW : Fp)
      (batch : OpenedBatchOpenings urs (evalVector urs.k χ)
        (x4BatchCommitments urs hk vk instanceCommitment (r.spliced ps) (r.challenges ch χ))
        (x4BatchEvals vk instanceCommitment (r.spliced ps) (r.challenges ch χ)) a pU pW),
      ∀ j, (openedDecodedCols batch j).eval χ
        = x4BatchEvals vk instanceCommitment (r.spliced ps) (r.challenges ch χ) j := by
  obtain ⟨z, blind, fs, t, ht⟩ :=
    canonicalX3Run_accepts urs hk vk instanceCommitment ps ch (evalVector urs.k χ) hacc
  obtain ⟨a, ha⟩ := ipaRelation_extract urs (evalVector urs.k χ) fs.openedCommitment
    (multiopenValue vk instanceCommitment ((canonicalX3Run urs hk vk instanceCommitment ps ch (evalVector urs.k χ) χ).spliced ps)
      ((canonicalX3Run urs hk vk instanceCommitment ps ch (evalVector urs.k χ) χ).challenges ch χ)) t ht
  refine ⟨canonicalX3Run urs hk vk instanceCommitment ps ch (evalVector urs.k χ) χ, a, fs.pU, fs.pW,
    openedX4Rewind_of_x4Prob_forked urs hk vk instanceCommitment
      ((canonicalX3Run urs hk vk instanceCommitment ps ch (evalVector urs.k χ) χ).spliced ps)
      ((canonicalX3Run urs hk vk instanceCommitment ps ch (evalVector urs.k χ) χ).challenges ch χ) fs ⟨t, ht⟩
      hprob4 a ha, ?_⟩
  intro j
  exact openedDecodedCols_eval_x3 urs hk vk instanceCommitment
    ((canonicalX3Run urs hk vk instanceCommitment ps ch (evalVector urs.k χ) χ).spliced ps)
    ((canonicalX3Run urs hk vk instanceCommitment ps ch (evalVector urs.k χ) χ).challenges ch χ) _ j

/-! ## The inner joint accept event and the budgeted value check -/

/-- **The inner joint accept event** over the `(x₂, x₃, x₄)` challenge draw at a fixed base: the
`x₂` rewind accepts at `v.1`; the `x₃` rewind accepts at `v.2.1` at the *canonical* `x₂` run's
base; the `x₄` rewind accepts at `v.2.2` at the *canonical* `x₃` run's base. The canonical
selectors make every level's base a function of the earlier challenges, so this is a genuine event
over `Fp × Fp × Fp` — the budgeted replacement for the `∀`-over-runs floor family of
`deployed_value_check_node_binding`. -/
def innerJointAccept [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b₂ : Fin (2 ^ urs.k) → Fp) : Set (Fp × Fp × Fp) :=
  {v : Fp × Fp × Fp |
    OpenedX2Accept urs hk vk instanceCommitment ps ch b₂ v.1 ∧
    OpenedX3Accept urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ v.1).spliced ps)
      ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ v.1).challenges ch v.1)
      (evalVector urs.k v.2.1) v.2.1 ∧
    OpenedX4Accept urs hk vk instanceCommitment
      ((canonicalX3Run urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ v.1).spliced ps)
          ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ v.1).challenges ch v.1)
          (evalVector urs.k v.2.1) v.2.1).spliced
        ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ v.1).spliced ps))
      ((canonicalX3Run urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ v.1).spliced ps)
          ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ v.1).challenges ch v.1)
          (evalVector urs.k v.2.1) v.2.1).challenges
        ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ v.1).challenges ch v.1) v.2.1)
      (evalVector urs.k v.2.1) v.2.2}

/-- Componentwise membership introduction for `innerJointAccept` (also the sanity check that the
tuple projections reduce to the plain challenges). -/
theorem innerJointAccept_mk [DecidableEq G] [Inhabited G] {shape : Shape} {urs : URS G}
    {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G} {instanceCommitment : Fin shape.numProofs → ℕ → G} {ps : ProofString shape Fp G}
    {ch : Challenges shape.k Fp} {b₂ : Fin (2 ^ urs.k) → Fp} {ζv χv ωv : Fp}
    (h2 : OpenedX2Accept urs hk vk instanceCommitment ps ch b₂ ζv)
    (h3 : OpenedX3Accept urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ ζv).spliced ps)
      ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ ζv).challenges ch ζv) (evalVector urs.k χv) χv)
    (h4 : OpenedX4Accept urs hk vk instanceCommitment
      ((canonicalX3Run urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ ζv).spliced ps)
          ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ ζv).challenges ch ζv)
          (evalVector urs.k χv) χv).spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ ζv).spliced ps))
      ((canonicalX3Run urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ ζv).spliced ps)
          ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ ζv).challenges ch ζv)
          (evalVector urs.k χv) χv).challenges
        ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ ζv).challenges ch ζv) χv)
      (evalVector urs.k χv) ωv) :
    (ζv, χv, ωv) ∈ innerJointAccept urs hk vk instanceCommitment ps ch b₂ :=
  ⟨h2, h3, h4⟩

/-- **The deployed multiopen value check from the joint accept floor.** The conclusion of
`deployed_value_check_node_binding` — each honest `x₄`-slot aggregate takes its claimed
interpolation at each set point, or a `(g, U, W)` relation exists — with the `∀`-over-runs floors
replaced by one joint floor `t₂ + t₃ + t₄ < μ(innerJointAccept)` at the honest-base thresholds.
The Markov descent peels one threshold per squeeze; each heavy set self-anchors and forks into the
sample family.

`t₃ = (max(2^k, |allPts|) + |allPts| + |allPts|) / |F|` is two charges in one line: the first two
summands are the interpolation *degree* bound `d` of `grid_hdeg_bound` (so beating `d/|F|` yields
the `d + 1` distinct samples the cleared-denominator core needs), the third is the *collision*
charge that lets those samples be drawn off `deployedAllPts`
(`exists_injective_accepting_avoiding_of_measure`). Acceptance cannot supply the latter — at a
colliding `χ` the verifier computes `(x₃ − p)⁻¹ = 0⁻¹ = 0` and the multiopen check degenerates
instead of failing — so it is paid for here, which is what retires the sample-avoidance hypothesis
this theorem used to take. -/
theorem deployed_value_check_node_binding_budgeted [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (b₂ : Fin (2 ^ urs.k) → Fp)
    (hJ : ((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp
      < (PMF.uniformOfFintype (Fp × Fp × Fp)).toOuterMeasure
          (innerJointAccept urs hk vk instanceCommitment ps ch b₂))
    (j₀ : Fin (deployedX4PairCount vk instanceCommitment ps ch)) {p : Fp}
    (hp : p ∈ deployedSetPts vk instanceCommitment ps ch (deployedX4PairCount vk instanceCommitment ps ch - 1 - (j₀ : ℕ))) :
    (openedDecodedCols pbatch ⟨(j₀ : ℕ), Nat.lt_succ_of_lt j₀.isLt⟩).eval p
        = (lagrangePoly ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j₀ : ℕ) ([], [], 0)).1
            ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j₀ : ℕ) ([], [], 0)).2.1).eval p
      ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  classical
  by_cases hrel : HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
  · exact Or.inr hrel
  refine Or.inl ?_
  have hcpos : 0 < deployedX4PairCount vk instanceCommitment ps ch := lt_of_le_of_lt (Nat.zero_le _) j₀.isLt
  have hn : deployedX4PairCount vk instanceCommitment ps ch - 1 + 1 = deployedX4PairCount vk instanceCommitment ps ch :=
    Nat.succ_pred_eq_of_pos hcpos
  have hcard0 : ((Fintype.card Fp : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have ht₃top : ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
      + (deployedAllPts vk instanceCommitment ps ch).card
      + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp ≠ ⊤ :=
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) hcard0).ne
  have ht₄top : (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp ≠ ⊤ :=
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) hcard0).ne
  -- level-2 descent: the heavy separation challenges keep the residual x₃+x₄ floor
  rw [add_assoc] at hJ
  have hheavy2 := uniformOfFintype_heavy_fiber_lt (α := Fp) (β := Fp × Fp)
    (innerJointAccept urs hk vk instanceCommitment ps ch b₂) (ENNReal.add_ne_top.mpr ⟨ht₃top, ht₄top⟩) hJ
  -- the x₂ sample family, reindexed to `Fin count`, each sample carrying its inner floor
  have hζfam : ∃ ζ : Fin (deployedX4PairCount vk instanceCommitment ps ch) → Fp,
      Function.Injective ζ ∧ ∀ s,
        ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fp × Fp)).toOuterMeasure
            {vw : Fp × Fp | (ζ s, vw) ∈ innerJointAccept urs hk vk instanceCommitment ps ch b₂} := by
    have hne : {ζv : Fp |
        ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fp × Fp)).toOuterMeasure
            {vw : Fp × Fp | (ζv, vw) ∈ innerJointAccept urs hk vk instanceCommitment ps ch b₂}}.Nonempty := by
      refine nonempty_of_uniformOfFintype_toOuterMeasure_ne_zero (fun h0 => ?_)
      rw [h0] at hheavy2
      exact absurd hheavy2 (not_lt.mpr zero_le)
    obtain ⟨ζ₀, hζ₀⟩ := hne
    rw [uniformOfFintype_toOuterMeasure_setOf_filter] at hheavy2
    obtain ⟨ζ', hinj, _, hacc⟩ := exists_injective_accepting_of_measure
      (acc := fun ζv =>
        ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fp × Fp)).toOuterMeasure
            {vw : Fp × Fp | (ζv, vw) ∈ innerJointAccept urs hk vk instanceCommitment ps ch b₂})
      hζ₀ hheavy2
    exact ⟨fun s => ζ' (Fin.cast hn.symm s),
      fun a b h => Fin.cast_injective hn.symm (hinj h), fun s => hacc _⟩
  obtain ⟨ζ, hζinj, hζheavy⟩ := hζfam
  -- each sampled fiber is nonempty, so each sample's x₂ rewind accepts
  have hζacc : ∀ s, OpenedX2Accept urs hk vk instanceCommitment ps ch b₂ (ζ s) := by
    intro s
    have hne : {vw : Fp × Fp | (ζ s, vw) ∈ innerJointAccept urs hk vk instanceCommitment ps ch b₂}.Nonempty := by
      refine nonempty_of_uniformOfFintype_toOuterMeasure_ne_zero (fun h0 => ?_)
      have := hζheavy s
      rw [h0] at this
      exact absurd this (not_lt.mpr zero_le)
    obtain ⟨vw, hvw⟩ := hne
    exact hvw.1
  -- level-3 descent per x₂ sample: the heavy interpolation challenges keep the x₄ floor, and the
  -- collision summand of `t₃` buys them off the opened set points
  have hχfam : ∀ s : Fin (deployedX4PairCount vk instanceCommitment ps ch),
      ∃ ξ : Fin (max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
          + (deployedAllPts vk instanceCommitment ps ch).card + 1) → Fp,
        Function.Injective ξ ∧ ∀ t,
          ((deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp
            < (PMF.uniformOfFintype Fp).toOuterMeasure
                {ωv : Fp | (ζ s, ξ t, ωv) ∈ innerJointAccept urs hk vk instanceCommitment ps ch b₂})
          ∧ ξ t ∉ deployedAllPts vk instanceCommitment ps ch := by
    intro s
    have hheavy3 := uniformOfFintype_heavy_fiber_lt (α := Fp) (β := Fp)
      {vw : Fp × Fp | (ζ s, vw) ∈ innerJointAccept urs hk vk instanceCommitment ps ch b₂} ht₄top (hζheavy s)
    rw [uniformOfFintype_toOuterMeasure_setOf_filter] at hheavy3
    exact exists_injective_accepting_avoiding_of_measure
      (acc := fun χv =>
        (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp
          < (PMF.uniformOfFintype Fp).toOuterMeasure
              {ωv : Fp | (ζ s, χv, ωv) ∈ innerJointAccept urs hk vk instanceCommitment ps ch b₂})
      (deployedAllPts vk instanceCommitment ps ch) hheavy3
  choose χ hχinj hχboth using hχfam
  have hχavoid : ∀ s t, χ s t ∉ deployedAllPts vk instanceCommitment ps ch := fun s t => (hχboth s t).2
  -- each sampled fiber is nonempty, so each sample's x₃ rewind accepts
  have hχacc : ∀ s t, OpenedX3Accept urs hk vk instanceCommitment
      ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps)
      ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
      (evalVector urs.k (χ s t)) (χ s t) := by
    intro s t
    have hne4 : {ωv : Fp | (ζ s, χ s t, ωv) ∈ innerJointAccept urs hk vk instanceCommitment ps ch b₂}.Nonempty := by
      refine nonempty_of_uniformOfFintype_toOuterMeasure_ne_zero (fun h0 => ?_)
      have := (hχboth s t).1
      rw [h0] at this
      exact absurd this (not_lt.mpr zero_le)
    obtain ⟨ωv, hωv⟩ := hne4
    exact hωv.2.1
  -- the sampled x₄ fiber is exactly the opened x₄ accept event at the canonical x₃ run's base
  have hχfloor : ∀ s t,
      (deployedX4PairCount vk instanceCommitment
          ((canonicalX3Run urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps)
              ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
              (evalVector urs.k (χ s t)) (χ s t)).spliced
            ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
          ((canonicalX3Run urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps)
              ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
              (evalVector urs.k (χ s t)) (χ s t)).challenges
            ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s)) (χ s t)) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk instanceCommitment
              ((canonicalX3Run urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps)
                  ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
                  (evalVector urs.k (χ s t)) (χ s t)).spliced
                ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
              ((canonicalX3Run urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps)
                  ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
                  (evalVector urs.k (χ s t)) (χ s t)).challenges
                ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s)) (χ s t))
              (evalVector urs.k (χ s t)))) := by
    intro s t
    have hsetEq : {ωv : Fp | (ζ s, χ s t, ωv) ∈ innerJointAccept urs hk vk instanceCommitment ps ch b₂}
        = {ωv : Fp | OpenedX4Accept urs hk vk instanceCommitment
            ((canonicalX3Run urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps)
                ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
                (evalVector urs.k (χ s t)) (χ s t)).spliced
              ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
            ((canonicalX3Run urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps)
                ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
                (evalVector urs.k (χ s t)) (χ s t)).challenges
              ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s)) (χ s t))
            (evalVector urs.k (χ s t)) ωv} :=
      Set.ext fun ωv => ⟨fun h => h.2.2, fun h => ⟨hζacc s, hχacc s t, h⟩⟩
    have hccK : deployedX4PairCount vk instanceCommitment
        ((canonicalX3Run urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps)
            ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
            (evalVector urs.k (χ s t)) (χ s t)).spliced
          ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
        ((canonicalX3Run urs hk vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps)
            ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
            (evalVector urs.k (χ s t)) (χ s t)).challenges
          ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s)) (χ s t))
        = deployedX4PairCount vk instanceCommitment ps ch :=
      (x3Run_pairCount vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps)
          ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s)) _ (χ s t)).trans
        (x2Run_pairCount vk instanceCommitment ps ch _ (ζ s))
    rw [hccK, ← uniformOfFintype_toOuterMeasure_setOf_filter, ← hsetEq]
    exact (hχboth s t).1
  -- per-grid-point extracted batch with all-slot values, from the canonical grid extraction
  have hbat : ∀ (s : Fin (deployedX4PairCount vk instanceCommitment ps ch))
      (t : Fin (max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
        + (deployedAllPts vk instanceCommitment ps ch).card + 1)),
      ∃ (r₃ : X3Run shape G) (a : Fin (2 ^ urs.k) → Fp) (pUχ pWχ : Fp)
        (B : OpenedBatchOpenings urs (evalVector urs.k (χ s t))
          (x4BatchCommitments urs hk vk instanceCommitment
            (r₃.spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
            (r₃.challenges ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
              (χ s t)))
          (x4BatchEvals vk instanceCommitment
            (r₃.spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
            (r₃.challenges ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
              (χ s t))) a pUχ pWχ),
        ∀ j, (openedDecodedCols B j).eval (χ s t)
          = x4BatchEvals vk instanceCommitment
              (r₃.spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
              (r₃.challenges ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
                (χ s t)) j :=
    fun s t => openedX3_rewound_batch_eval_canonical urs hk vk instanceCommitment
      ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps)
      ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
      (hχfloor s t) (hχacc s t)
  choose r₃f aF pUF pWF Bf hBspec using hbat
  -- pair counts of the doubly-rewound runs
  have hccst : ∀ s t, deployedX4PairCount vk instanceCommitment
      ((r₃f s t).spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
      ((r₃f s t).challenges ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
        (χ s t))
        = deployedX4PairCount vk instanceCommitment ps ch := fun s t =>
    (x3Run_pairCount vk instanceCommitment ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps)
      ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s)) (r₃f s t)
      (χ s t)).trans (x2Run_pairCount vk instanceCommitment ps ch _ (ζ s))
  -- premise: value-check set lengths
  have hlen' : ∀ s t, (deployedSetsForEval vk instanceCommitment
      ((r₃f s t).spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
      ((r₃f s t).challenges ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
        (χ s t))).length
        = deployedX4PairCount vk instanceCommitment ps ch :=
    fun s t => (deployedSetsForEval_length vk instanceCommitment _ _).trans (hccst s t)
  -- premise: the grid runs' sets share the honest points and compressed evals
  have hsetpts' : ∀ s t (j : Fin (deployedX4PairCount vk instanceCommitment ps ch)),
      ((deployedSetsForEval vk instanceCommitment
        ((r₃f s t).spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
        ((r₃f s t).challenges ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
          (χ s t))).reverse.getD (j : ℕ) ([], [], 0)).1
        = ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : ℕ) ([], [], 0)).1 :=
    fun s t j => (deployedSetsForEval_x2x3_reverse_getD_fields vk instanceCommitment ps ch _ (ζ s)
      (r₃f s t) (χ s t) j.isLt).1
  have hsetevals' : ∀ s t (j : Fin (deployedX4PairCount vk instanceCommitment ps ch)),
      ((deployedSetsForEval vk instanceCommitment
        ((r₃f s t).spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
        ((r₃f s t).challenges ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
          (χ s t))).reverse.getD (j : ℕ) ([], [], 0)).2.1
        = ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : ℕ) ([], [], 0)).2.1 :=
    fun s t j => (deployedSetsForEval_x2x3_reverse_getD_fields vk instanceCommitment ps ch _ (ζ s)
      (r₃f s t) (χ s t) j.isLt).2
  -- premise: the uniform degree bound
  have hdeg' : ∀ s, ((openedDecodedCols (Bf s 0)
      ⟨deployedX4PairCount vk instanceCommitment
        ((r₃f s 0).spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
        ((r₃f s 0).challenges ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
          (χ s 0)), Nat.lt_succ_self _⟩)
        * vanishingProd (deployedAllPts vk instanceCommitment ps ch)
      - ∑ j : Fin (deployedX4PairCount vk instanceCommitment ps ch), C (ζ s ^ (j : ℕ)) *
          ((openedDecodedCols pbatch ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩
            - lagrangePoly ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : ℕ) ([], [], 0)).1
                ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : ℕ) ([], [], 0)).2.1)
            * coProd (deployedAllPts vk instanceCommitment ps ch)
                (deployedSetPts vk instanceCommitment ps ch
                  (deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ))))).natDegree
      ≤ max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card + (deployedAllPts vk instanceCommitment ps ch).card := by
    intro s
    refine grid_hdeg_bound (deployedAllPts vk instanceCommitment ps ch)
      (fun j => deployedSetPts vk instanceCommitment ps ch (deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ)))
      (fun j => openedDecodedCols pbatch ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩)
      (fun j => lagrangePoly
        ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : ℕ) ([], [], 0)).1
        ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : ℕ) ([], [], 0)).2.1)
      (fun s' => openedDecodedCols (Bf s' 0)
        ⟨deployedX4PairCount vk instanceCommitment
          ((r₃f s' 0).spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s')).spliced ps))
          ((r₃f s' 0).challenges
            ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s')).challenges ch (ζ s')) (χ s' 0)),
          Nat.lt_succ_self _⟩)
      ζ ?_ ?_ s
    · intro s'
      exact le_trans (le_of_lt (coeffsToPoly_natDegree_lt (by positivity) _))
        (le_max_left _ _)
    · intro j
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · exact le_trans (le_of_lt (coeffsToPoly_natDegree_lt (by positivity) _))
          (le_max_left _ _)
      · have hnd := deployedSetsForEval_reverse_getD_nodup vk instanceCommitment ps ch j.isLt
        have hle := lagrangePoly_natDegree_le
          (points := ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : ℕ) ([], [], 0)).1)
          (evals := ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : ℕ) ([], [], 0)).2.1)
          (List.nodup_iff_injective_getElem.mp hnd)
        have hcard : ((deployedSetsForEval vk instanceCommitment ps ch).reverse.getD (j : ℕ) ([], [], 0)).1.length
            ≤ (deployedAllPts vk instanceCommitment ps ch).card := by
          rw [← List.toFinset_card_of_nodup hnd,
            deployedSetsForEval_reverse_getD_toFinset vk instanceCommitment ps ch j.isLt]
          exact Finset.card_le_card (deployedSetPts_subset vk instanceCommitment ps ch _)
        exact le_trans (le_trans hle hcard) (le_max_right _ _)
  -- premise: the samples avoid the nodes — they were drawn off `deployedAllPts`, which every set's
  -- points sit inside
  have hnode' : ∀ s t (j : Fin (deployedX4PairCount vk instanceCommitment ps ch)),
      (vanishingProd (deployedSetPts vk instanceCommitment ps ch
        (deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ)))).eval (χ s t) ≠ 0 :=
    fun s t j => vanishingProd_eval_ne
      (fun hmem => hχavoid s t (deployedSetPts_subset vk instanceCommitment ps ch _ hmem))
  -- premise: the run openings (top slot, t-independent via the fixed-q′ pair binding)
  have hopen' : ∀ s t, (openedDecodedCols (Bf s 0)
      ⟨deployedX4PairCount vk instanceCommitment
        ((r₃f s 0).spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
        ((r₃f s 0).challenges ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
          (χ s 0)), Nat.lt_succ_self _⟩).eval (χ s t)
      = multiopenEval (ζ s) (χ s t) (deployedSetsForEval vk instanceCommitment
          ((r₃f s t).spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
          ((r₃f s t).challenges ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
            (χ s t))) := by
    intro s t
    rcases openedX3_qprime_binding_pair urs hk vk instanceCommitment
        ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps)
        ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
        (r₃f s 0) (r₃f s t) (Bf s 0) (Bf s t) with heq | hdlr
    · rw [heq, hBspec s t, x4BatchEvals_top]
      exact deployedBaseEval_eq_multiopenEval vk instanceCommitment _ _
    · exact absurd hdlr hrel
  -- premise: the honest aggregate takes the grid runs' claimed set evals
  have hu' : ∀ s t (j : Fin (deployedX4PairCount vk instanceCommitment ps ch)),
      (openedDecodedCols pbatch ⟨(j : ℕ), Nat.lt_succ_of_lt j.isLt⟩).eval (χ s t)
        = ((deployedSetsForEval vk instanceCommitment
            ((r₃f s t).spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
            ((r₃f s t).challenges
              ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
              (χ s t))).reverse.getD (j : ℕ) ([], [], 0)).2.2 := by
    intro s t j
    have hjlt : deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ) < deployedX4PairCount vk instanceCommitment ps ch := by
      have := j.isLt; omega
    rcases openedX2X3_agg_binding urs hk vk instanceCommitment ps ch
        (canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)) (r₃f s t)
        (deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ)) hjlt pbatch (Bf s t) with heq | hdlr
    swap
    · exact absurd hdlr hrel
    have hval1 : deployedX4PairCount vk instanceCommitment ps ch - 1
        - (deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ)) = (j : ℕ) := by
      have := j.isLt; omega
    simp only [hval1] at heq
    rw [heq, hBspec s t]
    have hval2 : deployedX4PairCount vk instanceCommitment
        ((r₃f s t).spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
        ((r₃f s t).challenges ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
          (χ s t)) - 1
        - (deployedX4PairCount vk instanceCommitment ps ch - 1 - (j : ℕ)) = (j : ℕ) := by
      have h1 := hccst s t
      have h2 := j.isLt
      omega
    simp only [hval2]
    exact (deployedSetsForEval_reverse_getD_u vk instanceCommitment _ _
      (by rw [hccst s t]; exact j.isLt)).symm
  -- assemble
  exact deployed_node_binding_of_grid urs hk vk instanceCommitment ps ch pbatch
    (max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card + (deployedAllPts vk instanceCommitment ps ch).card)
    ζ hζinj χ hχinj
    (fun s => openedDecodedCols (Bf s 0)
      ⟨deployedX4PairCount vk instanceCommitment
        ((r₃f s 0).spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
        ((r₃f s 0).challenges ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
          (χ s 0)), Nat.lt_succ_self _⟩)
    (fun s t => deployedSetsForEval vk instanceCommitment
      ((r₃f s t).spliced ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).spliced ps))
      ((r₃f s t).challenges ((canonicalX2Run urs hk vk instanceCommitment ps ch b₂ (ζ s)).challenges ch (ζ s))
        (χ s t)))
    hlen' hsetpts' hsetevals' hdeg' hnode' hopen' hu' j₀ hp

/-! ## The full joint accept event and the budgeted member terminal -/

/-- **The full joint accept event** over the `(x₁, x₂, x₃, x₄)` challenge draw: the pinned `x₁`
rewind accepts at `w.1` (carrying its own opened `x₄` batch), and the inner joint event holds at
the *canonical* `x₁` run's base with the `x₂` blinder supplied by the strategy `b₂f` at that
challenge. Every level's base is a function of the earlier challenges through the canonical
selectors, so this is a genuine event over `Fp⁴` — the single-event replacement for the whole
`∀`-over-runs floor family of `deployed_member_node_binding`. -/
def memberJointAccept [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b₂f : Fp → Fin (2 ^ urs.k) → Fp) :
    Set (Fp × Fp × Fp × Fp) :=
  {w : Fp × Fp × Fp × Fp | OpenedX1PinnedAccept urs hk vk instanceCommitment ps ch w.1 ∧
    w.2 ∈ innerJointAccept urs hk vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch w.1).spliced ps)
      ((canonicalX1Run urs hk vk instanceCommitment ps ch w.1).challenges ch w.1) (b₂f w.1)}

/-- **The budgeted member terminal.** The conclusion of `deployed_member_node_binding` — each
decoded member column takes its claimed evaluation at each set point, or a `(g, U, W)` relation
exists — with the entire nested floor family replaced by the single joint floor
`t₁ + (t₂ + t₃ + t₄) < μ(memberJointAccept)` at the honest-base thresholds. The Markov descent
peels the `x₁` threshold and forks the member samples, each carrying the inner floor its canonical
base spends (`deployed_value_check_node_binding_budgeted`), whose `t₃` already pays the sample
collision charge — so the floor is the only premise. -/
theorem deployed_member_node_binding_budgeted [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW}
    (i : ℕ) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (md : OpenedMemberDecode urs hk vk instanceCommitment ps ch pbatch i hi)
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk instanceCommitment ps ch b₂f))
    (hql : ∀ qc ∈ deployedSetQueries vk instanceCommitment ps ch i,
      qc.2.length
        = ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length)
    (idx : Fin ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length)
    (m₀ : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) :
    (coeffsToPoly (md.cols m₀)).eval
        (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [])[idx])
      = ((deployedSetQueries vk instanceCommitment ps ch i).getD (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
    ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  classical
  by_cases hrel : HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
  · exact Or.inr hrel
  refine Or.inl ?_
  have hnpos : 0 < (deployedSetQueries vk instanceCommitment ps ch i).length :=
    lt_of_le_of_lt (Nat.zero_le _) m₀.isLt
  have hnn : (deployedSetQueries vk instanceCommitment ps ch i).length - 1 + 1
      = (deployedSetQueries vk instanceCommitment ps ch i).length := Nat.succ_pred_eq_of_pos hnpos
  have hcard0 : ((Fintype.card Fp : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- the residual (inner) threshold is finite
  have htres : (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
      + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
          + (deployedAllPts vk instanceCommitment ps ch).card
          + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
      + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨(ENNReal.div_lt_top (ENNReal.natCast_ne_top _) hcard0).ne,
          (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) hcard0).ne⟩,
        (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) hcard0).ne⟩
  -- level-1 descent: the heavy compression challenges keep the inner x₂+x₃+x₄ floor
  have hheavy1 := uniformOfFintype_heavy_fiber_lt (α := Fp) (β := Fp × Fp × Fp)
    (memberJointAccept urs hk vk instanceCommitment ps ch b₂f) htres hJ
  -- the x₁ sample family, reindexed to the member count, each sample carrying the inner floor
  have hξfam : ∃ ξ : Fin (deployedSetQueries vk instanceCommitment ps ch i).length → Fp,
      Function.Injective ξ ∧ ∀ s,
        ((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fp × Fp × Fp)).toOuterMeasure
            {v : Fp × Fp × Fp | (ξ s, v) ∈ memberJointAccept urs hk vk instanceCommitment ps ch b₂f} := by
    have hne : {ξv : Fp |
        ((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fp × Fp × Fp)).toOuterMeasure
            {v : Fp × Fp × Fp | (ξv, v) ∈ memberJointAccept urs hk vk instanceCommitment ps ch b₂f}}.Nonempty := by
      refine nonempty_of_uniformOfFintype_toOuterMeasure_ne_zero (fun h0 => ?_)
      rw [h0] at hheavy1
      exact absurd hheavy1 (not_lt.mpr zero_le)
    obtain ⟨ξ₀', hξ₀'⟩ := hne
    rw [uniformOfFintype_toOuterMeasure_setOf_filter] at hheavy1
    obtain ⟨ξ', hinj, _, hacc⟩ := exists_injective_accepting_of_measure
      (acc := fun ξv =>
        ((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype (Fp × Fp × Fp)).toOuterMeasure
            {v : Fp × Fp × Fp | (ξv, v) ∈ memberJointAccept urs hk vk instanceCommitment ps ch b₂f})
      hξ₀' hheavy1
    exact ⟨fun s => ξ' (Fin.cast hnn.symm s),
      fun a b h => Fin.cast_injective hnn.symm (hinj h), fun s => hacc _⟩
  obtain ⟨ξ, hξinj, hξheavy⟩ := hξfam
  -- each sampled fiber is nonempty, so each sample's pinned x₁ rewind accepts
  have hpin : ∀ s, OpenedX1PinnedAccept urs hk vk instanceCommitment ps ch (ξ s) := by
    intro s
    have hne : {v : Fp × Fp × Fp |
        (ξ s, v) ∈ memberJointAccept urs hk vk instanceCommitment ps ch b₂f}.Nonempty := by
      refine nonempty_of_uniformOfFintype_toOuterMeasure_ne_zero (fun h0 => ?_)
      have := hξheavy s
      rw [h0] at this
      exact absurd this (not_lt.mpr zero_le)
    obtain ⟨v, hv⟩ := hne
    exact hv.1
  -- the sampled fiber is the inner joint event at the canonical x₁ base
  have hinner : ∀ s,
      ((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp
      < (PMF.uniformOfFintype (Fp × Fp × Fp)).toOuterMeasure
          (innerJointAccept urs hk vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
            ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)) (b₂f (ξ s))) := by
    intro s
    have hset : {v : Fp × Fp × Fp | (ξ s, v) ∈ memberJointAccept urs hk vk instanceCommitment ps ch b₂f}
        = innerJointAccept urs hk vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
            ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)) (b₂f (ξ s)) :=
      Set.ext fun v => ⟨fun h => h.2, fun h => ⟨hpin s, h⟩⟩
    rw [← hset]
    exact hξheavy s
  -- per-sample canonical-run payload: the pinned x₄ batch at the canonical base
  have hbatch : ∀ s, ∃ (aR : Fin (2 ^ urs.k) → Fp) (pUR pWR : Fp),
      Nonempty (OpenedBatchOpenings urs
        (evalVector urs.k (((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)).x3))
        (x4BatchCommitments urs hk vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
          ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)))
        (x4BatchEvals vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
          ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s))) aR pUR pWR) := by
    intro s
    obtain ⟨aR, pUR, pWR, _, hne⟩ := canonicalX1Run_accepts urs hk vk instanceCommitment ps ch (hpin s)
    exact ⟨aR, pUR, pWR, hne⟩
  choose aF pUF pWF hBne using hbatch
  -- the node: the idx-th point of set i
  have hndp := constructIntermediateSets_points_nodup (assembleQueries vk instanceCommitment ps ch) i
  have hnodeinj := List.nodup_iff_injective_getElem.mp hndp
  -- per-sample aggregate identity: the ξ-fold of the member values equals the ξ-fold of the
  -- claimed evaluations
  have hagg : ∀ s : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
      ∑ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
          ξ s ^ (m : ℕ) * (coeffsToPoly (md.cols m)).eval
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [])[idx])
        = ∑ m : Fin (deployedSetQueries vk instanceCommitment ps ch i).length,
            ξ s ^ (m : ℕ)
              * ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0 := by
    intro s
    have hcc : deployedX4PairCount vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
          ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s))
        = deployedX4PairCount vk instanceCommitment ps ch := x1Run_pairCount vk instanceCommitment ps ch _ (ξ s)
    -- the node lies in set i at the ξ-rewound base
    have hp_i : (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [])[idx])
        ∈ deployedSetPts vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
            ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)) i := by
      rw [x1Run_setPts, deployedSetPts]
      exact List.mem_toFinset.mpr (List.getElem_mem idx.isLt)
    -- the inner joint floor, thresholds transported across the x₁ splice
    have hJ_s : ((deployedX4PairCount vk instanceCommitment
            ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
            ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)) - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment
              ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
              ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s))).card
            + (deployedAllPts vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
              ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s))).card
            + (deployedAllPts vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
              ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s))).card : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        + (deployedX4PairCount vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
            ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype (Fp × Fp × Fp)).toOuterMeasure
            (innerJointAccept urs hk vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
              ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)) (b₂f (ξ s))) := by
      rw [x1Run_pairCount vk instanceCommitment ps ch _ (ξ s), x1Run_allPts vk instanceCommitment ps ch _ (ξ s)]
      exact hinner s
    -- the budgeted value check at the ξ-rewound base
    have hA := deployed_value_check_node_binding_budgeted urs hk vk instanceCommitment
      ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
      ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s))
      (hBne s).some (b₂f (ξ s)) hJ_s
      ⟨deployedX4PairCount vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
          ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)) - 1 - i,
        by omega⟩
      (by
        rw [show deployedX4PairCount vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
            ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)) - 1
            - (deployedX4PairCount vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
                ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)) - 1 - i) = i from
          by omega]
        exact hp_i)
    rcases hA with hA | hdlr
    swap
    · exact absurd hdlr hrel
    -- reverse → forward set fields at the ξ-base
    have hrev : (deployedSetsForEval vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
          ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s))).reverse.getD
            (deployedX4PairCount vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
              ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)) - 1 - i) ([], [], 0)
        = (deployedSetsForEval vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
            ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s))).getD i ([], [], 0) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_reverse (by rw [deployedSetsForEval_length, hcc]; omega),
        deployedSetsForEval_length,
        show deployedX4PairCount vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
            ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)) - 1
          - (deployedX4PairCount vk instanceCommitment ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).spliced ps)
              ((canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)).challenges ch (ξ s)) - 1 - i) = i from
          by omega,
        ← List.getD_eq_getElem?_getD]
    obtain ⟨hfpts, hfevals⟩ :=
      deployedSetsForEval_x1_getD_fields vk instanceCommitment ps ch (canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)) (ξ s) hi
    rw [hrev, hfpts, hfevals] at hA
    -- the interpolant takes the compressed claimed evaluation at the node
    rw [lagrangePoly_eval_node hnodeinj idx] at hA
    rw [compressSet_snd_getD (ξ s) (deployedSetQueries vk instanceCommitment ps ch i) (.point 0, [])
      idx.isLt hql] at hA
    -- the aggregate is the ξ-fold of the member values
    have hB := openedX1_agg_member_eval urs hk vk instanceCommitment ps ch i hi md
      (canonicalX1Run urs hk vk instanceCommitment ps ch (ξ s)) (ξ s) (hBne s).some
      (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [])[idx])
    rcases hB with hB | hdlr
    swap
    · exact absurd hdlr hrel
    rw [← hB, hA, ← Fin.sum_univ_eq_sum_range (fun m => ξ s ^ m
      * ((deployedSetQueries vk instanceCommitment ps ch i).getD m (.point 0, [])).2.getD (idx : ℕ) 0)]
  -- separate the members at the distinct samples
  exact member_binding_of_x1_samples (fun m => coeffsToPoly (md.cols m))
    (fun m => ((deployedSetQueries vk instanceCommitment ps ch i).getD (m : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0)
    (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [])[idx])
    ξ hξinj hagg m₀

/-- The budgeted member node binding at a located set point: `deployed_member_node_binding_budgeted`
with the point membership supplied instead of a positional index and the `hql` bookkeeping
discharged (`deployedSetQueries_eval_length`). Each decoded member column takes its claimed
evaluation at any point of its set — located by `idxOf` — or a nontrivial `(g, U, W)` relation
exists. The budgeted counterpart of `deployed_member_node_binding_at_point`
(`Soundness.Multiopen.NodeBinding`), same conclusion from the joint accept floor. -/
theorem deployed_member_node_binding_at_point_budgeted [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW}
    (i : ℕ) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (md : OpenedMemberDecode urs hk vk instanceCommitment ps ch pbatch i hi)
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp)
    (hJ : (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
      < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
          (memberJointAccept urs hk vk instanceCommitment ps ch b₂f))
    {p : Fp} (hpt : p ∈ deployedSetPts vk instanceCommitment ps ch i)
    (m₀ : Fin (deployedSetQueries vk instanceCommitment ps ch i).length) :
    (coeffsToPoly (md.cols m₀)).eval p
      = ((deployedSetQueries vk instanceCommitment ps ch i).getD (m₀ : ℕ) (.point 0, [])).2.getD
          ((((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf p)) 0
    ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hmem : p ∈ (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [] := by
    rw [deployedSetPts] at hpt
    exact List.mem_toFinset.mp hpt
  have hlt : ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).idxOf p
      < ((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length :=
    List.idxOf_lt_length_iff.mpr hmem
  have hb := deployed_member_node_binding_budgeted urs hk vk instanceCommitment ps ch i hi md b₂f hJ
    (deployedSetQueries_eval_length vk instanceCommitment ps ch i) ⟨_, hlt⟩ m₀
  rcases hb with hb | hdlr
  · refine Or.inl ?_
    rwa [show (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i []))[
        (⟨_, hlt⟩ : Fin _)] = p from List.getElem_idxOf hlt] at hb
  · exact Or.inr hdlr

/-- **The combined soundness budget for the deployed member decode.** *Either* the joint accept
event over the four fresh challenges sits within the knowledge-error budget
`t₁ + (t₂ + t₃ + t₄)` — the four honest-base squeeze thresholds — *or* every decoded member column
of point set `i` takes its claimed evaluation at every one of the set's points (on pain of a
computed `(g, U, W)` relation). The contrapositive reading of the budgeted member terminal: any
adversary whose acceptance mass beats the budget extracts. -/
theorem deployed_member_budget [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW}
    (i : ℕ) (hi : i < deployedX4PairCount vk instanceCommitment ps ch)
    (md : OpenedMemberDecode urs hk vk instanceCommitment ps ch pbatch i hi)
    (b₂f : Fp → Fin (2 ^ urs.k) → Fp) :
    (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
        (memberJointAccept urs hk vk instanceCommitment ps ch b₂f)
      ≤ (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card
              + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
          + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
    ∨ ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).points.getD i []).length)
        (m₀ : Fin (deployedSetQueries vk instanceCommitment ps ch i).length),
        (coeffsToPoly (md.cols m₀)).eval
            (((constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)).points.getD i [])[idx])
          = ((deployedSetQueries vk instanceCommitment ps ch i).getD (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  by_cases hJ : (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
      + (((deployedX4PairCount vk instanceCommitment ps ch - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card
            + (deployedAllPts vk instanceCommitment ps ch).card : ℕ) : ℝ≥0∞) / Fintype.card Fp
        + (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp)
    < (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
        (memberJointAccept urs hk vk instanceCommitment ps ch b₂f)
  · exact Or.inr (fun idx m₀ => deployed_member_node_binding_budgeted urs hk vk instanceCommitment ps ch i hi md
      b₂f hJ (deployedSetQueries_eval_length vk instanceCommitment ps ch i) idx m₀)
  · exact Or.inl (not_lt.mp hJ)

end Zcash.Snark
