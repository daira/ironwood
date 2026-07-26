import Mathlib
import Zcash.Security.Ledger.Balance

/-!
# Probabilistic capstones

The deterministic layer quantifies over valid annotated ledgers. This layer quantifies
over a distribution of them: an adversary is an arbitrary `PMF` over `ValidAnnotated`,
and we do not model the interaction that produced it. That matches the games' stance —
the annotated-ledger quantification is a superset of what a real adversary can reach —
and it keeps the oracle bookkeeping inside the discharge of each per-arm hypothesis,
where the machine models exist.

Restricting the distribution to *valid* ledgers loses no generality. Every game's bad
event requires validity, so mass on invalid ledgers contributes nothing to success:
conditioning any adversary on validity can only increase its success probability, and
a bound for valid-only adversaries implies the bound for all of them.

Events are reduction-branch preimages: "the reduction lands in this arm on this
sample". An existential break predicate would need choice to extract data from; the
branch of a computed reduction needs none. The composition is pure event algebra — the
violation event is contained in the union of the arm events, so its probability is at
most the sum of the per-arm probabilities (`measure_mono` plus `measure_union_le`).
No independence, no counting. Each arm's probability is then bounded by a named ε
hypothesis. The intended discharges — the key-binding arm against the key-binding
layer's probability bound (`toInterface_break_measure_le`), the Merkle and
note-commitment arms against Sinsemilla/DLR hardness — are not wired here yet.
-/

namespace Zcash.Security.Ledger.Model

open scoped ENNReal

variable {F : Type*}
variable {G : Type*}
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}

/-! ## Event algebra -/

/-- Union bound over three events: an event contained in a triple union is bounded by
the sum of the three measures. -/
theorem toOuterMeasure_le_add₃ {α : Type*} (p : PMF α) {E B₁ B₂ B₃ : Set α}
    (h : E ⊆ B₁ ∪ B₂ ∪ B₃) :
    p.toOuterMeasure E
      ≤ p.toOuterMeasure B₁ + p.toOuterMeasure B₂ + p.toOuterMeasure B₃ :=
  le_trans (MeasureTheory.measure_mono h)
    (le_trans (MeasureTheory.measure_union_le _ _)
      (add_le_add (MeasureTheory.measure_union_le _ _) le_rfl))

section Validity

variable [Field F] [AddCommGroup G] [Module F G]
variable {P : Primitives F G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

variable (P kv issuance maxActions) in
/-- The adversary's sample space: a valid witness-annotated ledger, with its validity
proof. Bundling validity is a convenience, not a restriction — a bad event requires
validity, so conditioning any distribution on validity can only increase its success
probability, and a bound over this space implies the bound over bare ledgers. -/
abbrev ValidAnnotated :=
  {ledger : Ledger KW F G RHO PSI MHASH MENC MSG SIG P.depth //
    ValidLedger P kv issuance maxActions ledger}

/-! ## Balance-subset -/

/-- The three arms of a `BalanceBreak`, as a plain tag for naming the arm events. -/
inductive BalanceArm
  | merkle
  | noteCommit
  | keyBinding

/-- The arm a break lies in. -/
def BalanceBreak.arm : BalanceBreak P kv → BalanceArm
  | .merkle _ => .merkle
  | .noteCommit _ => .noteCommit
  | .keyBinding _ _ _ => .keyBinding

variable [DecidableEq F] [DecidableEq G] [DecidableEq RHO] [DecidableEq PSI]
  [DecidableEq MHASH] [DecidableEq MENC] [DecidableEq NK] [NoZeroSMulDivisors F G]

/-- The branch-preimage event for one arm: the samples on which the Balance-subset
reduction lands in that arm. -/
def balanceSubsetBreakEvent (i : ℕ) (arm : BalanceArm) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ b : BalanceBreak P kv, balanceSubsetOrBreak ω.2 i = .inr b ∧ b.arm = arm}

/-- The Balance-subset violation event: the nonzero spends of the first `i + 1`
transactions are not covered by the positioned outputs of the first `i`. -/
def balanceSubsetViolation (i : ℕ) : Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ¬ nonZeroSpends ω.1 (i + 1) ≤ ↑(positionedOutputs ω.1 i)}

/-- A violating sample lands in one of the three arms: on it, the reduction cannot
return the subset proof, so it returns a break, and the break's arm classifies it. -/
theorem balanceSubsetViolation_subset (i : ℕ) :
    balanceSubsetViolation (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) i
      ⊆ balanceSubsetBreakEvent i .merkle ∪ balanceSubsetBreakEvent i .noteCommit
        ∪ balanceSubsetBreakEvent i .keyBinding := by
  intro ω hω
  rcases h : balanceSubsetOrBreak ω.2 i with hle | b
  · exact absurd hle hω
  · cases b with
    | merkle c => exact Or.inl (Or.inl ⟨_, h, rfl⟩)
    | noteCommit nb => exact Or.inl (Or.inr ⟨_, h, rfl⟩)
    | keyBinding w₁ w₂ hbr => exact Or.inr ⟨_, h, rfl⟩

/-- **Balance-subset, probabilistically.** For any adversary — a distribution over
valid annotated ledgers — the probability that the nonzero spends of the first `i + 1`
transactions are not covered by the positioned outputs of the first `i` is at most the
sum of the three break-arm probabilities, each bounded by its named ε hypothesis. -/
theorem balanceSubset_measure_le (A : PMF (ValidAnnotated P kv issuance maxActions))
    (i : ℕ) {εm εnc εkb : ℝ≥0∞}
    (hm : A.toOuterMeasure (balanceSubsetBreakEvent i .merkle) ≤ εm)
    (hnc : A.toOuterMeasure (balanceSubsetBreakEvent i .noteCommit) ≤ εnc)
    (hkb : A.toOuterMeasure (balanceSubsetBreakEvent i .keyBinding) ≤ εkb) :
    A.toOuterMeasure (balanceSubsetViolation i) ≤ εm + εnc + εkb :=
  le_trans (toOuterMeasure_le_add₃ A (balanceSubsetViolation_subset i))
    (add_le_add (add_le_add hm hnc) hkb)

end Validity

end Zcash.Security.Ledger.Model
