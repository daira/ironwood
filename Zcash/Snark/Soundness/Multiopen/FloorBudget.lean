import Zcash.Snark.Soundness.Multiopen.Opened
import Zcash.Snark.Soundness.Forking.Probability

/-!
# Multiopen floor-failure budget

The deployed multiopen value check (`Soundness.Multiopen.NodeBinding`, `Soundness.Vesta`) consumes
forking-floor premises `hprob*` of the shape `threshold < measure(accept over the fresh Fp
challenge)` — one per squeeze `x₁`/`x₂`/`x₃`/`x₄`. Each such floor is a lower bound on the deployed
verifier's accept fraction over the single fresh uniform `Fp` challenge that squeeze reprograms
(`Soundness.Forking.reprogramX{1,2,3,4}`, `Soundness.Forking.Rewind`); the honest run witnesses it,
and `exists_injective_accepting_of_measure` turns it into the rewind samples the extraction spends.

This module prices the *failure* of the floors. Over a single fresh slot, the event "the deployed
run accepts yet the accept-measure sits at or below the threshold" — the negation of the floor —
has probability `≤ threshold` (`squeeze_floor_failure_le`); `openedX4_floor_failure_le` is the
deployed x₄ instantiation, and the other squeezes reuse the template verbatim. The nested union
(`combined_floor_failure_le`, `deployed_combined_floor_failure_le`) prices all four floors at once
at `t₁ + t₂ + t₃ + t₄`, and the heavy-fiber descent primitives at the end of the module are what
the budgeted extraction (`Soundness.Multiopen.BudgetedExtraction`) spends to consume that budget
with no `∀`-over-runs floor hypotheses.
-/

namespace Zcash.Snark

open Zcash.Arithmetic

open scoped ENNReal
open Classical

/-- **Single-squeeze floor-failure bound.** For any single-`Fp`-slot accept predicate `acc` and
threshold `t`, the event "`acc χ` holds but the accept-measure is `≤ t`" — exactly the negation of
the `hprob` floor `t < measure(filter acc)` — has probability `≤ t`. Immediate from
`uniformOfFintype_accept_below_threshold_le` (the threshold condition is `χ`-independent). This is
the reusable core each multiopen squeeze instantiates at its own accept predicate and threshold. -/
theorem squeeze_floor_failure_le (acc : Fp → Prop) [DecidablePred acc] (t : ℝ≥0∞) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        {χ : Fp | acc χ ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter acc))}
      ≤ t := by
  simp only [not_lt]
  exact uniformOfFintype_accept_below_threshold_le acc t

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- **The x₄-squeeze floor-failure bound.** `squeeze_floor_failure_le` at the deployed x₄ accept
predicate `OpenedX4Accept` and threshold `deployedX4PairCount / |Fp|`: over the fresh x₄ challenge
`ξ`, the deployed run accepting while the x₄ rewind accept-measure sits at or below the extraction
threshold — the negation of the terminal's `hprob4` floor — has probability
`≤ deployedX4PairCount / |Fp|`, negligible. `OpenedX4Accept urs hk vk instanceCommitment ps ch b : Fp → Prop` is
already the single-slot predicate over the x₄ challenge (its last argument), so this is a direct
instantiation; the x₃/x₂/x₁ squeezes follow the same template at `OpenedX3/X2/X1Accept` and their
own thresholds. -/
theorem openedX4_floor_failure_le [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        {ξ : Fp | OpenedX4Accept urs hk vk instanceCommitment ps ch b ξ ∧
          ¬ ((deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp
              < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (OpenedX4Accept urs hk vk instanceCommitment ps ch b)))}
      ≤ (deployedX4PairCount vk instanceCommitment ps ch : ℝ≥0∞) / Fintype.card Fp :=
  squeeze_floor_failure_le (OpenedX4Accept urs hk vk instanceCommitment ps ch b) _

/-- **The x₃-squeeze floor-failure bound.** `squeeze_floor_failure_le` at `OpenedX3Accept` and an
arbitrary threshold `t` (the terminal instantiates `t := (max (2 ^ k) |allPts| + |allPts|)/|Fp|`,
the `hprob3` floor threshold): over the fresh x₃ challenge the deployed run accepting while the x₃
rewind accept-measure sits at or below `t` has probability `≤ t`. Same template as
`openedX4_floor_failure_le`. -/
theorem openedX3_floor_failure_le [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp)
    (t : ℝ≥0∞) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        {χ : Fp | OpenedX3Accept urs hk vk instanceCommitment ps ch b χ ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (OpenedX3Accept urs hk vk instanceCommitment ps ch b)))}
      ≤ t :=
  squeeze_floor_failure_le (OpenedX3Accept urs hk vk instanceCommitment ps ch b) t

/-- **The x₂-squeeze floor-failure bound.** `squeeze_floor_failure_le` at `OpenedX2Accept` and an
arbitrary threshold `t` (the terminal instantiates `t := (deployedX4PairCount - 1)/|Fp|`, the `hx2`
floor threshold). Same template as `openedX4_floor_failure_le`. -/
theorem openedX2_floor_failure_le [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp)
    (t : ℝ≥0∞) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        {χ : Fp | OpenedX2Accept urs hk vk instanceCommitment ps ch b χ ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (OpenedX2Accept urs hk vk instanceCommitment ps ch b)))}
      ≤ t :=
  squeeze_floor_failure_le (OpenedX2Accept urs hk vk instanceCommitment ps ch b) t

/-- **The x₁-squeeze floor-failure bound.** `squeeze_floor_failure_le` at `OpenedX1Accept` (which
carries no blinder argument) and an arbitrary threshold `t` (the terminal instantiates
`t := ((deployedSetQueries vk instanceCommitment ps ch i).length - 1)/|Fp|`, the per-set `hprob1` floor threshold).
Same template as `openedX4_floor_failure_le`. -/
theorem openedX1_floor_failure_le [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (t : ℝ≥0∞) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        {χ : Fp | OpenedX1Accept urs hk vk instanceCommitment ps ch χ ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (OpenedX1Accept urs hk vk instanceCommitment ps ch)))}
      ≤ t :=
  squeeze_floor_failure_le (OpenedX1Accept urs hk vk instanceCommitment ps ch) t

/-- **Nested single-squeeze floor-failure bound (the Fubini primitive).** For accept predicates
indexed by an outer base, the event "the inner run accepts at its fresh slot while the inner
accept-measure at that base sits `≤ t`" has probability `≤ t` over the joint draw: at each base the
inner measure is constant in the slot, so the single-slot bound applies fiberwise and
`uniformOfFintype_prod_fiber_bound` lifts it — no slot-dependence leaks across the lift. -/
theorem nested_squeeze_floor_failure_le {B : Type*} [Fintype B] [Nonempty B]
    (acc : B → Fp → Prop) (t : ℝ≥0∞) :
    (PMF.uniformOfFintype (Fp × B)).toOuterMeasure
        {x : Fp × B | acc x.2 x.1 ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (acc x.2)))}
      ≤ t :=
  uniformOfFintype_prod_fiber_bound
    (fun b => {χ : Fp | acc b χ ∧
        ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc b)))})
    (fun b => squeeze_floor_failure_le (acc b) t)

/-- **Nested single-squeeze floor-failure bound, base-first orientation.** The mirror of
`nested_squeeze_floor_failure_le` for when the outer base is the *first* product coordinate and the
fresh inner slot is the *second* — the shape a squeeze takes when the challenges sampled before it
are packaged on the left. Same composition, via `uniformOfFintype_prod_fiber_bound_right`. -/
theorem nested_squeeze_floor_failure_le_right {A : Type*} [Fintype A] [Nonempty A]
    (acc : A → Fp → Prop) (t : ℝ≥0∞) :
    (PMF.uniformOfFintype (A × Fp)).toOuterMeasure
        {x : A × Fp | acc x.1 x.2 ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (acc x.1)))}
      ≤ t :=
  uniformOfFintype_prod_fiber_bound_right
    (fun a => {χ : Fp | acc a χ ∧
        ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc a)))})
    (fun a => squeeze_floor_failure_le (acc a) t)

/-- **Two-squeeze combined floor-failure budget.** Over the joint draw, the probability that
*either* floor fails — a squeeze accepts while its accept-measure sits at or below its threshold —
is `≤ t₁ + t₂`: the per-squeeze bounds union additively on the shared sampling space with no cross
term. The four-squeeze budget iterates exactly this union. -/
theorem combined_two_floor_failure_le (acc₁ : Fp → Prop) (acc₂ : Fp → Fp → Prop)
    (t₁ t₂ : ℝ≥0∞) :
    (PMF.uniformOfFintype (Fp × Fp)).toOuterMeasure
        ({x : Fp × Fp | acc₁ x.1 ∧
            ¬ (t₁ < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter acc₁))}
          ∪ {x : Fp × Fp | acc₂ x.1 x.2 ∧
            ¬ (t₂ < (PMF.uniformOfFintype Fp).toOuterMeasure
                    (Finset.univ.filter (acc₂ x.1)))})
      ≤ t₁ + t₂ := by
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add ?_ ?_)
  · exact nested_squeeze_floor_failure_le (fun _ : Fp => acc₁) t₁
  · exact nested_squeeze_floor_failure_le_right acc₂ t₂

/-- **Equiv-invariance of the uniform outer measure.** A measure-preserving relabelling of a finite
sample space leaves the uniform outer measure of a set unchanged: `μ_α (e ⁻¹' T) = μ_β T`. Both
sides are `Nat.card / card`, and an `Equiv` preserves both the numerator (it restricts to a
bijection `e ⁻¹' T ≃ T`) and the denominator (`Fintype.card_congr`). This is what lets each squeeze
route its fresh challenge slot to the coordinate its fiber bound consumes. -/
theorem uniformOfFintype_toOuterMeasure_preimage_equiv {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β) (T : Set β) :
    (PMF.uniformOfFintype α).toOuterMeasure (e ⁻¹' T)
      = (PMF.uniformOfFintype β).toOuterMeasure T := by
  rw [uniformOfFintype_toOuterMeasure_set, uniformOfFintype_toOuterMeasure_set,
      Fintype.card_congr e]
  congr 1
  exact_mod_cast Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

/-- **Reindexed single-squeeze floor-failure bound.** `nested_squeeze_floor_failure_le` transported
along a relabelling `e : W ≃ Fp × B` of the full sample space that names the squeeze's fresh slot as
the first coordinate `(e w).1` and its base as `(e w).2`. The failure set is `e ⁻¹'` the primitive's
set, so `uniformOfFintype_toOuterMeasure_preimage_equiv` reduces the bound to the primitive. This is
the general tool the four-squeeze budget applies once per squeeze. -/
theorem floor_failure_reindex_le {W B : Type*} [Fintype W] [Nonempty W] [Fintype B] [Nonempty B]
    (e : W ≃ Fp × B) (acc : B → Fp → Prop) (t : ℝ≥0∞) :
    (PMF.uniformOfFintype W).toOuterMeasure
        {w : W | acc (e w).2 (e w).1 ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure
                  (Finset.univ.filter (acc (e w).2)))}
      ≤ t := by
  have hset : {w : W | acc (e w).2 (e w).1 ∧
        ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc (e w).2)))}
      = e ⁻¹' {x : Fp × B | acc x.2 x.1 ∧
          ¬ (t < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc x.2)))} := rfl
  rw [hset, uniformOfFintype_toOuterMeasure_preimage_equiv e]
  exact nested_squeeze_floor_failure_le acc t

/-- Relabelling routing the x₂ challenge to the fiber's first coordinate, its predecessors to the
base. -/
def reindexX2 : (Fp × Fp × Fp × Fp) ≃ Fp × (Fp × Fp × Fp) :=
  ⟨fun w => (w.2.1, w.1, w.2.2.1, w.2.2.2), fun p => (p.2.1, p.1, p.2.2.1, p.2.2.2),
    fun _ => rfl, fun _ => rfl⟩

/-- Relabelling routing the x₃ challenge to the fiber's first coordinate, its predecessors to the
base. -/
def reindexX3 : (Fp × Fp × Fp × Fp) ≃ Fp × (Fp × Fp × Fp) :=
  ⟨fun w => (w.2.2.1, w.1, w.2.1, w.2.2.2), fun p => (p.2.1, p.2.2.1, p.1, p.2.2.2),
    fun _ => rfl, fun _ => rfl⟩

/-- Relabelling routing the x₄ challenge to the fiber's first coordinate, its predecessors to the
base. -/
def reindexX4 : (Fp × Fp × Fp × Fp) ≃ Fp × (Fp × Fp × Fp) :=
  ⟨fun w => (w.2.2.2, w.1, w.2.1, w.2.2.1), fun p => (p.2.1, p.2.2.1, p.2.2.2, p.1),
    fun _ => rfl, fun _ => rfl⟩

/-- **Four-squeeze combined floor-failure budget.** Over the joint uniform draw of
`(x₁, x₂, x₃, x₄)`, the probability that any squeeze floor fails is `≤ t₁ + t₂ + t₃ + t₄`: each
failure is bounded by its threshold (`floor_failure_reindex_le` routes the fresh challenge to its
fiber coordinate) and the four events union additively. -/
theorem combined_floor_failure_le
    (acc₁ : Fp → Prop) (acc₂ : Fp → Fp → Prop)
    (acc₃ : Fp → Fp → Fp → Prop) (acc₄ : Fp → Fp → Fp → Fp → Prop)
    (t₁ t₂ t₃ t₄ : ℝ≥0∞) :
    (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
        ({w : Fp × Fp × Fp × Fp | acc₁ w.1 ∧
            ¬ (t₁ < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter acc₁))}
          ∪ {w : Fp × Fp × Fp × Fp | acc₂ w.1 w.2.1 ∧
            ¬ (t₂ < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter (acc₂ w.1)))}
          ∪ {w : Fp × Fp × Fp × Fp | acc₃ w.1 w.2.1 w.2.2.1 ∧
            ¬ (t₃ < (PMF.uniformOfFintype Fp).toOuterMeasure
                    (Finset.univ.filter (acc₃ w.1 w.2.1)))}
          ∪ {w : Fp × Fp × Fp × Fp | acc₄ w.1 w.2.1 w.2.2.1 w.2.2.2 ∧
            ¬ (t₄ < (PMF.uniformOfFintype Fp).toOuterMeasure
                    (Finset.univ.filter (acc₄ w.1 w.2.1 w.2.2.1)))})
      ≤ t₁ + t₂ + t₃ + t₄ := by
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add ?_ ?_)
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add ?_ ?_)
  refine le_trans (MeasureTheory.measure_union_le _ _) (add_le_add ?_ ?_)
  · exact nested_squeeze_floor_failure_le (fun _ : Fp × Fp × Fp => acc₁) t₁
  · refine le_of_eq_of_le (congrArg _ ?_)
      (floor_failure_reindex_le reindexX2 (fun b c => acc₂ b.1 c) t₂)
    ext w
    simp only [reindexX2, Equiv.coe_fn_mk, Set.mem_setOf_eq]
  · refine le_of_eq_of_le (congrArg _ ?_)
      (floor_failure_reindex_le reindexX3 (fun b c => acc₃ b.1 b.2.1 c) t₃)
    ext w
    simp only [reindexX3, Equiv.coe_fn_mk, Set.mem_setOf_eq]
  · refine le_of_eq_of_le (congrArg _ ?_)
      (floor_failure_reindex_le reindexX4 (fun b d => acc₄ b.1 b.2.1 b.2.2 d) t₄)
    ext w
    simp only [reindexX4, Equiv.coe_fn_mk, Set.mem_setOf_eq]

/-- **The deployed four-squeeze floor-failure event.** `combined_floor_failure_le` instantiated at
the deployed accept predicates `OpenedX{1,2,3,4}Accept`, each squeeze's base threaded from the
earlier sampled challenges by the rewind-run strategies `g₁`/`g₂`/`g₃`: the probability that any
deployed squeeze floor fails is at most `t₁ + t₂ + t₃ + t₄`. The four failure sets are the exact
negations of the derived terminal's floor premises at the sampled runs; the splice-invariance
lemmas (`x1Run_pairCount`/`x1Run_allPts` and siblings) equate the sampled-base thresholds to the
honest-base constants where they are consumed. -/
def deployedFloorFailureSet [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (g₁ : Fp → X1Run shape G) (g₂ : Fp → Fp → X2Run shape G) (g₃ : Fp → Fp → Fp → X3Run shape G)
    (b₂ : Fp → Fin (2 ^ urs.k) → Fp) (t₁ t₂ t₃ t₄ : ℝ≥0∞) : Set (Fp × Fp × Fp × Fp) :=
  {w : Fp × Fp × Fp × Fp | OpenedX1Accept urs hk vk instanceCommitment ps ch w.1 ∧
      ¬ (t₁ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (OpenedX1Accept urs hk vk instanceCommitment ps ch)))}
    ∪ {w : Fp × Fp × Fp × Fp |
        OpenedX2Accept urs hk vk instanceCommitment ((g₁ w.1).spliced ps) ((g₁ w.1).challenges ch w.1)
            (b₂ w.1) w.2.1 ∧
      ¬ (t₂ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (OpenedX2Accept urs hk vk instanceCommitment ((g₁ w.1).spliced ps)
                ((g₁ w.1).challenges ch w.1) (b₂ w.1))))}
    ∪ {w : Fp × Fp × Fp × Fp |
        OpenedX3Accept urs hk vk instanceCommitment ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps))
            ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1)
            (evalVector urs.k w.2.2.1) w.2.2.1 ∧
      ¬ (t₃ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (fun χv => OpenedX3Accept urs hk vk instanceCommitment
                ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps))
                ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1)
                (evalVector urs.k χv) χv)))}
    ∪ {w : Fp × Fp × Fp × Fp |
        OpenedX4Accept urs hk vk instanceCommitment
            ((g₃ w.1 w.2.1 w.2.2.1).spliced ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps)))
            ((g₃ w.1 w.2.1 w.2.2.1).challenges
              ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1) w.2.2.1)
            (evalVector urs.k w.2.2.1) w.2.2.2 ∧
      ¬ (t₄ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (OpenedX4Accept urs hk vk instanceCommitment
                ((g₃ w.1 w.2.1 w.2.2.1).spliced
                  ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps)))
                ((g₃ w.1 w.2.1 w.2.2.1).challenges
                  ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1) w.2.2.1)
                (evalVector urs.k w.2.2.1))))}

/-- **The deployed four-squeeze floor-failure budget.** `combined_floor_failure_le` read
off `deployedFloorFailureSet`: over the joint uniform draw of the four fresh challenges, the deployed
floor-failure event has probability at most `t₁ + t₂ + t₃ + t₄`. -/
theorem deployed_combined_floor_failure_le [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (g₁ : Fp → X1Run shape G) (g₂ : Fp → Fp → X2Run shape G) (g₃ : Fp → Fp → Fp → X3Run shape G)
    (b₂ : Fp → Fin (2 ^ urs.k) → Fp) (t₁ t₂ t₃ t₄ : ℝ≥0∞) :
    (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
        (deployedFloorFailureSet urs hk vk instanceCommitment ps ch g₁ g₂ g₃ b₂ t₁ t₂ t₃ t₄)
      ≤ t₁ + t₂ + t₃ + t₄ :=
  combined_floor_failure_le
    (OpenedX1Accept urs hk vk instanceCommitment ps ch)
    (fun ξ ζ => OpenedX2Accept urs hk vk instanceCommitment ((g₁ ξ).spliced ps) ((g₁ ξ).challenges ch ξ) (b₂ ξ) ζ)
    (fun ξ ζ χ => OpenedX3Accept urs hk vk instanceCommitment ((g₂ ξ ζ).spliced ((g₁ ξ).spliced ps))
        ((g₂ ξ ζ).challenges ((g₁ ξ).challenges ch ξ) ζ) (evalVector urs.k χ) χ)
    (fun ξ ζ χ ω => OpenedX4Accept urs hk vk instanceCommitment
        ((g₃ ξ ζ χ).spliced ((g₂ ξ ζ).spliced ((g₁ ξ).spliced ps)))
        ((g₃ ξ ζ χ).challenges ((g₂ ξ ζ).challenges ((g₁ ξ).challenges ch ξ) ζ) χ)
        (evalVector urs.k χ) ω)
    t₁ t₂ t₃ t₄

/-- **The deployed floors hold except on the budget.** Complement of the failure bound: the
challenge tuples on which every deployed squeeze floor holds have probability at least
`1 − (t₁ + t₂ + t₃ + t₄)`. On the good event the derived terminal's floor premises hold at the
determined runs (`deployed_singlepath_floor_of_good`); the budgeted extraction consumes the same
budget through the joint accept floor directly. -/
theorem deployed_combined_floor_holds [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (g₁ : Fp → X1Run shape G) (g₂ : Fp → Fp → X2Run shape G) (g₃ : Fp → Fp → Fp → X3Run shape G)
    (b₂ : Fp → Fin (2 ^ urs.k) → Fp) (t₁ t₂ t₃ t₄ : ℝ≥0∞) :
    1 - (t₁ + t₂ + t₃ + t₄) ≤
      (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure
        (deployedFloorFailureSet urs hk vk instanceCommitment ps ch g₁ g₂ g₃ b₂ t₁ t₂ t₃ t₄)ᶜ := by
  set μ := (PMF.uniformOfFintype (Fp × Fp × Fp × Fp)).toOuterMeasure with hμ
  set S := deployedFloorFailureSet urs hk vk instanceCommitment ps ch g₁ g₂ g₃ b₂ t₁ t₂ t₃ t₄ with hS
  have hfail : μ S ≤ t₁ + t₂ + t₃ + t₄ :=
    deployed_combined_floor_failure_le urs hk vk instanceCommitment ps ch g₁ g₂ g₃ b₂ t₁ t₂ t₃ t₄
  have hsub : (1 : ℝ≥0∞) ≤ μ S + μ Sᶜ := by
    calc (1 : ℝ≥0∞) = μ (Set.univ : Set (Fp × Fp × Fp × Fp)) :=
          (uniformOfFintype_toOuterMeasure_univ).symm
      _ = μ (S ∪ Sᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ S + μ Sᶜ := MeasureTheory.measure_union_le _ _
  have hgood : (1 : ℝ≥0∞) - μ S ≤ μ Sᶜ := by
    rw [tsub_le_iff_right, add_comm]; exact hsub
  exact le_trans (tsub_le_tsub_left hfail 1) hgood

/-- Budget → single-path floors. On the good event `deployedFloorFailureSetᶜ` each level's squeeze
floor holds *conditioned on that level's sampled accept*: if the sampled run at level `i` accepts,
its accept-measure at the `g`-determined base exceeds the threshold `tᵢ` — the per-level de Morgan
reading of `w ∉ deployedFloorFailureSet` (`¬(accᵢ ∧ ¬floorᵢ) = accᵢ → floorᵢ`). The single-path
member terminal consuming floors of this run-pinned shape is
`deployed_member_node_binding_budgeted` (`Soundness.Multiopen.BudgetedExtraction`), which takes
them as one joint accept floor along the canonical rewind path rather than through this good-event
decomposition. -/
theorem deployed_singlepath_floor_of_good [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (g₁ : Fp → X1Run shape G) (g₂ : Fp → Fp → X2Run shape G) (g₃ : Fp → Fp → Fp → X3Run shape G)
    (b₂ : Fp → Fin (2 ^ urs.k) → Fp) (t₁ t₂ t₃ t₄ : ℝ≥0∞)
    {w : Fp × Fp × Fp × Fp}
    (hw : w ∉ deployedFloorFailureSet urs hk vk instanceCommitment ps ch g₁ g₂ g₃ b₂ t₁ t₂ t₃ t₄) :
    (OpenedX1Accept urs hk vk instanceCommitment ps ch w.1 →
        t₁ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    ∧ (OpenedX2Accept urs hk vk instanceCommitment ((g₁ w.1).spliced ps) ((g₁ w.1).challenges ch w.1) (b₂ w.1) w.2.1 →
        t₂ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (OpenedX2Accept urs hk vk instanceCommitment ((g₁ w.1).spliced ps)
                ((g₁ w.1).challenges ch w.1) (b₂ w.1))))
    ∧ (OpenedX3Accept urs hk vk instanceCommitment ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps))
          ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1)
          (evalVector urs.k w.2.2.1) w.2.2.1 →
        t₃ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (fun χv => OpenedX3Accept urs hk vk instanceCommitment
                ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps))
                ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1)
                (evalVector urs.k χv) χv)))
    ∧ (OpenedX4Accept urs hk vk instanceCommitment
          ((g₃ w.1 w.2.1 w.2.2.1).spliced ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps)))
          ((g₃ w.1 w.2.1 w.2.2.1).challenges
            ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1) w.2.2.1)
          (evalVector urs.k w.2.2.1) w.2.2.2 →
        t₄ < (PMF.uniformOfFintype Fp).toOuterMeasure
              (Finset.univ.filter (OpenedX4Accept urs hk vk instanceCommitment
                ((g₃ w.1 w.2.1 w.2.2.1).spliced
                  ((g₂ w.1 w.2.1).spliced ((g₁ w.1).spliced ps)))
                ((g₃ w.1 w.2.1 w.2.2.1).challenges
                  ((g₂ w.1 w.2.1).challenges ((g₁ w.1).challenges ch w.1) w.2.1) w.2.2.1)
                (evalVector urs.k w.2.2.1)))) := by
  simp only [deployedFloorFailureSet, Set.mem_union, Set.mem_setOf_eq, not_or, not_and,
    not_not] at hw
  exact ⟨hw.1.1.1, hw.1.1.2, hw.1.2, hw.2⟩

/-! ## The heavy-fiber descent primitives (budgeted forking)

The budgeted extraction (`Soundness.Multiopen.BudgetedExtraction`) replaces the `∀`-over-runs floor
premises with a single *joint* accept floor `Σtᵢ < μ(J)` over the nested challenge draw and descends
one squeeze at a time: a Markov (heavy-row) split peels the current squeeze's threshold off the
joint floor, leaving the remaining floor on every heavy fiber. These are the two counting facts that
descent consumes at each level. -/

/-- A set of nonzero uniform measure is nonempty — the self-anchoring fact that replaces the
per-squeeze anchor premises (`hξ₀`/`hζ₀`/`hx3anchor`) in the budgeted descent: each level's heavy
set has measure above its (nonnegative) threshold, so it is nonempty and anchors its own fork. -/
theorem nonempty_of_uniformOfFintype_toOuterMeasure_ne_zero {α : Type*} [Fintype α] [Nonempty α]
    {S : Set α} (h : (PMF.uniformOfFintype α).toOuterMeasure S ≠ 0) : S.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  rw [hne] at h
  exact h (by rw [uniformOfFintype_toOuterMeasure_set]; simp)

/-- The uniform measure of a satisfaction set equals that of its `Finset` filter — the bridge from
the descent's set-of heavy events to the `Finset.filter` shape `exists_injective_accepting_of_measure`
consumes. -/
theorem uniformOfFintype_toOuterMeasure_setOf_filter {α : Type*} [Fintype α] [Nonempty α]
    (p : α → Prop) [DecidablePred p] :
    (PMF.uniformOfFintype α).toOuterMeasure {a : α | p a}
      = (PMF.uniformOfFintype α).toOuterMeasure (Finset.univ.filter p : Finset α) := by
  congr 1
  ext a
  simp

open Classical in
/-- **The heavy-fiber Markov bound — the budgeted-forking descent primitive.** If the joint accept
event beats `t + T`, the heavy first coordinates — fiber measure above `T` — have measure above
`t`: peeling the current squeeze's threshold off the joint floor leaves the residual floor intact
on every heavy fiber, which is the recursion the budgeted extraction runs. Counting proof: the
light fibers contribute at most `T`, the heavy cylinder at most `μ(heavy)`; cancel `T`. -/
theorem uniformOfFintype_heavy_fiber_lt {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] (A : Set (α × β)) {t T : ℝ≥0∞} (hT : T ≠ ⊤)
    (hA : t + T < (PMF.uniformOfFintype (α × β)).toOuterMeasure A) :
    t < (PMF.uniformOfFintype α).toOuterMeasure
        {a : α | T < (PMF.uniformOfFintype β).toOuterMeasure {b : β | (a, b) ∈ A}} := by
  set H : Set α :=
    {a : α | T < (PMF.uniformOfFintype β).toOuterMeasure {b : β | (a, b) ∈ A}} with hH
  have hlight : (PMF.uniformOfFintype (α × β)).toOuterMeasure
      {x : α × β | x.2 ∈ (if x.1 ∈ H then (∅ : Set β) else {b : β | (x.1, b) ∈ A})} ≤ T := by
    refine uniformOfFintype_prod_fiber_bound_right
      (fun a => if a ∈ H then (∅ : Set β) else {b : β | (a, b) ∈ A}) (fun a => ?_)
    beta_reduce
    by_cases ha : a ∈ H
    · simp [ha]
    · rw [if_neg ha]
      exact not_lt.mp (by simpa [hH] using ha)
  have hsub : A ⊆ {x : α × β | x.2 ∈ (if x.1 ∈ H then (∅ : Set β) else {b : β | (x.1, b) ∈ A})}
      ∪ (H ×ˢ (Set.univ : Set β)) := by
    intro x hx
    by_cases hxa : x.1 ∈ H
    · exact Or.inr ⟨hxa, trivial⟩
    · exact Or.inl (by simp only [Set.mem_setOf_eq, if_neg hxa]; exact hx)
  have hcyl : (PMF.uniformOfFintype (α × β)).toOuterMeasure (H ×ˢ (Set.univ : Set β))
      = (PMF.uniformOfFintype α).toOuterMeasure H := by
    rw [uniformOfFintype_toOuterMeasure_prod, uniformOfFintype_toOuterMeasure_univ, mul_one]
  have hchain : t + T < (PMF.uniformOfFintype α).toOuterMeasure H + T := by
    calc t + T
        < (PMF.uniformOfFintype (α × β)).toOuterMeasure A := hA
      _ ≤ (PMF.uniformOfFintype (α × β)).toOuterMeasure
            {x : α × β | x.2 ∈ (if x.1 ∈ H then (∅ : Set β) else {b : β | (x.1, b) ∈ A})}
          + (PMF.uniformOfFintype (α × β)).toOuterMeasure (H ×ˢ (Set.univ : Set β)) :=
          le_trans ((PMF.uniformOfFintype (α × β)).toOuterMeasure.mono hsub)
            (MeasureTheory.measure_union_le _ _)
      _ ≤ T + (PMF.uniformOfFintype α).toOuterMeasure H := add_le_add hlight (le_of_eq hcyl)
      _ = (PMF.uniformOfFintype α).toOuterMeasure H + T := add_comm _ _
  exact (ENNReal.add_lt_add_iff_right hT).mp hchain

end Zcash.Snark
