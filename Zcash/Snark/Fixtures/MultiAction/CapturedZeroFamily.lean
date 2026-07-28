import Zcash.Snark.Fixtures.MultiAction.StaticChecks
import Zcash.Snark.Soundness.Composition.ZeroStraightLine

/-!
# Captured-data straight-line interface test, with eleven live IPA rounds

This instantiates the shape-generic zero prover of `Composition.ZeroStraightLine` at the captured
Post-NU6.3 key's own scalar data — `ω`, `n`, blinding count, `δ`, chunk length, gates, the three
query layouts, permutation chunks and lookup expressions — over the captured domain `k = 11`.  So
the staged IPA trace carries **eleven live rounds**, and the six deployed root events run against
the captured query layouts instead of an empty grouping.  `Composition.StraightLineWitness` does
the same at the witness shape, where `k = 0` empties the round obligations.

## What the instantiation gives up

* The group commitment families are zero, not the captured Vesta points.
  `CapturedVerifierKeyProfile` already omits them: in the AGM the verifier's points need
  representations over the *sampled* basis, so pinning them to fixture constants would leave the
  premise uninhabited for most bases.
* The shape is instance-free.  All-zero columns do not satisfy Orchard's permutation and lookup
  constraints, so with sub-proofs the pre-`x` constraint difference is nonzero and the
  constraint-`x` stage cannot be discharged.  That layer needs an honest prover.

## Scope

This is an interface test, not the deployed family.  The deployed family comes from
`ComputedStraightLineDeployedFSFamily.ofCovered`, which packages an online
representation-carrying prover with caller-supplied stages; the captured-key endpoint applies the
fixture metadata to that.
-/
namespace Zcash.Snark.Fixture2

open Zcash.Snark

/-- The captured shape with its sub-proofs removed: same domain `k = 11`, same column, point-set
and query arities, no instances. -/
def capturedZeroShape : Shape := { shape with numProofs := 0 }

/-- The captured verifying key's scalar and layout data at the instance-free shape, with zero
group commitment families. -/
def capturedZeroVk : VerifyingKey capturedZeroShape Fp VestaG where
  omega := vk.omega
  n := vk.n
  blindingFactors := vk.blindingFactors
  delta := vk.delta
  chunkLen := vk.chunkLen
  gates := vk.gates
  instanceQueryLayout := vk.instanceQueryLayout
  adviceQueryLayout := vk.adviceQueryLayout
  fixedQueryLayout := vk.fixedQueryLayout
  fixedCommitment := fun _ => 0
  permutationCommonCommitment := fun _ => 0
  permutationChunks := vk.permutationChunks
  lookupInputExprs := vk.lookupInputExprs
  lookupTableExprs := vk.lookupTableExprs

/-- The instance-free key's fixed-column commitments vanish. -/
theorem capturedZeroVk_fixed : ∀ i, capturedZeroVk.fixedCommitment i = 0 := fun _ => rfl

/-- The instance-free key's common permutation commitments vanish. -/
theorem capturedZeroVk_perm : ∀ i, capturedZeroVk.permutationCommonCommitment i = 0 := fun _ => rfl

/-- The instantiating shape has no sub-proofs. -/
theorem capturedZeroShape_numProofs : capturedZeroShape.numProofs = 0 := rfl

/-- The instantiating shape keeps the captured domain: eleven IPA rounds. -/
theorem capturedZeroShape_k : capturedZeroShape.k = 11 := rfl

/-- The instantiating shape keeps the captured point-set and query arities. -/
theorem capturedZeroShape_arities :
    capturedZeroShape.numPointSets = shape.numPointSets ∧
      capturedZeroShape.numAdviceQueries = shape.numAdviceQueries ∧
      capturedZeroShape.numFixedQueries = shape.numFixedQueries ∧
      capturedZeroShape.numInstanceQueries = shape.numInstanceQueries ∧
      capturedZeroShape.numQuotientPieces = shape.numQuotientPieces :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The instantiating key keeps the captured scalar and layout data. -/
theorem capturedZeroVk_data :
    capturedZeroVk.omega = vk.omega ∧ capturedZeroVk.n = vk.n ∧
      capturedZeroVk.gates = vk.gates ∧
      capturedZeroVk.instanceQueryLayout = vk.instanceQueryLayout ∧
      capturedZeroVk.adviceQueryLayout = vk.adviceQueryLayout ∧
      capturedZeroVk.fixedQueryLayout = vk.fixedQueryLayout ∧
      capturedZeroVk.permutationChunks = vk.permutationChunks :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The captured key's straight-line deployed family.**  Six staged root events, an empty
constraint-`x` stage, and a staged IPA trace over the captured domain's eleven rounds. -/
noncomputable def capturedZeroStraightLineFamily :
    ComputedStraightLineDeployedFSFamily capturedZeroShape :=
  zeroStraightLineDeployedFamily capturedZeroVk capturedZeroVk_fixed capturedZeroVk_perm rfl

/-- The captured key's deployed constraint family, one interface below. -/
noncomputable def capturedZeroDeployedConstraintFamily :
    ComputedDeployedConstraintFSFamily capturedZeroShape :=
  zeroDeployedConstraintFamily capturedZeroVk capturedZeroVk_fixed capturedZeroVk_perm rfl

/-- The captured key's deployed root family, two interfaces below. -/
noncomputable def capturedZeroDeployedRootFamily :
    ComputedDeployedRootFSFamily capturedZeroShape :=
  zeroDeployedRootFamily capturedZeroVk capturedZeroVk_fixed capturedZeroVk_perm

/-- **The static checks hold at the instantiating key.**  Its layouts and domain data are the
captured ones, so the same five decided facts apply. -/
theorem capturedZeroStaticChecks :
    DeployedConstraintStaticChecks capturedZeroStraightLineFamily.toRootFamily where
  adviceLength := fun _basis => vk_advice_layout_length
  instanceLength := fun _basis => vk_instance_layout_length
  fixedLength := fun _basis => vk_fixed_layout_length
  omegaOrder := fun _basis => vk_omega_order
  characteristic := fun _basis => vk_n_cast_ne_zero

/-- **The constraint-`x` squeeze schedule at budget zero.**  The stage's root set is empty on
every table, so the event costs nothing and its pinning is the staged trace's. -/
noncomputable def capturedZeroConstraintSchedule :
    DeployedConstraintXSqueezeSchedule capturedZeroStraightLineFamily.toRootFamily 0 where
  measure_le := fun basis O => by
    rw [show deployedConstraintXBadSet capturedZeroStraightLineFamily.toRootFamily basis O = ∅ from
      zeroConstraintXBadSet_empty capturedZeroVk capturedZeroVk_fixed capturedZeroVk_perm rfl
        basis O]
    simp
  pinned := capturedZeroStraightLineFamily.pinnedX

end Zcash.Snark.Fixture2
