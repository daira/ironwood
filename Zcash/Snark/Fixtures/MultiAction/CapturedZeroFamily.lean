import Zcash.Snark.Fixtures.MultiAction.StaticChecks
import Zcash.Snark.Soundness.Composition.ZeroStraightLine

/-!
# The captured key's straight-line family, with eleven live IPA rounds

`Composition.StraightLineWitness` inhabits the straight-line deployed interface at the degenerate
witness shape, where `k = 0` empties every IPA-round obligation.  This module instantiates the
shape-generic zero prover of `Composition.ZeroStraightLine` at the captured Post-NU6.3 key's own
scalar data — its `ω`, `n`, blinding count, `δ`, chunk length, gates, three query layouts,
permutation chunks and lookup expressions — over the captured domain `k = 11`.

The staged IPA trace therefore carries **eleven live rounds**, each discharged by the discrepancy
walk of `straightLineIpaRootPolynomial_of_zero_coordinates`, and the six deployed root events run
against the captured query layouts rather than against an empty grouping.

Two departures from the captured fixture are deliberate and are what the construction pays for:

* The group-valued commitment families are zero rather than the captured Vesta points.  This is
  the same choice `Fixture2.CapturedVerifierKeyProfile` already makes when it omits them — in the
  AGM the verifier's points must be supplied with representations over the *sampled* basis, so
  pinning them to fixture constants would leave the premise uninhabited for most bases.
* The shape is instance-free (`numProofs = 0`).  A prover that commits all-zero columns does not
  satisfy Orchard's permutation and lookup constraints, so with sub-proofs present the pre-`x`
  constraint difference would be a nonzero polynomial and the constraint-`x` stage could not be
  discharged.  Exhibiting that layer with sub-proofs needs an honest prover, not a degenerate one.

So this is an inhabitant that exercises the multiopen grouping, all six root events and all eleven
IPA rounds at captured key data, with a trivial constraint system — strictly more than the witness
shape provides, and short of a full honest Orchard prover.
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
