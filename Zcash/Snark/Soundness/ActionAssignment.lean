import Zcash.Bridge.VkProjection
import Zcash.Circuits.Action.Bundle
import Zcash.Snark.Soundness.Multiopen.ConstraintResolver
import Zcash.Snark.Soundness.PolynomialEnvironment

/-!
# Decoded Action assignments

The deployed proof exposes column polynomials through a `CommitmentId` resolver, while
`Action.Circuit.soundnessPost` consumes a placed Clean environment.  This file fixes the
remaining circuit-side choices:

* the usable-row count is the verifier key's `n - blindingFactors - 1`;
* region placement is the V1 floor-planner result for the derived Action operation stream;
* fixed columns are shared and advice/instance columns are selected by proof member.

`ActionAssignment.ofDecodedMembers` then specializes the construction to the polynomials
recovered by the deployed multiopen decoder.  It does not assume a concrete verification
key: concrete VK equality is a separate input-faithfulness theorem.
-/

namespace Zcash.Snark

open Halo2 Polynomial
open Zcash.Circuits.Fixtures

set_option maxHeartbeats 20000

/-- The Action circuit's V1 region starts, derived from its operation stream. -/
def actionRegionStarts : List ℕ :=
  FloorPlanner.V1.starts Bridge.actionOperations

/-- The placed row of an Action region.  The live top-level circuit starts at region zero. -/
def actionPlacement : RegionIndex → ℕ :=
  Layout.place actionRegionStarts

@[simp] theorem actionPlacement_apply (region : RegionIndex) :
    actionPlacement region = actionRegionStarts.getD region 0 := rfl

/-- Rows on which Halo 2 enforces gate, copy, and lookup constraints. -/
def actionUsableRows {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) : ℕ :=
  vk.n - vk.blindingFactors - 1

/-- The data needed to read one Action assignment from resolved column polynomials. -/
structure ActionAssignment {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) where
  proofIndex : Fin shape.numProofs
  polynomial : CommitmentId → Polynomial Fp

namespace ActionAssignment

variable {shape : Shape} {G : Type*} {vk : VerifyingKey shape Fp G}

/-- The row-indexed Clean environment of one proof member. -/
def environment (assignment : ActionAssignment vk) : Environment Fp :=
  resolverEnvironment vk assignment.polynomial assignment.proofIndex
    (actionUsableRows vk)

/-- The environment together with the Action circuit's derived floor-planner placement. -/
def placedEnvironment (assignment : ActionAssignment vk) : Placed Environment Fp :=
  ⟨actionPlacement, assignment.environment⟩

@[simp] theorem environment_usableRows (assignment : ActionAssignment vk) :
    assignment.environment.usableRows = actionUsableRows vk := rfl

@[simp] theorem environment_fixed (assignment : ActionAssignment vk)
    (column : Column .fixed) (row : ℤ) :
    assignment.environment.fixed column row =
      (assignment.polynomial (.fixedCol column.index)).eval (vk.omega ^ row) := rfl

@[simp] theorem environment_advice (assignment : ActionAssignment vk)
    (column : Column .advice) (row : ℤ) :
    assignment.environment.advice column row =
      (assignment.polynomial
        (.adviceCol assignment.proofIndex column.index)).eval (vk.omega ^ row) := rfl

@[simp] theorem environment_instance (assignment : ActionAssignment vk)
    (column : Column .instance) (row : ℤ) :
    assignment.environment.inst column row =
      (assignment.polynomial
        (.instanceCol assignment.proofIndex column.index)).eval (vk.omega ^ row) := rfl

/-- Build the Action assignment carried by a deployed decoded-member resolver. -/
noncomputable def ofDecodedMembers
    [AddCommGroup G] [Module Fp G] [DecidableEq G] [Inhabited G]
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments (instanceCommitment := instanceCommitment) urs hk vk ps ch)
      (x4BatchEvals (instanceCommitment := instanceCommitment) vk ps ch) a₀ pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch),
      OpenedMemberDecode (instanceCommitment := instanceCommitment)
        urs hk vk ps ch pbatch i hi)
    (route : CommitmentId →
      Option (DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch))
    (proofIndex : Fin shape.numProofs) :
    ActionAssignment vk where
  proofIndex := proofIndex
  polynomial :=
    decodedPolynomialResolver (instanceCommitment := instanceCommitment)
      urs hk vk ps ch memberDecode route

@[simp] theorem ofDecodedMembers_proofIndex
    [AddCommGroup G] [Module Fp G] [DecidableEq G] [Inhabited G]
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments (instanceCommitment := instanceCommitment) urs hk vk ps ch)
      (x4BatchEvals (instanceCommitment := instanceCommitment) vk ps ch) a₀ pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount (instanceCommitment := instanceCommitment) vk ps ch),
      OpenedMemberDecode (instanceCommitment := instanceCommitment)
        urs hk vk ps ch pbatch i hi)
    (route : CommitmentId →
      Option (DeployedMemberSlot (instanceCommitment := instanceCommitment) vk ps ch))
    (proofIndex : Fin shape.numProofs) :
    (ofDecodedMembers instanceCommitment urs hk vk ps ch memberDecode route
      proofIndex).proofIndex = proofIndex := rfl

end ActionAssignment

end Zcash.Snark
