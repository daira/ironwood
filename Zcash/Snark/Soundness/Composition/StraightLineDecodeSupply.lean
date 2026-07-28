import Zcash.Snark.Soundness.Composition.StraightLineConstraint

/-!
# The algebraic decode behind the straight-line constraint event

`straightLineConstraintDecoded` is proposition-only: it says the root decode succeeded and yielded
a constraint witness, but hands out no data.  The Action terminal needs the data — a
`DeployedAlgebraicDecode` at the run's own artifacts.

`straightLineConstraintDecoded_nonempty_decode` recovers the decode as a `Nonempty`, and
`straightLineDecode` picks one.  The decode is pinned by `family.outcome`, so the choice cannot
invent different AGM coordinates — `DeployedRootDecodeWitness.unique`.

The artifacts are the run's, not the Action circuit's.  Identifying the two is the caller's job;
`ActionTerminal.action_bundleStatement_or_relation_of_straightLineDecoded` does it with the keygen
certificate equalities.
-/

namespace Zcash.Snark

open Classical
open ComputedStraightLineDeployedFSFamily (straightLineDummyTape)

local instance vestaInhabitedStraightLineDecodeSupply : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- The one-run wrapped output: the straight-line event's run at `basis` and the oracle table `O`.
The dummy tape is the fixed index the root-decode witness type is reused at. -/
noncomputable abbrev straightLineRunOutput
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :=
  deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape)

/-- The run's own algebraic decode exists whenever the straight-line constraint event decodes.

Stepped through in the body: the event's nested existentials carry a `DeployedRootDecodeWitness`,
whose `decoded` field is the decode. -/
theorem straightLineConstraintDecoded_nonempty_decode
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (h : family.straightLineConstraintDecoded static basis O) :
    Nonempty (DeployedAlgebraicDecode (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      (deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape)).1.proof.1
      (wrappedPreIpaRecord
        (deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape)))
      ((deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape)).1.aMulti
        (wrappedPreIpaReads
          (deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape))))
      ((deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape)).1.multiU
        (wrappedPreIpaReads
          (deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape))))
      ((deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape)).1.multiBlind
        (wrappedPreIpaReads
          (deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape))))) := by
  -- The event is `deployedConstraintDecodedOfRoot` at the one-run coins: acceptance, a root
  -- decode witness, the pre-`x` exclusion, and the constraint witness it produces.
  obtain ⟨_haccept, root, _hxgood, _witness, _hw⟩ := h
  exact ⟨root.decoded⟩

/-- The decode picked out of the straight-line constraint event. -/
noncomputable def straightLineDecode
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  Classical.choice (straightLineConstraintDecoded_nonempty_decode family static basis O h)

end Zcash.Snark
