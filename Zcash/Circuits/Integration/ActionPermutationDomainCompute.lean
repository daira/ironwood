import Zcash.Snark.Keygen.Derivation
import Zcash.Snark.Soundness.PermutationInstantiation

/-!
# Closed computations for the Action permutation layout

This small module isolates the native computation certificates used by the semantic
Action permutation-domain package.  Every statement is against keygen data derived
from `orchardActionTopLevelCircuit`, never the captured verifying-key fixture.
-/

namespace Zcash.Snark

open Zcash.Circuits.Action (orchardActionTopLevelCircuit)

namespace ActionPermutationDomain

/-- The circuit-derived Action domain exponent is within Pasta's supported range. -/
theorem domainExponent_lt :
    orchardActionTopLevelCircuit.domainExponent < 33 := by
  native_decide

theorem domainExponent_eq :
    orchardActionTopLevelCircuit.domainExponent = 11 := by
  native_decide

/-- The derived Action permutation columns form two full chunks and one singleton. -/
theorem chunks_eq :
    Keygen.permutationChunksOf orchardActionTopLevelCircuit.selectorMap
        orchardActionTopLevelCircuit.constraintSystem =
      [[(.instance 0, 0), (.advice 0, 1), (.advice 1, 2),
          (.advice 2, 3), (.advice 3, 4), (.advice 4, 5),
          (.advice 5, 6)],
        [(.advice 6, 7), (.advice 7, 8), (.advice 8, 9),
          (.advice 9, 10), (.fixed 0, 11), (.fixed 7, 12),
          (.fixed 8, 13)],
        [(.fixed 9, 14)]] := by
  native_decide

/-- The Action permutation argument has 15 columns and verifier chunk width 7. -/
theorem columnCount_chunkLen_eq :
    (orchardActionTopLevelCircuit.constraintSystem.permutationColumns.length,
        orchardActionTopLevelCircuit.constraintSystem.chunkLen) =
      (15, 7) := by
  native_decide

/-- Query-layout coherence specialized to the derived Action pinned constraint system. -/
def derivedPinnedCS : Halo2.PinnedConstraintSystem Fp :=
  Halo2.PinnedConstraintSystem.derive
    orchardActionTopLevelCircuit.constraintSystem
    orchardActionTopLevelCircuit.selectorMap

/-- The two pinned-CS construction paths agree on the three query layouts used
by permutation routing. This is intentionally narrower than full pinned-CS
equality: no gate or lookup expression is part of this computation. -/
theorem queryLayouts_eq :
    (derivedPinnedCS.instanceQueryLayout,
      derivedPinnedCS.adviceQueryLayout,
      derivedPinnedCS.fixedQueryLayout) =
    (orchardActionTopLevelCircuit.pinnedCS.instanceQueryLayout,
      orchardActionTopLevelCircuit.pinnedCS.adviceQueryLayout,
      orchardActionTopLevelCircuit.pinnedCS.fixedQueryLayout) := by
  native_decide

set_option maxRecDepth 100000 in
theorem instanceQueryLayout_eq :
    derivedPinnedCS.instanceQueryLayout =
      orchardActionTopLevelCircuit.pinnedCS.instanceQueryLayout :=
  congrArg Prod.fst queryLayouts_eq

set_option maxRecDepth 100000 in
theorem adviceQueryLayout_eq :
    derivedPinnedCS.adviceQueryLayout =
      orchardActionTopLevelCircuit.pinnedCS.adviceQueryLayout :=
  congrArg (fun layouts => layouts.2.1) queryLayouts_eq

set_option maxRecDepth 100000 in
theorem fixedQueryLayout_eq :
    derivedPinnedCS.fixedQueryLayout =
      orchardActionTopLevelCircuit.pinnedCS.fixedQueryLayout :=
  congrArg (fun layouts => layouts.2.2) queryLayouts_eq

def ColumnRefCoherent : ColumnRef → Prop
  | .advice i =>
      i < orchardActionTopLevelCircuit.pinnedCS.adviceQueryLayout.length ∧
        (orchardActionTopLevelCircuit.pinnedCS.adviceQueryLayout.getD i (0, 0)).2 = 0
  | .fixed i =>
      i < orchardActionTopLevelCircuit.pinnedCS.fixedQueryLayout.length ∧
        (orchardActionTopLevelCircuit.pinnedCS.fixedQueryLayout.getD i (0, 0)).2 = 0
  | .instance i =>
      i < orchardActionTopLevelCircuit.pinnedCS.instanceQueryLayout.length ∧
        (orchardActionTopLevelCircuit.pinnedCS.instanceQueryLayout.getD i (0, 0)).2 = 0

/-- Every Action permutation reference selects an in-range rotation-zero query and
every accompanying common-permutation index is in range. -/
theorem routingCoherent :
    ∀ chunk ∈
        Keygen.permutationChunksOf orchardActionTopLevelCircuit.selectorMap
          orchardActionTopLevelCircuit.constraintSystem,
      ∀ ref ∈ chunk,
        ColumnRefCoherent ref.1 ∧
          ref.2 <
            orchardActionTopLevelCircuit.constraintSystem.permutationColumns.length := by
  rw [chunks_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro chunk (rfl | rfl | rfl)
  · intro ref href
    simp only [List.mem_cons, List.not_mem_nil, or_false] at href
    rcases href with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [ColumnRefCoherent]
      native_decide
  · intro ref href
    simp only [List.mem_cons, List.not_mem_nil, or_false] at href
    rcases href with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [ColumnRefCoherent]
      native_decide
  · intro ref href
    simp only [List.mem_cons, List.not_mem_nil, or_false] at href
    rcases href with rfl
    simp only [ColumnRefCoherent]
    native_decide

/-- The first 21 powers of Pasta's permutation coset generator are distinct.
Twenty-one is `3 * 7`, the padded Action permutation-column range. -/
theorem deltaPowers_injective :
    Function.Injective fun j : Fin 21 => deltaFp ^ (j : ℕ) := by
  native_decide

assert_no_sorry domainExponent_lt
assert_no_sorry domainExponent_eq
assert_no_sorry chunks_eq
assert_no_sorry columnCount_chunkLen_eq
assert_no_sorry queryLayouts_eq
assert_no_sorry routingCoherent
assert_no_sorry deltaPowers_injective

end ActionPermutationDomain

end Zcash.Snark
