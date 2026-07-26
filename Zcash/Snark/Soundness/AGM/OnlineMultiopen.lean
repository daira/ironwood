import Zcash.Snark.Soundness.Forking.Adversary.Algebraic

/-!
# Online AGM data for rewind-free multiopen unbatching

The deployed Rust transcript fixes the polynomial commitments before `x1`, fixes `qPrime` before
`x3`, and fixes the claimed `u` evaluations before `x4`.  The existing algebraic adversary output
already carries representations for every emitted group point, but its aggregate `aMulti` is an
arbitrary function of the complete pre-IPA challenge vector.  Consequently the present interface
does not by itself rule out choosing an alternative representation after seeing a later challenge.

This file adds a non-breaking refinement of `ComputedAlgebraicFSFamily` for the tighter route:

* the multiopen aggregate coordinates must be the deterministic MSM coordinates obtained from the
  actual representation-carrying commitments used by the assembly.

Exact deployed chronology is represented by the whole-root prefix schedule in
`DeployedPinnedRoots`; narrower final-output invariance predicates are deliberately omitted because
they do not establish when all ordinary proof fields affecting a root set were emitted.

No protocol point or scalar is added to the transcript.  These are ghost conditions on the AGM
adversary.
-/

namespace Zcash.Snark

open Classical

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}

/-! ## The representation-carrying points available to multiopen -/

/-- All prover-emitted commitments fixed before `x1`, in deployed transcript order.  Scalar
evaluations are omitted: they are already visible in the ordinary transcript prefix and carry no
AGM representation. -/
def AlgebraicProofString.preX1Points (aps : AlgebraicProofString shape basis) :
    List (AlgebraicPoint (F := Fp) basis) :=
  (List.ofFn fun p => List.ofFn fun i => aps.adviceCommitments p i).flatten ++
  (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedInput p i).flatten ++
  (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedTable p i).flatten ++
  (List.ofFn fun p => List.ofFn fun i => aps.permutationProduct p i).flatten ++
  (List.ofFn fun p => List.ofFn fun i => aps.lookupProduct p i).flatten ++
  [aps.vanishingRandom] ++ List.ofFn aps.hPieces

/-- The represented points from which the final multiopen MSM may be assembled.  `fixed` contains
representations of verifier-known commitments (for example fixed-column commitments); it is fixed
per public basis and does not depend on Fiat-Shamir answers. -/
def AlgebraicProofString.multiopenAssemblySource
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) :
    List (AlgebraicPoint (F := Fp) basis) :=
  aps.preX1Points ++ fixed ++ [aps.multiopenQPrime]

/-- Every represented quotient-piece commitment occurs in the pre-`x` portion of the online
assembly source. -/
theorem AlgebraicProofString.hPiece_mem_multiopenAssemblySource
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (i : Fin shape.numQuotientPieces) :
    aps.hPieces i ∈ aps.multiopenAssemblySource fixed := by
  simp [AlgebraicProofString.multiopenAssemblySource, AlgebraicProofString.preX1Points]

/-! ## Canonical aggregate coordinates -/

/-- Every non-URS point appended by the verifier's multiopen MSM is one of the represented points
that was available at the proper transcript prefix. -/
def MultiopenAssemblyCovered (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs -> Nat -> VestaG)
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) : Prop :=
  forall nu : Fin 11 -> Fp, forall pr,
    pr ∈ (multiopenMsm vk instanceCommitment aps.erase (chRecord nu (fun _ => 0))).other ->
      ∃ ap ∈ aps.multiopenAssemblySource fixed, ap.point = pr.2

/-- Construct the aggregate coordinates by looking up every appended MSM point in the fixed
representation source.  This removes the unconstrained choice of `aMulti`: its dependence on
`x1,...,x4` is now exactly the verifier's public MSM scalar dependence. -/
noncomputable def AlgebraicWfProof.ofOnlineMultiopenRepresented
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (aps : AlgebraicProofString shape basis) (hwf : PsWellFormed aps.erase)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcover : MultiopenAssemblyCovered vk instanceCommitment aps fixed) :
    AlgebraicWfProof basis vk instanceCommitment :=
  AlgebraicWfProof.ofRepresented aps hwf fun nu =>
    RepresentedMultiopen.ofCoveredList vk instanceCommitment aps.erase nu
      (aps.multiopenAssemblySource fixed) (hcover nu)

/-- The proof that an existing `AlgebraicWfProof` uses canonical online multiopen coordinates.
The three equalities deliberately mention `ofCoveredList`: a merely existential representation of
the final group point is not enough for algebraic unbatching. -/
structure CanonicalOnlineMultiopenCoordinates
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) : Prop where
  covered : MultiopenAssemblyCovered vk instanceCommitment p.algebraicProof fixed
  aMulti_eq : forall nu,
    p.aMulti nu =
      (multiopenMsm vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0))).gScalars +
        repsGPart
          (RepresentedMultiopen.ofCoveredList vk instanceCommitment p.proof.1 nu
            (p.algebraicProof.multiopenAssemblySource fixed) (covered nu)).reps
  multiU_eq : forall nu,
    p.multiU nu =
      (multiopenMsm vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0))).uScalar +
        repsU
          (RepresentedMultiopen.ofCoveredList vk instanceCommitment p.proof.1 nu
            (p.algebraicProof.multiopenAssemblySource fixed) (covered nu)).reps
  multiBlind_eq : forall nu,
    p.multiBlind nu =
      (multiopenMsm vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0))).wScalar +
        repsW
          (RepresentedMultiopen.ofCoveredList vk instanceCommitment p.proof.1 nu
            (p.algebraicProof.multiopenAssemblySource fixed) (covered nu)).reps
  s_eq : p.s = p.algebraicProof.ipaS.gPart
  sU_eq : p.sU = p.algebraicProof.ipaS.coeffs AugmentedIndex.u
  sBlind_eq : p.sBlind = p.algebraicProof.ipaS.coeffs AugmentedIndex.w

/-- The smart constructor above satisfies the canonical-coordinate interface definitionally. -/
theorem AlgebraicWfProof.ofOnlineMultiopenRepresented_canonical
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (aps : AlgebraicProofString shape basis) (hwf : PsWellFormed aps.erase)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (hcover : MultiopenAssemblyCovered vk instanceCommitment aps fixed) :
    CanonicalOnlineMultiopenCoordinates
      (AlgebraicWfProof.ofOnlineMultiopenRepresented aps hwf fixed hcover) fixed := by
  refine
    { covered := hcover
      aMulti_eq := ?_
      multiU_eq := ?_
      multiBlind_eq := ?_
      s_eq := rfl
      sU_eq := rfl
      sBlind_eq := rfl }
  · intro nu
    rfl
  · intro nu
    rfl
  · intro nu
    rfl

/-! ## Refined computed family -/

/-- A computed AGM family whose multiopen coordinates are canonical.  Exact deployed chronology
is added only at the root-family layer, where all data affecting each priced bad set is visible.
Extending, rather than modifying, `ComputedAlgebraicFSFamily` keeps all existing IPA/DLOG theorems
available through `toFamily`. -/
structure ComputedOnlineMultiopenFSFamily (shape : Shape)
    extends ComputedAlgebraicFSFamily shape where
  fixedRepresentations : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
    List (AlgebraicPoint (F := Fp) basis)
  canonical : forall basis O,
    CanonicalOnlineMultiopenCoordinates ((adversary basis).run O)
      (fixedRepresentations basis)

namespace ComputedOnlineMultiopenFSFamily

/-- Forget the canonical multiopen-coordinate evidence. -/
abbrev toFamily (family : ComputedOnlineMultiopenFSFamily shape) :
    ComputedAlgebraicFSFamily shape := family.toComputedAlgebraicFSFamily

end ComputedOnlineMultiopenFSFamily

end Zcash.Snark
