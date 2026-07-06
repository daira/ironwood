import Zcash.Snark

/-!
# Max-action verifier-shape fixture

A concrete Lean instantiation of the parametric verifier obligations at Orchard's consensus maximum
`numProofs = 2^16 - 1`, over the captured Orchard verifier shape (the `Fixture`/`Fixture2` shape with
the action count set to the consensus bound). Unlike the generated fixtures it is not a Rust/Halo2
capture and it does not claim a Rust<->Lean MSM match. Its content is deliberately thin: the theorems
below are the parametric lemmas of `Zcash.Snark.Verifier.Parametric` specialized to this shape, with
the verifying key, proof string, and challenges universally quantified — nothing is *evaluated* at
`N = 65535`. What is pinned is that the generic per-sub-proof folds specialize to the largest
consensus-valid action count: the statements elaborate at this shape, and drift in the parametric
statements fails here at the consensus maximum.

A real empirical max-action fixture would need the Rust/Halo2 dumper to create and verify a
65,535-action Orchard proof, then emit the captured proof string, challenges, and MSM. The generated
single- and two-action captures remain the empirical regressions for the Rust/Lean boundary.
-/

namespace Zcash.Snark.FixtureMax

open Zcash.Snark

abbrev G := ℕ

/-- The captured Orchard verifier shape (`Fixture`/`Fixture2`) with `numProofs` at the consensus
maximum. -/
def shape : Shape := {
  k := 11,
  numProofs := orchardConsensusMaxProofs,
  numAdviceColumns := 10,
  numLookups := 3,
  numPermutationSets := 3,
  numPermutationColumns := 15,
  numQuotientPieces := 8,
  numInstanceQueries := 1,
  numAdviceQueries := 25,
  numFixedQueries := 29,
  numPointSets := 5
}

theorem numProofs_is_consensus_max : shape.numProofs = orchardConsensusMaxProofs :=
  rfl

theorem shape_has_consensus_numProofs : shape.hasConsensusNumProofs := by
  change orchardConsensusMaxProofs ≤ orchardConsensusMaxProofs
  exact Nat.le_refl _

/-- `allExpressions_parametric_numProofs` at the consensus-max shape, for every verifying key, proof
string, and challenge assignment. -/
theorem allExpressions_parametric_at_consensus_max (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) (l0 lLast lBlind : Fp) :
    allExpressions vk ps ch l0 lLast lBlind =
      subProofBlocks (fun p : Fin shape.numProofs =>
        subProofExpressions vk ps ch l0 lLast lBlind p) :=
  allExpressions_parametric_numProofs vk ps ch l0 lLast lBlind

/-- `assembleQueries_parametric_numProofs` at the consensus-max shape, for every verifying key, proof
string, and challenge assignment. -/
theorem assembleQueries_parametric_at_consensus_max (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) :
    assembleQueries vk ps ch =
      let x := ch.x
      let xn := x ^ vk.n
      let xNext := rotateOmega vk.omega x 1
      let xInv := rotateOmega vk.omega x (-1)
      let xLast := rotateOmega vk.omega x (-((vk.blindingFactors : ℤ) + 1))
      let lb := lagrangeBasis vk.omega vk.n vk.blindingFactors xn x
      let exprs := allExpressions vk ps ch lb.1 lb.2.1 lb.2.2
      let eHEval := expectedHEval exprs ch.y xn
      let hComm := vanishingHCommitment shape.k xn (List.ofFn ps.hPieces)
      let perProof := subProofBlocks (fun p : Fin shape.numProofs =>
        subProofOpeningQueries vk ps x xInv xNext xLast p)
      let fixedQ := columnQueries vk.omega x vk.fixedCommitment CommitmentId.fixedCol
        vk.fixedQueryLayout (List.ofFn ps.fixedEvals)
      let permCommonQ := permutationCommonQueries x CommitmentId.permCommon
        (List.ofFn (fun c => (vk.permutationCommonCommitment c, ps.permutationCommonEvals c)))
      let vanishingQ := vanishingQueries x hComm eHEval ps.vanishingRandom ps.vanishingRandomEval
      perProof ++ fixedQ ++ permCommonQ ++ vanishingQ :=
  assembleQueries_parametric_numProofs vk ps ch

/-- `deriveChallenges_parametric_numProofs` at the consensus-max shape, for every proof string. -/
theorem deriveChallenges_parametric_at_consensus_max (fs : FiatShamir Fp G)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) :
    deriveChallenges fs init ps =
      let t := init ++ subProofBlocks (fun p : Fin shape.numProofs =>
        absorbPoints (ps.adviceCommitments p))
      let theta := fs.squeeze t
      let t := t ++ [.scalar theta] ++ subProofBlocks (fun p : Fin shape.numProofs =>
        subProofBlocks (fun l : Fin shape.numLookups =>
          [TranscriptElt.point (ps.lookupPermutedInput p l),
           TranscriptElt.point (ps.lookupPermutedTable p l)]))
      let beta := fs.squeeze t
      let t := t ++ [.scalar beta]
      let gamma := fs.squeeze t
      let t := t ++ [.scalar gamma]
        ++ subProofBlocks (fun p : Fin shape.numProofs => absorbPoints (ps.permutationProduct p))
        ++ subProofBlocks (fun p : Fin shape.numProofs => absorbPoints (ps.lookupProduct p))
        ++ [TranscriptElt.point ps.vanishingRandom]
      let y := fs.squeeze t
      let t := t ++ [.scalar y] ++ absorbPoints ps.hPieces
      let x := fs.squeeze t
      let evalElts := subProofBlocks (fun p : Fin shape.numProofs =>
        absorbScalars (ps.instanceEvals p))
        ++ subProofBlocks (fun p : Fin shape.numProofs => absorbScalars (ps.adviceEvals p))
        ++ absorbScalars ps.fixedEvals ++ [TranscriptElt.scalar ps.vanishingRandomEval]
        ++ absorbScalars ps.permutationCommonEvals
        ++ subProofBlocks (fun p : Fin shape.numProofs =>
          subProofBlocks (fun s : Fin shape.numPermutationSets =>
            absorbPermSet (ps.permutationSetEvals p s)))
        ++ subProofBlocks (fun p : Fin shape.numProofs =>
          subProofBlocks (fun l : Fin shape.numLookups => absorbLookup (ps.lookupEvals p l)))
      let t := t ++ [.scalar x] ++ evalElts
      let x1 := fs.squeeze t
      let t := t ++ [.scalar x1]
      let x2 := fs.squeeze t
      let t := t ++ [.scalar x2] ++ [TranscriptElt.point ps.multiopenQPrime]
      let x3 := fs.squeeze t
      let t := t ++ [.scalar x3] ++ absorbScalars ps.multiopenU
      let x4 := fs.squeeze t
      let t := t ++ [.scalar x4] ++ [TranscriptElt.point ps.ipaS]
      let xi := fs.squeeze t
      let t := t ++ [.scalar xi]
      let z := fs.squeeze t
      let t := t ++ [.scalar z]
      let ipaRes := (List.finRange shape.k).foldl
        (fun (st : List (TranscriptElt Fp G) × List Fp) j =>
          let t := st.1 ++ [TranscriptElt.point (ps.ipaRounds j).1,
            TranscriptElt.point (ps.ipaRounds j).2]
          let uj := fs.squeeze t
          (t ++ [TranscriptElt.scalar uj], st.2 ++ [uj])) (t, [])
      { theta := theta, beta := beta, gamma := gamma, y := y, x := x,
        x1 := x1, x2 := x2, x3 := x3, x4 := x4, xi := xi, z := z,
        ipaRound := fun j => ipaRes.2.getD j.val 0 } :=
  deriveChallenges_parametric_numProofs fs init ps

/-- `subProofOpeningQueries_commId_disjoint` at the consensus-max shape: even at `N = 65535`, no two
distinct sub-proofs' opening queries share a commitment slot, so the multiopen grouping cannot merge
across sub-proofs. -/
theorem commId_disjoint_at_consensus_max (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (x xInv xNext xLast : Fp) {p p' : Fin shape.numProofs}
    (hpp : p ≠ p') :
    ∀ q ∈ subProofOpeningQueries vk ps x xInv xNext xLast p,
      ∀ q' ∈ subProofOpeningQueries vk ps x xInv xNext xLast p',
        q.commId ≠ q'.commId :=
  subProofOpeningQueries_commId_disjoint vk ps x xInv xNext xLast hpp

end Zcash.Snark.FixtureMax
