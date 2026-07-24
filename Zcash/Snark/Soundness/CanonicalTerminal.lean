import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Zcash.Snark.Soundness.VestaBudget

/-!
# Canonical decoded-model constraint terminal

The deployed quotient capstone works with separate fixed, advice, instance,
permutation, lookup, and row-selector polynomial families. The circuit integration
boundary instead consumes the single model canonically routed from an accepting
query assembly.

This module joins those verifier-native views. It contains no Clean or Action
concepts.
-/

namespace Zcash.Snark

open Polynomial

set_option maxHeartbeats 20000

variable {G : Type*} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
The canonical decoded model evaluates at the quotient challenge to exactly the
claims carried by the accepted proof string.

This is the compact input expected from decoded-member node binding. It replaces
the terminal's older collection of independently chosen decoder functions.
-/
structure AcceptedModelClaimedEvaluations
    {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k}
    {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G}
    {ch : Challenges shape.k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi}
    {hblinding : vk.blindingFactors < vk.n}
    (haccepts :
      DeployedAccepts urs hk vk instanceCommitment ps ch) : Prop where
  fixed : ∀ column,
    ((CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).fixedCols column).eval ch.x =
        finFn ps.fixedEvals column
  advice : ∀ proofIndex column,
    ((CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).adviceCols
        proofIndex column).eval ch.x =
      finFn (ps.adviceEvals proofIndex) column
  «instance» : ∀ proofIndex column,
    ((CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).instanceCols
        proofIndex column).eval ch.x =
      finFn (ps.instanceEvals proofIndex) column
  sets : ∀ proofIndex,
    ((CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).sets proofIndex).map
        (PermSetEval.map fun polynomial => polynomial.eval ch.x) =
      subProofPermSets ps proofIndex
  chunks : ∀ proofIndex,
    ((CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).chunks proofIndex).map
        (fun chunk =>
          (chunk.1.map fun polynomial => polynomial.eval ch.x,
            chunk.2.map fun pair =>
              (pair.1.eval ch.x, pair.2.eval ch.x))) =
      subProofPermChunks vk ps proofIndex
  lookups : ∀ proofIndex,
    ((CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).lookups proofIndex).map
        (fun lookup =>
          (lookup.1.map fun polynomial => polynomial.eval ch.x,
            lookup.2.1, lookup.2.2)) =
      subProofLookups vk ps proofIndex
  l0 :
    (CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).l0.eval ch.x =
      (lagrangeBasis vk.omega vk.n vk.blindingFactors
        (ch.x ^ vk.n) ch.x).1
  lLast :
    (CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).lLast.eval ch.x =
      (lagrangeBasis vk.omega vk.n vk.blindingFactors
        (ch.x ^ vk.n) ch.x).2.1
  lBlind :
    (CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts).lBlind.eval ch.x =
      (lagrangeBasis vk.omega vk.n vk.blindingFactors
        (ch.x ^ vk.n) ch.x).2.2

namespace AcceptedModelClaimedEvaluations

/--
Construct the complete canonical fingerprint from uniform assembled-query
openings, the three column-feed equations, and the standard permutation/domain
facts.
-/
noncomputable def ofOpenings
    {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k}
    {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G}
    {ch : Challenges shape.k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi}
    {hblinding : vk.blindingFactors < vk.n}
    (haccepts :
      DeployedAccepts urs hk vk instanceCommitment ps ch)
    (fixed : ∀ column,
      ((CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts).fixedCols column).eval ch.x =
          finFn ps.fixedEvals column)
    (advice : ∀ proofIndex column,
      ((CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts).adviceCols
          proofIndex column).eval ch.x =
        finFn (ps.adviceEvals proofIndex) column)
    (instanceColumns : ∀ proofIndex column,
      ((CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts).instanceCols
          proofIndex column).eval ch.x =
        finFn (ps.instanceEvals proofIndex) column)
    (hopen : ∀ query ∈
      assembleQueries vk instanceCommitment ps ch,
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := memberDecode) haccepts query.commId).eval
          query.point = query.eval)
    (hpermutationWellFormed :
      permutationLastEvalsWellFormed ps = true)
    (hpermutationRouting :
      PermutationChunkRoutingCoherent vk)
    (hrows : Function.Injective
      fun row : Fin vk.n => vk.omega ^ (row : ℕ))
    (hroot : vk.omega ^ vk.n = 1)
    (hnFp : (vk.n : Fp) ≠ 0)
    (hxDomain : ch.x ^ vk.n ≠ 1) :
    AcceptedModelClaimedEvaluations
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts := by
  let polynomial :=
    CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := memberDecode) haccepts
  let selectors :=
    canonicalLagrangePolynomials vk.omega hblinding
  have hselectorEvaluations :=
    canonicalConstraintModelOfPermutationResolver_selectorEvaluations
      vk ch polynomial hblinding hrows hroot hnFp hxDomain
  refine
    { fixed := fixed
      advice := advice
      «instance» := instanceColumns
      sets := ?_
      chunks := ?_
      lookups := ?_
      l0 := ?_
      lLast := ?_
      lBlind := ?_ }
  · intro proofIndex
    simpa [CanonicalMemberConstraintRelation.acceptedModel,
      canonicalConstraintModelOfPermutationResolver,
      constraintModelOfPermutationResolver,
      constraintModelOfResolver, polynomial, selectors] using
      eval_permutationSetsOfResolver
        vk instanceCommitment ps ch polynomial
        hpermutationWellFormed proofIndex hopen
  · intro proofIndex
    simpa [CanonicalMemberConstraintRelation.acceptedModel,
      canonicalConstraintModelOfPermutationResolver,
      constraintModelOfPermutationResolver,
      constraintModelOfResolver, polynomial, selectors] using
      eval_permutationChunksOfResolver
        vk instanceCommitment ps ch polynomial
        hpermutationWellFormed hpermutationRouting proofIndex hopen
  · intro proofIndex
    simpa [CanonicalMemberConstraintRelation.acceptedModel,
      canonicalConstraintModelOfPermutationResolver,
      constraintModelOfPermutationResolver,
      constraintModelOfResolver, polynomial, selectors] using
      eval_lookupEntriesOfResolver_of_assembleQueries
        vk instanceCommitment ps ch polynomial proofIndex hopen
  · exact congrArg Prod.fst hselectorEvaluations
  · exact congrArg (fun values => values.2.1) hselectorEvaluations
  · exact congrArg (fun values => values.2.2) hselectorEvaluations

end AcceptedModelClaimedEvaluations

/--
The deployed quotient-member binding, instantiated at the accepted canonical
decoded model, proves that model's complete circuit identity or returns the shared
augmented commitment relation.
-/
theorem acceptedModelCircuitSat_or_relation
    {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hblinding : vk.blindingFactors < vk.n)
    (hpoly : Polynomial Fp)
    (i m : ℕ)
    (hm :
      m < (deployedSetQueries
        vk instanceCommitment ps ch i).length)
    (columnPolynomial :
      Fin (deployedSetQueries
        vk instanceCommitment ps ch i).length →
        Polynomial Fp)
    (hbindAll : ∀
      (pointIndex : Fin
        ((constructIntermediateSets
          (assembleQueries vk instanceCommitment ps ch)).points.getD
            i []).length)
      (memberIndex : Fin
        (deployedSetQueries
          vk instanceCommitment ps ch i).length),
      (columnPolynomial memberIndex).eval
          (((constructIntermediateSets
            (assembleQueries vk instanceCommitment ps ch)).points.getD
              i [])[pointIndex]) =
        ((deployedSetQueries
          vk instanceCommitment ps ch i).getD
            (memberIndex : ℕ) (.point 0, [])).2.getD
              (pointIndex : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hquot : hpoly = columnPolynomial ⟨m, hm⟩)
    (hroute :
      (constructIntermediateSets
        (assembleQueries vk instanceCommitment ps ch)).points.getD
          i [] = [ch.x])
    (hevals : ∀ defaultQuery,
      ((deployedSetQueries
        vk instanceCommitment ps ch i).getD m defaultQuery).2 =
        [expectedHEval
          (allExpressions vk ps ch
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).2.1
            (lagrangeBasis vk.omega vk.n vk.blindingFactors
              (ch.x ^ vk.n) ch.x).2.2)
          ch.y (ch.x ^ vk.n)])
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (combineConstraints
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).fixedCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).adviceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).instanceCols
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).gates
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).sets
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).chunks
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).lookups
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).beta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).gamma
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).delta
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).theta
          ch.y
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).chunkLen
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).l0
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).lLast
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).lBlind -
          hpoly * (X ^ vk.n - 1))) :
    (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts).CircuitSat
          ch.y hpoly vk.n a ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let model :=
    CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := memberDecode)
      (hblinding := hblinding) haccepts
  have hfold :=
    hfold_of_constraint_polys
      urs hk vk instanceCommitment ps ch
      model.fixedCols model.adviceCols model.instanceCols
      model.sets model.chunks model.lookups
      model.l0 model.lLast model.lBlind hpoly
      i m hm columnPolynomial hbindAll hquot hroute hevals haccepts
      claimed.fixed claimed.advice claimed.«instance»
      claimed.sets claimed.chunks claimed.lookups
      claimed.l0 claimed.lLast claimed.lBlind
  rcases hfold with hcheck | hrelation
  · apply Or.inl
    apply circuitSatViaConstraints_of_check
      model.fixedCols (fun _ => model.adviceCols)
      (fun _ => model.instanceCols)
      model.gates model.sets model.chunks model.lookups
      model.beta model.gamma model.delta model.theta ch.y
      model.chunkLen model.l0 model.lLast model.lBlind
      hpoly vk.n a ch.x
    · simpa [model, CanonicalMemberConstraintRelation.acceptedModel,
        canonicalConstraintModelOfPermutationResolver,
        constraintModelOfPermutationResolver,
        constraintModelOfResolver] using hcheck
    · apply hgood_of_good_challenge
      simpa only [model] using hxgood
  · exact Or.inr hrelation

end Zcash.Snark
