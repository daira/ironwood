import Mathlib
import Zcash.Snark.Soundness.LookupRows
import Zcash.Snark.Verifier.Parametric

/-!
# Instantiating lookup constraints with routed decoded polynomials

The verifier names each committed polynomial by `CommitmentId`.  Given a polynomial resolver keyed
by those names, this module constructs polynomial-valued lookup entries whose next/previous fields
are rotations of the same three base polynomials.  A single query-level opening hypothesis over the
verifier's actual `lookupQueries` then proves that evaluating those entries at `x` reproduces
`subProofLookups`.

Everything is parametric in the verification key, proof string, proof index, and resolver.  No
circuit fixture or concrete verification key occurs here.
-/

namespace Zcash.Snark

open Polynomial

/-- One proof's lookup commitments paired with their five claimed evaluations, in verifier order. -/
def subProofLookupCommitments {shape : Shape} {F G : Type*}
    (ps : ProofString shape F G) (p : Fin shape.numProofs) :
    List (LookupCommitments G × LookupEval F) :=
  List.ofFn fun l =>
    ({ product := ps.lookupProduct p l,
       permutedInput := ps.lookupPermutedInput p l,
       permutedTable := ps.lookupPermutedTable p l },
     ps.lookupEvals p l)

/-- The verifier's lookup-only query block for one sub-proof. -/
def subProofLookupQueries {shape : Shape} {F G : Type*} [Field F]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (p : Fin shape.numProofs) :
    List (VerifierQuery shape.k F G) :=
  lookupQueries ch.x (rotateOmega vk.omega ch.x (-1)) (rotateOmega vk.omega ch.x 1)
    (CommitmentId.lookupProduct p) (CommitmentId.lookupPermInput p)
    (CommitmentId.lookupPermTable p) (subProofLookupCommitments ps p)

/-- Every lookup-only query is an actual member of the verifier's complete assembled query list. -/
theorem mem_assembleQueries_of_mem_subProofLookupQueries
    {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (p : Fin shape.numProofs) {q : VerifierQuery shape.k F G}
    (hq : q ∈ subProofLookupQueries vk ps ch p) :
    q ∈ assembleQueries vk instanceCommitment ps ch := by
  have hblock : q ∈ subProofOpeningQueries vk instanceCommitment ps ch.x
      (rotateOmega vk.omega ch.x (-1)) (rotateOmega vk.omega ch.x 1)
      (rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1))) p := by
    exact List.mem_append_right _ (by
      simpa [subProofLookupQueries, subProofLookupCommitments] using hq)
  have hperProof : q ∈ subProofBlocks fun p : Fin shape.numProofs =>
      subProofOpeningQueries vk instanceCommitment ps ch.x
        (rotateOmega vk.omega ch.x (-1)) (rotateOmega vk.omega ch.x 1)
        (rotateOmega vk.omega ch.x (-((vk.blindingFactors : ℤ) + 1))) p := by
    exact List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, hblock⟩
  rw [assembleQueries_parametric_numProofs]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hperProof))

/-- Polynomial lookup entries built from an arbitrary commitment-ID resolver.  Coherence of the
rotations is definitional through `lookupEvalPolys`. -/
noncomputable def lookupEntriesOfResolver {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) :
    List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)) :=
  List.ofFn fun l =>
    (lookupEvalPolys vk.omega
      (poly (.lookupProduct p l))
      (poly (.lookupPermInput p l))
      (poly (.lookupPermTable p l)),
     vk.lookupInputExprs l,
     vk.lookupTableExprs l)

/-- The selected lookup's compressed input polynomial under the resolver-backed column feeds. -/
noncomputable def lookupInputPolyOfResolver {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) : Polynomial Fp :=
  compressExprs
    (fun j => poly (.fixedCol j))
    (fun j => poly (.adviceCol p j))
    (fun j => poly (.instanceCol p j))
    (C ch.theta) ((vk.lookupInputExprs l).map (Expr.map C))

/-- The selected lookup's compressed table polynomial under the same resolver-backed feeds. -/
noncomputable def lookupTablePolyOfResolver {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) : Polynomial Fp :=
  compressExprs
    (fun j => poly (.fixedCol j))
    (fun j => poly (.adviceCol p j))
    (fun j => poly (.instanceCol p j))
    (C ch.theta) ((vk.lookupTableExprs l).map (Expr.map C))

/-- A full constraint model whose column polynomials and lookup arguments are resolved by stable
commitment identities.  The permutation sets/chunks remain parameters until their analogous
canonical routing layer is installed. -/
noncomputable def constraintModelOfResolver {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (sets : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (l0 lLast lBlind : Polynomial Fp) :
    ConstraintPolyModel shape.numProofs where
  fixedCols j := poly (.fixedCol j)
  adviceCols p j := poly (.adviceCol p j)
  instanceCols p j := poly (.instanceCol p j)
  gates := vk.gates
  sets := sets
  chunks := chunks
  lookups := lookupEntriesOfResolver vk poly
  beta := ch.beta
  gamma := ch.gamma
  delta := vk.delta
  theta := ch.theta
  chunkLen := vk.chunkLen
  l0 := l0
  lLast := lLast
  lBlind := lBlind

@[simp] theorem constraintModelOfResolver_lookups {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (sets : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (l0 lLast lBlind : Polynomial Fp) (p : Fin shape.numProofs) :
    (constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind).lookups p
      = lookupEntriesOfResolver vk poly p := rfl

/-- The selected coherent lookup entry occurs in the resolver-built lookup list. -/
theorem lookupEntry_mem_lookupEntriesOfResolver {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) :
    (lookupEvalPolys vk.omega
        (poly (.lookupProduct p l))
        (poly (.lookupPermInput p l))
        (poly (.lookupPermTable p l)),
      vk.lookupInputExprs l,
      vk.lookupTableExprs l) ∈ lookupEntriesOfResolver vk poly p := by
  exact List.mem_ofFn.mpr ⟨l, rfl⟩

/-- The same selected entry, exposed directly through the full resolver-built model.  This is the
membership fact passed to `ConstraintSatisfaction.lookupStart`, `lookupEnd`,
`lookupProductStep`, `lookupRunStart`, and `lookupRunStep`. -/
theorem lookupEntry_mem_constraintModelOfResolver {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (sets : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (l0 lLast lBlind : Polynomial Fp)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) :
    (lookupEvalPolys vk.omega
        (poly (.lookupProduct p l))
        (poly (.lookupPermInput p l))
        (poly (.lookupPermTable p l)),
      vk.lookupInputExprs l,
      vk.lookupTableExprs l) ∈
        (constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind).lookups p :=
  lookupEntry_mem_lookupEntriesOfResolver vk poly p l

private theorem lookup_query_mem {shape : Shape} {F G : Type*} [Field F]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) (p : Fin shape.numProofs) (l : Fin shape.numLookups)
    (q : VerifierQuery shape.k F G)
    (hq : q ∈
      [{ point := ch.x,
         commitment := .point (ps.lookupProduct p l),
         eval := (ps.lookupEvals p l).productEval,
         commId := .lookupProduct p l },
       { point := ch.x,
         commitment := .point (ps.lookupPermutedInput p l),
         eval := (ps.lookupEvals p l).permutedInputEval,
         commId := .lookupPermInput p l },
       { point := ch.x,
         commitment := .point (ps.lookupPermutedTable p l),
         eval := (ps.lookupEvals p l).permutedTableEval,
         commId := .lookupPermTable p l },
       { point := rotateOmega vk.omega ch.x (-1),
         commitment := .point (ps.lookupPermutedInput p l),
         eval := (ps.lookupEvals p l).permutedInputInvEval,
         commId := .lookupPermInput p l },
       { point := rotateOmega vk.omega ch.x 1,
         commitment := .point (ps.lookupProduct p l),
         eval := (ps.lookupEvals p l).productNextEval,
         commId := .lookupProduct p l }]) :
    q ∈ subProofLookupQueries vk ps ch p := by
  rw [subProofLookupQueries, lookupQueries, List.mem_flatMap]
  refine ⟨(
    ({ product := ps.lookupProduct p l,
       permutedInput := ps.lookupPermutedInput p l,
       permutedTable := ps.lookupPermutedTable p l },
     ps.lookupEvals p l), (l : ℕ)), ?_, ?_⟩
  · rw [List.mem_iff_getElem]
    refine ⟨l, ?_, ?_⟩
    · simp [subProofLookupCommitments]
    · simp [subProofLookupCommitments]
  · simpa [subProofLookupCommitments] using hq

/-- **Generic lookup polynomial routing.** If the polynomial selected by every lookup query's
`CommitmentId` takes the query's claimed value at its opened point, evaluating the coherent
polynomial-valued lookup entries at `x` gives exactly the verifier's `subProofLookups`.

The hypothesis is deliberately query-shaped: multiopen extraction can supply it uniformly, and the
two queries sharing the product ID (respectively permuted-input ID) automatically use the same
polynomial. -/
theorem eval_lookupEntriesOfResolver {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs)
    (hopen : ∀ q ∈ subProofLookupQueries vk ps ch p,
      (poly q.commId).eval q.point = q.eval) :
    (lookupEntriesOfResolver vk poly p).map
        (fun lk => (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2))
      = subProofLookups vk ps p := by
  rw [lookupEntriesOfResolver, subProofLookups, List.map_ofFn]
  congr 1
  funext l
  have hproduct := hopen
    { point := ch.x,
      commitment := .point (ps.lookupProduct p l),
      eval := (ps.lookupEvals p l).productEval,
      commId := .lookupProduct p l }
    (lookup_query_mem vk ps ch p l _ (by simp))
  have hinput := hopen
    { point := ch.x,
      commitment := .point (ps.lookupPermutedInput p l),
      eval := (ps.lookupEvals p l).permutedInputEval,
      commId := .lookupPermInput p l }
    (lookup_query_mem vk ps ch p l _ (by simp))
  have htable := hopen
    { point := ch.x,
      commitment := .point (ps.lookupPermutedTable p l),
      eval := (ps.lookupEvals p l).permutedTableEval,
      commId := .lookupPermTable p l }
    (lookup_query_mem vk ps ch p l _ (by simp))
  have hinputInv := hopen
    { point := rotateOmega vk.omega ch.x (-1),
      commitment := .point (ps.lookupPermutedInput p l),
      eval := (ps.lookupEvals p l).permutedInputInvEval,
      commId := .lookupPermInput p l }
    (lookup_query_mem vk ps ch p l _ (by simp))
  have hproductNext := hopen
    { point := rotateOmega vk.omega ch.x 1,
      commitment := .point (ps.lookupProduct p l),
      eval := (ps.lookupEvals p l).productNextEval,
      commId := .lookupProduct p l }
    (lookup_query_mem vk ps ch p l _ (by simp))
  have hproduct' :
      (poly (.lookupProduct p l)).eval ch.x = (ps.lookupEvals p l).productEval := by
    simpa using hproduct
  have hproductNext' :
      ((poly (.lookupProduct p l)).comp (C vk.omega * X)).eval ch.x
        = (ps.lookupEvals p l).productNextEval := by
    rw [eval_comp_rotate, mul_comm vk.omega ch.x]
    simpa only [rotateOmega, zpow_one] using hproductNext
  have hinput' :
      (poly (.lookupPermInput p l)).eval ch.x
        = (ps.lookupEvals p l).permutedInputEval := by
    simpa using hinput
  have hinputInv' :
      ((poly (.lookupPermInput p l)).comp (C vk.omega⁻¹ * X)).eval ch.x
        = (ps.lookupEvals p l).permutedInputInvEval := by
    rw [eval_comp_rotate, mul_comm vk.omega⁻¹ ch.x]
    simpa only [rotateOmega, zpow_neg_one] using hinputInv
  have htable' :
      (poly (.lookupPermTable p l)).eval ch.x
        = (ps.lookupEvals p l).permutedTableEval := by
    simpa using htable
  apply Prod.ext
  · simp only [Function.comp_apply, LookupEval.map, lookupEvalPolys]
    rw [hproduct', hproductNext', hinput', hinputInv', htable']
  · rfl

/-- The same routing theorem with its opening premise supplied on the verifier's complete assembled
query list. -/
theorem eval_lookupEntriesOfResolver_of_assembleQueries
    {shape : Shape} {G : Type*} [Inhabited G]
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp) (p : Fin shape.numProofs)
    (hopen : ∀ q ∈ assembleQueries vk instanceCommitment ps ch,
      (poly q.commId).eval q.point = q.eval) :
    (lookupEntriesOfResolver vk poly p).map
        (fun lk => (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2))
      = subProofLookups vk ps p := by
  apply eval_lookupEntriesOfResolver vk ps ch poly p
  intro q hq
  exact hopen q (mem_assembleQueries_of_mem_subProofLookupQueries
    vk instanceCommitment ps ch p hq)

/-- The resolver-built model discharges the existing `hlookups` bridge from one uniform
query-opening fact per sub-proof. -/
theorem eval_constraintModelOfResolver_lookups {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (poly : CommitmentId → Polynomial Fp)
    (sets : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (l0 lLast lBlind : Polynomial Fp)
    (hopen : ∀ p q, q ∈ subProofLookupQueries vk ps ch p →
      (poly q.commId).eval q.point = q.eval) :
    ∀ p, ((constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind).lookups p).map
        (fun lk => (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2))
      = subProofLookups vk ps p :=
  fun p => eval_lookupEntriesOfResolver vk ps ch poly p (hopen p)

/-- The model-level `hlookups` bridge from one opening fact over the verifier's complete query
list. -/
theorem eval_constraintModelOfResolver_lookups_of_assembleQueries
    {shape : Shape} {G : Type*} [Inhabited G]
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (sets : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (l0 lLast lBlind : Polynomial Fp)
    (hopen : ∀ q ∈ assembleQueries vk instanceCommitment ps ch,
      (poly q.commId).eval q.point = q.eval) :
    ∀ p, ((constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind).lookups p).map
        (fun lk => (lk.1.map (fun q => q.eval ch.x), lk.2.1, lk.2.2))
      = subProofLookups vk ps p :=
  fun p => eval_lookupEntriesOfResolver_of_assembleQueries
    vk instanceCommitment ps ch poly p hopen

/-- Full family satisfaction specialized to one resolver-built lookup gives exactly the five
coherent divisibility facts consumed by `deployed_lookup_subset`. -/
theorem ConstraintSatisfaction.lookupConstraintsDvdOfResolver
    {shape : Shape} {G : Type*} {n : ℕ}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (sets : Fin shape.numProofs → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (l0 lLast lBlind : Polynomial Fp)
    (h : ConstraintSatisfaction
      (constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind) n)
    (p : Fin shape.numProofs) (l : Fin shape.numLookups) :
    LookupConstraintsDvd n vk.omega ch.beta ch.gamma
      (poly (.lookupProduct p l))
      (poly (.lookupPermInput p l))
      (poly (.lookupPermTable p l))
      (lookupInputPolyOfResolver vk ch poly p l)
      (lookupTablePolyOfResolver vk ch poly p l)
      l0 lLast lBlind := by
  let lk :
      LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp) :=
    (lookupEvalPolys vk.omega
        (poly (.lookupProduct p l))
        (poly (.lookupPermInput p l))
        (poly (.lookupPermTable p l)),
      vk.lookupInputExprs l,
      vk.lookupTableExprs l)
  have hlk : lk ∈
      (constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind).lookups p := by
    exact lookupEntry_mem_constraintModelOfResolver
      vk ch poly sets chunks l0 lLast lBlind p l
  constructor
  · simpa [lk, constraintModelOfResolver, lookupEvalPolys] using h.lookupStart p hlk
  · simpa [lk, constraintModelOfResolver, lookupEvalPolys] using h.lookupEnd p hlk
  · simpa [lk, constraintModelOfResolver, lookupEvalPolys,
      lookupInputPolyOfResolver, lookupTablePolyOfResolver] using h.lookupProductStep p hlk
  · simpa [lk, constraintModelOfResolver, lookupEvalPolys] using h.lookupRunStart p hlk
  · simpa [lk, constraintModelOfResolver, lookupEvalPolys] using h.lookupRunStep p hlk

end Zcash.Snark
