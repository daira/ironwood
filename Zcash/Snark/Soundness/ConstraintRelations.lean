import Mathlib
import Zcash.Snark.Soundness.KnowledgeSoundness
import Zcash.Snark.Soundness.PermutationRows
import Zcash.Snark.Soundness.LookupAssembly

/-!
# What the capstone's satisfaction predicate actually says

`circuitSatViaConstraints` is the capstone's notion of circuit satisfaction over the whole
constraint list. On its own that is just a polynomial identity. These theorems say what it buys:
the identity *is* the hypothesis the row-level results consume, so a witness satisfying it satisfies
the permutation argument's copy constraints and the lookup argument's inclusion.

That closes the loop. The capstone hands over `SnarkRelation … circuitSatViaConstraints`
(`snarkRelation_constraints`), and these read the two arguments' relations back out of it.
-/

namespace Zcash.Snark

open Polynomial Finset

open Finset in
/-- **The circuit's declared equalities, read out of the capstone's predicate.** Circuit
satisfaction over the full constraint list gives the permutation argument's conclusion: cells the
circuit's copy constraints force equal do hold equal values. -/
theorem declared_equalities_of_circuitSat
    (omega beta gamma delta theta y : Fp) (chunkLen : ℕ)
    (z : ℕ → Polynomial Fp) (lastP : ℕ → Option (Polynomial Fp))
    (cols : ℕ → List (Polynomial Fp × Polynomial Fp))
    {kk : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (adviceCols instanceCols : Fin 1 → ℕ → Polynomial Fp) (gates : List (Expr Fp))
    (lookups : Fin 1 → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpoly : Polynomial Fp) {n u : ℕ} (hn : n ≠ 0)
    (a : Fin (2 ^ kk) → Fp)
    (cs : List ((Fin u × Fin (cols 0).length) × (Fin u × Fin (cols 0).length)))
    (hsat : circuitSatViaConstraints fixedCols (fun _ => adviceCols) (fun _ => instanceCols) gates
      (fun _ => deployedPermSets omega 1 z lastP)
      (fun _ => deployedPermChunks omega 1 z lastP cols) lookups
      beta gamma delta theta y chunkLen l0P lLastP lBlindP hpoly n a)
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness (constraintPolys fixedCols adviceCols
      instanceCols gates (fun _ => deployedPermSets omega 1 z lastP)
      (fun _ => deployedPermChunks omega 1 z lastP cols) lookups
      beta gamma delta theta chunkLen l0P lLastP lBlindP) n j))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < u, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ u) ≠ 0)
    (hσ : ∀ c : Fin u × Fin (cols 0).length,
      rowSigmaName omega (cols 0) (c.1 : ℕ) (c.2 : ℕ)
        = rowName omega delta 0 ((PermConstruction.build cs c).1 : ℕ)
            ((PermConstruction.build cs c).2 : ℕ))
    (hnm : Function.Injective fun c : Fin u × Fin (cols 0).length =>
      rowName omega delta 0 (c.1 : ℕ) (c.2 : ℕ))
    (hgoodγ : gamma ∉ szBadSet (linProdDiff
      ((cellPairs u (cols 0).length (rowValue omega (cols 0))
        (rowSigmaName omega (cols 0))).map (fun q => q.1 + q.2 * beta))
      ((cellPairs u (cols 0).length (rowValue omega (cols 0))
        (rowName omega delta 0)).map (fun q => q.1 + q.2 * beta))))
    (hgoodβ : ∀ j, beta ∉ szBadSet ((pairProdDiff
      (cellPairs u (cols 0).length (rowValue omega (cols 0)) (rowSigmaName omega (cols 0)))
      (cellPairs u (cols 0).length (rowValue omega (cols 0))
        (rowName omega delta 0))).coeff j))
    {x w : Fin u × Fin (cols 0).length}
    (hxw : Relation.EqvGen (fun p q => (p, q) ∈ cs) x w) :
    rowValue omega (cols 0) (x.1 : ℕ) (x.2 : ℕ)
        = rowValue omega (cols 0) (w.1 : ℕ) (w.2 : ℕ)
      ∨ ∃ q ∈ range u ×ˢ range (cols 0).length,
          rowValue omega (cols 0) q.1 q.2
            + beta * rowName omega delta 0 q.1 q.2 + gamma = 0 :=
  deployed_declared_equalities_of_identity omega beta gamma delta theta y chunkLen z lastP cols
    fixedCols adviceCols instanceCols gates lookups l0P lLastP lBlindP hpoly hn 0 cs hsat hgoodY
    hrow hactive hl0 hlast hσ hnm hgoodγ hgoodβ hxw

open Finset in
/-- **The lookup relation, read out of the capstone's predicate.** The same satisfaction predicate
gives the lookup argument's conclusion: every input value appears in the table. -/
theorem lookup_relation_of_circuitSat (omega beta gamma delta theta y : Fp) (chunkLen : ℕ)
    (zP aP sP : Polynomial Fp) (inputExprs tableExprs : List (Expr Fp))
    {kk np : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (adviceCols instanceCols : Fin np → ℕ → Polynomial Fp) (gates : List (Expr Fp))
    (sets : Fin np → List (PermSetEval (Polynomial Fp)))
    (chunks : Fin np →
      List (PermSetEval (Polynomial Fp) × List (Polynomial Fp × Polynomial Fp)))
    (lookups : Fin np → List (LookupEval (Polynomial Fp) × List (Expr Fp) × List (Expr Fp)))
    (l0P lLastP lBlindP hpoly : Polynomial Fp) {n m : ℕ} (hn : n ≠ 0) (p : Fin np)
    (a : Fin (2 ^ kk) → Fp) (homega : omega ≠ 0)
    (hlk : (lookupEvalPolys omega zP aP sP, inputExprs, tableExprs) ∈ lookups p)
    (hsat : circuitSatViaConstraints fixedCols (fun _ => adviceCols) (fun _ => instanceCols) gates
      sets chunks lookups beta gamma delta theta y chunkLen l0P lLastP lBlindP hpoly n a)
    (hgoodY : ∀ j, y ∉ szBadSet (foldSplitWitness (constraintPolys fixedCols adviceCols
      instanceCols gates sets chunks lookups beta gamma delta theta chunkLen l0P lLastP lBlindP)
      n j))
    (hrow : ∀ i : ℕ, (omega ^ i) ^ n = 1)
    (hactive : ∀ i < m + 1, 1 - (lLastP.eval (omega ^ i) + lBlindP.eval (omega ^ i)) ≠ 0)
    (hl0 : l0P.eval (omega ^ 0) ≠ 0) (hlast : lLastP.eval (omega ^ (m + 1)) ≠ 0)
    (hgoodγ : gamma ∉ szBadSet ((lookupProdDiff
      (univ.val.map fun i : Fin (m + 1) => aP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) => sP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (inputExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (tableExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))).map (evalRingHom beta)))
    (hgoodβ : ∀ j, beta ∉ szBadSet ((lookupProdDiff
      (univ.val.map fun i : Fin (m + 1) => aP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) => sP.eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (inputExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))
      (univ.val.map fun i : Fin (m + 1) =>
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
          (tableExprs.map (Expr.map C))).eval (omega ^ (i : ℕ)))).coeff j))
    (i : Fin (m + 1)) :
    (∃ j : Fin (m + 1),
        (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (inputExprs.map (Expr.map C))).eval (omega ^ (i : ℕ))
          = (compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (tableExprs.map (Expr.map C))).eval (omega ^ (j : ℕ)))
    ∨ ∃ t ∈ range (m + 1), ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (inputExprs.map (Expr.map C))).eval (omega ^ t) + beta)
          * ((compressExprs fixedCols (adviceCols p) (instanceCols p) (C theta)
            (tableExprs.map (Expr.map C))).eval (omega ^ t) + gamma) = 0 :=
  deployed_lookup_relation_of_identity omega beta gamma delta theta y chunkLen zP aP sP inputExprs
    tableExprs fixedCols adviceCols instanceCols gates sets chunks lookups l0P lLastP lBlindP hpoly
    hn p homega hlk hsat hgoodY hrow hactive hl0 hlast hgoodγ hgoodβ i

end Zcash.Snark
