import Zcash.Snark.Verifier.Key

/-!
# Verifier constraint-system data

This is the circuit-independent structural data consumed by the verifier.  The
translation from a closed circuit into this representation lives at the circuit/SNARK
integration boundary.
-/

namespace Zcash.Snark

/-- The Ironwood-native constraint-system data consumed by the verifier. -/
structure VerifierCS (numLookups : ℕ) (F : Type*) where
  gates : List (Expr F)
  permutationChunks : List (List (ColumnRef × ℕ))
  lookupInputExprs : Fin numLookups → List (Expr F)
  lookupTableExprs : Fin numLookups → List (Expr F)

end Zcash.Snark
