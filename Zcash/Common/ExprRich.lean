import Zcash.Common.Expr
import Clean.Halo2.Keygen.RichExpression

/-!
# The verifier `Expr` ↔ pinned `RichExpression` boundary

The verifier keeps its own gate AST `Zcash.Snark.Expr` (`Zcash/Common/Expr.lean`), while
the pinned-constraint-system derivation in Clean core speaks `Halo2.RichExpression`
(`Clean.Halo2.Keygen.RichExpression`). The two types have identical constructor names and
semantics on the shared node set; `RichExpression` merely carries one extra node — a
pre-compression `selector` — that never survives selector compression and therefore never
appears in a verifier gate.

The canonical conversion is `Expr → RichExpression` (`RichExpression.ofExpr`): it is total
and value-preserving with no invented leaves, because every `Expr` constructor is a
`RichExpression` constructor. Evaluation is preserved unconditionally
(`RichExpression.eval_ofExpr`), so verifier-side gate evaluations transport into the pinned
derivation's `RichExpression.eval` semantics (and back) at the VK boundary.
-/

namespace Halo2

/-- Carry a verifier `Expr` into the pinned `RichExpression`, constructor by constructor.
Total: `Expr` has no `selector` node, so no leaf is invented. -/
def RichExpression.ofExpr {F : Type} : Zcash.Snark.Expr F → RichExpression F
  | .constant c => .constant c
  | .fixed i => .fixed i
  | .advice i => .advice i
  | .instance i => .instance i
  | .negated e => .negated (RichExpression.ofExpr e)
  | .sum a b => .sum (RichExpression.ofExpr a) (RichExpression.ofExpr b)
  | .product a b => .product (RichExpression.ofExpr a) (RichExpression.ofExpr b)
  | .scaled e c => .scaled (RichExpression.ofExpr e) c

/-- **Evaluation is preserved.** The pinned expression `RichExpression.ofExpr e` evaluates
exactly as the verifier `Expr` `e` does — no selector-freeness side condition, since
`ofExpr` introduces no `selector` node. -/
@[simp] theorem RichExpression.eval_ofExpr {F : Type} [CommRing F]
    (fE aE iE : ℕ → F) (e : Zcash.Snark.Expr F) :
    (RichExpression.ofExpr e).eval fE aE iE = e.eval fE aE iE := by
  induction e <;>
    simp_all only [RichExpression.ofExpr, RichExpression.eval, Zcash.Snark.Expr.eval]

end Halo2
