import Zcash.Circuits.Fixtures.ProjectSemantics
import Zcash.Snark.Core.Field
import Zcash.Snark.Verifier.Expressions

/-!
# From verifier gates to Clean gate expressions

The VK-match fixtures compare `projectCSPostMap` output (the fixture mirror
`Zcash.Circuits.Fixtures.Expr`) with the Rust dump; the verifier's `VerifyingKey`
carries the mirrored `Zcash.Snark.Expr`. This module crosses that mirror: `ofFixture`
translates one to the other, `ofFixture_eval` shows the translation preserves
evaluation on selector-free expressions (all post-compression gates), and
`ofFixture_eraseExpr_substSelectorMap_eval` composes it with the projection semantics
(`Zcash.Circuits.Fixtures.ProjectSemantics`): a VK gate matched to the projection
evaluates to the original Clean gate expression under the selector-replacement
valuation.

This is the per-gate step of the Clean-constraints transport in the Action integration
roadmap; the layout side (activation tables pinning the packed selector columns, the
placement, copies and lookups) is what remains to turn per-row applications of this
lemma into `Halo2.Constraints`.
-/

namespace Zcash.Snark

open Halo2
open Zcash.Circuits.Fixtures (QueryState SelCompress Interprets substValuation
  substSelectorMap eraseExpr)

/-- Translate the fixture `Expr` mirror to the verifier's; the `selector` atom
(absent post-compression) maps to a junk constant, guarded by `selectorFree` in
`ofFixture_eval`. -/
def Expr.ofFixture : Zcash.Circuits.Fixtures.Expr Fp → Expr Fp
  | .constant c => .constant c
  | .fixed i => .fixed i
  | .advice i => .advice i
  | .instance i => .instance i
  | .negated a => .negated (Expr.ofFixture a)
  | .sum a b => .sum (Expr.ofFixture a) (Expr.ofFixture b)
  | .product a b => .product (Expr.ofFixture a) (Expr.ofFixture b)
  | .scaled a c => .scaled (Expr.ofFixture a) c
  | .selector _ => .constant 0

/-- On selector-free expressions the mirror translation preserves evaluation. -/
theorem Expr.ofFixture_eval (fE aE iE selE : ℕ → Fp)
    (e : Zcash.Circuits.Fixtures.Expr Fp) (h : e.selectorFree = true) :
    (Expr.ofFixture e).eval fE aE iE = e.eval fE aE iE selE := by
  induction e with
  | constant c => rfl
  | fixed i => rfl
  | advice i => rfl
  | «instance» i => rfl
  | negated a ih =>
      simp only [Zcash.Circuits.Fixtures.Expr.selectorFree] at h
      simp only [ofFixture, Expr.eval, Zcash.Circuits.Fixtures.Expr.eval, ih h]
  | sum a b iha ihb =>
      simp only [Zcash.Circuits.Fixtures.Expr.selectorFree, Bool.and_eq_true] at h
      simp only [ofFixture, Expr.eval, Zcash.Circuits.Fixtures.Expr.eval,
        iha h.1, ihb h.2]
  | product a b iha ihb =>
      simp only [Zcash.Circuits.Fixtures.Expr.selectorFree, Bool.and_eq_true] at h
      simp only [ofFixture, Expr.eval, Zcash.Circuits.Fixtures.Expr.eval,
        iha h.1, ihb h.2]
  | scaled a c ih =>
      simp only [Zcash.Circuits.Fixtures.Expr.selectorFree] at h
      simp only [ofFixture, Expr.eval, Zcash.Circuits.Fixtures.Expr.eval, ih h]
  | selector i => simp [Zcash.Circuits.Fixtures.Expr.selectorFree] at h

/-- **A translated projected gate evaluates to the Clean gate expression** under the
selector-replacement valuation, at query families interpreting the projection walk's
layout. The per-gate, per-row step of the transport: a VK gate matched to the left-hand
side and known to vanish forces the Clean expression to `0`. -/
theorem Expr.ofFixture_eraseExpr_substSelectorMap_eval (m : ℕ → Option SelCompress)
    (fE aE iE selE : ℕ → Fp) (v : Query → Fp)
    (hsel : ∀ sel : Selector, selE sel.index = v (.selector sel))
    (p : Expression Fp Query) (s sfin : QueryState)
    (hfree : (eraseExpr (substSelectorMap m p) s).1.selectorFree = true)
    (hext : sfin.Extends (eraseExpr (substSelectorMap m p) s).2)
    (hint : Interprets sfin fE aE iE v) :
    (Expr.ofFixture (eraseExpr (substSelectorMap m p) s).1).eval fE aE iE
      = p.eval (substValuation m v) := by
  rw [Expr.ofFixture_eval fE aE iE selE _ hfree]
  exact Zcash.Circuits.Fixtures.eraseExpr_substSelectorMap_eval m fE aE iE selE v hsel
    p s sfin hext hint

end Zcash.Snark
