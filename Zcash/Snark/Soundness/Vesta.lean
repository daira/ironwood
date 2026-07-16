import Mathlib
import Zcash.Snark.Soundness.Main
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder

/-!
# Vesta instantiation: the verifier group at the deployed curve

The soundness theorems of `Zcash.Snark.Soundness.Main` are proven for an abstract
`Fp`-module `G`. Here `G` is pinned to the actual Vesta curve `SWPoint Vesta.curve` (`y² = x³ + 5`),
whose group law CompElliptic/mathlib have already proven (associativity transported from
`WeierstrassCurve.Affine.Point`). The deployed Orchard verifier runs over Vesta, so these theorems are
the concrete-curve forms of the abstract capstones.

## The setting

The only structure the `Fp`-action needs that the curve does not already carry is the Vesta group
order: every point is `p`-torsion (`p = scalarFieldOrder`). Given that, `AddCommGroup.zmodModule`
turns the curve into an `Fp`-module and the end-to-end theorems apply verbatim.

## Assumptions

* **The Vesta group order — no assumption.** CompElliptic's `Pasta.Vesta.card_eq` proves
  `Nat.card VestaG = scalarFieldOrder` (an elementary point-count bound stands in for Hasse, which
  Mathlib lacks — see CompElliptic's `CurveOrder`), whence every point is annihilated by the group
  order (`vestaOrder`).
-/

namespace Zcash.Snark

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder

/-- The verifier group `E_q`, concretely: the points of the Vesta curve `y² = x³ + 5`. -/
abbrev VestaG := SWPoint Vesta.curve

/-- The Vesta group order as a proposition: every Vesta point is `p`-torsion, i.e. the group order
divides `p = scalarFieldOrder`. Proven unconditionally (`vestaOrder`); carried as a `Fact` so
`vestaFpModule` can consume it. -/
abbrev VestaOrder : Prop := ∀ P : VestaG, (scalarFieldOrder : ℕ) • P = 0

/-- The Vesta group order, unconditionally: CompElliptic's `Pasta.Vesta.card_eq` gives
`Nat.card VestaG = scalarFieldOrder` with no assumption, and a finite group is annihilated by its
order. -/
theorem vestaOrder : VestaOrder := by
  intro P
  have hcard : Nat.card VestaG = scalarFieldOrder := Vesta.card_eq
  rw [← hcard]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard P)

/-- The Vesta order `Fact` — hence the `Fp`-module — is supplied unconditionally, from `vestaOrder`
(CompElliptic pins the order with no assumption). -/
instance : Fact VestaOrder := ⟨vestaOrder⟩

/-- Given the Vesta group order (`Fact VestaOrder`), the curve is an `Fp`-module
(`AddCommGroup.zmodModule` on the `p`-torsion). Conditional — it fires only when the order `Fact`
is in scope (now unconditionally, via `vestaOrder`). Computable (curve addition and the
`ZMod`-action both are), so the break reductions stay plain `def`s at the concrete curve. -/
instance vestaFpModule [h : Fact VestaOrder] : Module Fp VestaG :=
  AddCommGroup.zmodModule h.out

/-- **Conditional soundness at Vesta.** `orchard_verifier_sound_conditional` specialised to
`SWPoint Vesta.curve`; the Vesta group order (hence the `Fp`-module structure) is pinned
unconditionally. Inherits the conditional status — see that docstring.
The deployed Vesta capstones are `orchard_verifier_vesta_opening_of_forked`/`_constraint_of_forked`
below, with `NontrivialRelation.ofUnopenedForkVesta` the computed break. -/
theorem orchard_verifier_sound_vesta_conditional
    (urs : URS VestaG)
    {P : VestaG} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance urs P b v circuitSat accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs P b v circuitSat a → S) :
    S :=
  orchard_verifier_sound_conditional urs haccepts hextract hencodes

/-- **The deployed binding reduction over Vesta, as a computed relation.**
`NontrivialRelation.ofUnopenedFork` specialised to `SWPoint Vesta.curve`: a forked transcript
whose projection is not cleanly accepted computes a nontrivial discrete-log relation among the
Vesta generators `(g, U, W)`, which DLR hardness forbids (the contrapositive reading — see
`The reduction form` in `Soundness.Main`). -/
def NontrivialRelation.ofUnopenedForkVesta [DecidableEq VestaG]
    [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} (hz : z ≠ 0)
    (fs : ForkedTranscript urs hk vk ps ch b z blind)
    (hne : ¬ IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk ps ch)
      (projTree fs.tree)) :
    NontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  NontrivialRelation.ofUnopenedFork urs hk vk ps ch hz fs hne

/-- **Deployed opening over Vesta, given a clean fork.**
`orchard_verifier_deployed_opening_of_forked` specialised to `SWPoint Vesta.curve`: same
hypotheses as the abstract theorem (the Vesta order is unconditional). The opening witness `a` and
`IpaRelation` certificate `hrel` are supplied by the caller (derived from the clean accept via
`ipaRelation_of_acceptV`). -/
theorem orchard_verifier_vesta_opening_of_forked [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (a : Fin (2 ^ urs.k) → Fp) {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    (fs : ForkedTranscript urs hk vk ps ch b z blind)
    (hrel : IpaRelation urs fs.openedCommitment b (multiopenValue vk ps ch) a)
    (hcirc : circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs fs.openedCommitment b
      (multiopenValue vk ps ch) circuitSat a → S) :
    S :=
  orchard_verifier_deployed_opening_of_forked urs hk vk ps ch a fs hrel hcirc hencodes

open Polynomial in
/-- **Deployed opening and constraint over Vesta, given a clean fork.**
`orchard_verifier_deployed_constraint_of_forked` specialised to `SWPoint Vesta.curve`: the opening
for the declared `fs.openedCommitment` and the pinned `multiopenValue`, and `circuitSat` (concrete
`circuitSatViaGates`) from the verifier's gate point-check `hquot` at the challenge `x`, lifted
to the polynomial identity by Schwartz–Zippel (`hgood`). The `hquot`/`hgood` checks now constrain
the single extracted witness `a`. Same hypotheses as the abstract theorem (the Vesta order is
unconditional). -/
theorem orchard_verifier_vesta_constraint_of_forked [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (a : Fin (2 ^ urs.k) → Fp)
    (fs : ForkedTranscript urs hk vk ps ch b z blind)
    (hrel : IpaRelation urs fs.openedCommitment b (multiopenValue vk ps ch) a)
    (hquot : quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs fs.openedCommitment b (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S :=
  orchard_verifier_deployed_constraint_of_forked urs hk vk ps ch fixedCols decodeAdvice
    decodeInstance y gates hpoly deg x a fs hrel hquot hgood hencodes

end Zcash.Snark
