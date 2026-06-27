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

* **Hasse bound** (`Fact (HasseBound Vesta.curve)`) — the only remaining curve assumption. The Vesta
  group order is *derived* from it, not assumed (`vestaOrder_of_hasse`): given the Hasse bound,
  CompElliptic's `Pasta.Vesta.card_eq` proves `Nat.card VestaG = scalarFieldOrder`, whence every point
  is annihilated by the group order. Carried as a `Fact`, like the field modulus
  `Fact (Nat.Prime scalarFieldOrder)`; supplied as a hypothesis, never globally, so the development
  stays axiom-free. Mathlib lacks Hasse's theorem, so it is the irreducible gap (see CompElliptic's
  `CurveOrder`).
-/

namespace Zcash.Snark

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder

/-- The verifier group `E_q`, concretely: the points of the Vesta curve `y² = x³ + 5`. -/
abbrev VestaG := SWPoint Vesta.curve

/-- The Vesta group order as a proposition: every Vesta point is `p`-torsion, i.e. the group order
divides `p = scalarFieldOrder`. Derived from the Hasse bound by `vestaOrder_of_hasse` (via
CompElliptic's `Pasta.Vesta.card_eq`), not assumed; carried as a `Fact` so `vestaFpModule` can
consume it, with the supplied `Fact` being `Fact (HasseBound Vesta.curve)`. -/
abbrev VestaOrder : Prop := ∀ P : VestaG, (scalarFieldOrder : ℕ) • P = 0

/-- The Vesta group order, derived from the Hasse bound rather than assumed: given the Hasse bound,
CompElliptic's `Pasta.Vesta.card_eq` gives `Nat.card VestaG = scalarFieldOrder`, and a finite group is
annihilated by its order. -/
theorem vestaOrder_of_hasse (hHasse : HasseBound Vesta.curve) : VestaOrder := by
  intro P
  have hcard : Nat.card VestaG = scalarFieldOrder := Vesta.card_eq hHasse
  rw [← hcard]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard P)

/-- With the Hasse bound in scope, the Vesta order `Fact` — hence the `Fp`-module — is supplied
automatically. Conditional like `vestaFpModule`: it fires only when the Hasse `Fact` is a hypothesis,
never globally, so the development stays axiom-free. -/
instance factVestaOrder_of_hasse [Fact (HasseBound Vesta.curve)] : Fact VestaOrder :=
  ⟨vestaOrder_of_hasse Fact.out⟩

/-- Given the Vesta group order (`Fact VestaOrder`), the curve is an `Fp`-module: `AddCommGroup.zmodModule`
on the `p`-torsion. A conditional instance — it fires only when the order `Fact` is in scope, so it adds
no axiom (the `Fact` is supplied as a hypothesis, never globally). -/
noncomputable instance vestaFpModule [h : Fact VestaOrder] : Module Fp VestaG :=
  AddCommGroup.zmodModule h.out

/-- The conditional soundness composition over the concrete Vesta curve:
`orchard_verifier_sound_conditional` with the abstract `Fp`-module specialised to `SWPoint Vesta.curve`,
the abstract-curve assumption replaced by `Fact (HasseBound Vesta.curve)` (the order follows). It
inherits the conditional status of `orchard_verifier_sound_conditional` (assumed extraction + constraint
identity; `accepts` not tied to the fingerprint); see that docstring. The deployed Vesta capstones are
`orchard_verifier_sound_vesta_opening`/`_constraint` below. -/
theorem orchard_verifier_sound_vesta_conditional [Fact (HasseBound Vesta.curve)]
    (urs : URS VestaG) (hbind : CommitmentBinding (F := Fp) urs)
    {P : VestaG} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance urs P b v circuitSat accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs P b v circuitSat a → S) :
    S :=
  orchard_verifier_sound_conditional urs hbind haccepts hextract hencodes

/-- The deployed Orchard verifier is sound over Vesta, with the IPA opening derived.
`orchard_verifier_sound_deployed_opening` specialised to `SWPoint Vesta.curve`: the bridge `hFS` supplies
only the special-soundness transcript tree (the minimal Fiat–Shamir assumption), and `IpaRelation` is
derived from it (`ipa_soundV`), not assumed. Named assumptions: the rewinding (`hFS`), the circuit side
(`hcirc`), the Hasse bound (`Fact (HasseBound Vesta.curve)`), and VK-correctness (`hencodes`). -/
theorem orchard_verifier_sound_vesta_opening [Fact (HasseBound Vesta.curve)] [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {P : VestaG} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    (haccepts : DeployedAccepts urs hk vk ps ch)
    (hFS : FiatShamirTree urs b P v (DeployedAccepts urs hk vk ps ch))
    (hcirc : ∀ a, IpaRelation urs P b v a → circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs P b v circuitSat a → S) :
    S :=
  orchard_verifier_sound_deployed_opening urs hk vk ps ch haccepts hFS hcirc hencodes

open Polynomial in
/-- The deployed Orchard verifier is sound over Vesta, opening and constraint both derived.
`orchard_verifier_sound_deployed_constraint` specialised to `SWPoint Vesta.curve`: both conjuncts of
`SnarkRelation` are derived — `IpaRelation` via `ipa_soundV`, and `circuitSat` (concrete
`circuitSatViaGates`) from the verifier's gate point-check `hquot` lifted by Schwartz–Zippel (`hgood`).
Named assumptions: the rewinding (`hFS`), the gate check (`hquot`), the SZ good challenge (`hgood`), the
Hasse bound (`Fact (HasseBound Vesta.curve)`), and VK-correctness (`hencodes`). -/
theorem orchard_verifier_sound_vesta_constraint [Fact (HasseBound Vesta.curve)] [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {P : VestaG} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (haccepts : DeployedAccepts urs hk vk ps ch)
    (hFS : FiatShamirTree urs b P v (DeployedAccepts urs hk vk ps ch))
    (hquot : ∀ a, IpaRelation urs P b v a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs P b v a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs P b v
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S :=
  orchard_verifier_sound_deployed_constraint urs hk vk ps ch fixedCols decodeAdvice decodeInstance y gates
    hpoly deg x haccepts hFS hquot hgood hencodes

end Zcash.Snark
