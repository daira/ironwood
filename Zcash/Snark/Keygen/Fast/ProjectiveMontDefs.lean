/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Vendor.Montgomery.Native64x8Defs

/-!
# Vesta projective point arithmetic over Montgomery limbs: runtime definitions (core-only)

The Renes–Costello–Batina complete addition formulas of
`Zcash.Snark.Keygen.Fast.Projective`, transcribed operation-for-operation onto the eight-limb
Montgomery representation of the Vesta base field.  The expression trees mirror the `𝔽_q`
source exactly, so the equivalence proof in `Zcash.Snark.Keygen.Fast.ProjectiveMont` is a
per-coordinate push of the ring isomorphism.

Like `Zcash.Vendor.Montgomery.Native64x8Defs`, this module is core-only: it is part of the
`FastFieldNative` precompiled lane.  All proofs live in the sibling module.
-/

namespace Zcash.Snark.Keygen.Fast.ProjectiveMont

open Montgomery.Native64x8 (Limbs8)
open Montgomery.Native64x8.VestaFq

/-- A projective point in `(X : Y : Z)` coordinates, each coordinate an eight-limb Montgomery
residue of the Vesta base field. -/
structure PM where
  /-- The `X` coordinate. -/
  X : Limbs8
  /-- The `Y` coordinate. -/
  Y : Limbs8
  /-- The `Z` coordinate. -/
  Z : Limbs8
deriving DecidableEq, Inhabited

namespace PM

/-- The Montgomery residue of `3`. -/
def c3 : Limbs8 := ofNat 3
/-- The Montgomery residue of `15` (`b3 = 3b` for Vesta). -/
def c15 : Limbs8 := ofNat 15
/-- The Montgomery residue of `30`. -/
def c30 : Limbs8 := ofNat 30
/-- The Montgomery residue of `45`. -/
def c45 : Limbs8 := ofNat 45
/-- The Montgomery residue of `225`. -/
def c225 : Limbs8 := ofNat 225

/-- Renes–Costello–Batina complete addition (`add-2015-rcb`, `a = 0`, `b3 = 15`), on
Montgomery limbs. -/
@[inline] def padd (P Q : PM) : PM where
  X :=
    sub (sub (add (sub (sub (mul (mul (P.X) (P.Y)) (square (Q.Y))) (mul (mul (mul (c15) (P.X))
      (P.Y)) (square (Q.Z)))) (mul (mul (mul (mul (c30) (P.X)) (P.Z)) (Q.Y)) (Q.Z))) (mul (mul
      (square (P.Y)) (Q.X)) (Q.Y))) (mul (mul (mul (c15) (square (P.Z))) (Q.X)) (Q.Y))) (mul
      (mul (mul (mul (c30) (P.Y)) (P.Z)) (Q.X)) (Q.Z))
  Y :=
    sub (add (add (mul (square (P.Y)) (square (Q.Y))) (mul (mul (mul (c45) (square (P.X)))
      (Q.X)) (Q.Z))) (mul (mul (mul (c45) (P.X)) (P.Z)) (square (Q.X)))) (mul (mul (c225)
      (square (P.Z))) (square (Q.Z)))
  Z :=
    add (add (add (add (add (mul (mul (square (P.Y)) (Q.Y)) (Q.Z)) (mul (mul (P.Y) (P.Z))
      (square (Q.Y)))) (mul (mul (mul (c3) (square (P.X))) (Q.X)) (Q.Y))) (mul (mul (mul (c3)
      (P.X)) (P.Y)) (square (Q.X)))) (mul (mul (mul (c15) (P.Y)) (P.Z)) (square (Q.Z)))) (mul
      (mul (mul (c15) (square (P.Z))) (Q.Y)) (Q.Z))

/-- The projective identity `𝒪 = (0 : 1 : 0)`. -/
def pid : PM := ⟨zero, one, zero⟩

/-- Binary scalar multiplication, the same recursion as `CompElliptic.binNsmul` specialized to
`padd`/`pid`; kept here so that this module stays core-only. -/
def binNsmul (n : Nat) (P : PM) : PM :=
  if h : n = 0 then pid
  else
    let q := binNsmul (n / 2) P
    let d := padd q q
    if n % 2 = 1 then padd d P else d
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- Projective scalar multiplication `n • P`, the Montgomery twin of
`Zcash.Snark.Keygen.Fast.Projective.PVes.pnsmulFast`. -/
def pnsmulFast (n : Nat) (P : PM) : PM := binNsmul n P

end PM

end Zcash.Snark.Keygen.Fast.ProjectiveMont
