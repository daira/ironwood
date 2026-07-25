/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Vendor.NatKernel
import Zcash.Snark.Keygen.Fast.Projective

/-!
# The `Nat` kernel is the proven projective arithmetic

`Zcash.Vendor.NatKernel` is a zero-import transplant of the projective Vesta arithmetic, so
that it can sit in the `NatKernelNative` `precompileModules` leaf.  This module — which is
mathlib-side and therefore *not* in that lane — proves that the transplant computes the
statement-surface functions of `Zcash.Snark.Keygen.Fast.Projective`.

The bridge is the coordinatewise cast `toPVes : P3 → PVes`, `⟨x, y, z⟩ ↦ (x : 𝔽_q, y, z)`.  It
is a *representation* map, not an isomorphism: many `P3`s denote the same `PVes` (the kernel
keeps canonical representatives, so in fact `toPVes` is injective on canonical triples, but
nothing below needs that).  Each kernel operation is shown to commute with it, exactly as
`padd_eq_paddFast` relates `padd` to its fused raw-`ℕ` spelling.

## Main results

* `toPVes_padd` — the kernel's RCB addition is `PVes.padd`
* `toPVes_pid`, `toPVes_pneg` — identity and negation
* `pnsmul_spec` — the kernel's 256-step ladder is `n • ·` in the affine group, for `n < 2 ^ 256`
-/

namespace Zcash.Vendor.NatKernel

open Zcash.Snark.Keygen.Fast.Projective
open Zcash.Snark.Keygen.Fast.Projective.PVes

/-- The Vesta base field, the ambient field of the projective statement surface. -/
local notation "Fq" => Zcash.Snark.Keygen.Fast.Projective.Fq

/-- The kernel's modulus literal is the Vesta base field order. -/
theorem qv_eq : qv = CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := rfl

theorem qv_pos : 0 < qv := by decide

/-- Coordinatewise interpretation of a kernel triple as a projective point over `𝔽_q`. -/
def toPVes (p : P3) : PVes := ⟨(p.x : Fq), (p.y : Fq), (p.z : Fq)⟩

@[simp] theorem toPVes_X (p : P3) : (toPVes p).X = (p.x : Fq) := rfl
@[simp] theorem toPVes_Y (p : P3) : (toPVes p).Y = (p.y : Fq) := rfl
@[simp] theorem toPVes_Z (p : P3) : (toPVes p).Z = (p.z : Fq) := rfl

/-! ## The field operations -/

theorem cast_fadd (a b : ℕ) : ((fadd a b : ℕ) : Fq) = (a : Fq) + (b : Fq) := by
  rw [fadd, qv_eq, ZMod.natCast_mod, Nat.cast_add]

theorem cast_fmul (a b : ℕ) : ((fmul a b : ℕ) : Fq) = (a : Fq) * (b : Fq) := by
  rw [fmul, qv_eq, ZMod.natCast_mod, Nat.cast_mul]

theorem cast_fsub (a b : ℕ) : ((fsub a b : ℕ) : Fq) = (a : Fq) - (b : Fq) := by
  rw [fsub, qv_eq, ZMod.natCast_mod, Nat.cast_add,
    Nat.cast_sub (Nat.mod_lt _ (qv_eq ▸ qv_pos)).le, ZMod.natCast_mod, ZMod.natCast_self]
  ring

/-! ## The group operations -/

/-- **The kernel's addition is the projective addition.**  Same Renes–Costello–Batina closed
forms, evaluated on canonical representatives with fused mul-mod. -/
theorem toPVes_padd (p q : P3) : toPVes (padd p q) = PVes.padd (toPVes p) (toPVes q) := by
  simp only [padd, PVes.padd, toPVes, PVes.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [cast_fadd, cast_fmul, cast_fsub, Nat.cast_ofNat] <;> ring

set_option linter.unusedSimpArgs false in
@[simp] theorem toPVes_pid : toPVes pid = PVes.pid := by
  simp only [pid, toPVes, PVes.pid, PVes.mk.injEq, Nat.cast_zero, Nat.cast_one]

set_option linter.unusedSimpArgs false in
/-- **The kernel's negation is coordinate negation of `Y`**, the short-Weierstrass inverse. -/
theorem toPVes_pneg (p : P3) :
    toPVes (pneg p) = ⟨(toPVes p).X, -(toPVes p).Y, (toPVes p).Z⟩ := by
  simp only [pneg, toPVes, PVes.mk.injEq, cast_fsub, Nat.cast_zero, zero_sub]

/-! ## The scalar ladder

`pnsmul` is a fixed 256-step LSB-first double-and-add, which is a different schedule from the
statement-surface `pnsmulFast` (`binNsmul`, MSB-first recursion).  The equality is therefore
proved where the group law lives: through `toAffine`, using that `padd` is the affine
addition on valid points (`toAffine_padd`) and preserves validity (`valid_padd`). -/

/-- The ladder state after `i` steps: the accumulator holds `(n mod 2 ^ i) • A` and the base
holds `2 ^ i • A`, both valid. -/
private def LadderInv (A : G) (n i : ℕ) (st : P3 × P3) : Prop :=
  Valid (toPVes st.1) ∧ Valid (toPVes st.2) ∧
    toAffine (toPVes st.1) = (n % 2 ^ i) • A ∧ toAffine (toPVes st.2) = (2 ^ i : ℕ) • A

private theorem ladder_step {A : G} {n i : ℕ} {st : P3 × P3} (h : LadderInv A n i st) :
    LadderInv A n (i + 1)
      ((if (n >>> i) &&& 1 = 1 then padd st.1 st.2 else st.1), padd st.2 st.2) := by
  obtain ⟨hv1, hv2, ha1, ha2⟩ := h
  have hbit : (n >>> i) &&& 1 = n / 2 ^ i % 2 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  have hmod : n % 2 ^ (i + 1) = n % 2 ^ i + 2 ^ i * (n / 2 ^ i % 2) := by
    rw [pow_succ, Nat.mod_mul]
  have hdouble : toAffine (toPVes (padd st.2 st.2)) = (2 ^ (i + 1) : ℕ) • A := by
    rw [toPVes_padd, toAffine_padd hv2 hv2, ha2, ← two_nsmul, smul_smul, pow_succ]
    ring_nf
  refine ⟨?_, ?_, ?_, hdouble⟩
  · split
    · exact toPVes_padd _ _ ▸ valid_padd hv1 hv2
    · exact hv1
  · exact toPVes_padd _ _ ▸ valid_padd hv2 hv2
  · split
    · rename_i hodd
      rw [toPVes_padd, toAffine_padd hv1 hv2, ha1, ha2, ← add_nsmul]
      congr 1
      rw [hbit] at hodd
      rw [hmod, hodd, Nat.mul_one]
    · rename_i heven
      rw [ha1]
      congr 1
      rw [hbit] at heven
      have h0 : n / 2 ^ i % 2 = 0 := by omega
      rw [hmod, h0, Nat.mul_zero, Nat.add_zero]

/-- **The kernel ladder computes `n • ·`** in the affine group, for scalars below `2 ^ 256`
(all Pasta scalars).  Statement shape mirrors `PVes.pnsmulFast_spec`. -/
theorem pnsmul_spec {p : P3} (hp : Valid (toPVes p)) (n : ℕ) (hn : n < 2 ^ 256) :
    Valid (toPVes (pnsmul n p)) ∧
      toAffine (toPVes (pnsmul n p)) = n • toAffine (toPVes p) := by
  set A := toAffine (toPVes p) with hA
  have base : ∀ m : ℕ, m ≤ 256 →
      LadderInv A n m ((List.range m).foldl
        (fun (st : P3 × P3) i =>
          (if (n >>> i) &&& 1 = 1 then padd st.1 st.2 else st.1, padd st.2 st.2))
        (pid, p)) := by
    intro m
    induction m with
    | zero =>
        intro _
        simp only [List.range_zero, List.foldl_nil]
        refine ⟨?_, hp, ?_, ?_⟩
        · rw [toPVes_pid]; exact valid_pid
        · rw [toPVes_pid, toAffine_pid, pow_zero, Nat.mod_one, zero_nsmul]
        · rw [pow_zero, hA, one_nsmul]
    | succ k ih =>
        intro hk
        rw [List.range_succ, List.foldl_append]
        exact ladder_step (ih (by omega))
  obtain ⟨hv, -, hval, -⟩ := base 256 le_rfl
  refine ⟨hv, ?_⟩
  rw [pnsmul, hval, Nat.mod_eq_of_lt hn]

end Zcash.Vendor.NatKernel
