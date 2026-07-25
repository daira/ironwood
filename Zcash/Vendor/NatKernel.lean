/-!
# Core-only Nat kernel for Vesta group arithmetic (precompile probe)

UNPROVEN PROBE MODULE — nothing imports this for statements. It transplants the
proven `paddFast` arithmetic (`Zcash/Snark/Keygen/Fast/Projective.lean`, RCB complete
addition over raw canonical `ℕ` representatives, Vesta `a = 0, b = 5`) into a module
with ZERO imports, so it can sit in a `precompileModules` leaf lib
(`FastFieldNative`-style) without dragging any mathlib closure into native codegen.
Purpose: measure whether lake-precompiled native code is picked up by `native_decide`
callers, and what a natively-compiled MSM costs. Proven equalities come after the
measurement says this lane is real (the `paddFast` cast lemmas are the template).
-/

namespace Zcash.Vendor.NatKernel

/-- The Vesta base-field prime (= `CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD`),
as a literal so this module needs no imports. -/
def qv : Nat := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001

@[inline] def fadd (a b : Nat) : Nat := (a + b) % qv
@[inline] def fmul (a b : Nat) : Nat := (a * b) % qv
@[inline] def fsub (a b : Nat) : Nat := (a + (qv - b % qv)) % qv

/-- Projective Vesta point over canonical `Nat` representatives. -/
structure P3 where
  x : Nat
  y : Nat
  z : Nat

/-- `Array.get!`/`Array.set!` need a default; the projective identity is the right one, so a
bucket that is never hit reads back as `pid` and contributes nothing. -/
instance : Inhabited P3 := ⟨⟨0, 1, 0⟩⟩

/-- Projective identity `(0 : 1 : 0)`. -/
def pid : P3 := ⟨0, 1, 0⟩

/-- RCB complete addition, transplanted verbatim from `paddFast`. -/
def padd (P Q : P3) : P3 :=
  let x1 := P.x; let y1 := P.y; let z1 := P.z
  let x2 := Q.x; let y2 := Q.y; let z2 := Q.z
  let y2sq := fmul y2 y2
  let z2sq := fmul z2 z2
  let x1y1 := fmul x1 y1
  let y1sq := fmul y1 y1
  let z1sq := fmul z1 z1
  let x2y2 := fmul x2 y2
  let y1z1 := fmul y1 z1
  let x1z1 := fmul x1 z1
  let y2z2 := fmul y2 z2
  let x2z2 := fmul x2 z2
  let x1sq := fmul x1 x1
  let x2sq := fmul x2 x2
  let X3 := fsub (fadd (fsub (fsub (fmul x1y1 y2sq) (fmul 15 (fmul x1y1 z2sq)))
                    (fmul 30 (fmul x1z1 y2z2)))
               (fsub (fmul y1sq x2y2) (fmul 15 (fmul z1sq x2y2))))
              (fmul 30 (fmul y1z1 x2z2))
  let Y3 := fsub (fadd (fadd (fmul y1sq y2sq) (fmul 45 (fmul x1sq x2z2)))
                    (fmul 45 (fmul x1z1 x2sq)))
              (fmul 225 (fmul z1sq z2sq))
  let Z3 := fadd (fadd (fadd (fadd (fadd (fmul y1sq y2z2) (fmul y1z1 y2sq))
                    (fmul 3 (fmul x1sq x2y2)))
                    (fmul 3 (fmul x1y1 x2sq)))
                    (fmul 15 (fmul y1z1 z2sq)))
                    (fmul 15 (fmul z1sq y2z2))
  ⟨X3, Y3, Z3⟩

/-- Binary double-and-add over a fixed 256-bit window (Pasta scalars fit). -/
def pnsmul (n : Nat) (p : P3) : P3 :=
  (List.range 256).foldl
    (fun (st : P3 × P3) i =>
      let acc := if (n >>> i) &&& 1 = 1 then padd st.1 st.2 else st.1
      (acc, padd st.2 st.2))
    (pid, p) |>.1

/-- Bucket downsweep: `Σ_{k=1..mask} k • bucket_k` via running suffix sums. -/
def windowValue (mask : Nat) (buckets : Array P3) : P3 :=
  ((List.range mask).foldl
    (fun (st : Nat × P3 × P3) _ =>
      let k := st.1
      let running := padd st.2.1 buckets[k]!
      (k - 1, running, padd st.2.2 running))
    (mask, pid, pid)).2.2

/-- Windowed Pippenger MSM, window `c`: per-window Array-scatter buckets, bucket
downsweep, Horner recombination (most-significant window first, `c` doublings
between windows). -/
def msm (c : Nat) (terms : List (Nat × P3)) : P3 :=
  let numWindows := (256 + c - 1) / c
  let mask := (1 <<< c) - 1
  (List.range numWindows).foldl
    (fun acc wrev =>
      let w := numWindows - 1 - wrev
      let buckets := terms.foldl
        (fun bs t =>
          let d := (t.1 >>> (w * c)) &&& mask
          if d = 0 then bs else bs.set! d (padd bs[d]! t.2))
        (Array.replicate (mask + 1) pid)
      let doubled := (List.range c).foldl (fun a _ => padd a a) acc
      padd doubled (windowValue mask buckets))
    pid

/-! ## Projective negation and the radix-2 DIT FFT

The butterfly `(a, b) ↦ (a + tw·b, a − tw·b)` of `bestFftG`
(`Zcash/Snark/Keygen/Pipeline.lean`), transplanted onto `P3`: the group addition is `padd`,
the scalar action is `pnsmul`, and the subtraction is `padd` against `pneg`.  Twiddles arrive
as canonical `Nat` scalars (`Fp.val`), computed by the caller, so this module still needs no
imports. -/

/-- Projective negation: `-(x : y : z) = (x : −y : z)` on a short-Weierstrass curve. -/
@[inline] def pneg (p : P3) : P3 := ⟨p.x, fsub 0 p.y, p.z⟩

/-- Bit-reversal permutation index, transplanted from `Zcash.Snark.Keygen.bitreverse`. -/
def bitreverse (n l : Nat) : Nat := Id.run do
  let mut r := 0
  let mut m := n
  for _ in [0:l] do
    r := (r <<< 1) ||| (m &&& 1)
    m := m >>> 1
  return r

/-- In-place radix-2 DIT FFT over `P3`, mirroring `bestFftG`: bit-reversal permutation, then
`logN` rounds of decimation-in-time butterflies against the precomputed twiddle scalars `tw`
(`tw[i] = (omega ^ i).val`, `i < n / 2`). -/
def fft (a0 : Array P3) (tw : Array Nat) (logN : Nat) : Array P3 := Id.run do
  let n := a0.size
  let mut a := a0
  -- bit-reversal permutation
  for k in [0:n] do
    let rk := bitreverse k logN
    if k < rk then
      let ak := a[k]!
      let ark := a[rk]!
      a := (a.set! k ark).set! rk ak
  -- `logN` rounds of butterflies
  let mut half := 1
  for _ in [0:logN] do
    let chunk := 2 * half
    let twiddleChunk := n / chunk
    for c in [0:n / chunk] do
      let s := c * chunk
      for j in [0:half] do
        let twdl := tw[j * twiddleChunk]!
        let aIdx := s + j
        let bIdx := s + half + j
        let aOld := a[aIdx]!
        let t := pnsmul twdl a[bIdx]!
        a := a.set! aIdx (padd aOld t)
        a := a.set! bIdx (padd aOld (pneg t))
    half := chunk
  return a

end Zcash.Vendor.NatKernel
