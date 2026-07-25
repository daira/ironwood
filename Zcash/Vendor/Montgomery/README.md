# Vendored eight-limb Montgomery field (temporary)

This directory is a **temporary vendoring** of the CompPoly branch `fast_multilimb_fields`
(commit `28c8931`, https://github.com/…/CompPoly), which adds eight-limb (8 × 32-bit in
`UInt64`) Montgomery arithmetic for 255-bit prime moduli next to the existing single-word
`Montgomery/Native32*`.

**Delete this directory** when that branch lands upstream and ironwood's CompPoly pin moves
past it; the only changes needed then are the import paths (`Zcash.Vendor.Montgomery.X` →
`CompPoly.Fields.Montgomery.X`) and dropping `Pasta.lean` (see below).

| File | Upstream original | Change |
|---|---|---|
| `Basic.lean` | `CompPoly/Fields/Montgomery/Basic.lean` | none |
| `Native64x8Defs.lean` | `CompPoly/Fields/Montgomery/Native64x8.lean` (definitions) | split out, `ℕ` → `Nat`, plus the Pasta constants and monomorphic entry points |
| `Native64x8.lean` | `CompPoly/Fields/Montgomery/Native64x8.lean` (theorems) | imports the split-out definitions; two `norm_num` calls dropped (Lean 4.30 vs 4.31 `simp` drift) |
| `Native64x8Mul.lean` | same name | import path; one `norm_num` dropped |
| `Native64x8Field.lean` | same name | import path |
| `Pasta.lean` | `CompPoly/Fields/Pasta/{Basic,Fast}.lean` | **rewritten**: reuses `CompElliptic.Fields.Pasta`'s primes and Pratt certificates instead of vendoring a second copy, so the repo keeps exactly one `Field (ZMod PALLAS_SCALAR_CARD)` instance and the Montgomery carrier bridges directly into `Zcash.Snark.Keygen.Fast.Projective.Fq` |

The definition/proof split exists for the precompiled lane: `Native64x8Defs.lean` imports
nothing beyond Lean core, so it can be native-compiled (`FastFieldNative`) without dragging a
mathlib import closure through codegen. Keep it that way — the OOM note in
`/root/bin/lake-capped` is why.

Namespaces are unchanged from upstream (`Montgomery.Native64x8`); the pinned CompPoly predates
the `Montgomery` directory, so nothing clashes.
