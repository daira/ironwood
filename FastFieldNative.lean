/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Vendor.Montgomery.Native64x8Defs
import Zcash.Vendor.ProjectiveMontDefs
import Zcash.Vendor.ScalarFftDefs

/-!
# The precompiled native lane

Root module of the `FastFieldNative` library: the only `precompileModules` target in this
repository.  It exists so that the shared library Lake emits
(`.lake/build/lib/libZcash_FastFieldNative.so`) carries an initializer whose name matches the
library — Lean's dynlib loader derives the expected `initialize_…` symbol from the file name.

Its import closure is core-only by construction: the field definitions
(`Zcash.Vendor.Montgomery.Native64x8Defs`), the Vesta point definitions
(`Zcash.Vendor.ProjectiveMontDefs`) and the scalar FFT (`Zcash.Vendor.ScalarFftDefs`)
import nothing beyond Lean core, so native compilation stays at four modules instead of a
mathlib closure.
-/
