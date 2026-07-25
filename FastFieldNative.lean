/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Vendor.Montgomery.Native64x8Defs
import Zcash.Snark.Keygen.Fast.ProjectiveMontDefs

/-!
# The precompiled native lane

Root module of the `FastFieldNative` library: the only `precompileModules` target in this
repository.  It exists so that the shared library Lake emits
(`.lake/build/lib/libZcash_FastFieldNative.so`) carries an initializer whose name matches the
library — Lean's dynlib loader derives the expected `initialize_…` symbol from the file name.

Its import closure is core-only by construction: the field definitions
(`Zcash.Vendor.Montgomery.Native64x8Defs`) and the Vesta point definitions
(`Zcash.Snark.Keygen.Fast.ProjectiveMontDefs`) import nothing beyond Lean core, so native
compilation stays at three modules instead of a mathlib closure.
-/
