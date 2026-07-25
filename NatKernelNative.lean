/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Vendor.NatKernel

/-!
# The precompiled `Nat`-kernel lane

Root module of the `NatKernelNative` library. It exists for a Lake/Lean naming constraint:
Lean's dynlib loader derives the initializer symbol it looks for from the shared-library file
name (`libZcash_NatKernelNative.so` ⇒ `initialize_Zcash_NatKernelNative`), so a
`precompileModules` library must contain a module whose name matches the library, otherwise
every module that imports the lane fails to build with
`error loading plugin, initializer not found`.

Its import closure stays core-only: `Zcash.Vendor.NatKernel` imports nothing.
-/
