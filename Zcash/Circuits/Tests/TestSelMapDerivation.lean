import Zcash.Circuits.Fixtures.CompressSelectors
import Zcash.Circuits.Tests.TestVkLayoutAction
import Zcash.Circuits.Tests.TestVkMatchAction

/-!
# Derivation test: the computed selector-compression map is the Rust dump

Runs `deriveSelCompressMap` on the ported Action `configure` output and the real
synthesized activations (`Layout.activations` over the keygen-view operation stream, at
the layout fixture's placements) and checks the result equal to the Rust-dumped
`actionSelMap`. This certifies the `compress_selectors` port end to end; the dumped map
remains in use as the derivation's cross-checked reference until the placement input is
computed circuit-side as well.
-/

namespace Zcash.Circuits.Fixtures.Test.SelMapDerivation

open Halo2 Fixtures Fixtures.Layout
open LayoutAction (aProgram)
open MatchAction (actionCS)

#eval show IO Unit from do
  let fx ← Json.loadLayoutFixture "Zcash/Circuits/Fixtures/actionLayout.json"
    0x51cd2f7ce66a8c7
  let ops : Operations Fp := aProgram.operations
  let regions : List (ℕ × RegionOperations Fp) := (indexedRegions ops 0).1
  let starts : List ℕ := (fx.regions.filter (·.name ≠ "generator_table")).map (·.start)
  let acts : List (ℕ × ℕ) := activations starts regions
  Json.runChecks [
    ("derived selector-compression map = Rust dump",
      deriveSelCompressMap actionCS fx.n acts == actionSelMap)]

end Zcash.Circuits.Fixtures.Test.SelMapDerivation
