import Zcash.Circuits.Fixtures.Project
import Zcash.Circuits.Fixtures.ActionSelMap
import Zcash.Circuits.Fixtures.Json
import Zcash.Circuits.Specs.SinsemillaGenerators
import Zcash.Circuits.Action.Circuit

/-!
# VK-match test: the full Orchard Action circuit `configure`

Projects the `ConstraintSystem` produced by the ported `Action.Circuit.configure` to the
ironwood `CsFixture` shape and checks it EQUAL to the fixtures dumped from the actual
Rust circuit — both pre-compression (`actionPre.json`) and, via the Rust-dumped selector
map applied mechanically, post-`compress_selectors` (`actionPost.json`). `configure` is
version-independent (post-NU 6.2 and 6.3 share the CS), so this single test covers both
top-level circuits.

The fixtures are JSON data files loaded by name at `#eval` time (see `Fixtures/Json.lean`
for the codec, the SHA-256 pinning scheme, and why the data is not a Lean term); a
mismatch or failed load is a build failure, exactly like the former `#guard`s.
-/

namespace Zcash.Circuits.Fixtures.Test.MatchAction

open Halo2
open Fixtures.Json

def actionCS : ConstraintSystem Fp :=
  (Action.Circuit.configure Specs.Sinsemilla.orchardGenerators {}).2

/-- Registration-order query seed from a dumped fixture's query layouts. -/
def seedOf (f : CsFixture) : List Query :=
  f.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ f.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)
    ++ f.instanceQueryLayout.map (fun (c, r) => Query.instance ⟨c⟩ r)

#eval show IO Unit from do
  let actionPre ← loadCsFixture "actionPre.json"
  let actionPost ← loadCsFixture "actionPost.json"
  runChecks [
    -- Pre-compression: projected CS equals the dumped fixture.
    ("actionPre: projected CS = dump", projectCS (seedOf actionPre) actionCS == actionPre),
    -- Post-compression: the Rust-dumped selector map, applied mechanically, yields
    -- exactly the dumped post-compression CS.
    ("actionPost: projected CS = dump",
      projectCSPostMap (seedOf actionPost) actionSelMap actionCS == actionPost)]

end Zcash.Circuits.Fixtures.Test.MatchAction
