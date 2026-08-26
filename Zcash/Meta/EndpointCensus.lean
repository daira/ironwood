import Lean.Elab.Command

/-!
# Environment-level endpoint-census completeness

`scripts/check_endpoint_census.sh` discovers endpoints by scanning source text, so its reach ends
at surface syntax: a declaration produced by a custom command, an unrecognized modifier, multiline
declaration syntax, or declaration-emitting metaprogramming never matches its line parser.  This
module enforces the same rule against the elaborated environment, where every declaration exists
uniformly however it was written.

Three pieces:

* `censusPinExt` — `assert_axioms` / `assert_computable` record each name they successfully pin,
  and the record persists into the census modules' compiled output;
* `isEndpointBaseName` — the endpoint naming predicate, the Lean port of the script's
  `ENDPOINT_RE`.  Keep the two in sync;
* `assert_endpoint_census` — fails the build if some endpoint-named, project-owned declaration
  in the current environment has no recorded pin.

The command is complete only where the import closure contains every census file;
`Zcash/CensusCheck.lean` (the `CensusCheck` target) is that module.  The source scan keeps the
wider scope — it sees files no census imports — so the two checks are complements, not
replacements.

The pin record shares the declaration-range limitation: metaprogramming under `run_cmd` could
invoke `recordCensusPin` directly, so the standing review rule for declaration-emitting
metaprograms applies here too — this check guards accidental drift, not a deceptive author.
-/

namespace Zcash.Meta

open Lean Elab Command

/-- Every name a census entry has pinned, recorded by the elaborated
`assert_axioms` / `assert_computable` commands themselves. -/
initialize censusPinExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun nss =>
      nss.foldl (init := {}) fun s ns => ns.foldl (fun s n => s.insert n) s
  }

/-- Record a name whose census entry elaborated successfully. -/
def recordCensusPin (name : Name) : CommandElabM Unit :=
  modifyEnv fun env => censusPinExt.addEntry env name

/-- The semantic endpoint suffixes of `ENDPOINT_RE`, each also matched with one of the
`endpointTrailers`. -/
def endpointSuffixes : List String :=
  ["_error_bound", "_finite_security", "_measure_le", "_probability_bound", "_prob_le",
    "_capstone"]

/-- The qualifier trailers an endpoint suffix may carry: the consensus-generic forms take
the bundle size as a parameter (`_for`), `_experiment` marks a bound placed in the
challenge-oracle experiment, `_idealizedks` marks a capstone that names the
knowledge-soundness idealization, and the last two compose. -/
def endpointTrailers : List String :=
  ["", "_for", "_experiment", "_idealizedks", "_experiment_idealizedks"]

/-- Whether `pat` occurs anywhere in `s`. -/
def containsSubstring (s pat : String) : Bool :=
  (s.splitOn pat).length > 1

/-- The endpoint naming convention, applied to a declaration's base name: the Lean port of
`ENDPOINT_RE` in `scripts/check_endpoint_census.sh`.  Keep the two in sync. -/
def isEndpointBaseName (s : String) : Bool :=
  s.startsWith "orchard_verifier_" || s.startsWith "orchard_action_" ||
    s.startsWith "orchard_deployed_" ||
  s.startsWith "competing_" ||
  s.startsWith "nonInteractiveFingerprint_matches_derived" ||
  containsSubstring s "bundleStatement_or_relation" ||
  containsSubstring s "workFactor" ||
  containsSubstring s "fingerprint_matches_positional" ||
  endpointSuffixes.any fun suf => endpointTrailers.any fun tr => s.endsWith (suf ++ tr)

/-- Every elaborated constant kind can carry an endpoint-shaped declaration.  Keeping this match
exhaustive makes a new Lean declaration kind fail closed until it is classified, while inductive
types, structures/classes, their constructors and recursors, axioms, and opaque declarations cannot
bypass the census merely because their environment representation differs from an ordinary
definition or theorem. -/
def isCensusKind : ConstantInfo → Bool
  | .thmInfo _ => true
  | .defnInfo _ => true
  | .axiomInfo _ => true
  | .opaqueInfo _ => true
  | .quotInfo _ => true
  | .inductInfo _ => true
  | .ctorInfo _ => true
  | .recInfo _ => true

/-- The module that declared `n` — the module currently elaborating when `n` is local. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => env.mainModule

/-- Endpoint-named, project-owned declarations of the current environment with no recorded
census pin.  Internal and private names are skipped (a private helper is not a deliverable
endpoint), as is `Zcash.Meta.Tests` unless `excludeTests := false` — that library holds forged
declarations exercising the census machinery's rejection paths, this module's own included. -/
def unpinnedEndpoints (env : Environment) (excludeTests : Bool := true) : Array Name := Id.run do
  let pins := censusPinExt.getState env
  let mut bad : Array Name := #[]
  for (n, info) in env.constants.toList do
    unless isCensusKind info do continue
    if n.isInternal then continue
    let some base := (match n with | .str _ s => some s | _ => none) | continue
    unless isEndpointBaseName base do continue
    let mod := moduleOf env n
    unless mod.getRoot == `Zcash do continue
    if excludeTests && (`Zcash.Meta.Tests).isPrefixOf mod then continue
    unless pins.contains n do bad := bad.push n
  return bad.qsort Name.lt

/--
`assert_endpoint_census` fails the build unless every endpoint-named declaration in the current
environment is directly pinned by an elaborated `assert_axioms`/`assert_computable` entry.

Discovery reads the elaborated environment, not source text, so a declaration reaches this check
however it was written.  Run it only where the imports include every census file — an endpoint
pinned in a census file outside the closure would be reported as a false violation.
-/
elab "assert_endpoint_census" : command => do
  let bad := unpinnedEndpoints (← getEnv)
  unless bad.isEmpty do
    throwError "endpoint declaration(s) with no direct assert_axioms/assert_computable census \
      entry in the elaborated import closure: {bad.toList}"

end Zcash.Meta
