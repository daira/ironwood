# Clean-to-Ironwood integration boundary

This directory is the designated implementation boundary between Clean formal
circuits and ironwood's verifier and soundness development.

Modules here may import and reason about both vocabularies. Their job is to translate
a closed `TopLevelCircuit` and its circuit-derived keygen data into ironwood-native
interfaces:

* an ironwood `VerifyingKey` and pinned constraint view;
* reconstruction of Clean operation satisfaction from ironwood polynomial
  satisfaction;
* semantic projection of configured lookup tuples into the verifier's
  query-index expression language;
* a final circuit statement expressed without exposing Clean implementation details
  to verifier or soundness callers.

This directory is not a home for generally useful code merely because that code was
written during circuit integration:

* pure verifier algebra, decoded constraint models, permutation/lookup semantics, and
  challenge arguments remain under `Zcash/Snark/`;
* pure circuit definitions and semantics remain under `Zcash/Circuits/`, and reusable
  Halo2 compiler facts should migrate upstream to Clean;
* only code that genuinely translates between the two sides belongs here.

The normative architecture rule and current migration guidance are in
[`clean-boundary.md`](clean-boundary.md).

The lookup bridge is split deliberately:

* `LookupProjection.lean` proves the query-erasure and selector-substitution
  compiler semantics for configured lookups;
* `TopLevelLookups.lean` routes synthesis-enabled lookups through the
  circuit-derived verifying key, derives selector coverage, table freedom, tuple
  arity, and activation-row fit from Clean's top-level keygen invariants, reduces
  the remaining projection boundary to exact packed-selector values, and constructs
  the deployed witnesses consumed by the generic full-circuit bridge.
