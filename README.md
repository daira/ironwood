# Formalizing Ironwood

$\textsf{Ironwood}$ is a project to deploy a new shielded pool, built to restore
confidence for all Zcash'rs in the supply integrity of Zcash.

A formal verification is in progress, which is intended to cover at least soundness
of the Action circuit used by the *Orchard* and *Ironwood pools*, before the NU6.3
upgrade that activates the latter. An important part of this effort will be to clearly
and accurately document the scope of what is and is not formally verified.

## Verifying the proofs

The formalization is a Lean 4 development over Mathlib, and building it
re-elaborates every proof — a successful build *is* the verification. The single
command is `lake build --wfail`, with two one-time prerequisites: install
[`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager, which
reads [`lean-toolchain`](lean-toolchain) and installs the pinned toolchain
automatically), then, from the repository root, fetch Mathlib's prebuilt
artifacts so it need not be recompiled from source:

```sh
lake exe cache get   # one-time: download prebuilt Mathlib artifacts
lake build --wfail   # verify every proof; --wfail makes warnings fail, as CI does
```

CI runs the same build plus source-level consistency checks — census coverage,
fixture digests, and regeneration diffs — documented in
[Build and CI Checks](https://zcash.github.io/ironwood/formal-verification/ci-checks.html).

## Documentation

- <a href="https://zcash.github.io/ironwood/" class="raleway">The Ironwood Book</a>

## License

Copyright 2026 Zcash Protocol Developers.

All code in this workspace is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
