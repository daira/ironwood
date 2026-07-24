# Fixture provenance

The files in this directory are the empirical binding between the Lean circuit model
(`Zcash/Circuits/Action/Circuit.lean` and the isolated Add/Mul chains) and the actual
Rust halo2 circuit. They were dumped from instrumented Rust checkouts, **not** written
by hand, and are consumed by the `CircuitVkCheck` build target
(`Zcash/Circuits/Tests/TestVk*`). This file records where each artifact came from, how
it is pinned, and what is — and is not — currently reproducible.

## Generator tooling

Two custom dump entry points, living in **sibling checkouts** of the Rust repositories
(not in this repository):

| Tool | Location (in the instrumented checkout) | Produces |
|---|---|---|
| `dump_lean` | `halo2_proofs::plonk::dump_lean` (github.com/zcash/halo2, halo2_proofs 0.3.2 era) | `CsFixture` / `LayoutFixture` dumps: `AddPre/AddPost/MulPre/MulPost.lean`, `AddLayout/MulLayout.lean`, `action{Pre,Post}.json`, `action{,Base}Layout.json` |
| `layout_dump` | `halo2_gadgets/src/ecc/chip/layout_dump.rs` (`dump_layout_add`, `dump_layout_mul`) and `dump_layout_action` (orchard checkout) | the `*SelMap.lean` selector-compression maps |

Example regeneration command (Add chain, from the instrumented halo2 checkout):

```
cargo test --release -p halo2_gadgets --lib ecc::chip::layout_dump::dump_layout_add -- --nocapture
```

The isolated Mul chain uses `MulDumpCircuit` (`halo2_gadgets/src/ecc/chip/dump.rs`):
one real variable-base scalar mul, `Value::unknown()` witnesses, `k = 11`, run through
the `SimpleFloorPlanner` exactly as `keygen_vk` does.

## Source versions

| Fact | Status |
|---|---|
| halo2_proofs version | 0.3.2 (github.com/zcash/halo2) — recorded in `Layout.lean` |
| Base (pre-NU 6.3) circuit | orchard 0.14.0 — the `actionBase` dump is byte-identical to the 0.14.0 circuit, verified on the ironwood branch (`TestVkLayoutActionBase.lean`) |
| Post (NU 6.3 / ironwood) circuit | the orchard ironwood branch (`Circuit::synthesize` with `synthesize_cross_address_checks`) |
| Instrumented halo2 / orchard commit hashes | **UNKNOWN — not recorded at generation time.** The dump forks have not been published; regeneration is currently not reproducible from pinned sources. |

Closing that last row is the outstanding provenance task: publish the instrumented
halo2/orchard branches (or fold `dump_lean`/`layout_dump` behind a feature flag
upstream), record the exact commit hashes here, and add a CI job that regenerates the
JSON fixtures from those pins and diffs them against the checked-in bytes — the
circuit-side analogue of what `.github/workflows/fixtures.yml` already does for the
`Zcash/Snark/Fixtures/` verifier fingerprint captures (which use a separate pipeline:
orchard 0.15.1 / halo2 0.3.3, `orchard-fingerprint-instances`).

## Content pinning

Every JSON fixture is pinned by an FNV-1a-64 content hash **in the consuming test
source** (`Fixtures/Json.lean` `loadJsonChecked`): a byte change fails the build until
the pinned literal is updated, so the committed Lean source always pins the exact
fixture content. Current artifacts:

| File | FNV-1a-64 | Bytes | Pinned in |
|---|---|---|---|
| `actionPre.json` | `0x31656840fdb3156d` | 33,120 | `TestVkMatchAction.lean` |
| `actionPost.json` | `0xdb884f3c3174a41b` | 67,143 | `TestVkMatchAction.lean` |
| `actionLayout.json` | `0x051cd2f7ce66a8c7` | 943,608 | `TestVkLayoutAction.lean` |
| `actionBaseLayout.json` | `0x193f3922aa59191e` | 941,568 | `TestVkLayoutActionBase.lean` |

The Add/Mul fixtures and the SelMaps are small enough to live as Lean literals; they
are pinned by being source files (any edit is a reviewable diff), and their headers
carry the generating tool.

**What the hash does and does not guarantee.** The pin guarantees the bytes have not
drifted since the hash was recorded; it does **not** by itself certify the bytes were
produced from the claimed circuit. That certification is currently the one-time
generation event plus the `CircuitVkCheck` equality checks (the projected Lean CS must
equal the dump — a divergence in either side surfaces as a build failure); it becomes
reproducible once the generator pins above are recorded.
