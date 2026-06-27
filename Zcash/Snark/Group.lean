import Mathlib

/-!
# The verifier group `E_q` and the uniform reference string

The halo2 verifier operates over the Vesta curve `E_q` (`vesta::Affine`): every commitment in the
proof, every reference-string generator, and the final multiscalar-multiplication (MSM) check live in
this group. We model the group abstractly as an `F`-module `G` — the only structure the verifier's MSM
uses is the `F`-linear combination of group elements (`F = F_p`, the scalar field). The argument uses
only this abstract module structure and never reaches into the concrete curve arithmetic; where `G` is
instantiated at the concrete curve (below), the group law is CompElliptic's proven `AddCommGroup`, not an
assumption.

We keep `G` abstract in the fingerprint argument rather than instantiating it at CompElliptic's
concrete Vesta curve (`SWPoint Vesta.curve`) on purpose: the MSM needs only the `F`-linear (module)
structure, which the abstract `F`-module already supplies, so the argument stays curve-agnostic. The
concrete instantiation is available too, conditioned on the Hasse bound: CompElliptic's curve is an
`AddCommGroup`, and given `Fact (HasseBound Vesta.curve)` its order is `p` (`Pasta.Vesta.card_eq`),
which makes it a `Module (ZMod p)` (`Zcash.Snark.vestaFpModule`). The Vesta capstones in
`Zcash.Snark.Vesta` instantiate `G` there with no change to this argument.
-/

namespace Zcash.Snark

/-- The uniform reference string, mirroring halo2 `Params` (`poly/commitment.rs`): `k` is the
`log₂` of the domain size, `g` the `n = 2 ^ k` generators `g₀, …, g_{n-1}`, `w` the blinding
generator, and `u` the inner-product-argument generator. The Lagrange basis `g_lagrange` is omitted:
the verifier's MSM is expressed over the monomial basis `g`. -/
structure URS (G : Type*) where
  k : ℕ
  g : Fin (2 ^ k) → G
  w : G
  u : G

end Zcash.Snark
