import Zcash.Snark.VkCommit.Derivation
import Zcash.Circuits.TopLevelKeygen

/-!
# The method form: proof-shape parameters merged with circuit-derived `Shape`

`ProofParams` carries the only two `Shape` counts that are proof-shape rather than
circuit data (batch size, multiopen point sets); `ProofParams.mergeDerived` computes the
rest from a `TopLevelCircuit` (via the `TopLevelKeygen` methods), so a derived verifying
key can carry its `Shape` in the return type with no lawfulness side condition —
`derivedActionVk (pp.mergeDerived top) urs` is well-typed by construction, and the
fixture equality `shape_eq_mergeDerived`/`vk_eq_toVerifierKey` lives in
`Certificate.lean`'s target.

(A `TopLevelCircuit.toVerifierKey` generic over the circuit — with the commitment
pipeline abstracted over `(cs, operations)` rather than Action-specialized — is the
intended follow-up once the group-side generics of `Derivation.lean` are unified with
it; the Action-instantiated form below is what the capture certifies today.)
-/

namespace Zcash.Snark.VkCommit

open Zcash.Snark
open Halo2

/-- The two `Shape` counts that are genuinely proof-shape rather than circuit data: the
batch size and the multiopen point-set count. Everything else merges in derived
(`ProofParams.mergeDerived`). -/
structure ProofParams where
  numProofs : ℕ
  numPointSets : ℕ
deriving DecidableEq, Repr

open Zcash.Circuits in
/-- The `Shape` of a top-level circuit's proofs: the proof-shape counts merged with
everything the circuit derives — the domain exponent (`TopLevelCircuit.domainExponent`),
column/lookup/permutation counts from the configure-recorded constraint system, the
query counts from the derived pinned CS layouts (`TopLevelCircuit.pinnedCS`), the
verifier's permutation chunking `⌈columns / chunkLen⌉` (`permutation/verifier.rs:43-47`),
and the quotient split `cs.degree() − 1` (`vk.domain.get_quotient_poly_degree()`). -/
def ProofParams.mergeDerived (pp : ProofParams)
    {ConfigInput Config : Type} {Output : TypeMap} [CircuitType Output]
    (top : TopLevelCircuit Fp ConfigInput Config Output) : Shape :=
  let cs := top.constraintSystem
  let pinned := top.pinnedCS
  { k := top.domainExponent
    numProofs := pp.numProofs
    numAdviceColumns := cs.numAdviceColumns
    numLookups := cs.lookups.length
    numPermutationSets :=
      (cs.permutationColumns.length + cs.chunkLen - 1) / cs.chunkLen
    numPermutationColumns := cs.permutationColumns.length
    numQuotientPieces := csDegree cs - 1
    numInstanceQueries := pinned.instanceQueryLayout.length
    numAdviceQueries := pinned.adviceQueryLayout.length
    numFixedQueries := pinned.fixedQueryLayout.length
    numPointSets := pp.numPointSets }

/-- Transporting `derivedActionVk` along a shape equality is `derivedActionVk` at the
other shape — the record mentions the shape only in its `Fin`-domain types, never in a
field value. -/
theorem derivedActionVk_cast {G : Type} [AddCommGroup G] [Inhabited G]
    {s₁ s₂ : Shape} (hs : s₁ = s₂) (urs : URS G) :
    hs ▸ derivedActionVk s₁ urs = derivedActionVk s₂ urs := by
  cases hs; rfl

end Zcash.Snark.VkCommit
