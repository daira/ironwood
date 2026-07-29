import Zcash.Snark.Soundness.AGM.Adapter
import Zcash.Snark.Soundness.Forking.Extractor

/-!
# Algebraic prover and forking-certificate interfaces

An AGM prover returns each group element with coefficients over its public basis. This module adds
those coefficients to the types used by the forking extractor.

`AlgebraicProver` is the prefix-determined strategy. `AlgebraicDForkCert` is its explicit
`(3, …, 3)` fork tree. Both erase to the ordinary forking types.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A prefix-determined prover whose group outputs include coefficients over `basis`. -/
inductive AlgebraicProver {ι : Type*} [Fintype ι] (basis : ι → G) : ℕ → Type _ where
  | leaf : F → F → AlgebraicProver basis 0
  | node {d : ℕ} : AlgebraicPoint (F := F) basis → AlgebraicPoint (F := F) basis →
      (F → AlgebraicProver basis d) → AlgebraicProver basis (d + 1)

namespace AlgebraicProver

/-- Erase coefficient vectors to obtain the ordinary prover strategy. -/
def toProver {ι : Type*} [Fintype ι] {basis : ι → G} :
    {d : ℕ} → AlgebraicProver (F := F) basis d → Prover F G d
  | 0, .leaf c f => .leaf c f
  | _ + 1, .node L R cont => .node L.point R.point (fun u => toProver (cont u))

end AlgebraicProver

/-- A fork certificate whose round points include coefficients over one fixed public basis. -/
inductive AlgebraicDForkCert {ι : Type*} [Fintype ι] (basis : ι → G) : ℕ → Type _ where
  | leaf : F → F → AlgebraicDForkCert basis 0
  | node {d : ℕ} : AlgebraicPoint (F := F) basis → AlgebraicPoint (F := F) basis → F → F → F →
      AlgebraicDForkCert basis d → AlgebraicDForkCert basis d → AlgebraicDForkCert basis d →
      AlgebraicDForkCert basis (d + 1)

namespace AlgebraicDForkCert

/-- Erase coefficient vectors to obtain the certificate checked by `DeployedForkValid`. -/
def toDForkCert {ι : Type*} [Fintype ι] {basis : ι → G} :
    {d : ℕ} → AlgebraicDForkCert (F := F) basis d → DForkCert F G d
  | 0, .leaf c f => .leaf c f
  | _ + 1, .node L R u₁ u₂ u₃ c₁ c₂ c₃ =>
      .node L.point R.point u₁ u₂ u₃ (toDForkCert c₁) (toDForkCert c₂) (toDForkCert c₃)

end AlgebraicDForkCert



end Zcash.Snark
