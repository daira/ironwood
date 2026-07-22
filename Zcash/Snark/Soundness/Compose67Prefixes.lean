import Zcash.Snark.Soundness.Compose67Assembly

/-!
# The concrete multiopen prefixes for the #67 ladder

`snarkExtraction_prob_le_of_generatorRO_textbookDL_ladder` (`Soundness.Compose67Assembly`) takes an
abstract `prefixes : ∀ basis, AlgebraicWfProof … → Fin 4 → BTranscript …`. This module pins the
concrete choice: the four multiopen challenge squeeze points `x₁,x₂,x₃,x₄`, which the family reads
from the oracle table at `algebraicFullPrefixesPre` indices `5,6,7,8` (the `chRecord` layout,
`Soundness.Forking.Adversary.PreIpa`). `algebraicTableAcceptZ` (`…Algebraic`) sets the challenge
vector to `fun i => O (algebraicFullPrefixesPre init p i)`, so on any table the ladder's
`prefixReads` at these points are *definitionally* the four multiopen challenge fields of the record
squeezed from that table — the "lands" side of the ladder's `hcont`.
-/

namespace Zcash.Snark

open ComputedAlgebraicFSFamily
open scoped ENNReal

variable {shape : Shape}

/-- The four multiopen challenge squeeze points (`x₁,x₂,x₃,x₄` = `chRecord` / `ν`-indices `5,6,7,8`)
of an algebraic output, packaged as the ladder's `prefixes`. -/
def multiopenPrefixes (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (p : AlgebraicWfProof basis (family.vk basis)) : Fin 4 →
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) :=
  fun j => algebraicFullPrefixesPre family.init p ⟨5 + j.val, by omega⟩

/-- On any oracle table `O`, the ladder's four prefix reads at `multiopenPrefixes` are exactly the
four multiopen challenge fields (`x₁,x₂,x₃,x₄`) of the challenge record `chRecord` squeezed from `O`
at the algebraic output's own pre-IPA squeeze points — the value the family's acceptance test
(`algebraicTableAcceptZ`) uses. This is the definitional tie the ladder's `hcont` "lands" half needs:
`prefixReads = (ch.x1, ch.x2, ch.x3, ch.x4)` for the honest challenge record. -/
theorem multiopenPrefixReads_eq (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (χ : Fin shape.k → Fp) :
    PeelDecode.prefixReads (multiopenPrefixes family basis) (family.adversary basis) O
      = (let ν := fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) i)
         ((chRecord ν χ).x1, (chRecord ν χ).x2, (chRecord ν χ).x3, (chRecord ν χ).x4)) := by
  rfl

end Zcash.Snark
