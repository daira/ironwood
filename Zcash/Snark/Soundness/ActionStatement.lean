import Zcash.Circuits.Action.Statement
import Zcash.Snark.Soundness.PolynomialEnvironment

/-!
# Decoded instance rows to the Orchard Action statement

This module connects the canonical resolver environment to the structured ten-row
Action instance.  It assumes only the polynomial identity that commitment provenance
must eventually supply.
-/

namespace Zcash.Snark

open Halo2 Polynomial
open Zcash.Circuits.Action
open Zcash.Circuits.Action.Circuit

set_option maxHeartbeats 20000

/--
If the resolved primary instance column is the canonical zero-padded polynomial for
one Action's rows, reading that column through Clean produces exactly that Action's
structured public inputs.
-/
theorem actionPublicInputs_of_instanceRowPolynomial
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (usableRows : ℕ)
    (cfg : Config) (inputs : PublicInputs)
    (hsize : 10 ≤ 2 ^ shape.k)
    (hpoly : poly (.instanceCol p cfg.primary.index) =
      instanceRowPolynomial (2 ^ shape.k) vk.omega inputs.rows)
    (hrows : Function.Injective
      fun i : Fin (2 ^ shape.k) => vk.omega ^ (i : ℕ)) :
    PublicInputs.ofEnvironment cfg
      (resolverEnvironment vk poly p usableRows) = inputs := by
  have hread (row : Fin 10) :
      (resolverEnvironment vk poly p usableRows).inst cfg.primary (row : ℤ) =
        inputs.rows.getD (row : ℕ) 0 := by
    let domainRow : Fin (2 ^ shape.k) :=
      ⟨row, lt_of_lt_of_le row.isLt hsize⟩
    simpa [domainRow] using
      resolverEnvironment_instance_of_rowPolynomial
        vk poly p usableRows cfg.primary inputs.rows hpoly hrows domainRow
  apply PublicInputs.ext
  · simpa [PublicInputs.ofEnvironment, PublicInputs.rows, ANCHOR] using hread 0
  · simpa [PublicInputs.ofEnvironment, PublicInputs.rows, CV_NET_X] using hread 1
  · simpa [PublicInputs.ofEnvironment, PublicInputs.rows, CV_NET_Y] using hread 2
  · simpa [PublicInputs.ofEnvironment, PublicInputs.rows, NF_OLD] using hread 3
  · simpa [PublicInputs.ofEnvironment, PublicInputs.rows, RK_X] using hread 4
  · simpa [PublicInputs.ofEnvironment, PublicInputs.rows, RK_Y] using hread 5
  · simpa [PublicInputs.ofEnvironment, PublicInputs.rows, CMX] using hread 6
  · simpa [PublicInputs.ofEnvironment, PublicInputs.rows, ENABLE_SPEND] using hread 7
  · simpa [PublicInputs.ofEnvironment, PublicInputs.rows, ENABLE_OUTPUT] using hread 8
  · simpa [PublicInputs.ofEnvironment, PublicInputs.rows, DISABLE_CROSS_ADDRESS] using hread 9

end Zcash.Snark
