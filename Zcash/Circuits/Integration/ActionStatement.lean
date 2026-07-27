import Zcash.Circuits.Action.Statement
import Zcash.Arithmetic.Domain
import Zcash.Circuits.Integration.TopLevelCorrectness

/-!
# Decoded instance rows to the Orchard Action statement

This module connects the canonical resolver environment to the structured ten-row
Action instance.  It assumes only the polynomial identity that commitment provenance
must eventually supply.
-/

namespace Zcash.Snark

open Halo2 Polynomial
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Circuits.Action.Circuit

set_option maxHeartbeats 20000

/--
If the resolved primary instance column is the canonical zero-padded polynomial for
one Action's rows, reading that column through Clean produces exactly that Action's
structured public inputs.
-/
theorem actionPublicInputs_of_instanceRowPolynomial
    {TopConfigInput TopConfig : Type} {Output : TypeMap}
    [CircuitType Output]
    {top : TopLevelCircuit Fp TopConfigInput TopConfig Output}
    {numProofs : ℕ} {proofIndex : Fin numProofs}
    (assignment : TopLevelAssignment top numProofs proofIndex)
    (cfg : Config) (inputs : PublicInputs)
    (hsize : 10 ≤ 2 ^ top.domainExponent)
    (hpoly : assignment.polynomial
        (.instanceCol proofIndex cfg.primary.index) =
      instanceRowPolynomial (2 ^ top.domainExponent)
        (Zcash.Arithmetic.omegaOf top.domainExponent) inputs.rows)
    (hrows : Function.Injective
      fun i : Fin (2 ^ top.domainExponent) =>
        Zcash.Arithmetic.omegaOf top.domainExponent ^ (i : ℕ)) :
    PublicInputs.ofEnvironment cfg
      assignment.environment = inputs := by
  have hread (row : Fin 10) :
      assignment.environment.inst cfg.primary (row : ℤ) =
        inputs.rows.getD (row : ℕ) 0 := by
    let domainRow : Fin (2 ^ top.domainExponent) :=
      ⟨row, lt_of_lt_of_le row.isLt hsize⟩
    rw [TopLevelAssignment.environment_instance, hpoly]
    simpa only [domainRow] using instanceRowPolynomial_eval hrows domainRow
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

/--
Present the generic top-level bundle statement as the public Orchard Action
statement once the accepted primary-instance polynomial has been identified.
-/
theorem action_bundleStatement_of_topLevelBundleStatement
    (pp : Keygen.ProofParams)
    (poly : CommitmentId → Polynomial Fp)
    (inputs :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
        PublicInputs)
    (hbound : orchardActionTopLevelCircuit.domainExponent < 33)
    (hsize : 10 ≤ 2 ^ orchardActionTopLevelCircuit.domainExponent)
    (hinstance : ∀
      proofIndex :
        Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs,
      poly
          (.instanceCol proofIndex
            (Circuit.configure
              Specs.Sinsemilla.orchardGenerators {}).1.primary.index) =
        instanceRowPolynomial
          (2 ^ orchardActionTopLevelCircuit.domainExponent)
          (Zcash.Arithmetic.omegaOf
            orchardActionTopLevelCircuit.domainExponent)
          (inputs proofIndex).rows)
    (htop :
      TopLevelBundleStatement orchardActionTopLevelCircuit pp poly) :
    BundleStatement Specs.Sinsemilla.orchardGenerators orchardBases inputs := by
  intro proofIndex
  let assignment :
      TopLevelAssignment orchardActionTopLevelCircuit
        (pp.mergeDerived orchardActionTopLevelCircuit).numProofs proofIndex :=
    { polynomial := poly }
  have hstatement :=
    statement_of_topLevelStatement
      Specs.Sinsemilla.orchardGenerators orchardBases
      orchardActionTopLevelCircuit rfl 0
      assignment.placedEnvironment (htop proofIndex)
  have hpublic :
      PublicInputs.ofEnvironment
          (Circuit.configure
            Specs.Sinsemilla.orchardGenerators {}).1
          assignment.environment =
        inputs proofIndex := by
    apply actionPublicInputs_of_instanceRowPolynomial
      assignment
      (Circuit.configure
        Specs.Sinsemilla.orchardGenerators {}).1
      (inputs proofIndex) hsize
    · exact hinstance proofIndex
    · exact TopLevelAssignment.domainRowsInjective hbound
  change
    Statement Specs.Sinsemilla.orchardGenerators orchardBases
      (PublicInputs.ofEnvironment
        (Circuit.configure
          Specs.Sinsemilla.orchardGenerators {}).1
        assignment.environment) at hstatement
  rwa [hpublic] at hstatement

assert_no_sorry action_bundleStatement_of_topLevelBundleStatement

end Zcash.Snark
