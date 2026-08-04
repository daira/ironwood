import Zcash.Snark.Fixtures.SingleAction.Honest.StaticChecks
import Zcash.Snark.Soundness.Composition.ScheduleBudget
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity
import Zcash.Snark.Soundness.AGM.StraightLineOrchardConsensusBounds
import Zcash.Snark.Keygen.Certificate
import Zcash.Snark.Soundness.Action.StraightLineEvent
import Zcash.Snark.Soundness.Action.StraightLineBudgets
import Zcash.Snark.Soundness.Action.AdaptiveEvent

/-!
# The events the Action endpoints bound

The accepting-false-statement and knowledge-failure sets, at the captured Action parameters
and at arbitrary bundle size. The endpoints in `Capstones.Action` bound their probability;
this module only says which runs they are.
-/

namespace Zcash.Snark.Capstone

-- The captured facts these endpoints are stated at.
open Zcash.Snark.Fixture

open Zcash.Snark CompPoly.CPolynomial
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Keygen (actionProofParams actionProofParamsFor
  actionCircuitShape_eq_fixtureCircuitShape actionShapeFor_eq_fixtureShape
  actionShape_eq_fixtureShape vk_eq_toVerifierKey)
open Zcash.Circuits Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder URS)
open scoped ENNReal


/-- Merging Action proof parameters yields the matching fixture shape. -/
theorem actionProofShape_eq_maxShape (numProofs : ℕ) :
    actionCircuit.shape.withProofParams (actionProofParamsFor numProofs) =
      Zcash.Snark.FixtureMax.shape numProofs := by
  rw [actionShapeFor_eq_fixtureShape]
  rfl

/-! ## Exact false-statement events -/

/-- **The captured Action-soundness event.**  This definition is the set of captured-shape
experiment outcomes on which the deployed verifier accepts while the Orchard Action statement at
its supplied public inputs is false; the capstone theorem separately bounds its probability. -/
def capturedActionAcceptFalseStatementEvent
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams actionProofParams))
    (inputs : Fin actionProofParams.numProofs →
      PublicInputs Fp) :
    Set ((AugmentedIndex actionCircuit.n → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams actionProofParams) family.init.length 10
          + 3 * actionCircuit.domainExponent) → Fp)) :=
  family.straightLineConstraintSemanticFailureEvent
    (topLevelBundleStatementDecoded actionCircuit actionProofParams family inputs)

/-- The generic accepting-false-`BundleStatement` event at arbitrary `numProofs`.  This definition
is the outcome set; the corresponding soundness theorem separately supplies its probability
bound. -/
def actionAcceptFalseStatementEvent (numProofs : ℕ)
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp) :
    Set ((AugmentedIndex
      actionCircuit.n → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
          family.init.length 10 +
          3 * actionCircuit.domainExponent) → Fp)) :=
  family.straightLineConstraintSemanticFailureEvent
    (topLevelBundleStatementDecoded actionCircuit (actionProofParamsFor numProofs) family inputs)

end Zcash.Snark.Capstone
