import Zcash.Circuits.Integration.ActionTerminal
import Zcash.Snark.Soundness.AGM.DecodeToOpened

/-!
# The rewind-free decode at the Action terminal

`ActionTerminal` concludes the concrete Action bundle statement from the historical opened-batch
interface: an `OpenedBatchOpenings`, a per-set `OpenedMemberDecode`, deployed acceptance, the
canonical quotient, and the member-binding premise.  That interface was written for the rewinding
route.

`AGM.DecodeToOpened` presents a rewind-free `DeployedAlgebraicDecode` in exactly that shape, so the
straight-line route reaches the same terminal from one accepting execution.  This module ties the
two together: supply a decode and acceptance, and what remains are the challenge exclusions —
`hxgood`, `hgoodY`, and the permutation and lookup exclusions — which are priced separately, not
discharged here.

The terminal is used unchanged.  Nothing in this module weakens its statement: the verifying key
is still `actionCircuit.toVerifierKey`, and no free semantic proposition, `hencodes`, or decoded
column feed is reintroduced.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)

variable {G : Type} [AddCommGroup G] [Module Fp G] [DecidableEq G] [Inhabited G]

/-- **The Action bundle statement from a rewind-free decode.**  The decode supplies the batch
openings, the member decodes, the `x₄` designation and the member-binding premise; the caller
supplies acceptance and the challenge exclusions.

The member-binding premise never takes its relation branch here: a decode already carries the
value equations, so `memberBinding` lands on the left for every slot and point. -/
noncomputable def action_bundleStatement_or_relation_of_decode
    (pp : ProofParams) (urs : URS G)
    (hk : (pp.mergeDerived actionCircuit).k = urs.k)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp G)
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (decode : DeployedAlgebraicDecode urs hk
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch < scalarFieldOrder)
    (haccepts :
      DeployedAccepts urs hk
        (actionCircuit.toVerifierKey pp urs)
        (actionCircuit.instanceCommitment pp urs inputs) ps ch) :=
  action_bundleStatement_or_relation_of_decodedMemberPolynomial_eq
    pp urs hk inputs ps ch pU pW a
    (decode.toOpenedBatch hchar)
    (fun i hi => decode.toMemberDecode hchar i hi)
    haccepts _ rfl
    (fun slot point hpoint => PSum.inl (decode.memberBinding hchar slot point hpoint))

end ActionTerminal

end Zcash.Snark
