import Zcash.Snark.Soundness.Action.AdaptiveStatementTerminal
import Zcash.Snark.Soundness.AGM.AdaptiveComposition

/-!
# Statistical surfaces for adaptive Action statements

An adaptive statement changes the verifier-controlled initial transcript from run to run.  The
bounded oracle domain still has one shape-determined length, so query-time decoders existentially
recover the canonical VK/instance prefix and ordinary proof represented by an annotated squeeze
point.  Equality of squeeze points pins that initial prefix, hence every configured public-instance
commitment, before any bad-set polynomial is reconstructed.
-/

namespace Zcash.Snark

open Classical CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open scoped ENNReal

local instance adaptiveStatementSurfacesVestaInhabited : Inhabited VestaG := ⟨0⟩

namespace ComputedAdaptiveActionStatementFSFamily

/-- A canonical statement-bound pre-IPA squeeze embedded in the common adaptive oracle domain. -/
def prefixesPreOf {pp : ProofParams}
    (vkTranscriptRepr : Fp)
    (instanceCommitment :
      Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG)
    (proof : WfProof (AdaptiveActionStatementShape pp))
    (n : Fin 11) : AdaptiveActionStatementTranscript pp :=
  let t := fullPrefixesPre (initialTranscript vkTranscriptRepr instanceCommitment) proof n
  ⟨t.val, by simpa [adaptiveStatementInitLength] using t.prop⟩

/-- A canonical statement-bound IPA squeeze embedded in the same common oracle domain. -/
def prefixesOf {pp : ProofParams}
    (vkTranscriptRepr : Fp)
    (instanceCommitment :
      Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG)
    (proof : WfProof (AdaptiveActionStatementShape pp))
    (j : Fin (AdaptiveActionStatementShape pp).k) : AdaptiveActionStatementTranscript pp :=
  let t := fullPrefixes (initialTranscript vkTranscriptRepr instanceCommitment) proof j
  ⟨t.val, by simpa [adaptiveStatementInitLength] using t.prop⟩

@[simp] theorem prefixesPreOf_output {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (n : Fin 11) :
    prefixesPreOf vkTranscriptRepr
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        output.toAlgebraicWfProof.proof n =
      output.prefixesPre vkTranscriptRepr n := by
  rfl

@[simp] theorem prefixesOf_output {pp : ProofParams}
    {basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG}
    {fixedRepresentations : List (AlgebraicPoint (F := Fp) basis)}
    (vkTranscriptRepr : Fp)
    (output : AdaptiveActionStatementOutput pp basis fixedRepresentations)
    (j : Fin (AdaptiveActionStatementShape pp).k) :
    prefixesOf vkTranscriptRepr
        (adaptiveActionStatementInstanceCommitment pp basis output.inputs)
        output.toAlgebraicWfProof.proof j =
      output.prefixes vkTranscriptRepr j := by
  rfl

/-- A canonical verifier prefix and well-formed proof decoded from one pre-IPA query point. -/
structure DecodedStatementPrePrefix (pp : ProofParams) (n : Fin 11)
    (t : AdaptiveActionStatementTranscript pp) where
  vkTranscriptRepr : Fp
  instanceCommitment :
    Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG
  proof : WfProof (AdaptiveActionStatementShape pp)
  point_eq : prefixesPreOf vkTranscriptRepr instanceCommitment proof n = t

/-- A canonical verifier prefix and well-formed proof decoded from one IPA query point. -/
structure DecodedStatementIpaPrefix (pp : ProofParams)
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (t : AdaptiveActionStatementTranscript pp) where
  vkTranscriptRepr : Fp
  instanceCommitment :
    Fin (AdaptiveActionStatementShape pp).numProofs → ℕ → VestaG
  proof : WfProof (AdaptiveActionStatementShape pp)
  point_eq : prefixesOf vkTranscriptRepr instanceCommitment proof j = t

/-- Choose a canonical pre-IPA decode when one exists; unrelated oracle queries decode to `none`. -/
noncomputable def decodeStatementPrePrefix? {pp : ProofParams} (n : Fin 11)
    (t : AdaptiveActionStatementTranscript pp) :
    Option (DecodedStatementPrePrefix pp n t) :=
  if h : Nonempty (DecodedStatementPrePrefix pp n t) then some (Classical.choice h) else none

/-- Choose a canonical IPA decode when one exists. -/
noncomputable def decodeStatementIpaPrefix? {pp : ProofParams}
    (j : Fin (AdaptiveActionStatementShape pp).k)
    (t : AdaptiveActionStatementTranscript pp) :
    Option (DecodedStatementIpaPrefix pp j t) :=
  if h : Nonempty (DecodedStatementIpaPrefix pp j t) then some (Classical.choice h) else none

/-- Every actual output-selected pre-IPA squeeze has a canonical decode. -/
theorem decodeStatementPrePrefix?_isSome {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11) :
    (decodeStatementPrePrefix? n (family.preIpaPoint basis n
      (family.runOutput basis O))).isSome := by
  let output := family.runOutput basis O
  have h : Nonempty (DecodedStatementPrePrefix pp n
      (family.preIpaPoint basis n output)) := ⟨
    { vkTranscriptRepr := family.vkTranscriptRepr basis
      instanceCommitment := adaptiveActionStatementInstanceCommitment pp basis output.inputs
      proof := output.toAlgebraicWfProof.proof
      point_eq := by rfl }⟩
  rw [decodeStatementPrePrefix?, if_pos h]
  rfl

/-- Every actual output-selected IPA squeeze has a canonical decode. -/
theorem decodeStatementIpaPrefix?_isSome {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (j : Fin (AdaptiveActionStatementShape pp).k) :
    (decodeStatementIpaPrefix? j (family.ipaPoint basis j
      (family.runOutput basis O))).isSome := by
  let output := family.runOutput basis O
  have h : Nonempty (DecodedStatementIpaPrefix pp j
      (family.ipaPoint basis j output)) := ⟨
    { vkTranscriptRepr := family.vkTranscriptRepr basis
      instanceCommitment := adaptiveActionStatementInstanceCommitment pp basis output.inputs
      proof := output.toAlgebraicWfProof.proof
      point_eq := by rfl }⟩
  rw [decodeStatementIpaPrefix?, if_pos h]
  rfl

/-- Equal adaptive pre-IPA query points pin the complete canonical verifier prefix. -/
theorem DecodedStatementPrePrefix.initialTranscript_eq_output {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11)
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp n t)
    (ht : t = family.preIpaPoint basis n (family.runOutput basis O)) :
    initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment =
      (family.runOutput basis O).init (family.vkTranscriptRepr basis) := by
  let output := family.runOutput basis O
  have hpoint : preIpaSqueezePoints
        (initialTranscript decoded.vkTranscriptRepr decoded.instanceCommitment)
        decoded.proof.1 n =
      preIpaSqueezePoints (output.init (family.vkTranscriptRepr basis))
        output.toAlgebraicWfProof.proof.1 n := by
    exact congrArg Subtype.val (decoded.point_eq.trans (ht.trans (by rfl)))
  apply initial_eq_of_preIpaSqueezePoints_eq _ _ _ _ n
  · simp [adaptiveStatementInitLength]
  · exact hpoint

/-- Consequently every configured instance-commitment point decoded at that query is the point
derived from the adversary-selected public statement. -/
theorem DecodedStatementPrePrefix.instanceCommitment_eq_output {pp : ProofParams}
    (family : ComputedAdaptiveActionStatementFSFamily pp)
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) (n : Fin 11)
    {t : AdaptiveActionStatementTranscript pp}
    (decoded : DecodedStatementPrePrefix pp n t)
    (ht : t = family.preIpaPoint basis n (family.runOutput basis O))
    (p : Fin (AdaptiveActionStatementShape pp).numProofs)
    (column : Fin (AdaptiveActionStatementShape pp).numInstanceColumns) :
    decoded.instanceCommitment p column =
      adaptiveActionStatementInstanceCommitment pp basis
        (family.runOutput basis O).inputs p column := by
  exact instanceCommitment_eq_of_initialTranscript_eq _ _ _ _
    (decoded.initialTranscript_eq_output family basis O n ht) p column

end ComputedAdaptiveActionStatementFSFamily

end Zcash.Snark
