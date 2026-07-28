import Zcash.Snark.Soundness.AGM.AdaptiveOnline
import Zcash.Snark.Soundness.Composition.PrefixedSqueeze

/-!
# Semantic challenge surfaces for arbitrary adaptive online-AGM adversaries

The phase-based route proves that a final proof prefix is stable when its own challenge is
reprogrammed.  An arbitrary malicious random-oracle adversary need not have that shape.  Instead,
`firstLabelOrFallbackBad_measure_le` prices the first actual query of the prefix, or the verifier's
fresh completion query when the adversary never asked it.

The semantic bad set at pre-IPA index `n` depends only on the queried transcript and answers at
strictly shorter prefixes.  Consequently it is blind at the index-`n` point without any phase or
cut object.  This file supplies the generic table-level bound used by theta, beta, gamma, y, and
the constraint-x challenge.
-/

namespace Zcash.Snark

open scoped ENNReal
open Classical

local instance vestaInhabitedAdaptiveSurfaces : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- The prefix of `t` at an earlier pre-IPA squeeze index. -/
def adaptiveEarlierPrefix (init : List (TranscriptElt Fp VestaG))
    {L : ℕ} (t : BTranscript Fp VestaG L) (i : Fin 11) : BTranscript Fp VestaG L :=
  ⟨t.val.take (preIpaLen shape init.length i), by
    rw [List.length_take]
    exact le_trans (min_le_right _ _) t.prop⟩

/-- At a transcript of exactly the index-`n` length, every earlier prefix is a different oracle
point. -/
theorem adaptiveEarlierPrefix_ne
    (init : List (TranscriptElt Fp VestaG)) {L : ℕ}
    (n : Fin 11) (t : BTranscript Fp VestaG L)
    (hlen : t.val.length = preIpaLen shape init.length n)
    (i : Fin (n : ℕ)) :
    adaptiveEarlierPrefix (shape := shape) init t (i.castLE (le_of_lt n.isLt)) ≠ t := by
  intro heq
  have hlens := congrArg (fun q : BTranscript Fp VestaG L => q.val.length) heq
  simp only [adaptiveEarlierPrefix, List.length_take] at hlens
  have hlt : preIpaLen shape init.length (i.castLE (le_of_lt n.isLt)) < t.val.length := by
    rw [hlen]
    exact preIpaLen_lt_at shape init.length i.isLt
  rw [min_eq_left hlt.le] at hlens
  exact (Nat.ne_of_lt hlt) hlens

/-- A semantic bad set decoded from `t` and the answers at all earlier deployed prefixes.  Queries
of any other transcript length receive the empty set, which makes the definition safe for every
unrelated query an arbitrary adversary may issue. -/
noncomputable def adaptivePrefixBad (init : List (TranscriptElt Fp VestaG)) (n : Fin 11)
    (badF : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) →
      (Fin (n : ℕ) → Fp) → Set Fp)
    (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k))
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) : Set Fp :=
  if t.val.length = preIpaLen shape init.length n then
    badF t (fun i => O (adaptiveEarlierPrefix (shape := shape) init t
      (i.castLE (le_of_lt n.isLt))))
  else ∅

/-- Updating the index-`n` point does not change its decoded bad set. -/
theorem adaptivePrefixBad_update_self (init : List (TranscriptElt Fp VestaG)) (n : Fin 11)
    (badF : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) →
      (Fin (n : ℕ) → Fp) → Set Fp)
    (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k))
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) (v : Fp) :
    adaptivePrefixBad (shape := shape) init n badF t (Function.update O t v) =
      adaptivePrefixBad (shape := shape) init n badF t O := by
  unfold adaptivePrefixBad
  by_cases hlen : t.val.length = preIpaLen shape init.length n
  · simp only [if_pos hlen]
    congr 1
    funext i
    rw [Function.update_of_ne]
    exact adaptiveEarlierPrefix_ne init n t hlen i
  · simp [hlen]

/-- The decoded prefix bad set inherits any run-uniform per-challenge bound. -/
theorem adaptivePrefixBad_measure_le (init : List (TranscriptElt Fp VestaG)) (n : Fin 11)
    (badF : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) →
      (Fin (n : ℕ) → Fp) → Set Fp)
    {epsilon : ENNReal}
    (hbad : ∀ t nu, (PMF.uniformOfFintype Fp).toOuterMeasure (badF t nu) ≤ epsilon)
    (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k))
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
      (adaptivePrefixBad (shape := shape) init n badF t O) ≤ epsilon := by
  unfold adaptivePrefixBad
  split
  · exact hbad _ _
  · simp

namespace ComputedAdaptiveOnlineAGMFSFamily

/-- **Arbitrary-adversary semantic squeeze bound.**  No `PrefixDeterminedAt`, sequential phase,
or `ActionSequentialExecution` premise is present. -/
theorem adaptivePrefixSurface_table_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (badF : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin (n : ℕ) → Fp) → Set Fp)
    {epsilon : ENNReal}
    (hbad : ∀ t nu, (PMF.uniformOfFintype Fp).toOuterMeasure (badF t nu) ≤ epsilon) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
      {O | O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O).toAlgebraicWfProof n) ∈
        adaptivePrefixBad (shape := shape) family.init n badF
          (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O).toAlgebraicWfProof n) O} ≤
      (family.Q + 1 : ℕ) * epsilon := by
  let bad := fun (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
      (_label : AlgebraicTranscriptQuery (F := Fp) basis t) =>
        adaptivePrefixBad (shape := shape) family.init n badF t
  let fallback := fun (_data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
      (t : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k)) =>
        adaptivePrefixBad (shape := shape) family.init n badF t
  have hbound := LabeledOracleComp.firstLabelOrFallbackBad_measure_le
      (family.adversary basis)
      (fun data => algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n)
      bad fallback
      (fun t label O v => adaptivePrefixBad_update_self family.init n badF t O v)
      (fun data t O v => adaptivePrefixBad_update_self family.init n badF t O v)
      (fun t label O => adaptivePrefixBad_measure_le family.init n badF hbad t O)
      (fun data t O => adaptivePrefixBad_measure_le family.init n badF hbad t O)
      (family.queryBound basis)
  have hevent :
      {O | O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O).toAlgebraicWfProof n) ∈
        adaptivePrefixBad (shape := shape) family.init n badF
          (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O).toAlgebraicWfProof n) O} =
      {O | O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O).toAlgebraicWfProof n) ∈
        LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis) bad fallback
          (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O).toAlgebraicWfProof n) O} := by
    ext O
    simp only [Set.mem_setOf_eq]
    unfold LabeledOracleComp.firstLabelOrFallbackBad bad fallback
    cases (family.adversary basis).findLabel O
      (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O).toAlgebraicWfProof n) <;> rfl
  rw [hevent]
  exact hbound

end ComputedAdaptiveOnlineAGMFSFamily

end Zcash.Snark
