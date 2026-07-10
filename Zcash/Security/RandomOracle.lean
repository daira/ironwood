import Mathlib

/-!
# Random-oracle collision vocabulary (classical ROM)

Shared Layer-A foundation for the classical-ROM security arguments (key-binding `H^*`, and — reused
by the Layer-B games — note-commitment / nullifier `H^rcm`). We follow the *deterministic-exhibition*
style of `BindingSignature/Balance.lean`: a security theorem reduces a break to an **exhibited**
random-oracle collision, and the probability that such a collision occurs within `q` oracle queries —
the birthday bound `q(q-1)/(2·|F|)` — is a separate concern (Layer C), carried as a named quantity
until discharged.

An abstract oracle is any function `O : Q → F` from queries to field outputs; "randomness" enters only
at the probability layer, so nothing here mentions probability.

The `±`-collision variant `PMCollision` is the shape produced by arguments that pass through the
`Extract` coordinate extractor, whose fibers are `{P, -P}`: an `Extract`-equality of two commitments
yields an equality-or-negation of the underlying scalars. Both key-binding and the nullifier
(Faerie-Gold) argument bottom out in a `PMCollision`.
-/

namespace Zcash.Security.RandomOracle

variable {Q F : Type*}

/-- A plain collision of an oracle `O`: two distinct queries with equal outputs. -/
def Collision (O : Q → F) : Prop :=
  ∃ a b, a ≠ b ∧ O a = O b

/-- A `±`-collision of `O`: two distinct queries whose outputs are equal or negatives of each other.
This is the event exhibited by `Extract`-based reductions (key-binding, nullifier). -/
def PMCollision [Neg F] (O : Q → F) : Prop :=
  ∃ a b, a ≠ b ∧ (O a = O b ∨ O a = -O b)

/-- Every plain collision is a `±`-collision. -/
theorem Collision.toPM [Neg F] {O : Q → F} (h : Collision O) : PMCollision O := by
  obtain ⟨a, b, hab, hEq⟩ := h
  exact ⟨a, b, hab, Or.inl hEq⟩

end Zcash.Security.RandomOracle
