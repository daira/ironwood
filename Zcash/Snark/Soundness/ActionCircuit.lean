import Zcash.Circuits.Action.RealBases
import Zcash.Snark.Soundness.Vesta

/-!
# Connecting deployed SNARK soundness to the Ironwood Action circuit

This module is the integration boundary between two existing developments:

* `Zcash.Snark` extracts an opening of the polynomial committed to by the deployed
  verifier and eventually asks for an `hencodes` hypothesis saying that its abstract
  `circuitSat` predicate implies the intended protocol statement.
* `Zcash.Circuits.Action.Circuit.soundnessPost` proves that every Clean environment
  satisfying the concrete Action circuit operations yields the high-level
  `Action.Circuit.SpecPost` statement.

The remaining hard step is deliberately represented by `GateToActionBridge`.  Its
source is the predicate currently produced by the SNARK constraint proof; its target
is the exact Clean assignment predicate consumed below.  In particular, a proof of
that bridge must recover the individual committed columns from the batched IPA
opening, decode them into a placed Clean environment, prove lookup and permutation
semantics, and identify the public-instance column.

Everything after that representation theorem is proved here: the Clean circuit's
existing soundness theorem produces an `ActionStatement`, and that implication has
exactly the type required by every `hencodes` parameter in `Soundness.Main` and
`Soundness.Vesta`.
-/

namespace Zcash.Snark.ActionCircuit

open Halo2
open Polynomial
open Zcash.Circuits.Action

/-- The ten public rows consumed by one post-NU6.3 Orchard Action circuit. -/
structure PublicInputs where
  anchor : Fp
  cvX : Fp
  cvY : Fp
  nfOld : Fp
  rkX : Fp
  rkY : Fp
  cmx : Fp
  enableSpend : Fp
  enableOutput : Fp
  disableCrossAddress : Fp
deriving DecidableEq

/-- Project the public part of the Action circuit's constructive witness. -/
def PublicInputs.ofActionData (w : Zcash.Circuits.Action.Circuit.ActionData) : PublicInputs where
  anchor := w.anchor
  cvX := w.cvX
  cvY := w.cvY
  nfOld := w.nfOld
  rkX := w.rkX
  rkY := w.rkY
  cmx := w.cmx
  enableSpend := w.enableSpend
  enableOutput := w.enableOutput
  disableCrossAddress := w.disableCrossAddress

/-- Read the Action public rows directly from a Clean environment. -/
def PublicInputs.ofEnvironment (cfg : Zcash.Circuits.Action.Circuit.Config)
    (env : Placed Environment Fp) :
    PublicInputs where
  anchor := env.env.get cfg.primary (Zcash.Circuits.Action.Circuit.ANCHOR : ℤ)
  cvX := env.env.get cfg.primary (Zcash.Circuits.Action.Circuit.CV_NET_X : ℤ)
  cvY := env.env.get cfg.primary (Zcash.Circuits.Action.Circuit.CV_NET_Y : ℤ)
  nfOld := env.env.get cfg.primary (Zcash.Circuits.Action.Circuit.NF_OLD : ℤ)
  rkX := env.env.get cfg.primary (Zcash.Circuits.Action.Circuit.RK_X : ℤ)
  rkY := env.env.get cfg.primary (Zcash.Circuits.Action.Circuit.RK_Y : ℤ)
  cmx := env.env.get cfg.primary (Zcash.Circuits.Action.Circuit.CMX : ℤ)
  enableSpend := env.env.get cfg.primary (Zcash.Circuits.Action.Circuit.ENABLE_SPEND : ℤ)
  enableOutput := env.env.get cfg.primary (Zcash.Circuits.Action.Circuit.ENABLE_OUTPUT : ℤ)
  disableCrossAddress :=
    env.env.get cfg.primary (Zcash.Circuits.Action.Circuit.DISABLE_CROSS_ADDRESS : ℤ)

/-- The Action extractor reads exactly the ten public-instance rows above. -/
theorem PublicInputs.ofActionData_extract (cfg : Zcash.Circuits.Action.Circuit.Config)
    (input : Var Zcash.Circuits.Action.Circuit.PrivateInputs Fp)
    (i₀ : RegionIndex) (env : Placed Environment Fp) :
    PublicInputs.ofActionData (Zcash.Circuits.Action.Circuit.extract cfg input i₀ env) =
      PublicInputs.ofEnvironment cfg env := rfl

/-- The protocol-level conclusion for one Action with fixed public inputs.

The existential witness is the constructive `ActionData` extracted by the Clean
circuit proof.  Keeping the public-input equality in the statement makes the result
independent of the decoded low-level environment, as an `hencodes` conclusion must be.
-/
def ActionStatement (pubInputs : PublicInputs) : Prop :=
  ∃ w : Zcash.Circuits.Action.Circuit.ActionData,
    PublicInputs.ofActionData w = pubInputs ∧
    Zcash.Circuits.Action.Circuit.SpecBase
      Zcash.Circuits.Specs.Sinsemilla.orchardGenerators orchardBases w ∧
    (w.disableCrossAddress ≠ 0 → w.gdOld = w.gdNew ∧ w.pkdOld = w.pkdNew)

/-- All low-level data needed to apply the proved Clean Action soundness theorem. -/
structure Assignment where
  cfg : Zcash.Circuits.Action.Circuit.Config
  input : Var Zcash.Circuits.Action.Circuit.PrivateInputs Fp
  start : RegionIndex
  env : Placed Environment Fp

/-- The environment-level side conditions of the concrete Action circuit. -/
def Assignment.EnvAssumptions (x : Assignment) : Prop :=
  Zcash.Circuits.Action.Circuit.EnvAssumptions
    Zcash.Circuits.Specs.Sinsemilla.orchardGenerators x.cfg x.env

/-- Satisfaction of the exact post-NU6.3 Action operation trace. -/
def Assignment.Constraints (x : Assignment) : Prop :=
  Halo2.Constraints x.env.place x.env.env
    ((Zcash.Circuits.Action.Circuit.mainPost
      Zcash.Circuits.Specs.Sinsemilla.orchardGenerators orchardBases x.cfg x.input).operations x.start)
    x.start

/-- Public inputs carried by a decoded Action assignment. -/
def Assignment.publicInputs (x : Assignment) : PublicInputs :=
  PublicInputs.ofEnvironment x.cfg x.env

/-- The precise target of the SNARK-to-Clean representation theorem. -/
def Assignment.Satisfies (x : Assignment) (pubInputs : PublicInputs) : Prop :=
  x.EnvAssumptions ∧ x.Constraints ∧ x.publicInputs = pubInputs

/-- The existing `Action.Bundle.soundnessPost` theorem, exposed at the integration
boundary without weakening or restating its constraints. -/
theorem specPost_of_constraints (x : Assignment)
    (henv : x.EnvAssumptions) (hconstraints : x.Constraints) :
    Zcash.Circuits.Action.Circuit.SpecPost
      Zcash.Circuits.Specs.Sinsemilla.orchardGenerators orchardBases
      (eval x.env x.input) ()
      (Zcash.Circuits.Action.Circuit.extract x.cfg x.input x.start x.env) := by
  exact Zcash.Circuits.Action.Circuit.soundnessPost
    Zcash.Circuits.Specs.Sinsemilla.orchardGenerators orchardBases x.cfg
    x.start x.env x.input henv trivial hconstraints

/-- A satisfying Clean assignment proves the fixed-public-input Action statement. -/
theorem actionStatement_of_satisfies (pubInputs : PublicInputs) (x : Assignment)
    (h : x.Satisfies pubInputs) : ActionStatement pubInputs := by
  rcases h with ⟨henv, hconstraints, hpublic⟩
  let w := Zcash.Circuits.Action.Circuit.extract x.cfg x.input x.start x.env
  refine ⟨w, ?_, ?_⟩
  · rw [PublicInputs.ofActionData_extract]
    exact hpublic
  · exact specPost_of_constraints x henv hconstraints

/-- Interpret an IPA-sized extracted vector as a candidate Clean Action assignment.

This is data, not an assumption: the difficult proof obligation is that the decoder
is adequate for the predicate established by the SNARK proof.
-/
abbrev Decoder (k : ℕ) := (Fin (2 ^ k) → Fp) → Assignment

/-- The ideal circuit predicate at the integration boundary. -/
def ActionCircuitSat {k : ℕ} (decode : Decoder k) (pubInputs : PublicInputs)
    (a : Fin (2 ^ k) → Fp) : Prop :=
  (decode a).Satisfies pubInputs

/-- `SnarkRelation` is functorial in its circuit-satisfaction predicate. -/
theorem SnarkRelation.mapCircuitSat {G : Type*} [AddCommGroup G] [Module Fp G]
    {urs : URS G} {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {p q : (Fin (2 ^ urs.k) → Fp) → Prop} {a : Fin (2 ^ urs.k) → Fp}
    (hpq : ∀ a, p a → q a) (h : SnarkRelation urs P b v p a) :
    SnarkRelation urs P b v q a :=
  ⟨h.opens, hpq a h.satisfiesCircuit⟩

/-- Any implication out of `circuitSat` supplies the corresponding `hencodes`.

This records explicitly that the IPA-opening conjunct is not used by the semantic
last mile; its job is to justify that the same extracted vector is the one constrained
by the verifier.
-/
theorem hencodes_of_circuitSat {G : Type*} [AddCommGroup G] [Module Fp G]
    {urs : URS G} {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop} {S : Prop}
    (hsemantic : ∀ a, circuitSat a → S) :
    ∀ a, SnarkRelation urs P b v circuitSat a → S := by
  intro a h
  exact hsemantic a h.satisfiesCircuit

/-- The ideal decoded predicate has the `hencodes` property needed by SNARK
soundness, with no additional assumptions. -/
theorem actionCircuitSat_hencodes {G : Type*} [AddCommGroup G] [Module Fp G]
    {urs : URS G} {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    (decode : Decoder urs.k) (pubInputs : PublicInputs) :
    ∀ a, SnarkRelation urs P b v (ActionCircuitSat decode pubInputs) a →
      ActionStatement pubInputs := by
  apply hencodes_of_circuitSat
  intro a ha
  exact actionStatement_of_satisfies pubInputs (decode a) ha

/-- The main open representation theorem, named as a reusable proposition.

A proof must connect the current gate-polynomial predicate to the complete Clean
semantics.  Custom gates alone are insufficient: `Assignment.Satisfies` also contains
copy constraints, lookup membership/table contents, placement, environment assumptions,
and the public-instance identification.
-/
def GateToActionBridge {k : ℕ}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp)
    (deg : ℕ) (decode : Decoder k) (pubInputs : PublicInputs) : Prop :=
  ∀ a, circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a →
    ActionCircuitSat decode pubInputs a

/-- A proved gate-to-Action representation theorem discharges the exact `hencodes`
hypothesis used by the deployed constraint soundness capstones. -/
theorem gate_hencodes {G : Type*} [AddCommGroup G] [Module Fp G]
    {urs : URS G} {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp)
    (deg : ℕ) (decode : Decoder urs.k) (pubInputs : PublicInputs)
    (hbridge : GateToActionBridge fixedCols decodeAdvice decodeInstance y gates hpoly deg
      decode pubInputs) :
    ∀ a, SnarkRelation urs P b v
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a →
      ActionStatement pubInputs := by
  apply hencodes_of_circuitSat
  intro a ha
  exact actionStatement_of_satisfies pubInputs (decode a) (hbridge a ha)

/-- Blueprint capstone at the deployed Vesta verifier boundary.

This is `orchard_verifier_vesta_constraint_of_forked` with its free `S` fixed to
the concrete high-level Action statement and its `hencodes` argument discharged by
`gate_hencodes`.  The remaining hypotheses are upstream extraction/quotient facts
already visible in the existing capstone plus the named representation theorem
`hbridge`.
-/
theorem orchard_verifier_vesta_action_of_forked [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp)
    (deg : ℕ) (x : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (fs : ForkedTranscript urs hk vk ps ch b z blind)
    (hrel : IpaRelation urs fs.openedCommitment b (multiopenValue vk ps ch) a)
    (hquot : quotientCheck
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠
        hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates -
        hpoly * (X ^ deg - 1)).eval x ≠ 0)
    (decode : Decoder urs.k) (pubInputs : PublicInputs)
    (hbridge : GateToActionBridge fixedCols decodeAdvice decodeInstance y gates hpoly deg
      decode pubInputs) :
    ActionStatement pubInputs := by
  apply orchard_verifier_vesta_constraint_of_forked urs hk vk ps ch fixedCols
    decodeAdvice decodeInstance y gates hpoly deg x a fs hrel hquot hgood
  exact gate_hencodes fixedCols decodeAdvice decodeInstance y gates hpoly deg
    decode pubInputs hbridge

end Zcash.Snark.ActionCircuit
