import Zcash.Circuits.Action.TopLevel

/-!
# Public statement of a deployed Orchard Action

The proof-carrying circuit extracts its ten public instance rows as part of
`Circuit.ActionData`.  This module gives those rows a small external interface and
packages the circuit's proved `SpecPost` as an existential statement over exactly
that public data.
-/

namespace Zcash.Circuits.Action

open Halo2
open Specs.Sinsemilla (Generators)
open Circuit

/-- The ten field elements in one Orchard Action instance column, in row order. -/
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

namespace PublicInputs

@[ext] theorem ext
    {left right : PublicInputs}
    (anchor : left.anchor = right.anchor)
    (cvX : left.cvX = right.cvX)
    (cvY : left.cvY = right.cvY)
    (nfOld : left.nfOld = right.nfOld)
    (rkX : left.rkX = right.rkX)
    (rkY : left.rkY = right.rkY)
    (cmx : left.cmx = right.cmx)
    (enableSpend : left.enableSpend = right.enableSpend)
    (enableOutput : left.enableOutput = right.enableOutput)
    (disableCrossAddress :
      left.disableCrossAddress = right.disableCrossAddress) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Serialize the structured statement to the Action circuit's instance-column rows. -/
def rows (inputs : PublicInputs) : List Fp :=
  [inputs.anchor, inputs.cvX, inputs.cvY, inputs.nfOld, inputs.rkX,
    inputs.rkY, inputs.cmx, inputs.enableSpend, inputs.enableOutput,
    inputs.disableCrossAddress]

@[simp] theorem rows_length (inputs : PublicInputs) :
    inputs.rows.length = 10 :=
  rfl

/-- Project the public part of the circuit's extracted semantic witness. -/
def ofActionData (data : ActionData) : PublicInputs where
  anchor := data.anchor
  cvX := data.cvX
  cvY := data.cvY
  nfOld := data.nfOld
  rkX := data.rkX
  rkY := data.rkY
  cmx := data.cmx
  enableSpend := data.enableSpend
  enableOutput := data.enableOutput
  disableCrossAddress := data.disableCrossAddress

/-- Read the Action instance directly from the configured primary column. -/
def ofEnvironment (cfg : Config) (env : Environment Fp) : PublicInputs where
  anchor := env.inst cfg.primary (ANCHOR : ℤ)
  cvX := env.inst cfg.primary (CV_NET_X : ℤ)
  cvY := env.inst cfg.primary (CV_NET_Y : ℤ)
  nfOld := env.inst cfg.primary (NF_OLD : ℤ)
  rkX := env.inst cfg.primary (RK_X : ℤ)
  rkY := env.inst cfg.primary (RK_Y : ℤ)
  cmx := env.inst cfg.primary (CMX : ℤ)
  enableSpend := env.inst cfg.primary (ENABLE_SPEND : ℤ)
  enableOutput := env.inst cfg.primary (ENABLE_OUTPUT : ℤ)
  disableCrossAddress := env.inst cfg.primary (DISABLE_CROSS_ADDRESS : ℤ)

theorem ofActionData_extractPost
    (cfg : Config) (i : RegionIndex) (env : Placed Environment Fp) :
    ofActionData (extractPost cfg () i env) = ofEnvironment cfg env.env :=
  rfl

end PublicInputs

/--
The public semantic conclusion for one Action: the ten supplied instance values have
an extracted witness satisfying the complete post-NU6.3 Action specification.
-/
def Statement (G : Generators) (B : Bases) (inputs : PublicInputs) : Prop :=
  ∃ data : ActionData,
    PublicInputs.ofActionData data = inputs ∧
      SpecPost G B () () data

/--
The generic top-level circuit statement specializes to the externally named Action
statement.  Instance-polynomial provenance is deliberately separate: it only has to
identify `PublicInputs.ofEnvironment` with the values supplied to the verifier.
-/
theorem statement_of_topLevelStatement
    (G : Generators) (B : Bases)
    (top : TopLevelCircuit Fp Unit Config unit)
    (hformalCircuit : top.formalCircuit = circuit G B)
    (i : RegionIndex) (env : Placed Environment Fp)
    (h : top.Statement i env) :
    Statement G B (PublicInputs.ofEnvironment (configure G {}).1 env.env) := by
  have hconfigInput : top.configInput = () :=
    Subsingleton.elim _ _
  simp only [TopLevelCircuit.Statement, TopLevelCircuit.config] at h
  rw [hformalCircuit, hconfigInput] at h
  refine ⟨extractPost (configure G {}).1 () i env, rfl, ?_⟩
  exact h

end Zcash.Circuits.Action
