import Clean.Halo2.Formal

/-!
# Closed top-level formal circuits

`FormalCircuit` is the compositional interface: a child may require environment facts
from its parent.  A deployed circuit needs one additional boundary.  Its configuration,
operation stream, placement, and domain must describe a successful synthesis, and its
own setup operations must discharge every environment fact required by its children.

`TopLevelCircuit` records that boundary without adding those facts to the circuit's
public input or verifier assumptions.
-/

namespace Zcash.Circuits

open Halo2

/--
Generic well-formedness facts supplied by successful synthesis/layout rather than by
the proof's constraint polynomials.

The first required fact is table fit: every declared table's explicit block lies in
the usable rows.  Further compiler invariants (for example region bounds) belong in
this same structure when the operation semantics begins consuming them.
-/
structure SynthesisWellFormed
    {F : Type} [FiniteField F]
    (env : Environment F) (operations : Operations F) : Prop where
  tablesFit :
    ∀ (table : TableColumn) (values : List F),
      .loadTable table values ∈ operations →
      values.length ≤ env.usableRows

/--
A configured, unit-input formal circuit whose verifier assumptions are exactly
`True`, and whose own successful synthesis discharges its compositional environment
requirements.

The two closure fields correspond to the verifier and honest-prover views.  They are
separate because `Constraints` and `ExtendsWitnesses` expose the fixed/table data
through different predicates.
-/
structure TopLevelCircuit
    (F : Type) [FiniteField F]
    (ConfigInput Config : Type) (Output : TypeMap)
    [CircuitType Output] where
  formalCircuit : FormalCircuit F ConfigInput Config unit Output
  configInput : ConfigInput
  assumptions_eq : formalCircuit.Assumptions = fun _ => True
  closesEnvironmentSoundness :
    let config := (formalCircuit.configure configInput {}).1
    ∀ (i : RegionIndex) (env : Placed Environment F),
      SynthesisWellFormed env.env
        ((formalCircuit.synthesize config ()).operations i) →
      Constraints env.place env.env
        ((formalCircuit.synthesize config ()).operations i) i →
      formalCircuit.EnvAssumptions config env
  closesEnvironmentCompleteness :
    let config := (formalCircuit.configure configInput {}).1
    ∀ (i : RegionIndex) (env : Placed ProverEnvironment F),
      SynthesisWellFormed env.toEnvironment.env
        ((formalCircuit.synthesize config ()).operations i) →
      ExtendsWitnesses env.place env.env
        ((formalCircuit.synthesize config ()).operations i) i →
      formalCircuit.EnvAssumptions config env.toEnvironment

namespace TopLevelCircuit

variable
    {F : Type} [FiniteField F]
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]

/-- The configuration produced by the top-level circuit's own configure run. -/
def config (self : TopLevelCircuit F ConfigInput Config Output) : Config :=
  (self.formalCircuit.configure self.configInput {}).1

/-- The constraint system produced by that same configure run. -/
def constraintSystem (self : TopLevelCircuit F ConfigInput Config Output) :
    ConstraintSystem F :=
  (self.formalCircuit.configure self.configInput {}).2

/-- The closed top-level operation stream. -/
def operations (self : TopLevelCircuit F ConfigInput Config Output)
    (i : RegionIndex := 0) : Operations F :=
  (self.formalCircuit.synthesize self.config ()).operations i

/--
Generic verifier-side top-level soundness.  The public theorem consumes successful
synthesis/layout and the circuit constraints, but no circuit-specific environment or
input assumption.
-/
theorem soundness
    (self : TopLevelCircuit F ConfigInput Config Output)
    (i : RegionIndex) (env : Placed Environment F)
    (hwellFormed : SynthesisWellFormed env.env (self.operations i))
    (hconstraints : Constraints env.place env.env (self.operations i) i) :
    self.formalCircuit.Spec
      (eval env (show Var unit F from ()))
      (eval env (self.formalCircuit.output self.config () i))
      (self.formalCircuit.extract self.config () i env) := by
  apply self.formalCircuit.soundness self.config i env ()
  · exact self.closesEnvironmentSoundness i env hwellFormed hconstraints
  · rw [self.assumptions_eq]
    trivial
  · exact hconstraints

/--
Generic honest-prover top-level completeness.  As on the verifier side, successful
synthesis/layout closes the environment contract internally.
-/
theorem completeness
    (self : TopLevelCircuit F ConfigInput Config Output)
    (i : RegionIndex) (env : Placed ProverEnvironment F)
    (hwitnesses : ExtendsWitnesses env.place env.env (self.operations i) i)
    (hwellFormed : SynthesisWellFormed env.toEnvironment.env (self.operations i))
    (hprover : self.formalCircuit.ProverAssumptions
      (eval env (show Var unit F from ()))
      (self.formalCircuit.extract self.config () i env.toEnvironment)
      env.env.hint) :
    Constraints env.place env.toEnvironment.env (self.operations i) i ∧
      self.formalCircuit.ProverSpec
        (eval env (show Var unit F from ()))
        (eval env (self.formalCircuit.output self.config () i))
        (self.formalCircuit.extract self.config () i env.toEnvironment)
        env.env.hint := by
  apply self.formalCircuit.completeness self.config i env ()
  · exact hwitnesses
  · exact self.closesEnvironmentCompleteness i env hwellFormed hwitnesses
  · rw [self.assumptions_eq]
    trivial
  · exact hprover

end TopLevelCircuit

end Zcash.Circuits
