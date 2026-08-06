import Zcash.Snark.Soundness.AGM.AdaptiveOnline

/-!
# Costed adaptive oracle computations

`LabeledOracleComp` deliberately records only random-oracle interaction.  This module adds a
small, erasable accounting language for the other finite resource used by the concrete AGM
endpoints: Vesta group work.  A group node is an explicit audit event; erasure removes those
events and leaves exactly the original labeled oracle tree.

The cost rules count an addition, negation, scalar multiplication, or equality test as one group
operation.  An MSM node records its already-expanded number of group operations.  This matches
the convention used by `AssembleGroupCost`: fixed-generator sweeps and accumulated MSM terms are
charged explicitly, while field and list work are kept in their separate models.

The language does not narrow the oracle-control class: `ofLabeled` embeds every
`LabeledOracleComp`, and `erase_ofLabeled` proves that erasure is onto.  That embedding is not a
cost certificate for opaque group work hidden in an existing Lean term.  A finite-work endpoint
accepts a program written with the explicit group nodes and a structural `GroupWorkBound` proof;
this is the modeling boundary that makes the work premise machine-checkable.
-/

namespace Zcash.Snark

/-- Primitive Vesta work events used by the concrete accounting language. -/
inductive VestaGroupOperation where
  | add
  | neg
  | scalarMul
  | equality
  | additions (operations : Nat)
  | negations (operations : Nat)
  | scalarMultiplications (operations : Nat)
  | equalities (operations : Nat)
  | msm (operations : Nat)
deriving DecidableEq, Repr

namespace VestaGroupOperation

/-- Concrete cost of one reified Vesta operation. -/
def cost : VestaGroupOperation → Nat
  | .add | .neg | .scalarMul | .equality => 1
  | .additions operations | .negations operations | .scalarMultiplications operations
  | .equalities operations | .msm operations => operations

@[simp] theorem cost_add : cost .add = 1 := rfl
@[simp] theorem cost_neg : cost .neg = 1 := rfl
@[simp] theorem cost_scalarMul : cost .scalarMul = 1 := rfl
@[simp] theorem cost_equality : cost .equality = 1 := rfl
@[simp] theorem cost_additions (operations : Nat) : cost (.additions operations) = operations := rfl
@[simp] theorem cost_negations (operations : Nat) : cost (.negations operations) = operations := rfl
@[simp] theorem cost_scalarMultiplications (operations : Nat) :
    cost (.scalarMultiplications operations) = operations := rfl
@[simp] theorem cost_equalities (operations : Nat) :
    cost (.equalities operations) = operations := rfl
@[simp] theorem cost_msm (operations : Nat) : cost (.msm operations) = operations := rfl

end VestaGroupOperation

/-- A finite audit trace of Vesta operations. -/
abbrev VestaGroupTrace := List VestaGroupOperation

namespace VestaGroupTrace

/-- Total group work recorded by a trace. -/
def work (trace : VestaGroupTrace) : Nat :=
  (trace.map VestaGroupOperation.cost).sum

@[simp] theorem work_nil : work [] = 0 := rfl

@[simp] theorem work_cons (op : VestaGroupOperation) (trace : VestaGroupTrace) :
    work (op :: trace) = op.cost + work trace := by
  simp [work]

@[simp] theorem work_append (left right : VestaGroupTrace) :
    work (left ++ right) = work left + work right := by
  simp [work]

end VestaGroupTrace

/-- A labeled adaptive oracle computation interleaved with explicit Vesta-work events.  Group
events carry no oracle-visible data and disappear under `erase`. -/
inductive CostedLabeledOracleComp (T F : Type*) (Label : T → Type*) (α : Type*) where
  | pure (a : α)
  | query (t : T) (label : Label t)
      (k : F → CostedLabeledOracleComp T F Label α)
  | group (op : VestaGroupOperation) (next : CostedLabeledOracleComp T F Label α)

namespace CostedLabeledOracleComp

variable {T F α β : Type*} {Label : T → Type*}

/-- Forget group-accounting nodes, preserving the exact labeled random-oracle computation. -/
def erase : CostedLabeledOracleComp T F Label α → LabeledOracleComp T F Label α
  | .pure a => .pure a
  | .query t label k => .query t label (fun answer => (k answer).erase)
  | .group _ next => next.erase

/-- Run the erased computation against an ordinary oracle table. -/
def run (A : CostedLabeledOracleComp T F Label α) (O : T → F) : α :=
  A.erase.run O

/-- Group work on the adaptive path selected by one oracle table. -/
def groupWork : CostedLabeledOracleComp T F Label α → (T → F) → Nat
  | .pure _, _ => 0
  | .query t _ k, O => (k (O t)).groupWork O
  | .group op next, O => op.cost + next.groupWork O

/-- A structural worst-case group-work certificate. -/
def GroupWorkBound (A : CostedLabeledOracleComp T F Label α) (bound : Nat) : Prop :=
  ∀ O, A.groupWork O ≤ bound

/-- Sequence two costed computations. -/
def bind : CostedLabeledOracleComp T F Label α →
    (α → CostedLabeledOracleComp T F Label β) →
      CostedLabeledOracleComp T F Label β
  | .pure a, f => f a
  | .query t label k, f => .query t label (fun answer => (k answer).bind f)
  | .group op next, f => .group op (next.bind f)

/-- Apply a pure function without changing either oracle or group accounting. -/
def map (f : α → β) (A : CostedLabeledOracleComp T F Label α) :
    CostedLabeledOracleComp T F Label β :=
  A.bind (fun a => .pure (f a))

/-- Record one group operation before continuing. -/
def charge (op : VestaGroupOperation) (A : CostedLabeledOracleComp T F Label α) :
    CostedLabeledOracleComp T F Label α :=
  .group op A

/-- Reified Vesta addition. -/
def vestaAdd (left right : VestaG) : CostedLabeledOracleComp T F Label VestaG :=
  .group .add (.pure (left + right))

/-- Reified Vesta negation. -/
def vestaNeg (point : VestaG) : CostedLabeledOracleComp T F Label VestaG :=
  .group .neg (.pure (-point))

/-- Reified Vesta scalar multiplication. -/
def vestaScalarMul (scalar : Fp) (point : VestaG) :
    CostedLabeledOracleComp T F Label VestaG :=
  .group .scalarMul (.pure (scalar • point))

/-- Reified Vesta equality test. -/
def vestaEq (left right : VestaG) : CostedLabeledOracleComp T F Label Bool :=
  .group .equality (.pure (decide (left = right)))

/-- Reified Vesta MSM.  `operations` is the expanded cost certified by the caller's structural
MSM theorem; the value is the ordinary mathematical sum. -/
def vestaMsm (operations : Nat) (terms : List (Fp × VestaG)) :
    CostedLabeledOracleComp T F Label VestaG :=
  .group (.msm operations) (.pure ((terms.map fun term => term.1 • term.2).sum))

@[simp] theorem erase_pure (a : α) :
    (pure a : CostedLabeledOracleComp T F Label α).erase = .pure a := rfl

@[simp] theorem erase_query (t : T) (label : Label t)
    (k : F → CostedLabeledOracleComp T F Label α) :
    (query t label k).erase = .query t label (fun answer => (k answer).erase) := rfl

@[simp] theorem erase_group (op : VestaGroupOperation)
    (next : CostedLabeledOracleComp T F Label α) :
    (group op next).erase = next.erase := rfl

@[simp] theorem erase_bind (A : CostedLabeledOracleComp T F Label α)
    (f : α → CostedLabeledOracleComp T F Label β) :
    (A.bind f).erase = A.erase.bind (fun a => (f a).erase) := by
  induction A with
  | pure => rfl
  | query t label k ih =>
      simp only [bind, erase, LabeledOracleComp.bind]
      congr
      funext answer
      exact ih answer
  | group op next ih =>
      simpa only [bind, erase] using ih

@[simp] theorem run_pure (a : α) (O : T → F) :
    (pure a : CostedLabeledOracleComp T F Label α).run O = a := rfl

@[simp] theorem run_query (t : T) (label : Label t)
    (k : F → CostedLabeledOracleComp T F Label α) (O : T → F) :
    (query t label k).run O = (k (O t)).run O := rfl

@[simp] theorem run_group (op : VestaGroupOperation)
    (next : CostedLabeledOracleComp T F Label α) (O : T → F) :
    (group op next).run O = next.run O := rfl

@[simp] theorem run_bind (A : CostedLabeledOracleComp T F Label α)
    (f : α → CostedLabeledOracleComp T F Label β) (O : T → F) :
    (A.bind f).run O = (f (A.run O)).run O := by
  simp only [run, erase_bind, LabeledOracleComp.run_bind]

@[simp] theorem groupWork_pure (a : α) (O : T → F) :
    (pure a : CostedLabeledOracleComp T F Label α).groupWork O = 0 := rfl

@[simp] theorem groupWork_query (t : T) (label : Label t)
    (k : F → CostedLabeledOracleComp T F Label α) (O : T → F) :
    (query t label k).groupWork O = (k (O t)).groupWork O := rfl

@[simp] theorem groupWork_group (op : VestaGroupOperation)
    (next : CostedLabeledOracleComp T F Label α) (O : T → F) :
    (group op next).groupWork O = op.cost + next.groupWork O := rfl

@[simp] theorem groupWork_bind (A : CostedLabeledOracleComp T F Label α)
    (f : α → CostedLabeledOracleComp T F Label β) (O : T → F) :
    (A.bind f).groupWork O = A.groupWork O + (f (A.run O)).groupWork O := by
  induction A with
  | pure a => simp only [bind, groupWork, run_pure, Nat.zero_add]
  | query t label k ih =>
      simpa only [bind, groupWork, run_query] using ih (O t)
  | group op next ih =>
      simp only [bind, groupWork, run_group, ih, Nat.add_assoc]

@[simp] theorem groupWork_vestaAdd (left right : VestaG) (O : T → F) :
    (vestaAdd (T := T) (F := F) (Label := Label) left right).groupWork O = 1 := by
  simp [vestaAdd]

@[simp] theorem groupWork_vestaNeg (point : VestaG) (O : T → F) :
    (vestaNeg (T := T) (F := F) (Label := Label) point).groupWork O = 1 := by
  simp [vestaNeg]

@[simp] theorem groupWork_vestaScalarMul (scalar : Fp) (point : VestaG) (O : T → F) :
    (vestaScalarMul (T := T) (F := F) (Label := Label) scalar point).groupWork O = 1 := by
  simp [vestaScalarMul]

@[simp] theorem groupWork_vestaEq (left right : VestaG) (O : T → F) :
    (vestaEq (T := T) (F := F) (Label := Label) left right).groupWork O = 1 := by
  simp [vestaEq]

@[simp] theorem groupWork_vestaMsm (operations : Nat) (terms : List (Fp × VestaG))
    (O : T → F) :
    (vestaMsm (T := T) (F := F) (Label := Label) operations terms).groupWork O =
      operations := by
  simp [vestaMsm]

/-- Embed an existing labeled oracle tree without changing its oracle behavior.  Group work in
the old result/continuations is opaque, so this is an expressiveness theorem, not a cost proof. -/
def ofLabeled : LabeledOracleComp T F Label α → CostedLabeledOracleComp T F Label α
  | .pure a => .pure a
  | .query t label k => .query t label (fun answer => ofLabeled (k answer))

@[simp] theorem erase_ofLabeled (A : LabeledOracleComp T F Label α) :
    (ofLabeled A).erase = A := by
  induction A with
  | pure => rfl
  | query t label k ih =>
      simp only [ofLabeled, erase]
      congr
      funext answer
      exact ih answer

/-- Every labeled adaptive oracle computation is the erasure of a costed computation. -/
theorem erase_surjective (A : LabeledOracleComp T F Label α) :
    ∃ costed : CostedLabeledOracleComp T F Label α, costed.erase = A :=
  ⟨ofLabeled A, erase_ofLabeled A⟩

@[simp] theorem groupWork_ofLabeled (A : LabeledOracleComp T F Label α) (O : T → F) :
    (ofLabeled A).groupWork O = 0 := by
  induction A with
  | pure => rfl
  | query t label k ih =>
      simpa only [ofLabeled, groupWork] using ih (O t)

/-- A costed program certified to erase to one existing labeled adversary. -/
structure Certificate (A : LabeledOracleComp T F Label α) (bound : Nat) where
  program : CostedLabeledOracleComp T F Label α
  erase_eq : program.erase = A
  workBound : program.GroupWorkBound bound

namespace Certificate

theorem run_eq {A : LabeledOracleComp T F Label α} {bound : Nat}
    (certificate : Certificate A bound) (O : T → F) :
    certificate.program.run O = A.run O := by
  unfold CostedLabeledOracleComp.run
  rw [certificate.erase_eq]

theorem groupWork_le {A : LabeledOracleComp T F Label α} {bound : Nat}
    (certificate : Certificate A bound) (O : T → F) :
    certificate.program.groupWork O ≤ bound :=
  certificate.workBound O

end Certificate

end CostedLabeledOracleComp
end Zcash.Snark
