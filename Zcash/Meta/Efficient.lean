import Lean

/-!
# `efficient def` — a cost function derived from a definition (prototype)

A security reduction has to be more than computable. The adversary that it builds against an
assumption must run in time bounded by the adversary that it is given. Otherwise the reduction
transfers nothing. `assert_computable` (`Zcash.Meta.AxiomCheck`) checks the first half, that the
reduction is a plain `def` that does not reach any choice principle. This module is a prototype of
the second half.

`efficient def f (binders) : α := body` elaborates `f` as an ordinary definition and then derives
`f.cost (binders) : Nat`, a running-time function in the style of Isabelle's `time_fun` command:

* every call of a function with a registered cost function costs that function's cost at the
  actual arguments, plus one for the call;
* a recursive call costs `f.cost` at the actual arguments, plus one, so `f.cost` recurses as `f`
  does and reuses the same termination argument;
* every `if` and every `match` costs one for the decision, and then the cost of the branch taken;
* constructors, literals, projections and local variables are free beyond the cost of their
  arguments;
* a call of anything else is an error, exactly as an unexpected axiom is for `assert_computable`:
  mark it `efficient`, or register a cost function for it with `efficient_cost`.

Isabelle's `time_fun` is defined in HOL-Library's `Time_Commands` theory and applied to the
standard library in its `Time_Functions` theory:
<https://isabelle.in.tum.de/library/HOL/HOL-Data_Structures/HOL-Library.Time_Functions.html>.

The derived function is a definition like any other: `#eval` runs it, `simp [f.cost]` unfolds it,
and a bound `f.cost xs ≤ 3 * xs.length + 1` is an ordinary theorem, usually by induction.
`assert_efficient f` is defined beside `assert_computable` in `Zcash.Meta.AxiomCheck`. It fails the
build unless `f` passes the computability checks and has a derived or registered cost function. This
module itself imports only `Lean`, so the cost machinery can be used on its own.

Prototype restrictions, in the order in which they are likely to be lifted:

* the definition is written with explicit binders, a return type, and `:= body`, not as
  pattern-matching equations;
* functions are first order: a lambda or a local function passed as an argument is costed as free
  data, and applying a local function is an error;
* the cost is a single `Nat`, with no separate budget for group operations; and
* no bound is synthesized or proved automatically.
-/

open Lean Elab Command Meta Term

namespace Zcash.Meta.Efficient

/-- A registered cost function. `cost` takes exactly the binders of `fn` and returns `Nat`. -/
structure CostEntry where
  fn : Name
  cost : Name
  deriving Inhabited, Repr

/-- The registry of cost functions, derived by `efficient def` or declared by `efficient_cost`. -/
initialize costExt : SimplePersistentEnvExtension CostEntry (NameMap CostEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m e => m.insert e.fn e
    addImportedFn := fun ess => ess.foldl (fun m es => es.foldl (fun m e => m.insert e.fn e) m) {}
  }

/-- The cost function registered for `fn`, if any. -/
def costFn? (env : Environment) (fn : Name) : Option Name :=
  ((costExt.getState env).find? fn).map (·.cost)

/-- Constants whose applications cost nothing beyond their arguments: numerals and casts. -/
def freeConstants : Array Name := #[``OfNat.ofNat, ``Nat.cast, ``id]

/-- The function whose cost is being derived, and the local variable standing for its cost function
while that is being defined (`none` for a non-recursive definition). -/
structure Context where
  fn : Name
  recFVar : Option Expr

private def natLit (n : Nat) : Expr := mkNatLit n

/-- `a + b` over `Nat`, dropping zero summands. -/
private def add (a b : Expr) : MetaM Expr := do
  if a == natLit 0 then return b
  if b == natLit 0 then return a
  mkAppM ``HAdd.hAdd #[a, b]

/-- Whether an argument carries data that the cost should account for: not a type, a proof, or an
instance. -/
private def isDataArg (a : Expr) : MetaM Bool := do
  let t ← inferType a
  if t.isSort then return false
  if ← isProp t then return false
  if (← isClass? t).isSome then return false
  return true

/-- The derived cost of `e`, an expression of `Nat`. -/
partial def costOf (ctx : Context) (e : Expr) : MetaM Expr := do
  match e with
  | .mdata _ b => costOf ctx b
  | .proj _ _ s => costOf ctx s
  | .letE n t v b _ =>
    let cv ← costOf ctx v
    let cb ← withLetDecl n t v fun x => do
      mkLetFVars #[x] (← costOf ctx (b.instantiate1 x))
    add cv cb
  | .app .. => costApp e
  | _ => return natLit 0
where
  /-- The summed cost of the data arguments. -/
  argsCost (args : Array Expr) : MetaM Expr := do
    let mut acc := natLit 0
    for a in args do
      if ← isDataArg a then
        acc ← add acc (← costOf ctx a)
    return acc
  costApp (e : Expr) : MetaM Expr := do
    if let some m ← matchMatcherApp? e then
      unless m.remaining.isEmpty do
        throwError "efficient: a `match` that returns a function is not supported yet"
      let discrs ← argsCost m.discrs
      let m' ← m.transform
        (onMotive := fun _ _ => pure (mkConst ``Nat))
        (onAlt := fun _ _ _ alt => costOf ctx alt)
      return ← add (← add (natLit 1) discrs) m'.toExpr
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const c _ =>
      if c == ``ite && args.size == 5 then
        let ct ← costOf ctx args[3]!
        let ce ← costOf ctx args[4]!
        return ← add (natLit 1)
          (mkApp5 (mkConst ``ite [Level.one]) (mkConst ``Nat) args[1]! args[2]! ct ce)
      if c == ``dite && args.size == 5 then
        let branch (b : Expr) : MetaM Expr := lambdaTelescope b fun xs body => do
          mkLambdaFVars xs (← costOf ctx body)
        let ct ← branch args[3]!
        let ce ← branch args[4]!
        return ← add (natLit 1)
          (mkApp5 (mkConst ``dite [Level.one]) (mkConst ``Nat) args[1]! args[2]! ct ce)
      let inner ← argsCost args
      if c == ctx.fn then
        let some recFVar := ctx.recFVar
          | throwError "efficient: '{c}' calls itself, but no cost function is being defined for it"
        return ← add (← add (natLit 1) inner) (mkAppN recFVar args)
      let env ← getEnv
      if let some costName := costFn? env c then
        let call ← mkAppOptM costName (args.map some)
        return ← add (← add (natLit 1) inner) call
      -- A projection of a plain structure is free; a class method is a projection too, but it
      -- stands for an operation and must have a registered cost.
      let plainProjection := match env.getProjectionFnInfo? c with
        | some info => !info.fromClass
        | none => false
      if env.isConstructor c || freeConstants.contains c || plainProjection then
        return inner
      throwError "efficient: '{c}' has no cost function. Mark its definition `efficient`, or \
        register a cost function for it with `efficient_cost {c} := <cost function>`."
    | .fvar _ =>
      throwError "efficient: applying a local function ({f}) is not supported yet; the cost of \
        a higher-order argument has to be given symbolically"
    | _ => throwError "efficient: unsupported application head {f}"

/-- `efficient_cost% f body` elaborates `body` and produces its derived cost, with recursive calls
of `f` charged to the cost function being defined. -/
syntax (name := efficientCostTerm) "efficient_cost% " ident ppSpace term : term

@[term_elab efficientCostTerm] def elabEfficientCost : TermElab := fun stx _ => do
  let fn ← realizeGlobalConstNoOverloadWithInfo stx[1]
  let body ← elabTerm stx[2] none
  synthesizeSyntheticMVarsNoPostponing
  let body ← instantiateMVars body
  let costName := fn ++ `cost
  let lctx ← getLCtx
  let recFVar := lctx.decls.toList.findSome? fun d? => do
    let d ← d?
    guard d.isAuxDecl
    guard (lctx.auxDeclToFullName.get? d.fvarId == some costName)
    return d.toExpr
  -- Report a rejected call at the body, not at the synthesized cost definition.
  withRef stx[2][1] <| costOf { fn, recFVar } body

/-- `efficient_cost f := c` registers `c` as the cost function of `f`. `c` must take exactly the
binders of `f` and return `Nat`; it is checked against `f`'s type at every call that it prices. -/
syntax (name := efficientCostCmd) "efficient_cost " ident " := " ident : command

@[command_elab efficientCostCmd] def elabEfficientCostCmd : CommandElab := fun stx => do
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let cost ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[3]
  modifyEnv (costExt.addEntry · { fn, cost })

/-- `efficient def f (binders) : α := body` defines `f` and derives `f.cost`. The termination
suffix, if any, is copied to the cost function, which recurses exactly as `f` does. Modifiers
(a doc comment, attributes, `private`) go before `efficient`, as on a plain `def`. -/
syntax (name := efficientDef)
  declModifiers "efficient " Lean.Parser.Command.definition : command

@[command_elab efficientDef] def elabEfficientDef : CommandElab := fun stx => do
  let inner := stx[2]
  let decl : Syntax := (mkNode ``Lean.Parser.Command.declaration #[stx[0], inner]).raw
  -- `definition := "def " declId optDeclSig declVal (deriving)?`
  let declId := inner[1]
  let sig := inner[2]
  let declVal := inner[3]
  unless declVal.getKind == ``Lean.Parser.Command.declValSimple do
    throwErrorAt declVal "efficient (prototype): write the body as `:= term`, with explicit \
      binders, rather than as pattern-matching equations"
  if sig[1].getNumArgs == 0 then
    throwErrorAt sig "efficient (prototype): give the definition's return type"
  elabCommand decl
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo declId[0]
  -- The cost definition: the same binders, returning `Nat`, with the body replaced by its cost.
  let costId := mkIdentFrom declId[0] (declId[0].getId ++ `cost)
  let ty := sig[1][0][1]
  let body := declVal[1]
  let fullId := mkIdentFrom declId[0] (rootNamespace ++ fn)
  let costBody ← `(efficient_cost% $fullId ($(⟨body⟩) : $(⟨ty⟩)))
  let natTy ← `(Nat)
  let newSig := sig.setArg 1 (sig[1].setArg 0 (sig[1][0].setArg 1 natTy))
  let newDeclVal := declVal.setArg 1 costBody
  let newInner := (inner.setArg 1 (declId.setArg 0 costId)).setArg 2 newSig |>.setArg 3 newDeclVal
  -- `declModifiers` is six optional pieces: doc comment, attributes, visibility, `noncomputable`,
  -- `unsafe`, and `partial`/`nonrec`; the cost function takes none of the original's.
  let emptyMods := mkNode ``Lean.Parser.Command.declModifiers
    #[mkNullNode, mkNullNode, mkNullNode, mkNullNode, mkNullNode, mkNullNode]
  let newDecl := (decl.setArg 1 newInner).setArg 0 emptyMods
  -- Elaborate the cost function under its own message log. Term elaboration recovers from an error
  -- in the cost body with `sorry`, so the definition exists either way. Only the log shows whether
  -- it is real. On an error, `f` stays defined but unregistered, so `assert_efficient f` fails.
  let saved := (← get).messages
  modify fun s => { s with messages := {} }
  elabCommand newDecl
  let msgs := (← get).messages
  modify fun s => { s with messages := saved ++ msgs }
  let costName := fn ++ `cost
  if !msgs.hasErrors && (← getEnv).contains costName then
    modifyEnv (costExt.addEntry · { fn, cost := costName })

end Zcash.Meta.Efficient
