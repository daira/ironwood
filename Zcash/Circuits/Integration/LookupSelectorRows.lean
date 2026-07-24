import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Integration.TopLevelLookups

/-!
# Lookup selector rows

Lookup projection only needs packed-selector values for selector leaves that occur
in the selected lookup's input expressions. Unrelated gate selectors may legitimately
be active at the same absolute row.

This module separates the proof-independent dense-row fact from the proof-dependent
fixed-polynomial binding step. The latter transports exact packed rows into the
resolver environment, preserving the caller's existing commitment-relation branch.
-/

namespace Zcash.Snark

open Halo2 Polynomial

set_option maxHeartbeats 20000

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

variable
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]

/-- A structural predicate over exactly the selector leaves of an expression. -/
def ExpressionSelectorLeavesSatisfy
    {F : Type} (predicate : Selector → Prop) :
    Expression F Query → Prop
  | .var (.selector selector) => predicate selector
  | .var _ => True
  | .const _ => True
  | .add left right =>
      ExpressionSelectorLeavesSatisfy predicate left ∧
        ExpressionSelectorLeavesSatisfy predicate right
  | .mul left right =>
      ExpressionSelectorLeavesSatisfy predicate left ∧
        ExpressionSelectorLeavesSatisfy predicate right

def decideExpressionSelectorLeavesSatisfy
    {F : Type} (predicate : Selector → Prop)
    [DecidablePred predicate] :
    (expression : Expression F Query) →
      Decidable (ExpressionSelectorLeavesSatisfy predicate expression)
  | .var (.selector selector) =>
      show Decidable (predicate selector) from inferInstance
  | .var (.fixed _ _) => isTrue trivial
  | .var (.advice _ _) => isTrue trivial
  | .var (.instance _ _) => isTrue trivial
  | .const _ => isTrue trivial
  | .add left right =>
      @instDecidableAnd
        (ExpressionSelectorLeavesSatisfy predicate left)
        (ExpressionSelectorLeavesSatisfy predicate right)
        (decideExpressionSelectorLeavesSatisfy predicate left)
        (decideExpressionSelectorLeavesSatisfy predicate right)
  | .mul left right =>
      @instDecidableAnd
        (ExpressionSelectorLeavesSatisfy predicate left)
        (ExpressionSelectorLeavesSatisfy predicate right)
        (decideExpressionSelectorLeavesSatisfy predicate left)
        (decideExpressionSelectorLeavesSatisfy predicate right)

instance expressionSelectorLeavesSatisfyDecidable
    {F : Type} (predicate : Selector → Prop)
    [DecidablePred predicate] (expression : Expression F Query) :
    Decidable (ExpressionSelectorLeavesSatisfy predicate expression) :=
  decideExpressionSelectorLeavesSatisfy predicate expression

/-- A pointwise stronger selector-leaf property implies a weaker one. -/
theorem ExpressionSelectorLeavesSatisfy.mono
    {F : Type} {first second : Selector → Prop}
    {expression : Expression F Query}
    (h : ExpressionSelectorLeavesSatisfy first expression)
    (hmono : ∀ selector, first selector → second selector) :
    ExpressionSelectorLeavesSatisfy second expression := by
  induction expression with
  | var query =>
      cases query with
      | selector selector =>
          exact hmono selector h
      | fixed column rotation =>
          trivial
      | advice column rotation =>
          trivial
      | «instance» column rotation =>
          trivial
  | const value =>
      trivial
  | add left right ihLeft ihRight =>
      exact ⟨ihLeft h.1, ihRight h.2⟩
  | mul left right ihLeft ihRight =>
      exact ⟨ihLeft h.1, ihRight h.2⟩

/--
Agreement on the selector leaves occurring in an expression is sufficient for
selector substitution to agree with a concrete selector valuation.
-/
theorem expression_eval_substValuation_eq_queryEval_of_selectorLeaves
    (map : SelCompressMap) (environment : Environment Fp)
    (selectors : ℕ → Fp) (row : ℤ)
    (expression : Expression Fp Query)
    (hagrees :
      ExpressionSelectorLeavesSatisfy (fun selector =>
        substValuation map.lookup
            (Query.eval environment (fun _ => 0) row)
            (.selector selector) =
          selectors selector.index) expression) :
    expression.eval
        (substValuation map.lookup
          (Query.eval environment (fun _ => 0) row)) =
      expression.eval
        (Query.eval environment selectors row) := by
  revert hagrees
  induction expression with
  | var query =>
      intro hagrees
      cases query with
      | selector selector =>
          exact hagrees
      | fixed column rotation =>
          rfl
      | advice column rotation =>
          rfl
      | «instance» column rotation =>
          rfl
  | const value =>
      intro hagrees
      rfl
  | add left right ihLeft ihRight =>
      intro hagrees
      exact congrArg₂ (· + ·)
        (ihLeft hagrees.1) (ihRight hagrees.2)
  | mul left right ihLeft ihRight =>
      intro hagrees
      exact congrArg₂ (· * ·)
        (ihLeft hagrees.1) (ihRight hagrees.2)

/--
Proof-independent dense-row selector facts, restricted to selector leaves that
actually occur in this lookup's input expressions.

The intended structural source is the selector compiler: lookup inputs contain only
complex selectors, selector kinds are consistent by allocated index, degree-zero
selectors receive singleton packed columns, and V1 placement isolates their activation
rows. Until those compiler laws are exposed, a concrete circuit may certify this small
finite property directly.
-/
def EnabledLookup.InputSelectorLeafRowsExact
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (rows : ℕ → List Fp) (lookup : EnabledLookup Fp) : Prop :=
  lookup.argument.inputs.Forall fun expression =>
    ExpressionSelectorLeavesSatisfy (fun selector =>
      match top.selectorMap.lookup selector.index with
      | none =>
          lookup.selectorValue selector.index = 0
      | some compressed =>
          compressed.packedCol < top.pinnedCS.numFixedColumns ∧
            (selReplacement compressed).eval
                (fun
                  | .fixed column _ =>
                      (rows column.index).getD
                        (top.placement lookup.region + lookup.row) 0
                  | _ => 0) =
              lookup.selectorValue selector.index) expression

instance EnabledLookup.inputSelectorLeafRowsExactDecidable
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (rows : ℕ → List Fp) (lookup : EnabledLookup Fp) :
    Decidable (lookup.InputSelectorLeafRowsExact top rows) := by
  let predicate : Selector → Prop := fun selector =>
    match top.selectorMap.lookup selector.index with
    | none =>
        lookup.selectorValue selector.index = 0
    | some compressed =>
        compressed.packedCol < top.pinnedCS.numFixedColumns ∧
          (selReplacement compressed).eval
              (fun
                | .fixed column _ =>
                    (rows column.index).getD
                      (top.placement lookup.region + lookup.row) 0
                | _ => 0) =
            lookup.selectorValue selector.index
  change Decidable (lookup.argument.inputs.Forall fun expression =>
    ExpressionSelectorLeavesSatisfy predicate expression)
  haveI : DecidablePred predicate := fun selector => by
    dsimp only [predicate]
    split <;> infer_instance
  infer_instance

omit [AddCommGroup G] [Module Fp G] [DecidableEq G] [Inhabited G] in
private theorem resolverFixedRead_of_rowPolynomial
    {shape : Shape} (urs : URS G)
    (vk : VerifyingKey shape Fp G)
    (poly : CommitmentId → Polynomial Fp)
    (rows : ℕ → List Fp)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) => vk.omega ^ (i : ℕ))
    (proofIndex : Fin shape.numProofs) (usableRows column row : ℕ)
    (hrow : row < 2 ^ urs.k)
    (hpolynomial :
      poly (.fixedCol column) =
        instanceRowPolynomial (2 ^ urs.k) vk.omega (rows column)) :
    (resolverEnvironment vk poly proofIndex usableRows).fixed
        ⟨column⟩ row =
      (rows column).getD row 0 := by
  rw [resolverEnvironment_fixed, hpolynomial]
  simpa using instanceRowPolynomial_eval hrows ⟨row, hrow⟩

omit [Module Fp G] [DecidableEq G] in
/--
Relevant exact packed rows and fixed-polynomial binding recover precisely the
expression-level selector boundary consumed by lookup projection.
-/
theorem EnabledLookup.inputSelectorValuesRealized_or_bad
    {top : TopLevelCircuit Fp ConfigInput Config Output}
    {pp : Keygen.ProofParams} {urs : URS G}
    (poly : CommitmentId → Polynomial Fp)
    (rows : ℕ → List Fp)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey pp urs).omega ^ (i : ℕ))
    (hn : (top.toVerifierKey pp urs).n = 2 ^ urs.k)
    {Bad : Prop}
    (binding : ∀ column,
      column < top.pinnedCS.numFixedColumns →
        poly (.fixedCol column) =
            instanceRowPolynomial (2 ^ urs.k)
              (top.toVerifierKey pp urs).omega (rows column) ∨
          Bad)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    (lookup : EnabledLookup Fp)
    (hrow :
      top.placement lookup.region + lookup.row <
        (top.toVerifierKey pp urs).n)
    (hexact : lookup.InputSelectorLeafRowsExact top rows) :
    lookup.InputSelectorValuesRealized top
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)) ∨
      Bad := by
  classical
  by_cases hbad : Bad
  · exact Or.inr hbad
  · apply Or.inl
    intro expression hexpression
    apply expression_eval_substValuation_eq_queryEval_of_selectorLeaves
    apply
      (List.forall_iff_forall_mem.mp hexact
        expression hexpression).mono
    intro selector hstatic
    cases hcompressed :
        top.selectorMap.lookup selector.index with
    | none =>
        rw [hcompressed] at hstatic
        simpa [Halo2.substValuation, hcompressed, Query.eval] using
          hstatic.symm
    | some compressed =>
        rw [hcompressed] at hstatic
        obtain ⟨hcolumn, hstatic⟩ := hstatic
        have hpolynomial :=
          (binding compressed.packedCol hcolumn).resolve_right hbad
        have hdomainRow :
            top.placement lookup.region + lookup.row < 2 ^ urs.k := by
          rwa [← hn]
        have hfixed :
            (resolverEnvironment
                (top.toVerifierKey pp urs) poly proofIndex
                (top.usableRowsAt top.domainExponent)).fixed
                ⟨compressed.packedCol⟩
                (top.placement lookup.region + lookup.row : ℕ) =
              (rows compressed.packedCol).getD
                (top.placement lookup.region + lookup.row) 0 := by
          exact resolverFixedRead_of_rowPolynomial
            urs (top.toVerifierKey pp urs) poly rows hrows proofIndex
            (top.usableRowsAt top.domainExponent) compressed.packedCol
            (top.placement lookup.region + lookup.row)
            hdomainRow hpolynomial
        rw [Halo2.substValuation, hcompressed]
        change
          (selReplacement compressed).eval
              (Query.eval
                (resolverEnvironment
                  (top.toVerifierKey pp urs) poly proofIndex
                  (top.usableRowsAt top.domainExponent))
                (fun _ => 0)
                (top.placement lookup.region + lookup.row)) =
            lookup.selectorValue selector.index
        rw [selReplacement_eval]
        rw [selReplacement_eval] at hstatic
        have hfixed' :
            (resolverEnvironment
                (top.toVerifierKey pp urs) poly proofIndex
                (top.usableRowsAt top.domainExponent)).fixed
                ⟨compressed.packedCol⟩
                ((top.placement lookup.region : ℤ) +
                  (lookup.row : ℤ) + 0) =
              (rows compressed.packedCol).getD
                (top.placement lookup.region + lookup.row) 0 := by
          simpa only [Int.natCast_add, add_zero] using hfixed
        simpa only [Query.eval, hfixed'] using hstatic

end Zcash.Snark
