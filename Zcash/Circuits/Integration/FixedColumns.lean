import Zcash.Snark.Soundness.Canonical.InstanceCommitment
import Zcash.Circuits.Integration.FixedLayout
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Zcash.Circuits.Integration.SelectorCoherence
import Zcash.Circuits.Integration.OperationLookups
import Zcash.Snark.Keygen.Lagrange

/-!
# Fixed-column commitment provenance

The verifier's fixed columns are commitments in the verifying key, while the
multiopen extractor returns augmented monomial-basis openings. This module crosses
that representation boundary without assuming commitment binding: a routed decoded
fixed polynomial is the keygen row polynomial, or the two openings compute a
nontrivial relation among the augmented URS generators.

The result is generic in the fixed row vector and its Lagrange commitment key.
`TopLevelCircuit` keygen supplies those vectors; the Action endpoint only selects
the circuit-owned instance.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (derivedUrsGLagrange)
open Halo2 Polynomial
open CompElliptic.Curves.Pasta

set_option maxHeartbeats 20000

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

omit [AddCommGroup G] [Module Fp G] [DecidableEq G] in
/--
A fixed-column entry in the accepted key's query layout produces the assembled
query used by canonical member routing.
-/
theorem fixedQuery_of_layout
    {shape : Shape}
    (vk : VerifyingKey shape Fp G)
    (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp)
    (column : ℕ) (rotation : ℤ)
    (hcount :
      vk.fixedQueryLayout.length = shape.numFixedQueries)
    (hlayout : (column, rotation) ∈ vk.fixedQueryLayout) :
    ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = .fixedCol column := by
  obtain ⟨queryIndex, hqueryIndex, hentry⟩ :=
    List.mem_iff_getElem.mp hlayout
  have hevalIndex :
      queryIndex < (List.ofFn ps.fixedEvals).length := by
    simpa only [List.length_ofFn, ← hcount] using hqueryIndex
  obtain ⟨q, hq, hqid, -⟩ :=
    columnQueries_layout_mem
      (k' := shape.k) vk.omega ch.x vk.fixedCommitment
      CommitmentId.fixedCol vk.fixedQueryLayout
      (List.ofFn ps.fixedEvals) hqueryIndex hevalIndex
  refine ⟨q, ?_, ?_⟩
  · simp only [assembleQueries, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hq))
  · rw [List.getD_eq_getElem _ _ hqueryIndex, hentry] at hqid
    exact hqid

/-- Sparse table and region-local fixed assignments emitted by top-level keygen. -/
def topLevelFixedOperationEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (ℕ × ℕ × ℕ) :=
  Layout.tableFixed (ZMod.val : Fp → ℕ)
      (top.usableRowsAt top.domainExponent) (top.operations 0) ++
    Layout.regionAssignFixed (ZMod.val : Fp → ℕ)
      top.regionStarts (indexedRegions (top.operations 0) 0).1

/--
Sparse packed-selector assignments emitted by top-level keygen.

The current full-circuit realization check also fails closed if two selector
activations assign incompatible values to the same packed cell: the final dense
cell cannot realize both sparse entries. That failure is intentionally safe but
opaque. The structural replacement should instead derive non-overlap (or compatible
composition) from selector packing and region-placement invariants.
-/
def topLevelSelectorEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (ℕ × ℕ × ℕ) :=
  Layout.selectorFixed top.selectorMap top.selectorActivations

/--
Expected dense cells for lookup-relevant selectors that the selector compiler packed
alone at root one. Enabled leaves read one; disabled leaves read zero.

A missing or non-singleton map entry emits an out-of-bounds sentinel, so realization
of this interim list also rules those malformed cases out. This encoding relies on
the strict `column < numFixedColumns` check in `interimFixedRealizationFailures`;
widening or removing that bound would silently turn malformed selector mappings into
accepted zero entries. The structural replacement derives singleton ownership and
disabled-row zero from compiler invariants instead.
-/
def topLevelSingletonLookupSelectorEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (ℕ × ℕ × ℕ) :=
  let operations := top.operations 0
  let selectorMap := top.selectorMap
  let starts := top.regionStarts
  (operationEnabledLookups operations 0).flatMap fun lookup =>
    lookup.inputSelectorLeaves.filterMap fun selector =>
      match selectorMap.lookup selector.index with
      | some compressed =>
          if compressed.combinationLen = 1 ∧
              compressed.assignedRoot = 1 then
            some
              (compressed.packedCol,
                starts.getD lookup.region 0 + lookup.row,
                if lookup.enabled.any
                    (fun candidate =>
                      candidate.index == selector.index) then
                  1
                else
                  0)
          else
            some
              (top.pinnedCS.numFixedColumns,
                starts.getD lookup.region 0 + lookup.row, 0)
      | none =>
          some
            (top.pinnedCS.numFixedColumns,
              starts.getD lookup.region 0 + lookup.row, 0)

/-- Fixed cells allocated for `constrainConstant` values by the V1 floor planner. -/
def topLevelConstantEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (ℕ × ℕ × ℕ) :=
  Layout.constantsFixed
    (Keygen.constantsOf top.constraintSystem (top.operations 0))

/--
Every fixed cell whose value is consumed by the semantic bridge: emitted table,
region, constant, and selector assignments, plus the interim exact cells needed by
lookup-selector projection.
-/
def topLevelRequiredFixedEntries
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (ℕ × ℕ × ℕ) :=
  topLevelFixedOperationEntries top ++
    topLevelConstantEntries top ++
    topLevelSelectorEntries top ++
    topLevelSingletonLookupSelectorEntries top

/--
**INTERIM full-circuit fallback.** Columns allocated by the pinned constraint
system but absent from the final fixed-query layout.

This finite diagnostic exists only to unblock concrete circuits while the query
registration compiler is given a structural coverage theorem.  New generic
interfaces should consume that theorem, not this computation.
-/
def interimFixedQueryCoverageFailures
    (top : TopLevelCircuit Fp Config PublicInput) : List ℕ :=
  let pinned := top.pinnedCS
  let queried := pinned.fixedQueryLayout.map Prod.fst
  (List.range pinned.numFixedColumns).filter fun column =>
    decide (column ∉ queried)

/--
An empty interim query-coverage diagnostic supplies the current
`TopLevelFixedCoherence` coverage field.
-/
theorem fixedQueryCoverage_of_interimFailures_eq_nil
    (top : TopLevelCircuit Fp Config PublicInput)
    (hfail : interimFixedQueryCoverageFailures top = []) :
    ∀ column,
      column < top.pinnedCS.numFixedColumns →
        ∃ rotation, (column, rotation) ∈ top.pinnedCS.fixedQueryLayout := by
  intro column hcolumn
  have hnotFailure :
      column ∉ interimFixedQueryCoverageFailures top := by
    rw [hfail]
    simp
  have hcolumnMem :
      column ∈ top.pinnedCS.fixedQueryLayout.map Prod.fst := by
    by_contra hmissing
    apply hnotFailure
    simp [interimFixedQueryCoverageFailures, hcolumn, hmissing]
  rw [List.mem_map] at hcolumnMem
  obtain ⟨entry, hentry, hcolumnEntry⟩ := hcolumnMem
  rcases entry with ⟨entryColumn, rotation⟩
  simp only at hcolumnEntry
  subst entryColumn
  exact ⟨rotation, hentry⟩

/--
**INTERIM full-circuit fallback.** Required fixed/table/selector writes whose
final dense keygen cell does not have the required bounds and value.

The intended replacement follows the compiler pipeline:

* V1 placement proves that different regions never overlap in cells;
* region-local fixed writes are checked or proved within their small region;
* table layout, constant allocation, and selector packing expose their own
  collision and composition laws;
* generic last-write/dedup/scatter theorems assemble those local facts.

This diagnostic is deliberately named `interim` so a successful whole-circuit
`native_decide` certificate cannot silently become the permanent architecture.
-/
def interimFixedRealizationFailures
    (top : TopLevelCircuit Fp Config PublicInput) :
    List (ℕ × ℕ × ℕ) :=
  let n := 2 ^ top.domainExponent
  let numFixedColumns := top.pinnedCS.numFixedColumns
  let rows := top.fixedRows
  let required := topLevelRequiredFixedEntries top
  required.filter fun entry =>
    decide (¬ (
      entry.2.1 < n ∧
      entry.1 < numFixedColumns ∧
      (rows.getD entry.1 []).getD entry.2.1 0 =
        (entry.2.2 : Fp)))

/--
An empty interim realization diagnostic proves the exact sparse-to-dense fact
used by `TopLevelFixedCoherence`.
-/
theorem fixedRowsRealize_of_interimFailures_eq_nil
    (top : TopLevelCircuit Fp Config PublicInput)
    (hfail : interimFixedRealizationFailures top = []) :
    ∀ column row value,
      (column, row, value) ∈
          topLevelRequiredFixedEntries top →
        row < 2 ^ top.domainExponent ∧
          column < top.pinnedCS.numFixedColumns ∧
          (top.fixedRows.getD column []).getD row 0 =
            (value : Fp) := by
  intro column row value hentry
  let property : Prop :=
    row < 2 ^ top.domainExponent ∧
      column < top.pinnedCS.numFixedColumns ∧
      (top.fixedRows.getD column []).getD row 0 = (value : Fp)
  have hnotFailure :
      (column, row, value) ∉ interimFixedRealizationFailures top := by
    rw [hfail]
    simp
  have hnotnot : ¬ ¬ property := by
    intro hnot
    apply hnotFailure
    rw [interimFixedRealizationFailures, List.mem_filter]
    refine ⟨hentry, ?_⟩
    change decide (¬ property) = true
    exact decide_eq_true hnot
  exact Classical.not_not.mp hnotnot

/--
The fixed-row part of a top-level circuit's keygen boundary.

This record contains no proof-dependent data. Its rows, commitments, and query
coverage are shared by every proof in a bundle. `realizes` is the layout compiler's
sparse-to-dense correctness statement for exactly the entries consumed by Clean
fixed/table semantics and selector activation.
-/
structure TopLevelFixedCoherence
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G) where
  key :
    LagrangeCommitmentKey urs (top.toVerifierKey pp urs).omega
  rows : ℕ → List Fp
  commitment : ∀ column,
    column < top.pinnedCS.numFixedColumns →
      (top.toVerifierKey pp urs).fixedCommitment column =
        key.commitInstance (rows column) 1
  fixedQueryCount :
    (top.toVerifierKey pp urs).fixedQueryLayout.length =
      (pp.mergeDerived top).numFixedQueries
  queryLayout : ∀ column,
    column < top.pinnedCS.numFixedColumns →
      ∃ rotation,
        (column, rotation) ∈
          (top.toVerifierKey pp urs).fixedQueryLayout
  realizes : ∀ column row value,
    (column, row, value) ∈
        topLevelRequiredFixedEntries top →
      row < (top.toVerifierKey pp urs).n ∧
        column < top.pinnedCS.numFixedColumns ∧
        (rows column).getD row 0 = (value : Fp)

namespace TopLevelFixedCoherence

omit [DecidableEq G] in
/-- The circuit-derived VK's fixed commitment at one in-range column is the
full-list commitment of the corresponding keygen row vector. -/
theorem fixedCommitment_eq_commitInstance
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (hk : top.domainExponent = urs.k)
    (hlen : (derivedUrsGLagrange urs).length = 2 ^ urs.k)
    (hgenerators : ∀ i : Fin (2 ^ urs.k),
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial (top.toVerifierKey pp urs).omega
            (Pi.single i (1 : Fp)))))
    (column : ℕ) (hcolumn : column < top.pinnedCS.numFixedColumns) :
    (top.toVerifierKey pp urs).fixedCommitment column =
      (LagrangeCommitmentKey.ofFullList
        urs (top.toVerifierKey pp urs).omega
        (derivedUrsGLagrange urs) hgenerators).commitInstance
          (top.fixedRows.getD column []) 1 := by
  rw [top.toVerifierKey_fixedCommitment]
  have hcolumnRows : column < top.fixedRows.length := by
    simpa only [top.fixedRows_length] using hcolumn
  have hget :
      (top.fixedRows.map
        (Fast.Msm.commitLagrangeFastWith
          Fast.Msm.defaultWindow urs.w
          (derivedUrsGLagrange urs))).getD column 0 =
        Fast.Msm.commitLagrangeFastWith
          Fast.Msm.defaultWindow urs.w
          (derivedUrsGLagrange urs)
          (top.fixedRows.getD column []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hcolumnRows,
      List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hcolumnRows]
    rfl
  rw [TopLevelCircuit.fixedCommitments, List.parMap_eq_map, hget]
  apply Keygen.commitLagrangeFastWith_eq_ofFullList_commitInstance
    urs (top.toVerifierKey pp urs).omega hlen hgenerators
  rw [top.fixedRows_getD_length column hcolumn, hk]

/--
Construct fixed coherence from the exact circuit-derived keygen rows.

Dense-row shape, commitment provenance, and the query-count equality are generic.
The caller supplies only the setup's Lagrange-basis equations plus the two genuinely
static circuit/layout facts: coverage of every committed fixed column by the final
query layout, and preservation of the sparse assignments after last-write
deduplication and dense scattering.
-/
def ofKeygen
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (hk : top.domainExponent = urs.k)
    (hlen : (derivedUrsGLagrange urs).length = 2 ^ urs.k)
    (hgenerators : ∀ i : Fin (2 ^ urs.k),
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial (top.toVerifierKey pp urs).omega
            (Pi.single i (1 : Fp)))))
    (queryLayout : ∀ column,
      column < top.pinnedCS.numFixedColumns →
        ∃ rotation,
          (column, rotation) ∈
            (top.toVerifierKey pp urs).fixedQueryLayout)
    (realizes : ∀ column row value,
      (column, row, value) ∈
          topLevelRequiredFixedEntries top →
        row < (top.toVerifierKey pp urs).n ∧
          column < top.pinnedCS.numFixedColumns ∧
          (top.fixedRows.getD column []).getD row 0 =
            (value : Fp)) :
    TopLevelFixedCoherence top pp urs where
  key :=
    LagrangeCommitmentKey.ofFullList
      urs (top.toVerifierKey pp urs).omega
      (derivedUrsGLagrange urs) hgenerators
  rows := fun column => top.fixedRows.getD column []
  commitment :=
    fixedCommitment_eq_commitInstance
      top pp urs hk hlen hgenerators
  fixedQueryCount := top.toVerifierKey_fixedQueryCount pp urs
  queryLayout := queryLayout
  realizes := realizes

end TopLevelFixedCoherence

omit [Module Fp G] [DecidableEq G] in
/--
One required sparse fixed entry reads back from its canonically bound dense-row
polynomial, or the caller's shared exceptional branch fires.

This is the pointwise form used by consumers such as constant-copy replay; the
family theorem below merely applies it to selectors and fixed/table operations.
-/
theorem topLevelFixedEntryRead_or_bad
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    (poly : CommitmentId → Polynomial Fp)
    (rows : ℕ → List Fp)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey pp urs).omega ^ (i : ℕ))
    (hn : (top.toVerifierKey pp urs).n = 2 ^ urs.k)
    (realizes : ∀ column row value,
      (column, row, value) ∈ topLevelRequiredFixedEntries top →
        row < (top.toVerifierKey pp urs).n ∧
          column < top.pinnedCS.numFixedColumns ∧
          (rows column).getD row 0 = (value : Fp))
    {Bad : Prop}
    (binding : ∀ column,
      column < top.pinnedCS.numFixedColumns →
        poly (.fixedCol column) =
            instanceRowPolynomial (2 ^ urs.k)
              (top.toVerifierKey pp urs).omega (rows column) ∨
          Bad)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    {column row value : ℕ}
    (hentry :
      (column, row, value) ∈ topLevelRequiredFixedEntries top) :
    (resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent)).fixed
          ⟨column⟩ (row : ℤ) = (value : Fp) ∨
      Bad := by
  obtain ⟨hrow, hcolumn, hvalue⟩ :=
    realizes column row value hentry
  rcases binding column hcolumn with hpolyEq | hbad
  · apply Or.inl
    have hrow' : row < 2 ^ urs.k := by
      rwa [← hn]
    rw [resolverEnvironment_fixed, hpolyEq]
    simpa using
      (instanceRowPolynomial_eval hrows
        ⟨row, hrow'⟩).trans hvalue
  · exact Or.inr hbad

omit [Module Fp G] [DecidableEq G] in
/--
Polynomial binding for every used fixed column supplies selector and fixed/table
semantics. This lemma is independent of decoded-member provenance; callers choose
the exceptional event carried by `binding`.
-/
theorem topLevelFixedConstraints_or_bad
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    (poly : CommitmentId → Polynomial Fp)
    (rows : ℕ → List Fp)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey pp urs).omega ^ (i : ℕ))
    (hn : (top.toVerifierKey pp urs).n = 2 ^ urs.k)
    (realizes : ∀ column row value,
      (column, row, value) ∈
          topLevelRequiredFixedEntries top →
        row < (top.toVerifierKey pp urs).n ∧
          column < top.pinnedCS.numFixedColumns ∧
          (rows column).getD row 0 = (value : Fp))
    {Bad : Prop}
    (binding : ∀ column,
      column < top.pinnedCS.numFixedColumns →
        poly (.fixedCol column) =
            instanceRowPolynomial (2 ^ urs.k)
              (top.toVerifierKey pp urs).omega (rows column) ∨
          Bad)
    (proofIndex : Fin (pp.mergeDerived top).numProofs) :
    (SelectorActivationsRealized
        top.selectorMap top.selectorActivations
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)) ∧
      CircuitConstraintFamily.constraints .fixed top.placement
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations 0) 0) ∨ Bad := by
  classical
  by_cases hbad : Bad
  · exact Or.inr hbad
  · apply Or.inl
    let environment :=
      resolverEnvironment
        (top.toVerifierKey pp urs) poly proofIndex
        (top.usableRowsAt top.domainExponent)
    have fixedRead :
        ∀ {column row value},
          (column, row, value) ∈
              topLevelRequiredFixedEntries top →
            environment.fixed ⟨column⟩ (row : ℤ) = (value : Fp) := by
      intro column row value hentry
      exact
        (topLevelFixedEntryRead_or_bad
          poly rows hrows hn realizes binding proofIndex hentry).resolve_right
            hbad
    change
      SelectorActivationsRealized
          top.selectorMap top.selectorActivations environment ∧
        CircuitConstraintFamily.constraints .fixed
          (Layout.place top.regionStarts) environment
          (top.operations 0) 0
    constructor
    · apply selectorActivationsRealized_of_selectorFixed
      intro column row value hentry
      apply fixedRead
      change (column, row, value) ∈ topLevelSelectorEntries top at hentry
      simp [topLevelRequiredFixedEntries, hentry]
    · exact FixedLayout.constraints_of_entries
        top.regionStarts (top.usableRowsAt top.domainExponent)
        (top.operations 0) 0 environment rfl
        (fun column row value hentry => fixedRead (by
          change
            (column, row, value) ∈ topLevelFixedOperationEntries top at hentry
          simp [topLevelRequiredFixedEntries, hentry]))

namespace CanonicalMemberConstraintRelation

variable
    {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k}
    {vk : VerifyingKey shape Fp G}
    {instanceCommitment : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G}
    {ch : Challenges shape.k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi}
    {hblinding : vk.blindingFactors < vk.n}
    {y : Fp} {hpoly : Polynomial Fp} {deg : ℕ}

/--
A canonically routed fixed-column opening is the polynomial interpolating its
keygen rows, or it exhibits an augmented commitment relation.

`hcommit` is the circuit-keygen side of the boundary: the fixed commitment stored
in the derived VK is the Lagrange commitment to `rows` with Halo 2's default blind
`1`. It is independent of the proof and can be established once for the generic
`TopLevelCircuit.toVerifierKey` construction.
-/
theorem fixedColumn_eq_rowPolynomial_or_relation
    (relation : CanonicalMemberConstraintRelation
      urs hk vk instanceCommitment ps ch pU pW a
      batchOpenings memberDecode hblinding y hpoly deg)
    (column : ℕ)
    (key : LagrangeCommitmentKey urs vk.omega)
    (rows : List Fp)
    (hcommit :
      vk.fixedCommitment column =
        key.commitInstance rows 1)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) => vk.omega ^ (i : ℕ))
    (hquery : ∃ q ∈ assembleQueries vk instanceCommitment ps ch,
      q.commId = .fixedCol column) :
    relation.polynomial (.fixedCol column) =
        instanceRowPolynomial (2 ^ urs.k) vk.omega rows ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  classical
  obtain ⟨q, hq, hqid⟩ := hquery
  have routed :=
    assembledQueryMemberRoute_faithful
      (instanceCommitment := instanceCommitment)
      vk ps ch relation.groupingCount relation.noDuplicateQueries q hq
  have routedFixed :
      relation.route (.fixedCol column) = some routed.slot := by
    rw [← hqid]
    exact routed.route_eq
  have hid :
      (deployedSetCommIds (instanceCommitment := instanceCommitment)
        vk ps ch routed.slot.setIndex).getD
          (routed.slot.memberIndex : ℕ) .vanishingH =
        .fixedCol column := by
    apply assembledQueryMemberRoute_id
      (instanceCommitment := instanceCommitment)
      vk ps ch relation.groupingCount relation.noDuplicateQueries
      (.fixedCol column) routed.slot
    simpa [CanonicalMemberConstraintRelation.route] using routedFixed
  have href :=
    deployedMemberRef_eq_fixedCommitment
      (instanceCommitment := instanceCommitment)
      vk ps ch relation.groupingCount routed.slot column hid
  let decoded :=
    memberDecode routed.slot.setIndex routed.slot.setIndex_lt
  have hopen :
      commit urs (decoded.cols routed.slot.memberIndex) +
          decoded.uComp routed.slot.memberIndex • urs.u +
          decoded.wComp routed.slot.memberIndex • urs.w =
        key.commitInstance rows 1 := by
    calc
      commit urs (decoded.cols routed.slot.memberIndex) +
            decoded.uComp routed.slot.memberIndex • urs.u +
            decoded.wComp routed.slot.memberIndex • urs.w =
          ((deployedSetQueries
              (instanceCommitment := instanceCommitment)
              vk ps ch routed.slot.setIndex).getD
            (routed.slot.memberIndex : ℕ) (.point 0, [])).1.eval
              ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ :=
        decoded.commitment routed.slot.memberIndex
      _ = vk.fixedCommitment column := by
        rw [href]
        rfl
      _ = key.commitInstance rows 1 := hcommit
  have hbound :=
    coeffsToPoly_eq_instanceRowPolynomial_or_relation
      key rows 1
      (decoded.cols routed.slot.memberIndex)
      (decoded.uComp routed.slot.memberIndex)
      (decoded.wComp routed.slot.memberIndex)
      hrows hopen
  rcases hbound with heq | hrelation
  · apply Or.inl
    rw [CanonicalMemberConstraintRelation.polynomial,
      decodedPolynomialResolver, routedFixed]
    exact heq
  · exact Or.inr hrelation

/--
Circuit-derived fixed rows discharge both consumers of fixed-column semantics:
packed selector activations and explicit fixed/table operations. Commitment binding
is retained as an explicit alternative.
-/
theorem topLevelFixedConstraints_or_relation
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams}
    {urs : URS G}
    {hk : (pp.mergeDerived top).k = urs.k}
    {vk : VerifyingKey (pp.mergeDerived top) Fp G}
    {instanceCommitment :
      Fin (pp.mergeDerived top).numProofs → ℕ → G}
    {ps : ProofString (pp.mergeDerived top) Fp G}
    {ch : Challenges (pp.mergeDerived top).k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi}
    {hblinding : vk.blindingFactors < vk.n}
    {y : Fp} {hpoly : Polynomial Fp}
    (relation :
      CanonicalMemberConstraintRelation
        urs hk vk instanceCommitment ps ch pU pW a
        batchOpenings memberDecode hblinding y hpoly vk.n)
    (hvk : vk = top.toVerifierKey pp urs)
    (coherence : TopLevelFixedCoherence top pp urs)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey pp urs).omega ^ (i : ℕ))
    (hn : (top.toVerifierKey pp urs).n = 2 ^ urs.k)
    (proofIndex : Fin (pp.mergeDerived top).numProofs) :
    (SelectorActivationsRealized
        top.selectorMap top.selectorActivations
        (resolverEnvironment
          (top.toVerifierKey pp urs) relation.polynomial proofIndex
          (top.usableRowsAt top.domainExponent)) ∧
      CircuitConstraintFamily.constraints .fixed top.placement
        (resolverEnvironment
          (top.toVerifierKey pp urs) relation.polynomial proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations 0) 0) ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  subst vk
  apply topLevelFixedConstraints_or_bad
    relation.polynomial coherence.rows hrows hn coherence.realizes
  · intro column hcolumn
    exact relation.fixedColumn_eq_rowPolynomial_or_relation
      column coherence.key (coherence.rows column)
      (coherence.commitment column hcolumn) hrows
      (by
        obtain ⟨rotation, hlayout⟩ :=
          coherence.queryLayout column hcolumn
        exact fixedQuery_of_layout
          (top.toVerifierKey pp urs) instanceCommitment ps ch
          column rotation coherence.fixedQueryCount hlayout)

/--
Pointwise fixed-cell realization at the canonical decoded-member relation.
Constants replay uses this theorem for the V1-allocated constants cells; selector
and fixed/table family proofs use its bundled sibling above.
-/
theorem topLevelFixedEntryRead_or_relation
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams}
    {urs : URS G}
    {hk : (pp.mergeDerived top).k = urs.k}
    {vk : VerifyingKey (pp.mergeDerived top) Fp G}
    {instanceCommitment :
      Fin (pp.mergeDerived top).numProofs → ℕ → G}
    {ps : ProofString (pp.mergeDerived top) Fp G}
    {ch : Challenges (pp.mergeDerived top).k Fp}
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    {batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          vk ps ch)
        a pU pW}
    {memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk vk ps ch batchOpenings i hi}
    {hblinding : vk.blindingFactors < vk.n}
    {y : Fp} {hpoly : Polynomial Fp}
    (relation :
      CanonicalMemberConstraintRelation
        urs hk vk instanceCommitment ps ch pU pW a
        batchOpenings memberDecode hblinding y hpoly vk.n)
    (hvk : vk = top.toVerifierKey pp urs)
    (coherence : TopLevelFixedCoherence top pp urs)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey pp urs).omega ^ (i : ℕ))
    (hn : (top.toVerifierKey pp urs).n = 2 ^ urs.k)
    (proofIndex : Fin (pp.mergeDerived top).numProofs)
    {column row value : ℕ}
    (hentry :
      (column, row, value) ∈ topLevelRequiredFixedEntries top) :
    (resolverEnvironment
        (top.toVerifierKey pp urs) relation.polynomial proofIndex
        (top.usableRowsAt top.domainExponent)).fixed
          ⟨column⟩ (row : ℤ) = (value : Fp) ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  subst vk
  apply topLevelFixedEntryRead_or_bad
    relation.polynomial coherence.rows hrows hn coherence.realizes
  · intro fixedColumn hcolumn
    exact relation.fixedColumn_eq_rowPolynomial_or_relation
      fixedColumn coherence.key (coherence.rows fixedColumn)
      (coherence.commitment fixedColumn hcolumn) hrows
      (by
        obtain ⟨rotation, hlayout⟩ :=
          coherence.queryLayout fixedColumn hcolumn
        exact fixedQuery_of_layout
          (top.toVerifierKey pp urs) instanceCommitment ps ch
          fixedColumn rotation coherence.fixedQueryCount hlayout)
  · exact hentry

end CanonicalMemberConstraintRelation

end Zcash.Snark
