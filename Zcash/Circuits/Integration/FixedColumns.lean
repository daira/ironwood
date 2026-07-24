import Zcash.Snark.Soundness.InstanceCommitment
import Zcash.Snark.Soundness.FixedLayout
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Zcash.Snark.Soundness.SelectorCoherence
import Zcash.Snark.Keygen.Pipeline

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

open Halo2 Polynomial
open Zcash.Circuits
open Zcash.Circuits.Fixtures

set_option maxHeartbeats 20000

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

variable
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]

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
    (top : TopLevelCircuit Fp ConfigInput Config Output) :
    List (ℕ × ℕ × ℕ) :=
  Layout.tableFixed (ZMod.val : Fp → ℕ)
      (top.usableRowsAt top.domainExponent) (top.operations 0) ++
    Layout.regionAssignFixed (ZMod.val : Fp → ℕ)
      top.regionStarts (indexedRegions (top.operations 0) 0).1

/-- Sparse packed-selector assignments emitted by top-level keygen. -/
def topLevelSelectorEntries
    (top : TopLevelCircuit Fp ConfigInput Config Output) :
    List (ℕ × ℕ × ℕ) :=
  Layout.selectorFixed top.selectorMap top.selectorActivations

/--
The fixed-row part of a top-level circuit's keygen boundary.

This record contains no proof-dependent data. Its rows, commitments, and query
coverage are shared by every proof in a bundle. `realizes` is the layout compiler's
sparse-to-dense correctness statement for exactly the entries consumed by Clean
fixed/table semantics and selector activation.
-/
structure TopLevelFixedCoherence
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]
    (top : TopLevelCircuit Fp ConfigInput Config Output)
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
        (topLevelFixedOperationEntries top ++
          topLevelSelectorEntries top) →
      row < (top.toVerifierKey pp urs).n ∧
        column < top.pinnedCS.numFixedColumns ∧
        (rows column).getD row 0 = (value : Fp)

omit [Module Fp G] [DecidableEq G] in
/--
Polynomial binding for every used fixed column supplies selector and fixed/table
semantics. This lemma is independent of decoded-member provenance; callers choose
the exceptional event carried by `binding`.
-/
theorem topLevelFixedConstraints_or_bad
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]
    {top : TopLevelCircuit Fp ConfigInput Config Output}
    {pp : Keygen.ProofParams} {urs : URS G}
    (poly : CommitmentId → Polynomial Fp)
    (rows : ℕ → List Fp)
    (hrows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        (top.toVerifierKey pp urs).omega ^ (i : ℕ))
    (hn : (top.toVerifierKey pp urs).n = 2 ^ urs.k)
    (realizes : ∀ column row value,
      (column, row, value) ∈
          (topLevelFixedOperationEntries top ++
            topLevelSelectorEntries top) →
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
              (topLevelFixedOperationEntries top ++
                topLevelSelectorEntries top) →
            environment.fixed ⟨column⟩ (row : ℤ) = (value : Fp) := by
      intro column row value hentry
      obtain ⟨hrow, hcolumn, hvalue⟩ :=
        realizes column row value hentry
      have hpolyEq := (binding column hcolumn).resolve_right hbad
      have hrow' : row < 2 ^ urs.k := by
        rwa [← hn]
      rw [resolverEnvironment_fixed, hpolyEq]
      simpa using
        (instanceRowPolynomial_eval hrows
          ⟨row, hrow'⟩).trans hvalue
    change
      SelectorActivationsRealized
          top.selectorMap top.selectorActivations environment ∧
        CircuitConstraintFamily.constraints .fixed
          (Layout.place top.regionStarts) environment
          (top.operations 0) 0
    constructor
    · apply selectorActivationsRealized_of_selectorFixed
      intro column row value hentry
      exact fixedRead (List.mem_append_right _ hentry)
    · exact FixedLayout.constraints_of_entries
        top.regionStarts (top.usableRowsAt top.domainExponent)
        (top.operations 0) 0 environment rfl
        (fun column row value hentry =>
          fixedRead (List.mem_append_left _ hentry))

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
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]
    {top : TopLevelCircuit Fp ConfigInput Config Output}
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

end CanonicalMemberConstraintRelation

end Zcash.Snark
