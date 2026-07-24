import Zcash.Snark.Soundness.ResolverGates
import Zcash.Circuits.Fixtures.Layout
import Std.Data.HashSet.Lemmas

/-!
# Selector compiler coherence

Structural facts about Clean's `compress_selectors` port.  These proofs are
circuit-independent: they reason about the greedy packing algorithm rather than a
captured Action selector map.
-/

namespace Halo2

set_option maxHeartbeats 20000

/--
The inner greedy scan only transfers selector descriptions between the chosen
combination and the remainder.
-/
theorem extendCombination_length_conservation
    (maxDegree d : ℕ) (comb selectors : List SelectorDescription) :
    let result := extendCombination maxDegree d comb selectors
    result.1.length + result.2.length =
      comb.length + selectors.length := by
  induction selectors generalizing d comb with
  | nil =>
      simp [extendCombination]
  | cons selector rest ih =>
      simp only [extendCombination]
      split
      · simp
      · split
        · generalize hresult :
            extendCombination maxDegree d comb rest = result
          rcases result with ⟨chosen, remaining⟩
          have hlength := ih d comb
          rw [hresult] at hlength
          simp only [List.length_cons] at hlength ⊢
          omega
        · let nextDegree :=
            max d (selector.maxDegree - 1)
          split
          · generalize hresult :
              extendCombination maxDegree d comb rest = result
            rcases result with ⟨chosen, remaining⟩
            have hlength := ih d comb
            rw [hresult] at hlength
            simp only [List.length_cons] at hlength ⊢
            omega
          · have hlength :=
              ih nextDegree (comb ++ [selector])
            simpa [nextDegree, Nat.add_assoc, Nat.add_left_comm,
              Nat.add_comm] using hlength

/--
The greedy extension never exceeds the degree budget when its initial combination
already fits.  Candidate degrees need no separate bound: the algorithm checks the
updated degree and length before every insertion.
-/
theorem extendCombination_length_le
    (maxDegree d : ℕ) (comb selectors : List SelectorDescription)
    (hcomb : comb.length ≤ maxDegree) :
    (extendCombination maxDegree d comb selectors).1.length ≤
      maxDegree := by
  induction selectors generalizing d comb with
  | nil =>
      simpa [extendCombination] using hcomb
  | cons selector rest ih =>
      simp only [extendCombination]
      split
      · exact hcomb
      · split
        · exact ih d comb hcomb
        · let nextDegree :=
            max d (selector.maxDegree - 1)
          split
          · exact ih d comb hcomb
          · apply ih nextDegree (comb ++ [selector])
            simp only [List.length_append, List.length_singleton]
            omega

/-- Every combination returned by the outer packing loop fits in its input list. -/
theorem length_le_of_mem_buildCombinations
    (maxDegree fuel : ℕ) (selectors combination :
      List SelectorDescription)
    (hcombination :
      combination ∈ buildCombinations maxDegree fuel selectors) :
    combination.length ≤ selectors.length := by
  induction fuel generalizing selectors with
  | zero =>
      simp [buildCombinations] at hcombination
  | succ fuel ih =>
      cases selectors with
      | nil =>
          simp [buildCombinations] at hcombination
      | cons selector rest =>
          simp only [buildCombinations] at hcombination
          generalize hresult :
              extendCombination maxDegree
                (selector.maxDegree - 1) [selector] rest =
                result at hcombination
          rcases result with ⟨chosen, remaining⟩
          simp only [List.mem_cons] at hcombination
          have hlength :=
            extendCombination_length_conservation maxDegree
              (selector.maxDegree - 1) [selector] rest
          rw [hresult] at hlength
          simp only [List.length_cons, List.length_nil,
            Nat.zero_add] at hlength
          rcases hcombination with rfl | hcombination
          · simp only [List.length_cons]
            omega
          · have hrecursive :=
              ih remaining hcombination
            simp only [List.length_cons]
            omega

/--
Every combination returned by the outer packing loop fits in the selector
compression degree budget.
-/
theorem length_le_maxDegree_of_mem_buildCombinations
    (maxDegree fuel : ℕ) (selectors combination :
      List SelectorDescription)
    (hpositive : 1 ≤ maxDegree)
    (hcombination :
      combination ∈ buildCombinations maxDegree fuel selectors) :
    combination.length ≤ maxDegree := by
  induction fuel generalizing selectors with
  | zero =>
      simp [buildCombinations] at hcombination
  | succ fuel ih =>
      cases selectors with
      | nil =>
          simp [buildCombinations] at hcombination
      | cons selector rest =>
          simp only [buildCombinations] at hcombination
          generalize hresult :
              extendCombination maxDegree
                (selector.maxDegree - 1) [selector] rest =
                result at hcombination
          rcases result with ⟨chosen, remaining⟩
          simp only [List.mem_cons] at hcombination
          rcases hcombination with rfl | hcombination
          · have hchosen :=
              extendCombination_length_le maxDegree
                (selector.maxDegree - 1) [selector] rest
                (by simpa using hpositive)
            simpa [hresult] using hchosen
          · exact ih remaining hcombination

/--
Every `process` entry receives a positive root within its combination, and the
combination cannot be larger than the input selector list.
-/
theorem process_entry_root_bounds
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    (entry : ℕ × SelCompress)
    (hentry : entry ∈ (process selectors maxDegree).entries) :
    1 ≤ entry.2.assignedRoot ∧
      entry.2.assignedRoot ≤ entry.2.combinationLen ∧
      entry.2.combinationLen ≤ selectors.length := by
  let degreeZero := selectors.filter (·.maxDegree = 0)
  let remaining := selectors.filter (·.maxDegree ≠ 0)
  let combinations :=
    buildCombinations maxDegree remaining.length remaining
  change entry ∈
    (degreeZero.zipIdx.map fun (description, column) =>
      (description.selector, SelCompress.mk column 1 1)) ++
    (combinations.zipIdx.flatMap fun (combination, column) =>
      combination.zipIdx.map fun (description, position) =>
        (description.selector,
          SelCompress.mk (degreeZero.length + column)
            combination.length (position + 1))) at hentry
  rw [List.mem_append] at hentry
  rcases hentry with hdegreeZero | hcombination
  · obtain ⟨indexed, hindexed, rfl⟩ :=
      List.mem_map.mp hdegreeZero
    have hdescription : indexed.1 ∈ selectors := by
      have hfiltered :=
        List.fst_mem_of_mem_zipIdx hindexed
      exact (List.mem_filter.mp hfiltered).1
    have hselectorsPositive : 1 ≤ selectors.length := by
      have := List.length_pos_of_mem hdescription
      omega
    simpa using hselectorsPositive
  · rw [List.mem_flatMap] at hcombination
    obtain ⟨indexedCombination, hindexedCombination,
      hcombinationEntry⟩ := hcombination
    rcases indexedCombination with ⟨combination, column⟩
    obtain ⟨indexedDescription, hindexedDescription, rfl⟩ :=
      List.mem_map.mp hcombinationEntry
    rcases indexedDescription with ⟨description, position⟩
    have hposition :
        position < combination.length := by
      simpa using
        List.snd_lt_of_mem_zipIdx hindexedDescription
    have hcombinationMem :
        combination ∈ combinations :=
      List.fst_mem_of_mem_zipIdx hindexedCombination
    have hcombinationLength :
        combination.length ≤ remaining.length :=
      length_le_of_mem_buildCombinations maxDegree remaining.length
        remaining combination hcombinationMem
    have hremainingLength :
        remaining.length ≤ selectors.length := by
      exact List.length_filter_le _ _
    change 1 ≤ position + 1 ∧
      position + 1 ≤ combination.length ∧
      combination.length ≤ selectors.length
    refine ⟨by omega, by omega, ?_⟩
    exact hcombinationLength.trans hremainingLength

/--
Every `process` entry's assigned root is bounded by the compression degree,
independently of how many selectors the circuit declares.
-/
theorem process_entry_root_degree_bounds
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    (hpositive : 1 ≤ maxDegree)
    (entry : ℕ × SelCompress)
    (hentry : entry ∈ (process selectors maxDegree).entries) :
    1 ≤ entry.2.assignedRoot ∧
      entry.2.assignedRoot ≤ entry.2.combinationLen ∧
      entry.2.combinationLen ≤ maxDegree := by
  let degreeZero := selectors.filter (·.maxDegree = 0)
  let remaining := selectors.filter (·.maxDegree ≠ 0)
  let combinations :=
    buildCombinations maxDegree remaining.length remaining
  change entry ∈
    (degreeZero.zipIdx.map fun (description, column) =>
      (description.selector, SelCompress.mk column 1 1)) ++
    (combinations.zipIdx.flatMap fun (combination, column) =>
      combination.zipIdx.map fun (description, position) =>
        (description.selector,
          SelCompress.mk (degreeZero.length + column)
            combination.length (position + 1))) at hentry
  rw [List.mem_append] at hentry
  rcases hentry with hdegreeZero | hcombination
  · obtain ⟨indexed, _hindexed, rfl⟩ :=
      List.mem_map.mp hdegreeZero
    simpa using hpositive
  · rw [List.mem_flatMap] at hcombination
    obtain ⟨indexedCombination, hindexedCombination,
      hcombinationEntry⟩ := hcombination
    rcases indexedCombination with ⟨combination, column⟩
    obtain ⟨indexedDescription, hindexedDescription, rfl⟩ :=
      List.mem_map.mp hcombinationEntry
    rcases indexedDescription with ⟨description, position⟩
    have hposition :
        position < combination.length := by
      simpa using
        List.snd_lt_of_mem_zipIdx hindexedDescription
    have hcombinationMem :
        combination ∈ combinations :=
      List.fst_mem_of_mem_zipIdx hindexedCombination
    have hcombinationLength :
        combination.length ≤ maxDegree :=
      length_le_maxDegree_of_mem_buildCombinations
        maxDegree remaining.length remaining combination
        hpositive hcombinationMem
    change 1 ≤ position + 1 ∧
      position + 1 ≤ combination.length ∧
      combination.length ≤ maxDegree
    exact ⟨by omega, by omega, hcombinationLength⟩

/-- A successful association-list lookup originates in the map's entries. -/
theorem SelCompressMap.exists_mem_entries_of_lookup
    (map : SelCompressMap) {selector : ℕ} {compressed : SelCompress}
    (hlookup : map.lookup selector = some compressed) :
    ∃ entry ∈ map.entries, entry.2 = compressed := by
  simp only [SelCompressMap.lookup, Option.map_eq_some_iff] at hlookup
  obtain ⟨entry, hfind, hcompressed⟩ := hlookup
  exact ⟨entry, List.mem_of_find?_eq_some hfind, hcompressed⟩

end Halo2

namespace Zcash.Circuits.Fixtures.Layout

open Halo2

set_option maxHeartbeats 20000

/--
Folding `HashSet.insert` over a list retains every element of both the initial
set and the input list.
-/
private theorem mem_foldl_insert_iff
    (item : ℕ × ℕ) (items : List (ℕ × ℕ))
    (initial : Std.HashSet (ℕ × ℕ)) :
    item ∈ items.foldl (fun set next => set.insert next) initial ↔
      item ∈ initial ∨ item ∈ items := by
  induction items generalizing initial with
  | nil =>
      simp
  | cons head tail ih =>
      rw [List.foldl_cons, ih]
      simp only [Std.HashSet.mem_insert, beq_iff_eq, List.mem_cons]
      aesop

/--
Every activated selector with a compression-map entry is emitted by the generic
layout compiler as the corresponding packed fixed assignment.
-/
theorem mem_selectorFixed_of_activation
    (map : SelCompressMap) (activationRows : List (ℕ × ℕ))
    {selector row : ℕ} {compressed : SelCompress}
    (hactivation : (selector, row) ∈ activationRows)
    (hlookup : map.lookup selector = some compressed) :
    (compressed.packedCol, row, compressed.assignedRoot) ∈
      selectorFixed map activationRows := by
  simp only [SelCompressMap.lookup, Option.map_eq_some_iff] at hlookup
  obtain ⟨entry, hfind, hcompressed⟩ := hlookup
  unfold selectorFixed
  rw [List.mem_filterMap]
  refine ⟨(selector, row), ?_, ?_⟩
  · rw [Std.HashSet.mem_toList, mem_foldl_insert_iff]
    exact Or.inr hactivation
  · simp only [hfind, Option.map_some]
    rw [← hcompressed]

/--
Conversely, every packed fixed assignment emitted by `selectorFixed` retains the
row of some source activation.  Selector deduplication may forget multiplicity and
order, but it cannot invent rows.
-/
theorem exists_activation_of_mem_selectorFixed
    (map : SelCompressMap) (activationRows : List (ℕ × ℕ))
    {column row value : ℕ}
    (hentry :
      (column, row, value) ∈ selectorFixed map activationRows) :
    ∃ selector, (selector, row) ∈ activationRows := by
  unfold selectorFixed at hentry
  rw [List.mem_filterMap] at hentry
  obtain ⟨⟨selector, sourceRow⟩, huniq, hmapped⟩ := hentry
  rw [Std.HashSet.mem_toList, mem_foldl_insert_iff] at huniq
  rcases huniq with hfalse | hactivation
  · simp at hfalse
  · simp only [Option.map_eq_some_iff] at hmapped
    obtain ⟨entry, _hfind, hresult⟩ := hmapped
    simp only [Prod.mk.injEq] at hresult
    exact ⟨selector, by simpa [hresult.2.1] using hactivation⟩

end Zcash.Circuits.Fixtures.Layout

namespace Zcash.Snark

open Halo2
open Zcash.Circuits.Fixtures.Layout

set_option maxHeartbeats 20000

/--
The selector packer assigns valid roots whenever its compression degree fits below
the scalar-field characteristic.
-/
theorem selectorRootsWellFormed_process
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    (hpositive : 1 ≤ maxDegree)
    (hdegree : maxDegree < scalarFieldOrder) :
    SelectorRootsWellFormed (process selectors maxDegree) := by
  intro selector compressed hlookup
  obtain ⟨entry, hentry, hcompressed⟩ :=
    SelCompressMap.exists_mem_entries_of_lookup
      (process selectors maxDegree) hlookup
  have hbounds :=
    process_entry_root_degree_bounds selectors maxDegree
      hpositive entry hentry
  rw [← hcompressed]
  exact ⟨hbounds.1, hbounds.2.1,
    hbounds.2.2.trans_lt hdegree⟩

/--
The circuit-derived selector map has valid roots under the minimal generic size
condition: the constraint-system degree is below the scalar-field order.
-/
theorem selectorRootsWellFormed_deriveSelCompressMap
    {F : Type} (cs : ConstraintSystem F) (n : ℕ)
    (activations : List (ℕ × ℕ))
    (hdegree : csDegree cs < scalarFieldOrder) :
    SelectorRootsWellFormed
      (deriveSelCompressMap cs n activations) := by
  let table := activationTable n cs.numSelectors activations
  let degrees := selectorMaxDegrees cs
  let descriptions :=
    (List.range cs.numSelectors).map fun index =>
      SelectorDescription.mk index table[index]! degrees[index]!
  let packing := process descriptions (csDegree cs)
  intro selector compressed hlookup
  obtain ⟨entry, hentry, hcompressed⟩ :=
    SelCompressMap.exists_mem_entries_of_lookup
      (deriveSelCompressMap cs n activations) hlookup
  change entry ∈ packing.entries.map (fun (sourceSelector, source) =>
    (sourceSelector,
      { source with
        packedCol := source.packedCol + cs.numFixedColumns })) at hentry
  obtain ⟨⟨sourceSelector, source⟩, hsource, rfl⟩ :=
    List.mem_map.mp hentry
  have hbounds :=
    process_entry_root_degree_bounds descriptions (csDegree cs)
      (by
        unfold csDegree
        exact le_trans (by omega) (Nat.le_max_left _ _))
      (sourceSelector, source) hsource
  rw [← hcompressed]
  exact ⟨hbounds.1, hbounds.2.1,
    hbounds.2.2.trans_lt hdegree⟩

/--
It is enough to realize the fixed assignments emitted by `selectorFixed` in
order to realize every selector activation expected by the gate resolver.
-/
theorem selectorActivationsRealized_of_selectorFixed
    (map : SelCompressMap) (activationRows : List (ℕ × ℕ))
    (environment : Environment Fp)
    (hfixed :
      ∀ {column row value : ℕ},
        (column, row, value) ∈ selectorFixed map activationRows →
          environment.fixed ⟨column⟩ row = (value : Fp)) :
    SelectorActivationsRealized map activationRows environment := by
  intro selector row compressed hactivation hlookup
  exact hfixed
    (mem_selectorFixed_of_activation map activationRows
      hactivation hlookup)

/--
Dense fixed-column rows compiled into their canonical interpolation polynomials
realize selector activations whenever the sparse selector assignments occur at
in-domain rows with the expected dense values.

This is the polynomial boundary expected from key generation: the selector compiler
does not need to know how commitments or a concrete verifying key are assembled.
-/
theorem selectorActivationsRealized_of_fixedRowPolynomials
    {n : ℕ} (omega : Fp)
    (fixedRows : ℕ → List Fp)
    (adviceCols instanceCols : ℕ → Polynomial Fp)
    (usableRows : ℕ)
    (map : SelCompressMap) (activationRows : List (ℕ × ℕ))
    (hrows :
      Function.Injective fun row : Fin n => omega ^ (row : ℕ))
    (hroots : SelectorRootsWellFormed map)
    (hlength : ∀ column, (fixedRows column).length = n)
    (hfixed :
      ∀ {column row value : ℕ},
        (column, row, value) ∈ selectorFixed map activationRows →
          (fixedRows column).getD row 0 = (value : Fp)) :
    SelectorActivationsRealized map activationRows
      (polynomialEnvironment omega usableRows
        (fun column =>
          rowPolynomial omega
            (zeroPaddedRows (n := n) (fixedRows column)))
        adviceCols instanceCols) := by
  intro selector row compressed hactivation hlookup
  have hentry :=
    mem_selectorFixed_of_activation map activationRows
      hactivation hlookup
  have hvalue := hfixed hentry
  obtain ⟨hpositive, hrootBound, hcombinationBound⟩ :=
    hroots hlookup
  have hrootLt :
      compressed.assignedRoot < scalarFieldOrder :=
    hrootBound.trans_lt hcombinationBound
  have hrootNe :
      (compressed.assignedRoot : Fp) ≠ 0 := by
    intro hzero
    have hval := congrArg ZMod.val hzero
    have : compressed.assignedRoot = 0 := by
      simpa [ZMod.val_cast_of_lt hrootLt] using hval
    omega
  have hrow : row < n := by
    by_contra hout
    have hge : (fixedRows compressed.packedCol).length ≤ row := by
      rw [hlength]
      omega
    have hzero :
        (fixedRows compressed.packedCol).getD row 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
      rfl
    rw [hzero] at hvalue
    exact hrootNe hvalue.symm
  rw [polynomialEnvironment_fixed_nat,
    rowPolynomial_eval hrows ⟨row, hrow⟩]
  exact hvalue

end Zcash.Snark
