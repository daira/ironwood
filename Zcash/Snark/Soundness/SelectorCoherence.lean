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

end Zcash.Circuits.Fixtures.Layout

namespace Zcash.Snark

open Halo2
open Zcash.Circuits.Fixtures.Layout

set_option maxHeartbeats 20000

/--
The selector packer assigns valid roots whenever the number of candidate selectors
fits below the scalar-field characteristic.
-/
theorem selectorRootsWellFormed_process
    (selectors : List SelectorDescription) (maxDegree : ℕ)
    (hselectorCount : selectors.length < scalarFieldOrder) :
    SelectorRootsWellFormed (process selectors maxDegree) := by
  intro selector compressed hlookup
  obtain ⟨entry, hentry, hcompressed⟩ :=
    SelCompressMap.exists_mem_entries_of_lookup
      (process selectors maxDegree) hlookup
  have hbounds :=
    process_entry_root_bounds selectors maxDegree entry hentry
  rw [← hcompressed]
  exact ⟨hbounds.1, hbounds.2.1,
    hbounds.2.2.trans_lt hselectorCount⟩

/--
The circuit-derived selector map has valid roots under the minimal generic size
condition: the configured selector count is below the scalar-field order.
-/
theorem selectorRootsWellFormed_deriveSelCompressMap
    {F : Type} (cs : ConstraintSystem F) (n : ℕ)
    (activations : List (ℕ × ℕ))
    (hselectorCount : cs.numSelectors < scalarFieldOrder) :
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
    process_entry_root_bounds descriptions (csDegree cs)
      (sourceSelector, source) hsource
  have hdescriptionLength :
      descriptions.length = cs.numSelectors := by
    simp [descriptions]
  rw [← hcompressed]
  refine ⟨hbounds.1, hbounds.2.1, ?_⟩
  rw [hdescriptionLength] at hbounds
  exact hbounds.2.2.trans_lt hselectorCount

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

end Zcash.Snark
