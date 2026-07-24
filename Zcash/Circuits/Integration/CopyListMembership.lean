import Zcash.Circuits.Integration.PermutationReplay

/-!
# Declared copies resolve into the keygen copy list

The copy-replay witness needs, per declared Clean copy, a value-agreement fact; for the
cell/cell and cell/instance kinds that fact transports through the keygen permutation,
whose copy list is the floor planner's. This module proves the membership half: every
non-constant declared copy, resolved to absolute permutation-column coordinates, is a
member of the V1 copy list. (Constant copies consume the positional constants
allocation; their membership couples to the allocation walk and lives with the
constants instantiation.)
-/

namespace Zcash.Snark

open Halo2
open Zcash.Circuits.Fixtures Zcash.Circuits.Fixtures.Layout

/-- Resolve a non-constant declared copy to the keygen copy tuple: region cells through
the placement, instance endpoints at their absolute rows. Constant endpoints resolve to
`none` — their cells are the planner's positional constants allocation. -/
def resolveDeclared (permCols : List ColRef) (starts : List ℕ) :
    CopyEndpoint Fp × CopyEndpoint Fp → Option (ℕ × ℕ × ℕ × ℕ)
  | (.cell l, .cell r) =>
      some ((resolveCell permCols starts l).1, (resolveCell permCols starts l).2,
        (resolveCell permCols starts r).1, (resolveCell permCols starts r).2)
  | (.cell c, .instance col row) =>
      some ((resolveCell permCols starts c).1, (resolveCell permCols starts c).2,
        permIndex permCols col.toAny, row)
  | _ => none

/-- The declared-copy extraction is a `filterMap`. -/
theorem regionDeclaredCopies_eq_filterMap (body : RegionOperations Fp) :
    regionDeclaredCopies body = body.filterMap regionOperationDeclaredCopy? := by
  induction body with
  | nil => rfl
  | cons op rest ih =>
      rw [regionDeclaredCopies, List.filterMap_cons]
      cases hop : regionOperationDeclaredCopy? (F := Fp) op with
      | none => simpa [hop] using ih
      | some copy => simpa [hop] using ih

/-- A resolvable declared copy of a region body is among the region's extracted
equality/instance copies. -/
theorem mem_regionCopiesSplit_fst_of_declared
    (permCols : List ColRef) (starts : List ℕ)
    (body : RegionOperations Fp) (consts : List (ℕ × ℕ × ℕ))
    (copy : CopyEndpoint Fp × CopyEndpoint Fp) (tuple : ℕ × ℕ × ℕ × ℕ)
    (hres : resolveDeclared permCols starts copy = some tuple)
    (hmem : copy ∈ regionDeclaredCopies body) :
    tuple ∈ (regionCopiesSplit permCols starts body consts).1 := by
  rw [regionDeclaredCopies_eq_filterMap, List.mem_filterMap] at hmem
  obtain ⟨op, hop, hcopy⟩ := hmem
  simp only [regionCopiesSplit]
  rw [List.mem_filterMap]
  refine ⟨op, hop, ?_⟩
  cases op with
  | constrainEqual a b =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      simp only [resolveDeclared] at hres
      obtain rfl := Option.some.inj hres
      rfl
  | constrainInstance cell col row =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      simp only [resolveDeclared] at hres
      obtain rfl := Option.some.inj hres
      rfl
  | constrainConstant cell value =>
      simp only [regionOperationDeclaredCopy?] at hcopy
      obtain rfl := Option.some.inj hcopy
      simp [resolveDeclared] at hres
  | assignAdvice col off val => simp [regionOperationDeclaredCopy?] at hcopy
  | assignFixed col off val => simp [regionOperationDeclaredCopy?] at hcopy
  | enableGate gate off => simp [regionOperationDeclaredCopy?] at hcopy
  | enableLookup arg enabled off => simp [regionOperationDeclaredCopy?] at hcopy

/-- **Every resolvable declared copy is in the V1 copy list**: region-local copies land
in their region's extracted stream, layouter-level instance copies inline, and the
whole equality/instance stream prefixes the copy list. -/
theorem mem_V1_copyList_of_declared
    (permCols : List ColRef) (starts : List ℕ)
    (ops : Operations Fp) (consts : List (ℕ × ℕ × ℕ))
    (copy : CopyEndpoint Fp × CopyEndpoint Fp) (tuple : ℕ × ℕ × ℕ × ℕ)
    (hres : resolveDeclared permCols starts copy = some tuple)
    (hmem : copy ∈ operationDeclaredCopies ops) :
    tuple ∈ V1.copyList permCols starts ops consts := by
  suffices h : tuple ∈ (V1.go permCols starts ops consts).1.1 by
    rw [V1.copyList]
    exact List.mem_append_left _ h
  induction ops generalizing consts with
  | nil => simp [operationDeclaredCopies] at hmem
  | cons op rest ih =>
      cases op with
      | region name body =>
          rw [operationDeclaredCopies] at hmem
          rcases hsplit : regionCopiesSplit permCols starts body consts with
            ⟨eqs, cnsts, cs'⟩
          rcases hgo : V1.go permCols starts rest cs' with ⟨⟨r1, r2⟩, cs''⟩
          simp only [V1.go, hsplit, hgo]
          rcases List.mem_append.mp hmem with hcopy | hcopy
          · refine List.mem_append_left _ ?_
            have := mem_regionCopiesSplit_fst_of_declared permCols starts body consts
              copy tuple hres hcopy
            rwa [hsplit] at this
          · refine List.mem_append_right _ ?_
            have := ih cs' hcopy
            rwa [hgo] at this
      | constrainInstance cell col row =>
          rw [operationDeclaredCopies] at hmem
          rcases hgo : V1.go permCols starts rest consts with ⟨⟨r1, r2⟩, cs''⟩
          simp only [V1.go, hgo]
          rcases List.mem_cons.mp hmem with hcopy | hcopy
          · subst hcopy
            simp only [resolveDeclared] at hres
            obtain rfl := Option.some.inj hres
            exact List.mem_cons_self ..
          · refine List.mem_cons_of_mem _ ?_
            have := ih consts hcopy
            rwa [hgo] at this
      | loadTable tbl values =>
          rw [operationDeclaredCopies] at hmem
          rcases hgo : V1.go permCols starts rest consts with ⟨⟨r1, r2⟩, cs''⟩
          simp only [V1.go, hgo]
          have := ih consts hmem
          rwa [hgo] at this

end Zcash.Snark
