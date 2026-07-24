import Zcash.Circuits.Integration.ActionEncoding
import Zcash.Circuits.Integration.ActionPermutationDomain
import Zcash.Circuits.Integration.CopyListMembership

/-!
# The Action copy-replay witness

The concrete copy adapter: Action's permutation cells, the endpoint encoding (cells
through the placement, instance endpoints at absolute rows, constants at their
allocated constants-column cells), the cell valuation (the environment read of the
cell's permutation column), and the witness constructor feeding
`CopyReplayWitness.ofPairValues` with kind-dispatched pair facts — non-constant copies
through the keygen copy list and the σ-semantics value transport, constant copies
through the allocation zip and the constants-column reads.
-/

namespace Zcash.Snark

open Halo2 Halo2.Layout Zcash.Circuits Zcash.Circuits.Action
open Keygen

/-- Action's permutation columns, in verifying-key order. -/
def actionPermCols : List ColRef :=
  permColsOf orchardActionTopLevelCircuit.constraintSystem

/-- The permutation-column count (15 for the deployed Action circuit). -/
def actionNumPermCols : ℕ := actionPermCols.length

/-- The evaluation-domain size at the derived exponent. -/
def actionDomainSize : ℕ := 2 ^ orchardActionTopLevelCircuit.domainExponent

/-- The V1 constants allocation of the Action operation stream. -/
def actionConsts : List (ℕ × ℕ × ℕ) :=
  constantsOf orchardActionTopLevelCircuit.constraintSystem
    (orchardActionTopLevelCircuit.operations 0)

/-- The keygen copy list of the Action operation stream. -/
def actionCopyRaw : List (ℕ × ℕ × ℕ × ℕ) :=
  Halo2.Layout.V1.copyList actionPermCols
    orchardActionTopLevelCircuit.regionStarts
    (orchardActionTopLevelCircuit.operations 0) actionConsts

/-- The last usable row of the circuit-derived Action domain. -/
def actionActiveRows : ℕ :=
  orchardActionTopLevelCircuit.usableRowsAt
    orchardActionTopLevelCircuit.domainExponent

theorem actionNumPermCols_pos : 0 < actionNumPermCols := by
  native_decide

theorem actionDomainSize_pos : 0 < actionDomainSize :=
  Nat.two_pow_pos _

@[simp]
theorem actionDomainSize_eq
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    actionDomainSize = (ActionPermutationDomain.actionVk pp urs).n := by
  simp [actionDomainSize]

theorem actionActiveRows_le_domainSize :
    actionActiveRows ≤ actionDomainSize := by
  unfold actionActiveRows TopLevelCircuit.usableRowsAt
  exact le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)

@[simp]
theorem actionActiveRows_eq
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    actionActiveRows = ActionPermutationDomain.activeRows pp urs := by
  simp [actionActiveRows, ActionPermutationDomain.activeRows,
    TopLevelCircuit.usableRowsAt]

/-- Every keygen copy tuple is in range: 15 permutation columns, `2^11` rows. -/
theorem actionCopyBounds : ∀ t ∈ actionCopyRaw, t.1 < actionNumPermCols ∧
    t.2.1 < actionDomainSize ∧ t.2.2.1 < actionNumPermCols ∧
    t.2.2.2 < actionDomainSize := by
  native_decide

/-- The decoded Action copy list. -/
def actionCopies :
    List (FlatCell actionNumPermCols actionDomainSize ×
      FlatCell actionNumPermCols actionDomainSize) :=
  decodeCopies actionNumPermCols actionDomainSize actionCopyRaw actionCopyBounds

/-- Decoded copy pairs whose endpoints escape the usable-row prefix. -/
def actionCopyActiveRowFailures :
    List (FlatCell actionNumPermCols actionDomainSize ×
      FlatCell actionNumPermCols actionDomainSize) :=
  actionCopies.filter fun pair =>
    decide (¬ (
      (pair.1.2 : ℕ) < actionActiveRows ∧
        (pair.2.2 : ℕ) < actionActiveRows))

/-- Every Action keygen copy endpoint lies in the usable-row prefix. -/
theorem actionCopyActiveRowFailures_eq_nil :
    actionCopyActiveRowFailures = [] := by
  native_decide

/-- Pointwise usable-row bounds extracted from the finite copy diagnostic. -/
theorem actionCopyRowsActive
    (pair : FlatCell actionNumPermCols actionDomainSize ×
      FlatCell actionNumPermCols actionDomainSize)
    (hpair : pair ∈ actionCopies) :
    (pair.1.2 : ℕ) < actionActiveRows ∧
      (pair.2.2 : ℕ) < actionActiveRows := by
  by_contra hnot
  have hfailure : pair ∈ actionCopyActiveRowFailures := by
    rw [actionCopyActiveRowFailures, List.mem_filter]
    exact ⟨hpair, decide_eq_true hnot⟩
  rw [actionCopyActiveRowFailures_eq_nil] at hfailure
  simp at hfailure

/-- Action keygen replays preserve the usable-row prefix. -/
theorem actionReplayPreservesActive
    (cell : FlatCell actionNumPermCols actionDomainSize)
    (hcell : (cell.2 : ℕ) < actionActiveRows) :
    ((replayKeygenPermutation actionCopies cell).2 : ℕ) <
      actionActiveRows := by
  apply replayKeygenPermutation_preserves actionCopies
    (fun candidate => (candidate.2 : ℕ) < actionActiveRows)
  · intro pair hpair
    exact actionCopyRowsActive pair hpair
  · exact hcell

set_option maxRecDepth 100000 in
/-- The Action permutation argument has three chunks. -/
theorem actionNumPermutationSets_eq
    (pp : ProofParams) :
    (ActionPermutationDomain.actionShape pp).numPermutationSets = 3 := by
  change
    (orchardActionTopLevelCircuit.constraintSystem.permutationColumns.length +
        orchardActionTopLevelCircuit.constraintSystem.chunkLen - 1) /
      orchardActionTopLevelCircuit.constraintSystem.chunkLen = 3
  have hdata := ActionPermutationDomain.columnCount_chunkLen_eq
  have hcolumns :
      orchardActionTopLevelCircuit.constraintSystem.permutationColumns.length =
        15 :=
    congrArg Prod.fst hdata
  have hchunkLen :
      orchardActionTopLevelCircuit.constraintSystem.chunkLen = 7 :=
    congrArg Prod.snd hdata
  rw [hcolumns, hchunkLen]

/-- The Action permutation argument has 15 columns. -/
theorem actionNumPermCols_eq : actionNumPermCols = 15 := by
  native_decide

set_option maxRecDepth 100000 in
/-- The Action permutation chunk width is seven. -/
theorem actionChunkLen_eq
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G) :
    (ActionPermutationDomain.actionVk pp urs).chunkLen = 7 := by
  change orchardActionTopLevelCircuit.constraintSystem.chunkLen = 7
  exact congrArg Prod.snd
    ActionPermutationDomain.columnCount_chunkLen_eq

set_option maxRecDepth 100000 in
/-- Resolver-backed Action permutation chunks have the exact `[7,7,1]` widths. -/
theorem actionResolverChunkWidth
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs)
    (chunk :
      Fin (ActionPermutationDomain.actionShape pp).numPermutationSets) :
    (ResolverPermutationPairs
        (ActionPermutationDomain.actionVk pp urs)
        poly proofIndex chunk).length =
      min (ActionPermutationDomain.actionVk pp urs).chunkLen
        (actionNumPermCols -
          (chunk : ℕ) *
            (ActionPermutationDomain.actionVk pp urs).chunkLen) := by
  simp only [ResolverPermutationPairs,
    permutationChunkPairsOfResolver, List.length_map]
  rw [ActionPermutationDomain.permutationChunks_eq,
    actionChunkLen_eq, actionNumPermCols_eq]
  have hchunk : (chunk : ℕ) < 3 := by
    simpa only [actionNumPermutationSets_eq] using chunk.isLt
  have hcases :
      (chunk : ℕ) = 0 ∨ (chunk : ℕ) = 1 ∨ (chunk : ℕ) = 2 := by
    omega
  rcases hcases with hzero | hone | htwo
  · simp [hzero]
  · simp [hone]
  · simp [htwo]

/-- Flatten the derived `[7,7,1]` Action chunks to `(row, global column)`. -/
noncomputable def actionChunkFlatten
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs) :
    ResolverPermutationCell
        (ActionPermutationDomain.actionVk pp urs)
        poly proofIndex actionDomainSize ≃
      Fin actionDomainSize × Fin actionNumPermCols :=
  Layout.Asm.chunkFlatten
    (ActionPermutationDomain.actionShape pp).numPermutationSets
    actionNumPermCols
    (ActionPermutationDomain.actionVk pp urs).chunkLen
    actionDomainSize
    (fun chunk =>
      (ResolverPermutationPairs
        (ActionPermutationDomain.actionVk pp urs)
        poly proofIndex chunk).length)
    (by rw [actionChunkLen_eq]; decide)
    (by
      rw [actionNumPermCols_eq, actionNumPermutationSets_eq,
        actionChunkLen_eq]
      decide)
    (actionResolverChunkWidth pp urs poly proofIndex)

/-- The full-domain Action keygen permutation in resolver chunk coordinates. -/
noncomputable def actionFullSigma
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs) :
    Equiv.Perm
      (ResolverPermutationCell
        (ActionPermutationDomain.actionVk pp urs)
        poly proofIndex actionDomainSize) :=
  chunkPermutationOfFlat
    (actionChunkFlatten pp urs poly proofIndex)
    ((Equiv.prodComm
        (Fin actionNumPermCols) (Fin actionDomainSize)).permCongr
      (replayKeygenPermutation actionCopies))

/-- The full-domain Action replay sends active chunk cells to active chunk
cells. This is structural after the finite endpoint-row certificate: flattening
and unflattening preserve the row coordinate. -/
theorem actionFullSigma_preservesActive
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs)
    (cell : ResolverPermutationCell
      (ActionPermutationDomain.actionVk pp urs)
      poly proofIndex actionActiveRows) :
    (((actionFullSigma pp urs poly proofIndex)
        (widenPermutationChunkCell actionActiveRows_le_domainSize cell)).2.1 :
      ℕ) < actionActiveRows := by
  let flat : FlatCell actionNumPermCols actionDomainSize :=
    (Equiv.prodComm (Fin actionNumPermCols) (Fin actionDomainSize)).symm
      (actionChunkFlatten pp urs poly proofIndex
        (widenPermutationChunkCell actionActiveRows_le_domainSize cell))
  have hflat : (flat.2 : ℕ) < actionActiveRows := by
    change
      (((actionChunkFlatten pp urs poly proofIndex)
        (widenPermutationChunkCell actionActiveRows_le_domainSize cell)).1 :
        ℕ) < actionActiveRows
    simpa only [actionChunkFlatten,
      _root_.Zcash.Snark.Layout.Asm.chunkFlatten_apply_row,
      widenPermutationChunkCell_row] using cell.2.1.isLt
  have hreplay := actionReplayPreservesActive flat hflat
  simpa only [actionFullSigma, chunkPermutationOfFlat_apply,
    Equiv.permCongr_apply, Equiv.prodComm_apply, actionChunkFlatten,
    _root_.Zcash.Snark.Layout.Asm.chunkFlatten_symm_apply_row, flat] using hreplay

/-- Restrict the full Action keygen replay to the usable-row prefix. -/
noncomputable def actionActiveSigma
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs) :
    Equiv.Perm
      (ResolverPermutationCell
        (ActionPermutationDomain.actionVk pp urs)
        poly proofIndex actionActiveRows) :=
  Layout.Asm.restrictActivePerm actionActiveRows_le_domainSize
    (actionFullSigma pp urs poly proofIndex)
    (actionFullSigma_preservesActive pp urs poly proofIndex)

/-- The active Action replay is the restriction of its full-domain replay. -/
theorem actionActiveSigma_widen
    {G : Type} [AddCommGroup G] [Inhabited G]
    (pp : ProofParams) (urs : URS G)
    (poly : CommitmentId → Polynomial Fp)
    (proofIndex :
      Fin (ActionPermutationDomain.actionShape pp).numProofs)
    (cell : ResolverPermutationCell
      (ActionPermutationDomain.actionVk pp urs)
      poly proofIndex actionActiveRows) :
    widenPermutationChunkCell actionActiveRows_le_domainSize
        (actionActiveSigma pp urs poly proofIndex cell) =
      actionFullSigma pp urs poly proofIndex
        (widenPermutationChunkCell actionActiveRows_le_domainSize cell) :=
  Layout.Asm.restrictActivePerm_widen
    actionActiveRows_le_domainSize
    (actionFullSigma pp urs poly proofIndex)
    (actionFullSigma_preservesActive pp urs poly proofIndex)
    cell

/-- A raw coordinate pair as a typed Action permutation cell (`mod` totalization —
the identity on every in-range coordinate, and every declared coordinate is). -/
def mkActionCell (p : ℕ × ℕ) : FlatCell actionNumPermCols actionDomainSize :=
  (⟨p.1 % actionNumPermCols, Nat.mod_lt _ actionNumPermCols_pos⟩,
    ⟨p.2 % actionDomainSize, Nat.mod_lt _ actionDomainSize_pos⟩)

/-- The Action endpoint encoding: region cells through the placement, instance
endpoints at their absolute rows, constants at their first allocated
constants-column cell. -/
def actionCopyEncode : CopyEndpoint Fp → FlatCell actionNumPermCols actionDomainSize
  | .cell c => mkActionCell
      (resolveCell actionPermCols orchardActionTopLevelCircuit.regionStarts c)
  | .instance col row => mkActionCell (permIndex actionPermCols col.toAny, row)
  | .constant v => mkActionCell
      (match actionConsts.find? (fun e => e.1 = v.val) with
        | some e => (permIndex actionPermCols (ColRef.toAny (.fixed e.2.1)), e.2.2)
        | none => (0, 0))

/-- The Action cell valuation: the environment read of the cell's permutation column
at the cell's absolute row. -/
def actionCopyValue (env : Environment Fp)
    (fc : FlatCell actionNumPermCols actionDomainSize) : Fp :=
  env.get (ColRef.toAny (actionPermCols.getD (fc.1 : ℕ) (.advice 0)))
    (((fc.2 : ℕ) : ℕ) : ℤ)

/-- The concrete column/row denoted directly by an Action copy endpoint. -/
def actionEndpointAddress : CopyEndpoint Fp → AnyColumn × ℕ
  | .cell c =>
      (c.column,
        orchardActionTopLevelCircuit.regionStarts.getD c.regionIndex 0 +
          c.rowOffset)
  | .instance column row => (column.toAny, row)
  | .constant value =>
      match actionConsts.find? (fun entry => entry.1 = value.val) with
      | some entry => (ColRef.toAny (.fixed entry.2.1), entry.2.2)
      | none => (ColRef.toAny (.advice 0), 0)

/-- The concrete column/row recovered after encoding an Action endpoint. -/
def actionEncodedAddress (endpoint : CopyEndpoint Fp) : AnyColumn × ℕ :=
  let encoded := actionCopyEncode endpoint
  (ColRef.toAny
      (actionPermCols.getD (encoded.1 : ℕ) (.advice 0)),
    encoded.2)

/-- Every endpoint occurring in the declared Action copy stream. -/
def actionDeclaredEndpoints : List (CopyEndpoint Fp) :=
  (operationDeclaredCopies
      (orchardActionTopLevelCircuit.operations 0)).flatMap
    fun copy => [copy.1, copy.2]

/--
Finite diagnostic for declared endpoints whose encoded permutation cell does not
decode to the endpoint's concrete column and row.
-/
def actionCopyAddressFailures : List (CopyEndpoint Fp) :=
  let endpoints := actionDeclaredEndpoints
  endpoints.filter fun endpoint =>
    decide (actionEncodedAddress endpoint ≠ actionEndpointAddress endpoint)

/-- Whether a constant endpoint has a V1 constants allocation. -/
def actionConstantAllocated : CopyEndpoint Fp → Bool
  | .constant value =>
      (actionConsts.find? (fun entry => entry.1 = value.val)).isSome
  | _ => true

/-- Declared endpoints whose constant value has no V1 allocation. -/
def actionMissingConstantAllocations : List (CopyEndpoint Fp) :=
  let endpoints := actionDeclaredEndpoints
  endpoints.filter fun endpoint => !actionConstantAllocated endpoint

/-- Positional Action constant sites paired with their V1 allocation entries. -/
def actionConstantAllocations :
    List ((Cell × Fp) × (ℕ × ℕ × ℕ)) :=
  (operationConstSites (orchardActionTopLevelCircuit.operations 0)).zip
    actionConsts

/-- Positional constant allocations whose stored natural value disagrees with the site. -/
def actionConstantValueFailures :
    List ((Cell × Fp) × (ℕ × ℕ × ℕ)) :=
  actionConstantAllocations.filter fun allocation =>
    decide (allocation.2.1 ≠ allocation.1.2.val)

/-- Decode a raw Action permutation coordinate back to its concrete column and row. -/
def actionRawCellAddress (coordinate : ℕ × ℕ) : AnyColumn × ℕ :=
  let cell := mkActionCell coordinate
  (ColRef.toAny
      (actionPermCols.getD (cell.1 : ℕ) (.advice 0)),
    cell.2)

/-- Allocated constant cells that fail the permutation-column address roundtrip. -/
def actionConstantCellAddressFailures : List (ℕ × ℕ × ℕ) :=
  actionConsts.filter fun entry =>
    decide (
      actionRawCellAddress
          (permIndex actionPermCols
              (ColRef.toAny (.fixed entry.2.1)),
            entry.2.2) ≠
        (ColRef.toAny (.fixed entry.2.1), entry.2.2))

/--
The Action layout compiler preserves the concrete address of every declared
copy endpoint through finite permutation-cell encoding.
-/
theorem actionCopyAddressFailures_eq_nil :
    actionCopyAddressFailures = [] := by
  native_decide

/-- Every declared Action constant endpoint has a V1 constants allocation. -/
theorem actionMissingConstantAllocations_eq_nil :
    actionMissingConstantAllocations = [] := by
  native_decide

/-- V1 allocates at least one fixed cell for every Action constant site. -/
theorem actionConstantSites_fit :
    (operationConstSites
        (orchardActionTopLevelCircuit.operations 0)).length ≤
      actionConsts.length := by
  native_decide

/-- The positional V1 allocation stores the value of every Action constant site. -/
theorem actionConstantValueFailures_eq_nil :
    actionConstantValueFailures = [] := by
  native_decide

/-- Every allocated Action constant cell survives permutation-coordinate encoding. -/
theorem actionConstantCellAddressFailures_eq_nil :
    actionConstantCellAddressFailures = [] := by
  native_decide

/-- A member of the positional allocation zip stores its site's field value. -/
theorem actionConstantAllocation_value
    {site : Cell × Fp} {entry : ℕ × ℕ × ℕ}
    (hallocation : (site, entry) ∈ actionConstantAllocations) :
    entry.1 = site.2.val := by
  by_contra hne
  have hfailure : (site, entry) ∈ actionConstantValueFailures := by
    rw [actionConstantValueFailures, List.mem_filter]
    exact ⟨hallocation, decide_eq_true hne⟩
  rw [actionConstantValueFailures_eq_nil] at hfailure
  simp at hfailure

/-- An allocated Action constant cell has the expected concrete address. -/
theorem actionConstantCellAddress
    {entry : ℕ × ℕ × ℕ} (hentry : entry ∈ actionConsts) :
    actionRawCellAddress
        (permIndex actionPermCols
            (ColRef.toAny (.fixed entry.2.1)),
          entry.2.2) =
      (ColRef.toAny (.fixed entry.2.1), entry.2.2) := by
  by_contra hne
  have hfailure : entry ∈ actionConstantCellAddressFailures := by
    rw [actionConstantCellAddressFailures, List.mem_filter]
    exact ⟨hentry, decide_eq_true hne⟩
  rw [actionConstantCellAddressFailures_eq_nil] at hfailure
  simp at hfailure

/-- Either endpoint of a declared copy occurs in `actionDeclaredEndpoints`. -/
theorem mem_actionDeclaredEndpoints
    {copy : DeclaredCopy Fp}
    (hcopy : copy ∈ operationDeclaredCopies
      (orchardActionTopLevelCircuit.operations 0)) :
    copy.1 ∈ actionDeclaredEndpoints ∧
      copy.2 ∈ actionDeclaredEndpoints := by
  constructor
  · rw [actionDeclaredEndpoints, List.mem_flatMap]
    exact ⟨copy, hcopy, by simp⟩
  · rw [actionDeclaredEndpoints, List.mem_flatMap]
    exact ⟨copy, hcopy, by simp⟩

/-- Declared endpoint encoding preserves its concrete address. -/
theorem actionEncodedAddress_eq
    {endpoint : CopyEndpoint Fp}
    (hendpoint : endpoint ∈ actionDeclaredEndpoints) :
    actionEncodedAddress endpoint = actionEndpointAddress endpoint := by
  by_contra hne
  have hfailure : endpoint ∈ actionCopyAddressFailures := by
    rw [actionCopyAddressFailures, List.mem_filter]
    exact ⟨hendpoint, decide_eq_true hne⟩
  rw [actionCopyAddressFailures_eq_nil] at hfailure
  simp at hfailure

/-- A declared constant endpoint has a concrete allocation entry of that value. -/
theorem exists_actionConst_of_declared
    {value : Fp}
    (hendpoint :
      CopyEndpoint.constant value ∈ actionDeclaredEndpoints) :
    ∃ entry ∈ actionConsts, entry.1 = value.val := by
  have hnotMissing :
      CopyEndpoint.constant value ∉ actionMissingConstantAllocations := by
    rw [actionMissingConstantAllocations_eq_nil]
    simp
  have hisSome :
      (actionConsts.find? (fun entry => entry.1 = value.val)).isSome = true := by
    cases hfind :
        actionConsts.find? (fun entry => entry.1 = value.val) with
    | none =>
        exfalso
        apply hnotMissing
        rw [actionMissingConstantAllocations, List.mem_filter]
        exact ⟨hendpoint, by
          simp [actionConstantAllocated, hfind]⟩
    | some entry =>
        simp
  obtain ⟨entry, hfind⟩ :
      ∃ entry,
        actionConsts.find? (fun entry => entry.1 = value.val) = some entry := by
    exact Option.isSome_iff_exists.mp hisSome
  have hmem : entry ∈ actionConsts :=
    List.mem_of_find?_eq_some hfind
  have hvalue :
      entry.1 = value.val := by
    simpa using List.find?_some hfind
  exact ⟨entry, hmem, hvalue⟩

/--
A declared Action constant copy has its positional V1 allocation and the
corresponding raw keygen copy tuple.
-/
theorem actionConstantRawPair
    {cell : Cell} {value : Fp}
    (hcopy :
      (CopyEndpoint.cell cell, CopyEndpoint.constant value) ∈
        operationDeclaredCopies
          (orchardActionTopLevelCircuit.operations 0)) :
    ∃ entry ∈ actionConsts,
      entry.1 = value.val ∧
        (permIndex actionPermCols
            (ColRef.toAny (.fixed entry.2.1)),
          entry.2.2,
          (resolveCell actionPermCols
            orchardActionTopLevelCircuit.regionStarts cell).1,
          (resolveCell actionPermCols
            orchardActionTopLevelCircuit.regionStarts cell).2) ∈
          actionCopyRaw := by
  have hsite :
      (cell, value) ∈
        operationConstSites
          (orchardActionTopLevelCircuit.operations 0) :=
    mem_operationConstSites_of_declared_constant
      (orchardActionTopLevelCircuit.operations 0) cell value hcopy
  obtain ⟨entry, hallocation⟩ :=
    exists_mem_zip_of_mem_left
      (operationConstSites
        (orchardActionTopLevelCircuit.operations 0))
      actionConsts actionConstantSites_fit hsite
  have hentry : entry ∈ actionConsts :=
    (List.of_mem_zip hallocation).2
  have hvalue : entry.1 = value.val :=
    actionConstantAllocation_value hallocation
  refine ⟨entry, hentry, hvalue, ?_⟩
  have hgo :=
    (V1_go_snd_eq actionPermCols
      orchardActionTopLevelCircuit.regionStarts
      (orchardActionTopLevelCircuit.operations 0)
      actionConsts actionConstantSites_fit).1
  have hmapped :
      (permIndex actionPermCols
          (ColRef.toAny (.fixed entry.2.1)),
        entry.2.2,
        (resolveCell actionPermCols
          orchardActionTopLevelCircuit.regionStarts cell).1,
        (resolveCell actionPermCols
          orchardActionTopLevelCircuit.regionStarts cell).2) ∈
        ((operationConstSites
            (orchardActionTopLevelCircuit.operations 0)).zip
          actionConsts).map (fun siteEntry =>
            (permIndex actionPermCols
                (ColRef.toAny (.fixed siteEntry.2.2.1)),
              siteEntry.2.2.2,
              (resolveCell actionPermCols
                orchardActionTopLevelCircuit.regionStarts
                siteEntry.1.1).1,
              (resolveCell actionPermCols
                orchardActionTopLevelCircuit.regionStarts
                siteEntry.1.1).2)) := by
    exact List.mem_map.mpr ⟨((cell, value), entry), hallocation, rfl⟩
  rw [← hgo] at hmapped
  rw [actionCopyRaw, Halo2.Layout.V1.copyList]
  exact List.mem_append_right _ hmapped

/-- Decode membership in the raw Action copy list to a typed copy pair. -/
theorem exists_actionCopy_of_raw
    {tuple : ℕ × ℕ × ℕ × ℕ} (hraw : tuple ∈ actionCopyRaw) :
    ∃ pair ∈ actionCopies,
      pair.1.pair = (tuple.1, tuple.2.1) ∧
        pair.2.pair = (tuple.2.2.1, tuple.2.2.2) := by
  have hrawMap :
      actionCopyRaw = actionCopies.map
        (fun pair =>
          (pair.1.pair.1, pair.1.pair.2,
            pair.2.pair.1, pair.2.pair.2)) :=
    (decodeCopies_map actionNumPermCols actionDomainSize
      actionCopyRaw actionCopyBounds).symm
  rw [hrawMap, List.mem_map] at hraw
  obtain ⟨pair, hpair, htuple⟩ := hraw
  refine ⟨pair, hpair, ?_, ?_⟩
  · rw [← htuple]
  · rw [← htuple]

/-- `actionCopyValue` is exactly the environment read at the encoded address. -/
theorem actionCopyValue_eq_encodedAddress
    (env : Environment Fp) (endpoint : CopyEndpoint Fp) :
    actionCopyValue env (actionCopyEncode endpoint) =
      env.get (actionEncodedAddress endpoint).1
        ((actionEncodedAddress endpoint).2 : ℤ) := by
  rfl

/-- `actionCopyValue` at a raw coordinate reads its decoded concrete address. -/
theorem actionCopyValue_mkActionCell
    (env : Environment Fp) (coordinate : ℕ × ℕ) :
    actionCopyValue env (mkActionCell coordinate) =
      env.get (actionRawCellAddress coordinate).1
        ((actionRawCellAddress coordinate).2 : ℤ) := by
  rfl

/--
Cell and instance endpoints read back directly after Action permutation-cell
encoding. Constant endpoints additionally need committed fixed-row realization.
-/
theorem actionNonconstantEndpointRead
    (env : Environment Fp)
    {endpoint : CopyEndpoint Fp}
    (hendpoint : endpoint ∈ actionDeclaredEndpoints)
    (hnonconstant : ∀ value, endpoint ≠ .constant value) :
    endpoint.eval orchardActionTopLevelCircuit.placement env =
      actionCopyValue env (actionCopyEncode endpoint) := by
  have haddress := actionEncodedAddress_eq hendpoint
  rw [actionCopyValue_eq_encodedAddress, haddress]
  cases endpoint with
  | cell cell =>
      rfl
  | «instance» column row =>
      rfl
  | constant value =>
      exact absurd rfl (hnonconstant value)

/--
A declared constant endpoint reads back through its allocated fixed cell, or the
shared fixed-commitment exceptional branch fires.
-/
theorem actionConstantEndpointRead_or_bad
    (env : Environment Fp) {Bad : Prop}
    (fixedRead : ∀ {column row value : ℕ},
      (column, row, value) ∈
          topLevelRequiredFixedEntries orchardActionTopLevelCircuit →
        env.fixed ⟨column⟩ (row : ℤ) = (value : Fp) ∨ Bad)
    (value : Fp)
    (hendpoint :
      CopyEndpoint.constant value ∈ actionDeclaredEndpoints) :
    (CopyEndpoint.constant value).eval
        orchardActionTopLevelCircuit.placement env =
          actionCopyValue env
            (actionCopyEncode (.constant value)) ∨
      Bad := by
  obtain ⟨witness, hwitnessMem, hwitnessValue⟩ :=
    exists_actionConst_of_declared hendpoint
  cases hfind :
      actionConsts.find? (fun entry => entry.1 = value.val) with
  | none =>
      have hsome :
          (actionConsts.find? (fun entry => entry.1 = value.val)).isSome =
            true := by
        exact List.find?_isSome.mpr
          ⟨witness, hwitnessMem, decide_eq_true hwitnessValue⟩
      simp [hfind] at hsome
  | some entry =>
      have hentryMem : entry ∈ actionConsts :=
        List.mem_of_find?_eq_some hfind
      have hentryValue : entry.1 = value.val := by
        simpa using List.find?_some hfind
      have hconstantEntry :
          (entry.2.1, entry.2.2, entry.1) ∈
            topLevelConstantEntries orchardActionTopLevelCircuit := by
        rw [topLevelConstantEntries, Layout.constantsFixed, List.mem_map]
        exact ⟨entry, hentryMem, rfl⟩
      have hrequired :
          (entry.2.1, entry.2.2, entry.1) ∈
            topLevelRequiredFixedEntries orchardActionTopLevelCircuit := by
        simp only [topLevelRequiredFixedEntries, List.mem_append]
        exact Or.inl (Or.inr hconstantEntry)
      rcases fixedRead hrequired with hread | hbad
      · apply Or.inl
        have haddress := actionEncodedAddress_eq hendpoint
        rw [actionCopyValue_eq_encodedAddress, haddress,
          actionEndpointAddress, hfind]
        change value = env.fixed ⟨entry.2.1⟩ (entry.2.2 : ℤ)
        simpa [hentryValue] using hread.symm
      · exact Or.inr hbad

/-- A typed cell is its raw coordinate pair, so the `mod` totalization is inert. -/
theorem mkActionCell_eq_of_pair {fc : FlatCell actionNumPermCols actionDomainSize}
    {p : ℕ × ℕ} (h : fc.pair = p) : mkActionCell p = fc := by
  rcases fc with ⟨a, b⟩
  subst h
  show (⟨(a : ℕ) % actionNumPermCols, _⟩, ⟨(b : ℕ) % actionDomainSize, _⟩) = (a, b)
  refine Prod.ext_iff.mpr ⟨Fin.ext ?_, Fin.ext ?_⟩
  · exact Nat.mod_eq_of_lt a.isLt
  · exact Nat.mod_eq_of_lt b.isLt

/-- **Declared-copy linkage.** Every resolvable declared copy's encoded endpoints are
linked by the decoded keygen copy list: membership through the floor planner, decoding
through the bounds certificate, and the replay pair link. -/
theorem actionCopyLink :
    ∀ copy ∈ operationDeclaredCopies (orchardActionTopLevelCircuit.operations 0),
      ∀ tuple, resolveDeclared actionPermCols
          orchardActionTopLevelCircuit.regionStarts copy = some tuple →
        (replayKeygenPermutation actionCopies).SameCycle
          (actionCopyEncode copy.1) (actionCopyEncode copy.2) := by
  intro copy hcopy tuple hres
  have hmem : tuple ∈ actionCopyRaw :=
    mem_V1_copyList_of_declared actionPermCols
      orchardActionTopLevelCircuit.regionStarts
      (orchardActionTopLevelCircuit.operations 0) actionConsts copy tuple hres hcopy
  have hraw : actionCopyRaw = actionCopies.map
      (fun p => (p.1.pair.1, p.1.pair.2, p.2.pair.1, p.2.pair.2)) :=
    (decodeCopies_map actionNumPermCols actionDomainSize actionCopyRaw
      actionCopyBounds).symm
  rw [hraw, List.mem_map] at hmem
  obtain ⟨pr, hpr, henc⟩ := hmem
  have hlinked := replayKeygenPermutation_pair_linked actionCopies hpr
  have hp1 : pr.1.pair = (tuple.1, tuple.2.1) := by
    rw [← henc]
  have hp2 : pr.2.pair = (tuple.2.2.1, tuple.2.2.2) := by
    rw [← henc]
  -- identify the encoded endpoints with the decoded pair, by copy kind
  rcases copy with ⟨e1, e2⟩
  cases e1 with
  | cell l =>
      cases e2 with
      | cell r =>
          simp only [resolveDeclared] at hres
          obtain rfl := Option.some.inj hres
          rw [show actionCopyEncode (.cell l) = pr.1 from
              mkActionCell_eq_of_pair (by rw [hp1]),
            show actionCopyEncode (.cell r) = pr.2 from
              mkActionCell_eq_of_pair (by rw [hp2])]
          exact hlinked
      | «instance» col row =>
          simp only [resolveDeclared] at hres
          obtain rfl := Option.some.inj hres
          rw [show actionCopyEncode (.cell l) = pr.1 from
              mkActionCell_eq_of_pair (by rw [hp1]),
            show actionCopyEncode (.instance col row) = pr.2 from
              mkActionCell_eq_of_pair (by rw [hp2])]
          exact hlinked
      | constant v => simp [resolveDeclared] at hres
  | «instance» col row => simp [resolveDeclared] at hres
  | constant v => simp [resolveDeclared] at hres

/-- **The Action copy-replay witness.** Kind-dispatched from three leaf families over
the concrete data: value agreement along each decoded keygen copy (the σ-semantics
transport), value agreement of each declared constant copy (two constants-column
reads), and the declared-endpoint read equations (resolution coordinates). -/
noncomputable def actionCopyReplayWitness
    (env : Environment Fp) {Bad : Prop}
    (hpairval : ∀ pr ∈ actionCopies,
      actionCopyValue env pr.1 = actionCopyValue env pr.2 ∨ Bad)
    (hconstval : ∀ copy ∈ operationDeclaredCopies
        (orchardActionTopLevelCircuit.operations 0),
      ∀ c v, copy = (.cell c, .constant v) →
        actionCopyValue env (actionCopyEncode (.cell c)) =
          actionCopyValue env (actionCopyEncode (.constant v)) ∨ Bad)
    (hread : ∀ copy ∈ operationDeclaredCopies
        (orchardActionTopLevelCircuit.operations 0),
      copy.1.eval orchardActionTopLevelCircuit.placement env =
          actionCopyValue env (actionCopyEncode copy.1) ∧
        copy.2.eval orchardActionTopLevelCircuit.placement env =
          actionCopyValue env (actionCopyEncode copy.2)) :
    CopyReplayWitness orchardActionTopLevelCircuit.placement env
      (orchardActionTopLevelCircuit.operations 0)
      (FlatCell actionNumPermCols actionDomainSize) Bad :=
  Zcash.Snark.Layout.Asm.CopyReplayWitness.ofPairValues actionCopyEncode (actionCopyValue env)
    (by
      intro pr hpr
      rw [encodeDeclaredCopies, List.mem_map] at hpr
      obtain ⟨copy, hcopy, rfl⟩ := hpr
      rcases declared_shape (orchardActionTopLevelCircuit.operations 0)
          actionPermCols orchardActionTopLevelCircuit.regionStarts copy hcopy with
        ⟨tuple, hres⟩ | ⟨c, v, hcv⟩
      · exact Zcash.Snark.Layout.Asm.value_eq_or_bad_of_replay_sameCycle (actionCopyValue env) _
          hpairval (actionCopyLink copy hcopy tuple hres)
      · subst hcv
        exact hconstval _ hcopy c v rfl)
    hread

/--
The value of a declared constant-copy cell agrees with the canonical encoded
constant cell, or the shared exceptional branch fires.

The keygen copy pair relates the advice cell to its *positional* constant
allocation. Both that allocation and the canonical same-value allocation read
the declared literal through fixed-row coherence.
-/
theorem actionConstantCopyValue_or_bad
    (env : Environment Fp) {Bad : Prop}
    (hpairval : ∀ pair ∈ actionCopies,
      actionCopyValue env pair.1 = actionCopyValue env pair.2 ∨ Bad)
    (fixedRead : ∀ {column row value : ℕ},
      (column, row, value) ∈
          topLevelRequiredFixedEntries orchardActionTopLevelCircuit →
        env.fixed ⟨column⟩ (row : ℤ) = (value : Fp) ∨ Bad)
    (copy : DeclaredCopy Fp)
    (hcopy : copy ∈ operationDeclaredCopies
      (orchardActionTopLevelCircuit.operations 0))
    (cell : Cell) (value : Fp)
    (hshape : copy = (.cell cell, .constant value)) :
    actionCopyValue env (actionCopyEncode (.cell cell)) =
        actionCopyValue env (actionCopyEncode (.constant value)) ∨
      Bad := by
  classical
  subst copy
  by_cases hbad : Bad
  · exact Or.inr hbad
  · apply Or.inl
    obtain ⟨entry, hentry, hentryValue, hraw⟩ :=
      actionConstantRawPair hcopy
    obtain ⟨pair, hpair, hpairLeft, hpairRight⟩ :=
      exists_actionCopy_of_raw hraw
    let constantCoordinate : ℕ × ℕ :=
      (permIndex actionPermCols
          (ColRef.toAny (.fixed entry.2.1)),
        entry.2.2)
    let cellCoordinate : ℕ × ℕ :=
      resolveCell actionPermCols
        orchardActionTopLevelCircuit.regionStarts cell
    have hleft :
        mkActionCell constantCoordinate = pair.1 := by
      apply mkActionCell_eq_of_pair
      simpa [constantCoordinate] using hpairLeft
    have hright :
        actionCopyEncode (.cell cell) = pair.2 := by
      apply mkActionCell_eq_of_pair
      simpa [actionCopyEncode, cellCoordinate] using hpairRight
    have hpairEq :
        actionCopyValue env (mkActionCell constantCoordinate) =
          actionCopyValue env (actionCopyEncode (.cell cell)) := by
      simpa only [hleft, hright] using
        (hpairval pair hpair).resolve_right hbad
    have hconstantEntry :
        (entry.2.1, entry.2.2, entry.1) ∈
          topLevelConstantEntries orchardActionTopLevelCircuit := by
      rw [topLevelConstantEntries, Layout.constantsFixed, List.mem_map]
      exact ⟨entry, hentry, rfl⟩
    have hrequired :
        (entry.2.1, entry.2.2, entry.1) ∈
          topLevelRequiredFixedEntries orchardActionTopLevelCircuit := by
      simp only [topLevelRequiredFixedEntries, List.mem_append]
      exact Or.inl (Or.inr hconstantEntry)
    have hfixed :=
      (fixedRead hrequired).resolve_right hbad
    have hpositional :
        actionCopyValue env (mkActionCell constantCoordinate) = value := by
      rw [actionCopyValue_mkActionCell,
        show actionRawCellAddress constantCoordinate =
            (ColRef.toAny (.fixed entry.2.1), entry.2.2) by
          simpa [constantCoordinate] using actionConstantCellAddress hentry]
      change env.fixed ⟨entry.2.1⟩ (entry.2.2 : ℤ) = value
      simpa [hentryValue] using hfixed
    have hendpoint :
        CopyEndpoint.constant value ∈ actionDeclaredEndpoints :=
      (mem_actionDeclaredEndpoints hcopy).2
    have hcanonical :=
      (actionConstantEndpointRead_or_bad
        env fixedRead value hendpoint).resolve_right hbad
    exact hpairEq.symm.trans (hpositional.trans hcanonical)

/--
Construct the Action copy witness, or return the shared exceptional branch,
without asking the caller for declared-endpoint read equations.

Nonconstant reads follow from the certified endpoint-address roundtrip. Constant
reads follow from the fixed compiler's allocated-constant realization. The two
remaining semantic inputs are pairwise σ-copy value agreement and linkage of a
constant declaration to its allocated copy pair.
-/
noncomputable def actionCopyReplayWitness_or_bad
    (env : Environment Fp) {Bad : Prop}
    (hpairval : ∀ pr ∈ actionCopies,
      actionCopyValue env pr.1 = actionCopyValue env pr.2 ∨ Bad)
    (hconstval : ∀ copy ∈ operationDeclaredCopies
        (orchardActionTopLevelCircuit.operations 0),
      ∀ c v, copy = (.cell c, .constant v) →
        actionCopyValue env (actionCopyEncode (.cell c)) =
          actionCopyValue env (actionCopyEncode (.constant v)) ∨ Bad)
    (fixedRead : ∀ {column row value : ℕ},
      (column, row, value) ∈
          topLevelRequiredFixedEntries orchardActionTopLevelCircuit →
        env.fixed ⟨column⟩ (row : ℤ) = (value : Fp) ∨ Bad) :
    Nonempty
        (CopyReplayWitness orchardActionTopLevelCircuit.placement env
          (orchardActionTopLevelCircuit.operations 0)
          (FlatCell actionNumPermCols actionDomainSize) Bad) ∨
      Bad := by
  classical
  by_cases hbad : Bad
  · exact Or.inr hbad
  · apply Or.inl
    constructor
    apply actionCopyReplayWitness env hpairval hconstval
    intro copy hcopy
    have hendpoints := mem_actionDeclaredEndpoints hcopy
    rcases declared_shape
        (orchardActionTopLevelCircuit.operations 0)
        actionPermCols orchardActionTopLevelCircuit.regionStarts
        copy hcopy with hresolved | hconstant
    · obtain ⟨tuple, hresolve⟩ := hresolved
      rcases copy with ⟨left, right⟩
      cases left with
      | cell leftCell =>
          cases right with
          | cell rightCell =>
              constructor
              · exact actionNonconstantEndpointRead env hendpoints.1
                  (by intro value h; cases h)
              · exact actionNonconstantEndpointRead env hendpoints.2
                  (by intro value h; cases h)
          | «instance» column row =>
              constructor
              · exact actionNonconstantEndpointRead env hendpoints.1
                  (by intro value h; cases h)
              · exact actionNonconstantEndpointRead env hendpoints.2
                  (by intro value h; cases h)
          | constant value =>
              simp [resolveDeclared] at hresolve
      | «instance» column row =>
          simp [resolveDeclared] at hresolve
      | constant value =>
          simp [resolveDeclared] at hresolve
    · obtain ⟨cell, value, hcopyShape⟩ := hconstant
      subst hcopyShape
      constructor
      · exact actionNonconstantEndpointRead env hendpoints.1
          (by intro other h; cases h)
      · exact
          (actionConstantEndpointRead_or_bad
            env fixedRead value hendpoints.2).resolve_right hbad

/--
The Action copy witness from the sole remaining semantic leaf: value agreement
on each decoded keygen copy pair. Constant-copy linkage and all declared endpoint
reads are derived internally from the compiler pipeline and fixed-row realization.
-/
noncomputable def actionCopyReplayWitness_ofPairValues_or_bad
    (env : Environment Fp) {Bad : Prop}
    (hpairval : ∀ pair ∈ actionCopies,
      actionCopyValue env pair.1 = actionCopyValue env pair.2 ∨ Bad)
    (fixedRead : ∀ {column row value : ℕ},
      (column, row, value) ∈
          topLevelRequiredFixedEntries orchardActionTopLevelCircuit →
        env.fixed ⟨column⟩ (row : ℤ) = (value : Fp) ∨ Bad) :
    Nonempty
        (CopyReplayWitness orchardActionTopLevelCircuit.placement env
          (orchardActionTopLevelCircuit.operations 0)
          (FlatCell actionNumPermCols actionDomainSize) Bad) ∨
      Bad :=
  actionCopyReplayWitness_or_bad env hpairval
    (fun copy hcopy cell value hshape =>
      actionConstantCopyValue_or_bad
        env hpairval fixedRead copy hcopy cell value hshape)
    fixedRead

end Zcash.Snark
