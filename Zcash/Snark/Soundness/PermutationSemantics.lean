import Zcash.Snark.Soundness.PermutationInstantiation

/-!
# Semantic endpoint for resolver-backed permutation constraints

`PermutationInstantiation` obtains the four polynomial divisibility families from the decoded
commitment resolver.  This file supplies the other half of the call to
`deployed_perm_copy_constraints_all_chunks`: the evaluation-domain facts, the keygen permutation
semantics, and the priced `β`/`γ` exclusions.

The keygen-facing record is intentionally independent of how the witness is obtained.  For the
Action circuit it should be instantiated by the layout replay and VK-matching work: its `sigma`
field is the replayed global cell permutation, and `mapsNames` says that the decoded common
permutation polynomials interpolate the names of the cells to which that permutation sends each
source cell.
-/

namespace Zcash.Snark

open Polynomial

set_option maxHeartbeats 20000

/-- Flatten a variable-width chunk cell to its global `(row, column)` coordinate.  The width bound
is exactly the verifier invariant that each permutation chunk contains at most `chunkLen` columns. -/
def flattenPermutationChunkCell {nc m chunkLen : ℕ} {width : ℕ → ℕ}
    (hwidth : ∀ c < nc, width c ≤ chunkLen) :
    ChunkCell nc m width → Fin m × Fin (nc * chunkLen)
  | ⟨c, i, j⟩ =>
      (i, ⟨c * chunkLen + j, by
        have hj : (j : ℕ) < chunkLen :=
          lt_of_lt_of_le j.isLt (hwidth c c.isLt)
        calc
          (c : ℕ) * chunkLen + j < (c : ℕ) * chunkLen + chunkLen :=
            Nat.add_lt_add_left hj _
          _ = ((c : ℕ) + 1) * chunkLen := (Nat.succ_mul _ _).symm
          _ ≤ nc * chunkLen :=
            Nat.mul_le_mul_right chunkLen (Nat.succ_le_of_lt c.isLt)⟩)

/-- Flattening is injective even when the final chunk is shorter than `chunkLen`. -/
theorem flattenPermutationChunkCell_injective
    {nc m chunkLen : ℕ} {width : ℕ → ℕ}
    (hwidth : ∀ c < nc, width c ≤ chunkLen) :
    Function.Injective (flattenPermutationChunkCell (m := m) hwidth) := by
  rintro ⟨c, i, j⟩ ⟨c', i', j'⟩ h
  simp only [flattenPermutationChunkCell, Prod.mk.injEq, Fin.mk.injEq] at h
  rcases h with ⟨hi, hoff⟩
  have hj : (j : ℕ) < chunkLen :=
    lt_of_lt_of_le j.isLt (hwidth c c.isLt)
  have hj' : (j' : ℕ) < chunkLen :=
    lt_of_lt_of_le j'.isLt (hwidth c' c'.isLt)
  have hc : (c : ℕ) = c' := by
    rcases lt_trichotomy (c : ℕ) c' with hlt | heq | hgt
    · have hle : (c : ℕ) + 1 ≤ c' := Nat.succ_le_iff.mpr hlt
      have hcol :
          (c : ℕ) * chunkLen + j < (c' : ℕ) * chunkLen + j' := by
        calc
          (c : ℕ) * chunkLen + j < (c : ℕ) * chunkLen + chunkLen :=
            Nat.add_lt_add_left hj _
          _ = ((c : ℕ) + 1) * chunkLen := (Nat.succ_mul _ _).symm
          _ ≤ (c' : ℕ) * chunkLen := Nat.mul_le_mul_right chunkLen hle
          _ ≤ (c' : ℕ) * chunkLen + j' := Nat.le_add_right _ _
      exact False.elim ((Nat.ne_of_lt hcol) hoff)
    · exact heq
    · have hle : (c' : ℕ) + 1 ≤ c := Nat.succ_le_iff.mpr hgt
      have hcol :
          (c' : ℕ) * chunkLen + j' < (c : ℕ) * chunkLen + j := by
        calc
          (c' : ℕ) * chunkLen + j' < (c' : ℕ) * chunkLen + chunkLen :=
            Nat.add_lt_add_left hj' _
          _ = ((c' : ℕ) + 1) * chunkLen := (Nat.succ_mul _ _).symm
          _ ≤ (c : ℕ) * chunkLen := Nat.mul_le_mul_right chunkLen hle
          _ ≤ (c : ℕ) * chunkLen + j := Nat.le_add_right _ _
      exact False.elim ((Nat.ne_of_gt hcol) hoff)
  have hcFin : c = c' := Fin.ext hc
  subst c'
  have hjFin : j = j' := Fin.ext (by simpa using hoff)
  subst j'
  subst i'
  rfl

/-- Injective names on the flat Halo2 column range induce injective names on the verifier's
variable-width permutation chunks. -/
theorem chunkRowName_injective_of_flat
    {omega delta : Fp} {nc m chunkLen : ℕ} {width : ℕ → ℕ}
    (hwidth : ∀ c < nc, width c ≤ chunkLen)
    (hflat : Function.Injective fun c : Fin m × Fin (nc * chunkLen) =>
      omega ^ (c.1 : ℕ) * delta ^ (c.2 : ℕ)) :
    Function.Injective fun c : ChunkCell nc m width =>
      chunkRowName omega delta chunkLen c.1 c.2.1 c.2.2 := by
  intro c d hname
  apply flattenPermutationChunkCell_injective hwidth
  apply hflat
  simpa [flattenPermutationChunkCell, chunkRowName, rowName] using hname

/-- The standard root-of-unity/coset conditions imply injectivity for all chunked cell names. -/
theorem chunkRowName_injective_of_coset
    {omega delta : Fp} {nc m chunkLen : ℕ} {width : ℕ → ℕ}
    (hwidth : ∀ c < nc, width c ≤ chunkLen)
    (hne : ∀ j : Fin (nc * chunkLen), delta ^ (j : ℕ) ≠ 0)
    (homega : omega ^ m = 1)
    (horder : ∀ i i' : ℕ, i < m → i' < m → omega ^ i = omega ^ i' → i = i')
    (hcoset : ∀ (j j' : Fin (nc * chunkLen)) (t : ℕ),
      delta ^ (j : ℕ) = omega ^ t * delta ^ (j' : ℕ) → j = j') :
    Function.Injective fun c : ChunkCell nc m width =>
      chunkRowName omega delta chunkLen c.1 c.2.1 c.2.2 :=
  chunkRowName_injective_of_flat hwidth
    (name_injective_of_coset (fun j : Fin (nc * chunkLen) => delta ^ (j : ℕ))
      hne homega horder hcoset)

/-- The polynomial pairs, indexed by permutation chunk, selected from one resolver-backed proof. -/
noncomputable abbrev ResolverPermutationPairs
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) : ℕ → List (Polynomial Fp × Polynomial Fp) :=
  permutationChunkPairsOfResolver vk poly p

/-- Cells covered by one resolver-backed permutation argument. -/
abbrev ResolverPermutationCell
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (m : ℕ) :=
  ChunkCell shape.numPermutationSets m
    (fun c => (ResolverPermutationPairs vk poly p c).length)

/-- VK structure and evaluation-domain facts needed after the polynomial constraints have been
extracted.  These are independent of the proof's committed witness columns. -/
structure ResolverPermutationDomain
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (l0 lLast lBlind : Polynomial Fp) (n m : ℕ) : Prop where
  nonempty : 0 < shape.numPermutationSets
  chunkCount : vk.permutationChunks.length = shape.numPermutationSets
  lastRotation :
    vk.omega ^ m = vk.omega ^ (-((vk.blindingFactors : ℤ) + 1))
  root : vk.omega ^ n = 1
  active : ∀ i < m,
    1 - (lLast.eval (vk.omega ^ i) + lBlind.eval (vk.omega ^ i)) ≠ 0
  firstSelector : l0.eval (vk.omega ^ 0) ≠ 0
  lastSelector : lLast.eval (vk.omega ^ m) ≠ 0

/-- The semantic content of the common permutation columns.

`mapsNames` connects each decoded common polynomial to the image of that cell under the replayed
keygen permutation. `namesInjective` is the usual root-of-unity/coset property of Halo2's
`ωⁱ · δʲ` cell names. -/
structure ResolverPermutationCycle
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (m : ℕ) where
  sigma : Equiv.Perm (ResolverPermutationCell vk poly p m)
  mapsNames : ∀ c : ResolverPermutationCell vk poly p m,
    chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p)
        c.1 c.2.1 c.2.2 =
      chunkRowName vk.omega vk.delta vk.chunkLen
        (sigma c).1 (sigma c).2.1 (sigma c).2.2
  namesInjective :
    Function.Injective fun c : ResolverPermutationCell vk poly p m =>
      chunkRowName vk.omega vk.delta vk.chunkLen c.1 c.2.1 c.2.2

/-- The two challenge exclusions used to recover the multiset of `(value, name)` pairs from the
grand-product identity.  They are kept separate from VK semantics because the forking/bad-set
accounting, rather than key generation, supplies them. -/
structure ResolverPermutationGoodChallenges
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (p : Fin shape.numProofs) (m : ℕ) : Prop where
  gamma : ch.gamma ∉ szBadSet (linProdDiff
    ((chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p))).map
        (fun q => q.1 + q.2 * ch.beta))
    ((chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen)).map
        (fun q => q.1 + q.2 * ch.beta)))
  beta : ∀ j, ch.beta ∉ szBadSet ((pairProdDiff
    (chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowSigmaName vk.omega (ResolverPermutationPairs vk poly p)))
    (chunkedCellPairs shape.numPermutationSets m
      (fun c => (ResolverPermutationPairs vk poly p c).length)
      (chunkRowValue vk.omega (ResolverPermutationPairs vk poly p))
      (chunkRowName vk.omega vk.delta vk.chunkLen))).coeff j)

/-- Resolver-backed full constraint satisfaction enforces equality on every replayed keygen
permutation cycle, apart from the explicit zero-factor branch already present in the permutation
soundness theorem.

The proof does no new algebra: it joins the polynomial half from
`ConstraintSatisfaction.resolverPermutationConstraints` to the domain, keygen-semantic, and
good-challenge halves at `deployed_perm_copy_constraints_all_chunks`. -/
theorem ConstraintSatisfaction.resolverPermutationCopyConstraints
    {shape : Shape} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (l0 lLast lBlind : Polynomial Fp)
    (p : Fin shape.numProofs) {n m : ℕ}
    (h : ConstraintSatisfaction
      (constraintModelOfPermutationResolver vk ch poly l0 lLast lBlind) n)
    (hdom : ResolverPermutationDomain vk l0 lLast lBlind n m)
    (hcycle : ResolverPermutationCycle vk poly p m)
    (hgood : ResolverPermutationGoodChallenges vk ch poly p m)
    {c d : ResolverPermutationCell vk poly p m}
    (hcd : hcycle.sigma.SameCycle c d) :
    chunkRowValue vk.omega (ResolverPermutationPairs vk poly p)
        c.1 c.2.1 c.2.2 =
      chunkRowValue vk.omega (ResolverPermutationPairs vk poly p)
        d.1 d.2.1 d.2.2
      ∨ ∃ chunk ∈ Finset.range shape.numPermutationSets,
          ∃ i ∈ Finset.range m,
          ∃ j ∈ Finset.range (ResolverPermutationPairs vk poly p chunk).length,
            chunkRowValue vk.omega (ResolverPermutationPairs vk poly p) chunk i j
                + ch.beta *
                  chunkRowName vk.omega vk.delta vk.chunkLen chunk i j
                + ch.gamma = 0 := by
  have hconstraints :=
    h.resolverPermutationConstraints vk ch poly l0 lLast lBlind p
      hdom.nonempty hdom.chunkCount hdom.lastRotation
  exact deployed_perm_copy_constraints_all_chunks
    vk.omega ch.beta ch.gamma vk.delta vk.chunkLen
    (fun chunk => poly (.permProduct p chunk))
    (ResolverPermutationPairs vk poly p)
    l0 lLast lBlind hdom.nonempty hcycle.sigma
    hconstraints.step hconstraints.chain hconstraints.start hconstraints.finish
    (by
      intro i
      rw [← pow_mul, Nat.mul_comm, pow_mul, hdom.root, one_pow])
    hdom.active hdom.firstSelector hdom.lastSelector
    hcycle.mapsNames hcycle.namesInjective hgood.gamma hgood.beta hcd

end Zcash.Snark
