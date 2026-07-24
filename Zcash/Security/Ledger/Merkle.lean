import Mathlib
import Zcash.Security.Common.RandomOracle

/-!
# Fixed-depth Merkle trees are position-binding, up to an exhibited hash collision

This module proves the Merkle lemma of the ledger-model layer: from a validating
authentication path for a leaf that is *not* the committed one at its position,
`Merkle.collisionOfWrongLeaf` **computes** a collision of the tree hash — a
`RandomOracle.Collision`, so the shared collision vocabulary applies directly. This is the
position-binding vector commitment property that the Balance and Spendability arguments
require of the note commitment tree.

The tree hash takes its two children as a pair (`H : B × B → B`), so a collision's data is
directly the two input pairs. Leaves are indexed by root-to-leaf paths `Fin d → Bool`
(`false` = left, `true` = right), so the tree is the full binary tree of depth `d` and no
arithmetic on positions is needed.

Per the breaks-as-computed-data convention (documented in `Zcash.Security.RandomOracle`):
collisions of a compressing hash always exist propositionally, so the reduction is a
computable function producing the collision as data, not a theorem with a `∨ ∃-collision`
conclusion. No hardness assumption appears here; prequantumly, collision-resistance of
Sinsemilla reduces to a DLR break (Zcash protocol specification Theorems 5.4.3 and 5.4.4).
For the ZIP 2005 Recovery Protocol, the Merkle tree will be rehashed using a hash function
that is assumed to be collapsing.
-/

namespace Zcash.Security.Ledger.Merkle

variable {B : Type*}

/-- The root of the depth-`d` full binary Merkle tree over leaves `f`, indexed by
root-to-leaf paths. -/
def root (H : B × B → B) : (d : ℕ) → ((Fin d → Bool) → B) → B
  | 0, f => f Fin.elim0
  | d+1, f =>
    H (root H d fun p => f (Fin.cons false p), root H d fun p => f (Fin.cons true p))

/-- Recompute the root from a claimed `leaf` at position `pos`, given the sibling subtree
values `sibs`, both indexed from the top level down. -/
def pathRoot (H : B × B → B) : (d : ℕ) → (Fin d → Bool) → (Fin d → B) → B → B
  | 0, _, _, leaf => leaf
  | d+1, pos, sibs, leaf =>
    let child := pathRoot H d (Fin.tail pos) (Fin.tail sibs) leaf
    H (cond (pos 0) (sibs 0) child, cond (pos 0) child (sibs 0))

/-- The honest authentication path for position `pos`: the sibling subtree root at each
level, from the top level down. -/
def authPath (H : B × B → B) : (d : ℕ) → ((Fin d → Bool) → B) → (Fin d → Bool) → Fin d → B
  | 0, _, _ => Fin.elim0
  | d+1, f, pos =>
    Fin.cons (root H d fun p => f (Fin.cons (!pos 0) p))
      (authPath H d (fun p => f (Fin.cons (pos 0) p)) (Fin.tail pos))

/-- The two candidate colliding input pairs located by descending a wrong-leaf opening: the
recomputed (path-side) pair and the tree-side pair, at the first level where the child
components differ. Pure data — the executable half of the reduction;
`collisionInputsOfWrongLeaf_spec` certifies the collision under the wrong-leaf hypotheses.
At depth `0` there is no pair, and the spec's hypotheses are contradictory, so any value
serves. -/
private def collisionInputsOfWrongLeaf [DecidableEq B] (H : B × B → B) :
    (d : ℕ) → ((Fin d → Bool) → B) → (Fin d → Bool) → (Fin d → B) → B → (B × B) × (B × B)
  | 0, _, _, _, leaf => ((leaf, leaf), (leaf, leaf))
  | d+1, f, pos, sibs, leaf =>
    let child := pathRoot H d (Fin.tail pos) (Fin.tail sibs) leaf
    let sub : Bool → B := fun i => root H d fun p => f (Fin.cons i p)
    if child = sub (pos 0) then
      collisionInputsOfWrongLeaf H d (fun p => f (Fin.cons (pos 0) p)) (Fin.tail pos)
        (Fin.tail sibs) leaf
    else
      ((cond (pos 0) (sibs 0) child, cond (pos 0) child (sibs 0)), (sub false, sub true))

/-- The located input pairs are distinct and hash equally: the certification half of the
reduction, by the same recursion as `collisionInputsOfWrongLeaf`. -/
private theorem collisionInputsOfWrongLeaf_spec [DecidableEq B] (H : B × B → B) :
    ∀ (d : ℕ) (f : (Fin d → Bool) → B) (pos : Fin d → Bool) (sibs : Fin d → B) (leaf : B),
      pathRoot H d pos sibs leaf = root H d f → leaf ≠ f pos →
      (collisionInputsOfWrongLeaf H d f pos sibs leaf).1
          ≠ (collisionInputsOfWrongLeaf H d f pos sibs leaf).2
        ∧ H (collisionInputsOfWrongLeaf H d f pos sibs leaf).1
            = H (collisionInputsOfWrongLeaf H d f pos sibs leaf).2
  | 0, f, _, _, _, h, hne =>
    absurd (h.trans (congrArg f (funext fun i => i.elim0))) hne
  | d+1, f, pos, sibs, leaf, h, hne => by
    have h' : H (cond (pos 0) (sibs 0) (pathRoot H d (Fin.tail pos) (Fin.tail sibs) leaf),
          cond (pos 0) (pathRoot H d (Fin.tail pos) (Fin.tail sibs) leaf) (sibs 0))
        = H (root H d fun p => f (Fin.cons false p),
             root H d fun p => f (Fin.cons true p)) := by
      simpa only [pathRoot, root] using h
    rw [collisionInputsOfWrongLeaf]
    split
    · exact collisionInputsOfWrongLeaf_spec H d _ (Fin.tail pos) (Fin.tail sibs) leaf
        (by assumption)
        (fun heq => hne (heq.trans (congrArg f (Fin.cons_self_tail pos))))
    · next hchild =>
      refine ⟨fun hp => hchild ?_, h'⟩
      have h1 := congrArg Prod.fst hp
      have h2 := congrArg Prod.snd hp
      cases hb : pos 0 <;>
        simp only [hb, Bool.cond_false, Bool.cond_true] at h1 h2 <;>
        first | exact h1 | exact h2

/-- **Position binding, as an explicit reduction.** From a path that validates `leaf` at
position `pos` against the root of the tree over `f`, together with `leaf ≠ f pos`, compute
a collision of the tree hash: the standard fixed-depth Merkle argument, as a computable
`def` per the breaks-as-computed-data convention. The recursive search is
`collisionInputsOfWrongLeaf` (pure data), its certification is
`collisionInputsOfWrongLeaf_spec`, and this definition packages the two. -/
def collisionOfWrongLeaf [DecidableEq B] (H : B × B → B) (d : ℕ) (f : (Fin d → Bool) → B)
    (pos : Fin d → Bool) (sibs : Fin d → B) (leaf : B)
    (h : pathRoot H d pos sibs leaf = root H d f) (hne : leaf ≠ f pos) :
    RandomOracle.Collision H :=
  { q₁ := (collisionInputsOfWrongLeaf H d f pos sibs leaf).1
    q₂ := (collisionInputsOfWrongLeaf H d f pos sibs leaf).2
    ne := (collisionInputsOfWrongLeaf_spec H d f pos sibs leaf h hne).1
    eq := (collisionInputsOfWrongLeaf_spec H d f pos sibs leaf h hne).2 }

/-- Completeness: the honest authentication path for position `pos` validates the leaf
`f pos` against the tree root. -/
theorem pathRoot_authPath (H : B × B → B) (d : ℕ) (f : (Fin d → Bool) → B)
    (pos : Fin d → Bool) :
    pathRoot H d pos (authPath H d f pos) (f pos) = root H d f := by
  induction d with
  | zero =>
    simp only [pathRoot, root]
    exact congrArg f (funext fun i => i.elim0)
  | succ d ih =>
    induction pos using Fin.consCases with
    | cons b q =>
    cases b <;>
      simp only [pathRoot, root, authPath, Fin.cons_zero, Fin.tail_cons, Bool.cond_false,
        Bool.cond_true, Bool.not_false, Bool.not_true, ih]

end Zcash.Security.Ledger.Merkle


namespace Zcash.Security.Ledger.Merkle

variable {B E : Type*}

/-- The Merkle-specific part of the ledger primitive interface.  `E` is the raw
encoding consumed by the compression function; it is deliberately separate from the
node type `B`, since an Orchard field element can have more than one accepted 255-bit
encoding. -/
structure MerklePrimitives (B E : Type*) where
  depth : ℕ
  decode : E → B
  compress : Fin depth → E × E → B

/-- Select the raw child on the path.  `false` selects the left child and `true`
selects the right child. -/
def selectedChild (side : Bool) (children : E × E) : E :=
  if side then children.2 else children.1

/-- The running node after the first `i` leaf-to-root path cells.  In particular,
`node ... 0` is the leaf and `node ... (i + 1)` is the compression at layer `i`.
The selected-child equations in `Path` tie these otherwise raw inputs together. -/
def node (P : MerklePrimitives B E) (leaf : B) (children : Fin P.depth → E × E) :
    Fin (P.depth + 1) → B :=
  Fin.cases leaf (fun i => P.compress i (children i))

/-- A raw Orchard-style authentication path, ordered from the leaf towards the root.
Every layer carries both *raw* child encodings and its selected side.  The selected
encoding must decode to the current node, and compression at level `i` produces the
next node. -/
def Path (P : MerklePrimitives B E) (leaf root : B)
    (children : Fin P.depth → E × E) (side : Fin P.depth → Bool) : Prop :=
  (∀ i, P.decode (selectedChild (side i) (children i)) = node P leaf children (Fin.castSucc i)) ∧
    node P leaf children (Fin.last P.depth) = root

/-- A Merkle collision records the layer whose personalization was collided. -/
abbrev Collision (P : MerklePrimitives B E) :=
  Σ i : Fin P.depth, RandomOracle.Collision (P.compress i)

end Zcash.Security.Ledger.Merkle

/-- The raw-encoding Merkle interface, re-exported at the ledger namespace for the
statement layer. -/
abbrev Zcash.Security.Ledger.MerklePrimitives (B E : Type*) :=
  Zcash.Security.Ledger.Merkle.MerklePrimitives B E
