import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Forking.Rewind
import Zcash.Snark.Soundness.Multiopen.Opened
import Zcash.Snark.Soundness.Multiopen.ValueCheckDeployed
import Zcash.Snark.Soundness.Multiopen.NodeBinding
import Zcash.Snark.Soundness.Forking.KnowledgeError
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder

/-!
# Vesta instantiation: the verifier group at the deployed curve

The soundness theorems of `Zcash.Snark.Soundness.Main` are proven for an abstract
`Fp`-module `G`. Here `G` is pinned to the actual Vesta curve `SWPoint Vesta.curve` (`y² = x³ + 5`),
whose group law CompElliptic/mathlib have already proven (associativity transported from
`WeierstrassCurve.Affine.Point`). The deployed Orchard verifier runs over Vesta, so these theorems are
the concrete-curve forms of the abstract capstones.

## The setting

The only structure the `Fp`-action needs that the curve does not already carry is the Vesta group
order: every point is `p`-torsion (`p = scalarFieldOrder`). Given that, `AddCommGroup.zmodModule`
turns the curve into an `Fp`-module and the abstract theorems specialize to Vesta.

## Assumptions

* **The Vesta group order.** CompElliptic's `Pasta.Vesta.card_eq` supplies
  `Nat.card VestaG = scalarFieldOrder`, from which `vestaOrder` proves that every point is annihilated
  by the scalar-field order. This does not require a caller-supplied hypothesis, but `card_eq` is a
  closed computation certified with `native_decide`; concrete Vesta endpoints inherit that pinned
  compiler-trust axiom.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.evalNat_eq_eval scalarFieldOrder)

-- The deployed grouping definitions appear inside index types, so a defeq check on an index can
-- pull the whole `constructIntermediateSets (assembleQueries …)` computation through `whnf`.
-- Sealing them keeps those checks syntactic; the proofs below use their equation lemmas.
attribute [local irreducible] deployedSetQueries deployedSetCommIds deployedX4PairCount
  x4BatchCommitments x4BatchEvals

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder

/-- The deployed verifier group `E_q`, concretely `SWPoint Vesta.curve`: the points of `y² = x³ + 5`. -/
abbrev VestaG := SWPoint Vesta.curve

/-- The Vesta group-order proposition: every Vesta point is `p`-torsion for
`p = scalarFieldOrder`. `vestaOrder` supplies it from CompElliptic's pinned point-count result, and
`vestaFpModule` consumes it through `Fact`. -/
abbrev VestaOrder : Prop := ∀ P : VestaG, (scalarFieldOrder : ℕ) • P = 0

/-- Derive the Vesta group-order proposition from CompElliptic's `Pasta.Vesta.card_eq` and the fact
that a finite group is annihilated by its cardinality. The theorem has no explicit hypothesis, but
inherits `card_eq`'s pinned `native_decide` axiom. -/
theorem vestaOrder : VestaOrder := by
  intro P
  have hcard : Nat.card VestaG = scalarFieldOrder := Vesta.card_eq
  rw [← hcard]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard P)

/-- Install the Vesta order proved by `vestaOrder` as the `Fact` used by the `Fp`-module instance. -/
instance : Fact VestaOrder := ⟨vestaOrder⟩

/-- Given the Vesta group order (`Fact VestaOrder`), the curve is an `Fp`-module
(`AddCommGroup.zmodModule` on the `p`-torsion). Conditional — it fires only when the order `Fact`
is in scope; this file installs that fact via `vestaOrder`. Computable (curve addition and the
`ZMod`-action both are), so the break reductions stay plain `def`s at the concrete curve. -/
instance vestaFpModule [h : Fact VestaOrder] : Module Fp VestaG :=
  AddCommGroup.zmodModule h.out

/-- **The concrete-to-abstract MSM bridge at Vesta.** `Msm.evalNat_eq_eval` specialised to
`SWPoint Vesta.curve`: the pinned Vesta group order supplies the `Fp`-module structure
unconditionally (via `vestaFpModule`, as for the capstones below), so the executable natural-scalar
evaluation the concrete fixtures compute (`capturedMsm.evalNat`, `(assemble ..).evalNat`) coincides
with the module-theoretic `eval` the soundness capstones consume. So the fixtures' `evalNat = 0`
checks *are* the `eval = 0` acceptance condition of the abstract verifier, not merely an analogous
computation. -/
theorem Msm.evalNat_eq_eval_vesta (urs : URS VestaG)
    (m : Msm urs.k Fp VestaG) : m.evalNat urs = m.eval urs :=
  Msm.evalNat_eq_eval urs m

def NontrivialRelation.ofUnopenedForkVesta [DecidableEq VestaG]
    [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} (hz : z ≠ 0)
    (fs : ForkedTranscript urs hk vk instanceCommitment ps ch b z blind)
    (hne : ¬ IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
      (projTree fs.tree)) :
    NontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  NontrivialRelation.ofUnopenedFork urs hk vk instanceCommitment ps ch hz fs hne

open Polynomial in
/-- **Deployed opening and constraint over Vesta, given a clean fork.**
`orchard_verifier_deployed_constraint_of_forked` specialised to `SWPoint Vesta.curve`: the opening
for the declared `fs.openedCommitment` and the pinned `multiopenValue`, and `circuitSat` (concrete
`circuitSatViaGates`) from the verifier's gate point-check `hquot` lifted by Schwartz–Zippel
(`hgood`). The `Fp`-module comes from the pinned Vesta point-count result. `hquot`/`hgood` share
`hcirc`'s unsatisfiable shape (see the section note in `Soundness.Main`). -/
theorem orchard_verifier_vesta_constraint_of_forked [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (fs : ForkedTranscript urs hk vk instanceCommitment ps ch b z blind)
    (hclean : IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk instanceCommitment ps ch)
      (projTree fs.tree))
    (hquot : ∀ a, IpaRelation urs fs.openedCommitment b
      (multiopenValue vk instanceCommitment ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs fs.openedCommitment b
      (multiopenValue vk instanceCommitment ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs fs.openedCommitment b (multiopenValue vk instanceCommitment ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S :=
  orchard_verifier_deployed_constraint_of_forked urs hk vk instanceCommitment ps ch fixedCols
    decodeAdvice decodeInstance y gates hpoly deg x fs hclean hquot hgood hencodes

/-- The powers evaluation vector has leading entry `1` (`evalVector k x 0 = x⁰ = 1`), discharging the IPA's
`hb0` structural fact at the concrete deployed `b = evalVector`. -/
theorem evalVector_zero {F : Type*} [Field F] (k : ℕ) (x : F) : evalVector k x 0 = 1 := by
  simp [evalVector]

/-- The IPA witness after folding in the value term and synthetic blinder. -/
def adjustedWitness {k : ℕ} (aMulti s : Fin (2 ^ k) → Fp) (v ξ : Fp) : Fin (2 ^ k) → Fp :=
  aMulti - Pi.single 0 v + ξ • s

/-- The adjusted witness commits to halo2's adjusted commitment — `hP` holds by linearity, not by assumption. -/
theorem commit_adjustedWitness {G : Type*} [AddCommGroup G] [Module Fp G] (urs : URS G)
    (aMulti s : Fin (2 ^ urs.k) → Fp) (v ξ : Fp) :
    commit urs (adjustedWitness aMulti s v ξ) = commit urs aMulti - v • urs.g 0 + ξ • commit urs s := by
  have csub : ∀ a a' : Fin (2 ^ urs.k) → Fp, commit urs (a - a') = commit urs a - commit urs a' := by
    intro a a'; simp only [commit, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [adjustedWitness, commit_add, csub, commit_single, commit_smul]

open scoped ENNReal in
/-- A nonzero blinding shift vanishes for at most a `1 / |Fp|` fraction of uniform `ξ` challenges. -/
theorem blinder_value_recovery_badSet {k : ℕ} (s : Fin (2 ^ k) → Fp) (xEval : Fp)
    (hδ : innerProduct s (evalVector k xEval) ≠ 0) :
    uniformChallenge.toOuterMeasure
        (Finset.univ.filter (fun ξ : Fp => ξ * innerProduct s (evalVector k xEval) = 0))
      ≤ 1 / (Fintype.card Fp : ℝ≥0∞) :=
  blinder_shift_badSet_measure (innerProduct s (evalVector k xEval)) 0 hδ

/-- The single-entry value term in the adjusted commitment is `-v • g 0`. -/
theorem sum_getD_single {k : ℕ} {G : Type*} [AddCommGroup G] [Module Fp G] (gg : Fin (2 ^ k) → G)
    (v : Fp) :
    (∑ i, ([-v].getD i.val 0 : Fp) • gg i) = -v • gg 0 := by
  rw [Finset.sum_eq_single (0 : Fin (2 ^ k))]
  · simp
  · intro i _ hi
    have hival : i.val ≠ 0 := Fin.val_ne_zero_iff.mpr hi
    rw [List.getD_eq_default, zero_smul]
    simp only [List.length_cons, List.length_nil, Nat.zero_add]
    omega
  · intro h; exact absurd (Finset.mem_univ _) h
open Polynomial in
open scoped ENNReal in
open Classical in
/-- **Deployed member-column constraint capstone: the gate check on the real circuit columns.**
*Either* the SNARK relation holds with the circuit checked on the decoded *member* columns — the
actual queried column commitments' openings — *or* a nontrivial `(g, u, w)` relation exists. The
member decodes are produced per point set by spending the `x₁` accept measure
(`openedMemberDecode_of_x1Prob`); the honest opening is the designated batch itself. `hquot`/`hgood`
state the gate check once, on the produced member polynomials; deriving them from the verifier's
accepted `assemble.eval = 0` is the remaining constraint-side work. Measures carry the usual
random-oracle uniformity axiom. -/
theorem orchard_verifier_vesta_member_constraint_deployed_x4 [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (hacc0 : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hquot : quotientCheck
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates) hpoly deg x)
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    (p : Fin shape.numProofs)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk instanceCommitment ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk instanceCommitment ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk instanceCommitment ps ch)
        (hMem : Fin (deployedSetQueries vk instanceCommitment ps ch hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk instanceCommitment ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns urs hk vk instanceCommitment ps ch
        (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg pU pW a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  -- The honest opening is the *given* `pbatch` (`ipaRelation_of_x4Current`); the member constraint
  -- `S` follows from it and the gate hypotheses directly. There is no free augmented `(u, w)`
  -- decomposition to assume here (`hcommit`/`hs`/`hU`/`hξ` and the second `x`-round fork are gone):
  -- the vanish-or-DLR dichotomy on those components is discharged *upstream*, where `pbatch` itself
  -- is produced from acceptance (`openedX4Rewind_of_x4Prob` and the `x₄`/`x₁` forks) — re-forking
  -- them here only re-introduced the free components the audit flagged. The `HasNontrivialRelation`
  -- disjunct is retained so the composition can surface that upstream branch unchanged.
  Or.inl (member_constraint_of_relation_and_batch urs hk vk instanceCommitment ps ch adviceSet hadviceSet
    adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg x
    (pbatch.ipaRelation_of_x4Current hξcur) pbatch
    (fun i hi => openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch i hi (hlen i hi)
      (hprob1 i hi) hacc0)
    hquot hgood p hadviceLayout hinstanceLayout hquotCommitted hencodes)

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **Derived deployed member capstone: the claimed evaluations produced from the floors.** The
gate check runs at `ch.x` on the decoded member columns, whose claimed evaluations are *derived*:
each in-range layout entry is a deployed opening query, its rotated point a point of the member's
set, and the member node binding pins the decoded column's value there
(`deployed_member_node_binding_at_point`), on pain of a computed `(g, U, W)` relation. `hfold` is
stated at exactly those deployed claimed evaluations (the expression-fold fingerprint surface), and
`hgood`'s production surface is `hgood_of_xProb`. The residual premises are the forking floors,
sample avoidance, and the layout/eval range facts — no per-column value hypothesis remains. -/
theorem orchard_verifier_vesta_member_constraint_derived [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (pU pW : Fp)
    {numAdvice numInstance : ℕ}
    (adviceSet : Fin numAdvice → ℕ)
    (hadviceSet : ∀ j, adviceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (adviceMem : ∀ j : Fin numAdvice, Fin (deployedSetQueries vk instanceCommitment ps ch (adviceSet j)).length)
    (instanceSet : Fin numInstance → ℕ)
    (hinstanceSet : ∀ j, instanceSet j < deployedX4PairCount vk instanceCommitment ps ch)
    (instanceMem : ∀ j : Fin numInstance,
      Fin (deployedSetQueries vk instanceCommitment ps ch (instanceSet j)).length)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch : OpenedBatchOpenings urs (evalVector urs.k ch.x3)
      (x4BatchCommitments urs hk vk instanceCommitment ps ch) (x4BatchEvals vk instanceCommitment ps ch) a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch
      → 0 < (deployedSetQueries vk instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1Accept urs hk vk instanceCommitment ps ch)))
    (hacc0 : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (p : Fin shape.numProofs)
    (hadvLen : ∀ j : Fin numAdvice, (j : ℕ) < vk.adviceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.adviceEvals p)).length)
    (hinstLen : ∀ j : Fin numInstance, (j : ℕ) < vk.instanceQueryLayout.length
      ∧ (j : ℕ) < (List.ofFn (ps.instanceEvals p)).length)
    {ξ₀ : Fp} (hξ₀p : OpenedX1PinnedAccept urs hk vk instanceCommitment ps ch ξ₀)
    (hprob1p : ∀ i, i < deployedX4PairCount vk instanceCommitment ps ch →
      (((deployedSetQueries vk instanceCommitment ps ch i).length - 1 : ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX1PinnedAccept urs hk vk instanceCommitment ps ch)))
    (hx2 : ∀ (r₁ : X1Run shape VestaG) (ξv : Fp), ∃ (b₂ : Fin (2 ^ urs.k) → Fp) (ζ₀ : Fp),
      OpenedX2Accept urs hk vk instanceCommitment (r₁.spliced ps) (r₁.challenges ch ξv) b₂ ζ₀ ∧
      ((deployedX4PairCount vk instanceCommitment (r₁.spliced ps) (r₁.challenges ch ξv) - 1 : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX2Accept urs hk vk instanceCommitment (r₁.spliced ps) (r₁.challenges ch ξv) b₂)))
    (hprob3 : ∀ (r₁ : X1Run shape VestaG) (ξv : Fp) (r₂ : X2Run shape VestaG) (ζv : Fp),
      ((max (2 ^ urs.k) (deployedAllPts vk instanceCommitment (r₁.spliced ps) (r₁.challenges ch ξv)).card
          + (deployedAllPts vk instanceCommitment (r₁.spliced ps) (r₁.challenges ch ξv)).card
          + (deployedAllPts vk instanceCommitment (r₁.spliced ps) (r₁.challenges ch ξv)).card : ℕ) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (fun χv => OpenedX3Accept urs hk vk instanceCommitment (r₂.spliced (r₁.spliced ps))
              (r₂.challenges (r₁.challenges ch ξv) ζv) (evalVector urs.k χv) χv)))
    (hprob4 : ∀ (r₁ : X1Run shape VestaG) (ξv : Fp) (r₂ : X2Run shape VestaG) (ζv χv : Fp)
        (r₃ : X3Run shape VestaG),
      (deployedX4PairCount vk instanceCommitment (r₃.spliced (r₂.spliced (r₁.spliced ps)))
          (r₃.challenges (r₂.challenges (r₁.challenges ch ξv) ζv) χv) : ℝ≥0∞)
          / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
            (OpenedX4Accept urs hk vk instanceCommitment (r₃.spliced (r₂.spliced (r₁.spliced ps)))
              (r₃.challenges (r₂.challenges (r₁.challenges ch ξv) ζv) χv)
              (evalVector urs.k χv))))
    (hfold : (List.ofFn (fun i : Fin ng =>
        (gates i).eval (fun n => (fixedCols n).eval ch.x)
          (deployedClaimedFeed vk instanceCommitment ps ch adviceSet adviceMem vk.adviceQueryLayout)
          (deployedClaimedFeed vk instanceCommitment ps ch instanceSet instanceMem vk.instanceQueryLayout))).foldl
          (fun acc v => acc * y + v) 0 = hpoly.eval ch.x * (ch.x ^ deg - 1))
    (hgood :
      combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols
        (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
            (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols (adviceMem j))))
        (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
          coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
            (hinstanceSet j) (hlen _ (hinstanceSet j))
            (hprob1 _ (hinstanceSet j)) hacc0).cols (instanceMem j))))
        y gates - hpoly * (X ^ deg - 1)).eval ch.x ≠ 0)
    (hadviceLayout : ∀ j : Fin numAdvice,
      (deployedSetCommIds vk instanceCommitment ps ch (adviceSet j)).getD (adviceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.adviceCol p (vk.adviceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hinstanceLayout : ∀ j : Fin numInstance,
      (deployedSetCommIds vk instanceCommitment ps ch (instanceSet j)).getD (instanceMem j : ℕ) CommitmentId.vanishingH
        = CommitmentId.instanceCol p (vk.instanceQueryLayout.getD (j : ℕ) (0, 0)).1)
    (hquotCommitted : ∃ (hSet : ℕ) (hhSet : hSet < deployedX4PairCount vk instanceCommitment ps ch)
        (hMem : Fin (deployedSetQueries vk instanceCommitment ps ch hSet).length),
      hpoly = coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch hSet hhSet
          (hlen _ hhSet) (hprob1 _ hhSet) hacc0).cols hMem) ∧
      (deployedSetCommIds vk instanceCommitment ps ch hSet).getD (hMem : ℕ) CommitmentId.randomPoly
        = CommitmentId.vanishingH)
    {S : Prop}
    (hencodes : ∀ a,
      SnarkRelationWithMemberColumns urs hk vk instanceCommitment ps ch
        (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
        (evalVector urs.k ch.x3) (multiopenValue vk instanceCommitment ps ch) p adviceSet hadviceSet adviceMem
        instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg pU pW a → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  by_cases hrel : HasNontrivialRelation (F := Fp) urs.g urs.u urs.w
  · exact Or.inr hrel
  -- derive `hadvice`: the rotated advice feed's value at `ch.x` is the deployed claimed eval
  have hadvice : ∀ n, (rotatedFeed vk.omega vk.adviceQueryLayout (fun j : Fin numAdvice =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet j)
        (hadviceSet j) (hlen _ (hadviceSet j)) (hprob1 _ (hadviceSet j)) hacc0).cols
          (adviceMem j))) n).eval ch.x
      = deployedClaimedFeed vk instanceCommitment ps ch adviceSet adviceMem vk.adviceQueryLayout n := by
    intro n
    by_cases h : n < numAdvice
    · obtain ⟨q, hqmem, hqid, hqpt⟩ := advice_query_mem_assembleQueries vk instanceCommitment ps ch p
        (hadvLen ⟨n, h⟩).1 (hadvLen ⟨n, h⟩).2
      have hltm : ((adviceMem ⟨n, h⟩ : ℕ))
          < (deployedSetCommIds vk instanceCommitment ps ch (adviceSet ⟨n, h⟩)).length := by
        rw [deployedSetCommIds_length]
        exact (adviceMem ⟨n, h⟩).isLt
      have hid : (deployedSetCommIds vk instanceCommitment ps ch (adviceSet ⟨n, h⟩)).getD ((adviceMem ⟨n, h⟩ : ℕ))
          CommitmentId.vanishingH = q.commId := (hadviceLayout ⟨n, h⟩).trans hqid.symm
      have hpt := deployed_query_point_mem vk instanceCommitment ps ch hqmem hltm hid
      rw [hqpt] at hpt
      have hb := deployed_member_node_binding_at_point urs hk vk instanceCommitment ps ch (adviceSet ⟨n, h⟩)
        (hadviceSet ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (adviceSet ⟨n, h⟩)
          (hadviceSet ⟨n, h⟩) (hlen _ (hadviceSet ⟨n, h⟩)) (hprob1 _ (hadviceSet ⟨n, h⟩)) hacc0)
        hξ₀p (hprob1p _ (hadviceSet ⟨n, h⟩)) hx2 hprob3 hprob4 hpt
        (adviceMem ⟨n, h⟩)
      rcases hb with hb | hdlr
      swap
      · exact absurd hdlr hrel
      rw [rotatedFeed_eval vk.omega vk.adviceQueryLayout _ h ch.x, hb, deployedClaimedFeed,
        dif_pos h]
    · rw [rotatedFeed_eval_of_ge vk.omega vk.adviceQueryLayout _ (Nat.not_lt.mp h) ch.x,
        deployedClaimedFeed, dif_neg h]
  -- derive `hinstance` symmetrically
  have hinstance : ∀ n, (rotatedFeed vk.omega vk.instanceQueryLayout (fun j : Fin numInstance =>
      coeffsToPoly ((openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet j)
        (hinstanceSet j) (hlen _ (hinstanceSet j)) (hprob1 _ (hinstanceSet j)) hacc0).cols
          (instanceMem j))) n).eval ch.x
      = deployedClaimedFeed vk instanceCommitment ps ch instanceSet instanceMem vk.instanceQueryLayout n := by
    intro n
    by_cases h : n < numInstance
    · obtain ⟨q, hqmem, hqid, hqpt⟩ := instance_query_mem_assembleQueries vk instanceCommitment ps ch p
        (hinstLen ⟨n, h⟩).1 (hinstLen ⟨n, h⟩).2
      have hltm : ((instanceMem ⟨n, h⟩ : ℕ))
          < (deployedSetCommIds vk instanceCommitment ps ch (instanceSet ⟨n, h⟩)).length := by
        rw [deployedSetCommIds_length]
        exact (instanceMem ⟨n, h⟩).isLt
      have hid : (deployedSetCommIds vk instanceCommitment ps ch (instanceSet ⟨n, h⟩)).getD
          ((instanceMem ⟨n, h⟩ : ℕ)) CommitmentId.vanishingH = q.commId :=
        (hinstanceLayout ⟨n, h⟩).trans hqid.symm
      have hpt := deployed_query_point_mem vk instanceCommitment ps ch hqmem hltm hid
      rw [hqpt] at hpt
      have hb := deployed_member_node_binding_at_point urs hk vk instanceCommitment ps ch (instanceSet ⟨n, h⟩)
        (hinstanceSet ⟨n, h⟩)
        (openedMemberDecode_of_x1Prob urs hk vk instanceCommitment ps ch pbatch (instanceSet ⟨n, h⟩)
          (hinstanceSet ⟨n, h⟩) (hlen _ (hinstanceSet ⟨n, h⟩)) (hprob1 _ (hinstanceSet ⟨n, h⟩))
          hacc0)
        hξ₀p (hprob1p _ (hinstanceSet ⟨n, h⟩)) hx2 hprob3 hprob4 hpt
        (instanceMem ⟨n, h⟩)
      rcases hb with hb | hdlr
      swap
      · exact absurd hdlr hrel
      rw [rotatedFeed_eval vk.omega vk.instanceQueryLayout _ h ch.x, hb, deployedClaimedFeed,
        dif_pos h]
    · rw [rotatedFeed_eval_of_ge vk.omega vk.instanceQueryLayout _ (Nat.not_lt.mp h) ch.x,
        deployedClaimedFeed, dif_neg h]
  -- the gate check at the deployed opening challenge, from the derived claimed evaluations
  exact orchard_verifier_vesta_member_constraint_deployed_x4 urs hk vk instanceCommitment ps ch pU pW adviceSet
    hadviceSet adviceMem instanceSet hinstanceSet instanceMem fixedCols y gates hpoly deg ch.x
    pbatch hξcur hlen hprob1 hacc0
    (quotientCheck_of_claimed fixedCols _ _ y gates hpoly deg ch.x
      (fun n => (fixedCols n).eval ch.x)
      (deployedClaimedFeed vk instanceCommitment ps ch adviceSet adviceMem vk.adviceQueryLayout)
      (deployedClaimedFeed vk instanceCommitment ps ch instanceSet instanceMem vk.instanceQueryLayout)
      (fun _ => rfl) hadvice hinstance hfold)
    hgood p hadviceLayout hinstanceLayout hquotCommitted hencodes

end Zcash.Snark
