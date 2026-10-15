import Zcash.Meta.Efficient
import Zcash.Meta.AxiomCheck

/-!
# Regression tests for `Zcash.Meta.Efficient` and `assert_efficient`

Cost functions derived for small first-order definitions, with their values pinned by `#eval`,
one bound proved by induction, and the rejections pinned by `#guard_msgs`. `assert_efficient`
is pinned on a passing definition, on a rejected one, and with a flag it does not deserve.
-/

namespace Zcash.Meta.Tests.Efficient

universe u v w

/-! ## Primitive costs: one unit per arithmetic operation, `length` linear. -/

def hAddCost {α : Type u} {β : Type v} {γ : Type w} [HAdd α β γ] (_a : α) (_b : β) : Nat := 1
def hMulCost {α : Type u} {β : Type v} {γ : Type w} [HMul α β γ] (_a : α) (_b : β) : Nat := 1
def hModCost {α : Type u} {β : Type v} {γ : Type w} [HMod α β γ] (_a : α) (_b : β) : Nat := 1
def lengthCost {α : Type u} (xs : List α) : Nat := xs.length + 1

efficient_cost HAdd.hAdd := hAddCost
efficient_cost HMul.hMul := hMulCost
efficient_cost HMod.hMod := hModCost
efficient_cost List.length := lengthCost

/-! ## Derived costs -/

/-- One addition: one unit for the call and one for the operation. -/
efficient def double (n : Nat) : Nat := n + n

/-- info: 2 -/
#guard_msgs in
#eval double.cost 5

/-- Structural recursion through `match`: one unit per decision, then the branch. -/
efficient def sumList (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => x + sumList rest

/-- info: 13 -/
#guard_msgs in
#eval sumList.cost [1, 2, 3]

theorem sumList_cost_le (xs : List Nat) : sumList.cost xs ≤ 4 * xs.length + 1 := by
  induction xs with
  | nil => simp [sumList.cost]
  | cons x rest ih => simp [sumList.cost, hAddCost]; omega

/-- A call of an `efficient` function is priced at its cost function. -/
efficient def twiceSum (xs : List Nat) : Nat := double (sumList xs)

/-- info: 17 -/
#guard_msgs in
#eval twiceSum.cost [1, 2, 3]

/-- Insertion with an `if`: the comparison is one decision, so inserting past three elements
costs three matches, three comparisons, three recursive calls, and the final match. -/
efficient def insort1 (x : Nat) (xs : List Nat) : List Nat :=
  match xs with
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insort1 x ys

/-- info: 10 -/
#guard_msgs in
#eval insort1.cost 5 [1, 2, 3]

/-- Well-founded recursion: the termination suffix is copied to the cost function. -/
efficient def gcd' (a b : Nat) : Nat :=
  if _h : b = 0 then a else gcd' b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _h)

/-- info: 13 -/
#guard_msgs in
#eval gcd'.cost 12 18

-- A pin is silent on success, like `assert_computable`.
#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.gcd'

-- The flags are `assert_computable`'s, with the same checks behind them.
#guard_msgs in
assert_efficient Zcash.Meta.Tests.Efficient.double

/--
error: Zcash.Meta.Tests.Efficient.double does not depend on Classical.choice; drop the '+choice' flag
-/
#guard_msgs (whitespace := lax) in
assert_efficient Zcash.Meta.Tests.Efficient.double +choice

/-! ## Rejections -/

/--
error: efficient: 'List.reverse' has no cost function. Mark its definition `efficient`, or register a cost function for it with `efficient_cost List.reverse := <cost function>`.
-/
#guard_msgs (whitespace := lax) in
efficient def rev (xs : List Nat) : List Nat := xs.reverse

/--
error: Zcash.Meta.Tests.Efficient.rev has no cost function: define it with `efficient def`, or register one with `efficient_cost`
-/
#guard_msgs (whitespace := lax) in
assert_efficient Zcash.Meta.Tests.Efficient.rev

/--
error: efficient: applying a local function (f) is not supported yet; the cost of a higher-order argument has to be given symbolically
-/
#guard_msgs (whitespace := lax) in
efficient def applyTwice (f : Nat → Nat) (n : Nat) : Nat := f (f n)

end Zcash.Meta.Tests.Efficient
