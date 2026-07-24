/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Mathlib.Data.List.Basic

/-!
# Parallel `List.map` via the task runtime, with a proof it is just `List.map`

`List.parMap f xs` evaluates `f` on every element of `xs` concurrently, using the Lean
task runtime (`Task.spawn` / `Task.get`), and collects the results in order. It is a *pure*
function — `Task` is logically the one-field structure `⟨get : α⟩`, `Task.spawn fn = ⟨fn ()⟩`
and `Task.get ⟨a⟩ = a` are both definitional — so it is provably equal to `List.map`
(`List.parMap_eq_map`). The only thing `parMap` changes is the *evaluation strategy*: under
`native_decide` (compiled to C, run on the real task scheduler) the elementwise work runs on
the thread pool (up to `nproc` workers), which is the point for the independent
`commit_lagrange` commitments of the VK-commitment certification.

Because the equality to `List.map` is definitional, swapping `List.map` for `List.parMap` in a
`native_decide`-backed definition changes nothing about the statement's meaning or trust base:
the compiled `Task` primitives are already part of the `native_decide` trust boundary, and the
`Std`/kernel view is literally `List.map`.

## References
* Lean task runtime: `Init/Core.lean` (`Task`, `Task.spawn`, `Task.get`); the runtime overrides
  `Task`'s representation, `Task.spawn`/`Task.get` are `@[extern]` — but the reference Lean bodies
  `Task.spawn fn = ⟨fn ()⟩`, `Task.get ⟨a⟩ = a` are what the kernel and `decide` see.
-/

namespace Zcash.Snark.VkCommit.Fast

universe u v

/-- Parallel map: spawn a task per element, then collect the results in order. Pure — equal to
`List.map` (`List.parMap_eq_map`) — but evaluates the elementwise work concurrently on the task
runtime under `native_decide`/compiled execution. -/
def _root_.List.parMap {α : Type u} {β : Type v} (f : α → β) (xs : List α) : List β :=
  (xs.map (fun x => Task.spawn (fun _ => f x))).map Task.get

/-- `List.parMap` is `List.map`: the task round-trip `Task.get (Task.spawn (fun _ => f x))` is
`f x` definitionally, so nothing but the evaluation strategy differs. -/
@[simp] theorem _root_.List.parMap_eq_map {α : Type u} {β : Type v} (f : α → β) (xs : List α) :
    xs.parMap f = xs.map f := by
  rw [List.parMap, List.map_map]; rfl

/-- Split a list into consecutive chunks of size `n+1` (the last chunk may be shorter). Used to
control task granularity: one spawned task per chunk rather than per element, when per-element work
is small relative to spawn overhead. `n+1` keeps the recursion structurally decreasing. -/
def chunk {α : Type u} (n : ℕ) : List α → List (List α)
  | [] => []
  | (x :: xs) => (x :: xs).take (n + 1) :: chunk n ((x :: xs).drop (n + 1))
  termination_by l => l.length
  decreasing_by
    simp only [List.length_drop, List.length_cons]
    omega

/-- `chunk n` concatenated back is the identity — `chunk` only regroups, it drops nothing. -/
theorem chunk_flatten {α : Type u} (n : ℕ) (xs : List α) : (chunk n xs).flatten = xs := by
  fun_induction chunk n xs with
  | case1 => rfl
  | case2 x xs ih =>
    simp only [List.flatten_cons, ih, List.take_append_drop]

/-- Chunked parallel map: `parMap` over chunks of size `chunkSize+1`, mapping `f` within each chunk
on a single task. Provably `List.map f` (`parMapChunked_eq_map`), with coarser task granularity. -/
def parMapChunked {α : Type u} {β : Type v} (chunkSize : ℕ) (f : α → β) (xs : List α) : List β :=
  ((chunk chunkSize xs).parMap (fun c => c.map f)).flatten

/-- The chunked parallel map is `List.map`. -/
@[simp] theorem parMapChunked_eq_map {α : Type u} {β : Type v}
    (chunkSize : ℕ) (f : α → β) (xs : List α) : parMapChunked chunkSize f xs = xs.map f := by
  unfold parMapChunked
  rw [List.parMap_eq_map, ← List.map_flatten, chunk_flatten]

end Zcash.Snark.VkCommit.Fast
