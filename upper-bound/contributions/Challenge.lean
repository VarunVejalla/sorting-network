/-
  # Challenge: a limsup upper bound for sorting-network depth (DRAFT)

  Mathlib-only specification, suitable for use with
  [comparator](https://github.com/leanprover/comparator) and similar tools. The definitions below must
  stay textually identical to `upper-bound/best/AKS/Sort/{Defs,Depth,Monotone}.lean` (the trusted base,
  see `upper-bound/TRUSTED.md`). The constant is substituted by `scripts/make-limsup-challenge`.
-/

import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Order.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! **Comparator network definitions: depth, size, and sorting** -/

/-- A comparator on `n` wires swaps positions `i` and `j` if out of order. -/
structure Comparator (n : ℕ) where
  i : Fin n
  j : Fin n
  h : i < j

/-- Apply a single comparator to a vector. -/
def Comparator.apply {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) : Fin n → α :=
  fun k ↦
    if k = c.i then min (v c.i) (v c.j)
    else if k = c.j then max (v c.i) (v c.j)
    else v k

/-- A comparator network is a sequence of comparators applied in order. -/
@[ext] structure ComparatorNetwork (n : ℕ) where
  comparators : List (Comparator n)

/-- The size of a network is the total number of comparators. -/
def ComparatorNetwork.size {n : ℕ} (net : ComparatorNetwork n) : ℕ :=
  net.comparators.length

def depthStep {n : ℕ} (state : (Fin n → ℕ) × ℕ) (c : Comparator n) :
    (Fin n → ℕ) × ℕ :=
  let wt := state.1
  let t := max (wt c.i) (wt c.j) + 1
  (Function.update (Function.update wt c.i t) c.j t, max state.2 t)

/-- The depth of a comparator network, computed via greedy critical-path scheduling.

    Each comparator is assigned time step `max(wireTime c.i, wireTime c.j) + 1`,
    then both wires are updated to that time. The network depth is the maximum
    assigned time step.

    This is an upper bound on the minimum number of parallel rounds needed to
    execute the network (see `depth_le_of_decomposition`). -/
def ComparatorNetwork.depth {n : ℕ} (net : ComparatorNetwork n) : ℕ :=
  (net.comparators.foldl depthStep (fun _ ↦ 0, 0)).2

/-- Execute an entire comparator network on an input vector. -/
def ComparatorNetwork.exec {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) : Fin n → α :=
  net.comparators.foldl (fun acc c ↦ c.apply acc) v

/-- A network is a *sorting network* if it sorts every input. -/
def ComparatorNetwork.Sorts {n : ℕ} (net : ComparatorNetwork n) : Prop :=
  ∀ (α : Type*) [LinearOrder α] (v : Fin n → α),
    Monotone (net.exec v)

/-- **Challenge.** For every `ε > 0`, for all large `n` there is a sorting network on `n` wires whose
depth is at most `(C + ε) · log₂ n`, with `C = 1419` in this instance. This implies
`limsup D(n)/log₂ n ≤ C` for the minimum depth `D(n)`. -/
theorem upper_bound_certified : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ net : ComparatorNetwork n, ComparatorNetwork.Sorts.{0} net ∧
      (net.depth : ℝ) ≤ ((1419 : ℝ) + ε) * Real.logb 2 (n : ℝ) := sorry
