module

/-
# `D(n)`: the minimum depth of a sorting network on `n` wires

Same definition as `AKS/Bounds/Upper.lean` in the main repository (there it sits next to the
Seiferas-based upper bounds, which this self-contained folder does not need).
-/

public import AKS.Bitonic.Shrink

@[expose] public section

namespace SortingDepth

theorem exists_sorting_depth (n : ℕ) :
    ∃ d : ℕ, ∃ net : ComparatorNetwork n, ComparatorNetwork.Sorts.{0} net ∧ net.depth = d :=
  ⟨(bitonicNetwork n).depth, bitonicNetwork n, bitonicNetwork_sorts n, rfl⟩

/-- `D(n)`: the minimum depth among all sorting networks on `n` wires. -/
noncomputable def minimum (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_sorting_depth n)

theorem minimum_le {n : ℕ} (net : ComparatorNetwork n)
    (hs : ComparatorNetwork.Sorts.{0} net) :
    minimum n ≤ net.depth := by
  classical
  exact Nat.find_min' _ ⟨net, hs, rfl⟩

end SortingDepth
