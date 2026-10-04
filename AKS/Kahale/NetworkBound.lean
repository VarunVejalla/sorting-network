module

public import AKS.Kahale.LayeredBound
public import AKS.Kahale.GreedyLayers

/-! # Kahale's finite lower bound for the repository's network depth

Greedy scheduling is proved to preserve execution. Thus the bound applies to
`ComparatorNetwork.depth`, with no external layering hypothesis.
-/

@[expose] public section

namespace Kahale

theorem sorting_network_fibonacci_bound {n : ℕ} (net : ComparatorNetwork n)
    (hs : ComparatorNetwork.Sorts.{0} net) :
    n * Nat.fib (net.depth + 1) ≤ 2 ^ (net.depth + 1) * (net.depth + 1) ^ 2 := by
  have hs' : ComparatorNetwork.Sorts.{0} ⟨(greedyLayers net).flatten⟩ := by
    intro α _ v
    rw [greedyLayers_exec]
    exact hs α v
  simpa only [greedyLayers_length] using
    sorting_layers_fibonacci_bound (greedyLayers net) (greedyLayers_parallel net) hs'

theorem sorting_network_exponential_bound {n : ℕ} (net : ComparatorNetwork n)
    (hs : ComparatorNetwork.Sorts.{0} net) :
    (n : ℝ) * Real.goldenRatio ^ net.depth ≤
      Real.goldenRatio * 2 ^ (net.depth + 1) * ((net.depth + 1 : ℕ) : ℝ) ^ 2 := by
  have hs' : ComparatorNetwork.Sorts.{0} ⟨(greedyLayers net).flatten⟩ := by
    intro α _ v
    rw [greedyLayers_exec]
    exact hs α v
  simpa only [greedyLayers_length] using
    sorting_layers_exponential_bound (greedyLayers net) (greedyLayers_parallel net) hs'

end Kahale
