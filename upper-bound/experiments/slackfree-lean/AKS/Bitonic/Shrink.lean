module
/-
  # Bitonic sort for arbitrary n

  Restricts `bitonicSort k` (on `2^k` wires) to `n` wires via `restrictWires`, `k = ⌈log₂ n⌉`.

  - `bitonicNetwork`, `bitonicNetwork_sorts`
  - `bitonicNetwork_depth_le_budget` : depth `≤ k(k+1)/2` with `k = ⌈log₂ n⌉`
-/

public import AKS.Bitonic.Sorts
public import AKS.Sort.Shrink

@[expose] public section

/-- Bitonic sorting network for arbitrary `n`: `bitonicSort ⌈log₂ n⌉` restricted to `n` wires. -/
def bitonicNetwork (n : ℕ) : ComparatorNetwork n :=
  (Bitonic.bitonicSort (Nat.clog 2 n)).restrictWires n (Nat.le_pow_clog (by omega) n)

theorem bitonicNetwork_sorts (n : ℕ) : (bitonicNetwork n).Sorts :=
  restrictWires_sorts _ _ _ (Bitonic.bitonicSort_sorts_bool _)

theorem bitonicDepthBudget_double (k : ℕ) :
    2 * bitonicDepthBudget k = k * (k + 1) := by
  induction k with
  | zero => simp [bitonicDepthBudget]
  | succ k ih => simp only [bitonicDepthBudget]; nlinarith

/-- Batcher's triangular depth budget: `∑_{i=1}^p i = p(p+1)/2`. -/
theorem bitonicDepthBudget_eq (k : ℕ) : bitonicDepthBudget k = k * (k + 1) / 2 := by
  rw [← bitonicDepthBudget_double k]; omega

theorem bitonicDepthBudget_mono : Monotone bitonicDepthBudget := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [bitonicDepthBudget]
  omega

theorem bitonicNetwork_depth_le_budget (n : ℕ) :
    (bitonicNetwork n).depth ≤ bitonicDepthBudget (Nat.clog 2 n) :=
  (restrictWires_depth_le _ _ _).trans (Bitonic.bitonicSort_depth_le_budget _)

/-- §7 final sorter: `42·43/2 = 903` comparator layers for `2^42` wires. -/
theorem bitonicNetwork_2pow42_depth_le_903 : (bitonicNetwork (2 ^ 42)).depth ≤ 903 := by
  refine (bitonicNetwork_depth_le_budget _).trans ?_
  rw [show Nat.clog 2 (2 ^ 42) = 42 from by decide +kernel, bitonicDepthBudget_eq]

end
