module

public import AKS.Kahale.RankInputs
public import AKS.Kahale.Fanout
public import AKS.Kahale.FibonacciBound

/-! # The complete finite lower bound for a sorting network in parallel layers

The conversion from the repository's greedy `ComparatorNetwork.depth` to a
parallel execution of that length is a separate scheduling obligation.
-/

@[expose] public section

namespace Kahale

theorem sorting_layers_binomial_constraint {n : ℕ} (layers : List (List (Comparator n)))
    (hp : ∀ cs ∈ layers, IsParallelLayer cs)
    (hs : ComparatorNetwork.Sorts.{0} ⟨layers.flatten⟩) (s : ℕ) (hsl : s ≤ layers.length) :
    n * Nat.choose (layers.length - s) s ≤ 2 ^ (layers.length + 1) * (s + 1) := by
  let q := layers.length - s
  let pre := layers.take q
  let suf := layers.drop q
  have hq : q ≤ layers.length := Nat.sub_le _ _
  have hpre : pre.length = q := by simp only [pre, List.length_take, min_eq_left hq]
  have hsuf : suf.length = s := by simp only [suf, List.length_drop, q]; omega
  have hpp : ∀ cs ∈ pre, IsParallelLayer cs :=
    fun cs hc ↦ hp cs (List.mem_of_mem_take hc)
  have hps : ∀ cs ∈ suf, IsParallelLayer cs :=
    fun cs hc ↦ hp cs (List.mem_of_mem_drop hc)
  have heq : pre.flatten ++ suf.flatten = layers.flatten := by
    rw [← List.flatten_append]
    exact congrArg List.flatten (List.take_append_drop q layers)
  have hsorted (σ : Equiv.Perm (Fin n)) :
      (ComparatorNetwork.mk suf.flatten).exec ((ComparatorNetwork.mk pre.flatten).exec σ) = id := by
    rw [← ComparatorNetwork.exec_append, heq]
    exact sorting_rank_identity _ hs σ
  have ha := sorted_suffix_approx_select ⟨pre.flatten⟩ suf hps hsorted (2 ^ s)
  rw [hsuf] at ha
  have hz := approx_select_zeros _ ha
  have hc := yao_binomial_constraint pre hpp hz
  rw [hpre] at hc
  have ht : q + s + 1 = layers.length + 1 := by dsimp [q]; omega
  rwa [ht] at hc

theorem sorting_layers_fibonacci_bound {n : ℕ} (layers : List (List (Comparator n)))
    (hp : ∀ cs ∈ layers, IsParallelLayer cs)
    (hs : ComparatorNetwork.Sorts.{0} ⟨layers.flatten⟩) :
    n * Nat.fib (layers.length + 1) ≤ 2 ^ (layers.length + 1) * (layers.length + 1) ^ 2 :=
  binomial_constraints_fibonacci_bound n layers.length
    (sorting_layers_binomial_constraint layers hp hs)

theorem sorting_layers_exponential_bound {n : ℕ} (layers : List (List (Comparator n)))
    (hp : ∀ cs ∈ layers, IsParallelLayer cs)
    (hs : ComparatorNetwork.Sorts.{0} ⟨layers.flatten⟩) :
    (n : ℝ) * Real.goldenRatio ^ layers.length ≤
      Real.goldenRatio * 2 ^ (layers.length + 1) * ((layers.length + 1 : ℕ) : ℝ) ^ 2 :=
  binomial_constraints_exponential_bound n layers.length
    (sorting_layers_binomial_constraint layers hp hs)

end Kahale
