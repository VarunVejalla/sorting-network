import AKS.Bitonic.Shrink
open ComparatorNetwork

namespace Bitonic

/-- Bitonic sort with blocks of size `2^s` already sorted: recursion cut at size `2^s`. -/
def bitonicBlockSort (s : ℕ) : (k : ℕ) → ComparatorNetwork (2 ^ k)
  | 0 => ⟨[]⟩
  | k + 1 =>
    if k + 1 ≤ s then ⟨[]⟩ else
    (par (two_pow_succ' k) (bitonicBlockSort s k) (bitonicBlockSort s k)).append
      ((layer (two_pow_succ' k) Fin.revPerm).append
        (par (two_pow_succ' k) (bitonicMerge k) (bitonicMerge k)))

theorem bitonicBlockSort_depth_le (s : ℕ) :
    ∀ k, (bitonicBlockSort s k).depth ≤ bitonicDepthBudget k - bitonicDepthBudget s
  | 0 => by simp [bitonicBlockSort, depth_nil]
  | k + 1 => by
    unfold bitonicBlockSort
    split_ifs with h
    · have := bitonicDepthBudget_mono h
      simp [depth_nil]
    · have ih := bitonicBlockSort_depth_le s k
      have hs : bitonicDepthBudget s ≤ bitonicDepthBudget k := bitonicDepthBudget_mono (by omega)
      refine (depth_append_le _ _).trans ?_
      have h1 := depth_par (two_pow_succ' k) (bitonicBlockSort s k) (bitonicBlockSort s k) _ ih ih
      have h2 := layer_depth_le (two_pow_succ' k) Fin.revPerm
      have h3 := depth_append_le (layer (two_pow_succ' k) Fin.revPerm)
        (par (two_pow_succ' k) (bitonicMerge k) (bitonicMerge k))
      have h4 := depth_par (two_pow_succ' k) (bitonicMerge k) (bitonicMerge k) k
        (bitonicMerge_depth_le k) (bitonicMerge_depth_le k)
      simp only [bitonicDepthBudget]
      omega

end Bitonic
