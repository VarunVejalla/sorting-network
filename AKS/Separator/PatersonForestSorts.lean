module

public import AKS.Separator.PatersonForestRanks
public import AKS.Sort.KnownPermutation
public import AKS.Sort.Perm

/-! Complete correctness of the rounded Paterson forest.
Its input-independent rank arrangement is corrected by one fixed network. -/

@[expose] public section

namespace Paterson.Bags

theorem exists_corrected_forest (k : ℕ) :
    ∃ net : ComparatorNetwork (2 ^ k), ComparatorNetwork.Sorts.{0} net ∧
      net.depth ≤ 989 * idealStageCount k + 562 * k + 561 := by
  let first := preliminaryNetwork k
  obtain ⟨last, hd, hs⟩ := exists_known_permutation_correction k (first.exec id)
    (ComparatorNetwork.exec_injective first Function.injective_id)
  let net : ComparatorNetwork (2 ^ k) := ⟨first.comparators ++ last.comparators⟩
  refine ⟨net, ?_, ?_⟩
  · apply perm_principle
    intro σ
    have hi := preliminaryNetwork_independent k σ id σ.injective Function.injective_id
    change first.exec σ = first.exec id at hi
    change Monotone ((ComparatorNetwork.mk (first.comparators ++ last.comparators)).exec σ)
    rw [ComparatorNetwork.exec_append]
    rw [hi, hs]
    exact monotone_id
  · apply (depth_append first last).trans
    have hf := preliminaryNetwork_depth_le k
    change first.depth ≤ _ at hf
    omega

noncomputable def correctedForest (k : ℕ) : ComparatorNetwork (2 ^ k) :=
  (exists_corrected_forest k).choose

theorem correctedForest_sorts (k : ℕ) : (correctedForest k).Sorts := by
  apply perm_principle
  intro σ
  exact (exists_corrected_forest k).choose_spec.1 _ σ

theorem correctedForest_depth_double (k : ℕ) :
    2 * (correctedForest k).depth ≤ 13981 * k + 13979 := by
  have hd := (exists_corrected_forest k).choose_spec.2
  have ht := idealStageCount_le k
  change (correctedForest k).depth ≤ _ at hd
  omega

end Paterson.Bags
