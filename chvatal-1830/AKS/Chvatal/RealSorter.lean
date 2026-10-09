module

/-
  # The 1830 sorting network on `64^d` wires (Chvátal DCS-TR-294, §7)

  Assembles the proved pieces: the `t_f` stage networks (`stagesNet`, with the node networks
  `realNets`), rank-purity of the level-`(d-7)` blocks (`finalS_image_real`), the final layer of
  `2^42`-wire Batcher sorters (`final_layer_sorts`, which also untangles the generalized network
  into a standard one), and the depth count.
-/

public import AKS.Chvatal.RealBlocks
public import AKS.Chvatal.RealNetwork
public import AKS.Chvatal.FinalSorts
public import AKS.Chvatal.DepthSkeleton

@[expose] public section

namespace Chvatal

/-- **Chvátal's sorting network**: for every `d ≥ 14` there is a sorting network on `64^d` wires
of depth at most `totalDepth d = 6320 + (3d-21)·3660 + 903`. -/
theorem chvatal_sorter_exists {d : ℕ} (hd14 : 14 ≤ d) :
    ∃ net : ComparatorNetwork (64 ^ d),
      ComparatorNetwork.Sorts.{0} net ∧ net.depth ≤ totalDepth d := by
  have hd : 7 ≤ d := by omega
  set A := stagesNet (flowSizes7 d hd) (realNets d hd) (tf7 d) with hA
  have hcard : ∀ b, (finalS d hd b).card = 0 ∨ (finalS d hd b).card = 2 ^ 42 := by
    intro b
    by_cases hb : b.l = d - 7
    · exact Or.inr (finalS_card d hd b hb)
    · left; simp [finalS, hb]
  obtain ⟨T, hTd, hTs⟩ := final_layer_sorts (finalS d hd) (finalS_disjoint d hd)
    (finalS_cover d hd) (fun b => b.x * 2 ^ 42) A (by
      intro p b
      rw [hA, stagesNet_exec]
      exact finalS_image_real hd14 p b)
  refine ⟨T, hTs, hTd.trans ?_⟩
  have hst := stagesNet_depth_le (flowSizes7 d hd) (realNets d hd)
    depthBound (tf7 d) (Nat.le_succ _)
    (fun t ht b n => realNets_depth_le hd hd14 t ht b n)
  have hsum : ∑ t ∈ Finset.range (tf7 d), depthBound t = 6320 + (3 * d - 21) * 3660 := by
    have : tf7 d = (3 * d - 21) + 1 := by unfold tf7; omega
    rw [this, Finset.sum_range_succ']
    have h2 : ∀ i ∈ Finset.range (3 * d - 21), depthBound (i + 1) = 3660 := by
      intro i _; simp [depthBound]
    rw [Finset.sum_congr rfl h2]
    simp [depthBound]
    ring
  have hA' : A.depth ≤ 6320 + (3 * d - 21) * 3660 := by rw [← hsum]; exact hst
  have hf : (stageNet (finalS d hd) (fun _ n => bitonicNetwork n)).depth ≤ 903 :=
    finalLayer_depth_le (finalS d hd) (finalS_disjoint d hd) hcard
  unfold totalDepth ordinaryRounds rootSeparatorPaperDepth ordinaryStagePaperDepth
    finalSorterPaperDepth
  omega

end Chvatal
