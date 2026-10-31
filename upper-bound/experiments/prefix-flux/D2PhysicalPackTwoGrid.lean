import D2BandRepair4096Network
import AKS.Chvatal.PhysicalPack2
import AKS.Bitonic.Shrink

namespace Chvatal.D2PhysicalPackTwoGrid

/-- A genuine comparator network: the physical two-round pack followed by the
fixed two-grid band repair. All rowwise permutations are encoded in the pack's
relabelled comparators. -/
noncomputable def physicalPackTwoGridNet (sigma1 sigma2 : Chvatal.Scramble 4096 64) :
    ComparatorNetwork (4096 * 64) :=
  (Chvatal.physicalPack2Net 4096 64 (by omega) sigma1 sigma2).append
    Chvatal.D2BandRepair4096Network.twoGridRepair

theorem columnSort_depth_le_78 :
    (Chvatal.columnSortNetwork 4096 64 (by omega)).depth <= 78 := by
  have h := Chvatal.columnSortNetwork_depth_le_budget 4096 64 (by omega)
  have hc : Nat.clog 2 4096 = 12 := by decide
  rw [hc, bitonicDepthBudget_eq] at h
  norm_num at h
  exact h

theorem physicalPackTwoGridNet_depth_le_276
    (sigma1 sigma2 : Chvatal.Scramble 4096 64) :
    (physicalPackTwoGridNet sigma1 sigma2).depth <= 276 := by
  have hp := Chvatal.physicalPack2Net_depth_le 4096 64 (by omega) sigma1 sigma2
  have hc := columnSort_depth_le_78
  have hr := Chvatal.D2BandRepair4096Network.twoGridRepair_depth_le_42
  unfold physicalPackTwoGridNet
  calc
    _ <= (Chvatal.physicalPack2Net 4096 64 (by omega) sigma1 sigma2).depth +
        Chvatal.D2BandRepair4096Network.twoGridRepair.depth :=
      ComparatorNetwork.depth_append_le _ _
    _ <= 3 * 78 + 42 := by omega
    _ = 276 := by norm_num

end Chvatal.D2PhysicalPackTwoGrid
