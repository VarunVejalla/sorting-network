module

public import AKS.Paterson.RootAllocationBudget

/-! # Slack for the proposed sorted-bin root rebuild

These scalar certificates do not assert root-splitting correctness.
-/

@[expose] public section

namespace Paterson.Bags

theorem root_rebuild_ratio : fastParams.A * fastParams.delta = 1 / 12 := by
  norm_num [fastParams]

theorem root_rebuild_level4_error :
    128 * fastParams.delta ^ 2 * fastParams.A ^ 2 /
      (1 - 4 * fastParams.delta ^ 2 * fastParams.A ^ 2) = 32 / 35 := by
  norm_num [fastParams]

theorem root_rebuild_level2_error :
    128 * fastParams.delta ^ 4 * fastParams.A ^ 4 /
      (1 - 4 * fastParams.delta ^ 2 * fastParams.A ^ 2) = 2 / 315 := by
  norm_num [fastParams]

theorem root_rebuild_level4_slack :
    128 * fastParams.delta ^ 2 * fastParams.A ^ 2 /
      (1 - 4 * fastParams.delta ^ 2 * fastParams.A ^ 2) < 1 := by
  rw [root_rebuild_level4_error]
  norm_num

end Paterson.Bags
