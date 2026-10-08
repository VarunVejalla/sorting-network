import AKS.Bounds.Chvatal1830Batcher

/-! Kernel dependency checks for the finite-range Chvátal 1830 Batcher endpoint. -/

/-- info: 'SortingDepth.minimum_depth_le_1830_logb_of_batcher_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SortingDepth.minimum_depth_le_1830_logb_of_batcher_range

/-- info: 'SortingDepth.exists_batcher_totalDepth_of_le_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SortingDepth.exists_batcher_totalDepth_of_le_max

/-- info: 'Chvatal.bitonicDepthBudget_6d_le_totalDepth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.bitonicDepthBudget_6d_le_totalDepth

/-- info: 'Chvatal.paperDepthShellNetwork_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.paperDepthShellNetwork_depth_le
