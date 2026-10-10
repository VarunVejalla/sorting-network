import AKS.Bounds.PatersonTight

/-! Kernel dependency checks for the complete refined sorting bound. -/

/-- info: 'Paterson.Bags.allocatedRebuild_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.allocatedRebuild_preserves

/-- info: 'Paterson.Bags.scheduledChild_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.scheduledChild_invariant

/-- info: 'Paterson.exists_known_permutation_correction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.exists_known_permutation_correction

/-- info: 'Paterson.Bags.correctedForest_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.correctedForest_sorts

/-- info: 'SortingDepth.minimum_depth_le_6991' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SortingDepth.minimum_depth_le_6991

/-- info: 'SortingDepth.limsup_minimum_div_logb_le_6990_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SortingDepth.limsup_minimum_div_logb_le_6990_5

/-- info: 'SortingDepth.eventually_minimum_depth_le_7000_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SortingDepth.eventually_minimum_depth_le_7000_logb
