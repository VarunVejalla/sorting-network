import AKS.Bounds.Chvatal1830Final

/-! Kernel dependency checks for the two headline theorems. -/

/-- info: 'SortingDepth.minimum_depth_le_1830_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SortingDepth.minimum_depth_le_1830_logb

/-- info: 'SortingDepth.limsup_minimum_div_logb_le_1830' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SortingDepth.limsup_minimum_div_logb_le_1830
