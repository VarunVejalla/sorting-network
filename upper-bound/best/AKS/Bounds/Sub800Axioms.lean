import AKS.Bounds.Sub800Final

/-! Kernel dependency checks for the unconditional 789.75 headline theorems and the network family
(no hypothesis argument remains). -/

/-- info: 'R1T.r1_sorter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms R1T.r1_sorter

/-- info: 'R1T.r1_sorter_78975' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms R1T.r1_sorter_78975

/-- info: 'SortingDepth.minimum_depth_le_78975_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SortingDepth.minimum_depth_le_78975_logb

/-- info: 'SortingDepth.limsup_minimum_div_logb_le_78975' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SortingDepth.limsup_minimum_div_logb_le_78975

/-- info: 'SortingDepth.limsup_minimum_div_logb_le_800' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SortingDepth.limsup_minimum_div_logb_le_800
