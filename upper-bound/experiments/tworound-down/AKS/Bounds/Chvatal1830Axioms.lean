import AKS.Bounds.Chvatal1830Final

/-! Kernel dependency checks for the two headline theorems (the hypothesis `TwoRoundSeparatorExists`
is an ordinary argument, not an axiom). -/

/-- info: 'SortingDepth.minimum_depth_le_1419_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SortingDepth.minimum_depth_le_1419_logb

/-- info: 'SortingDepth.limsup_minimum_div_logb_le_1419' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SortingDepth.limsup_minimum_div_logb_le_1419
