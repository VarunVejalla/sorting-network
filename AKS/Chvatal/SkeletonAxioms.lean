import AKS.Chvatal.DepthSkeleton

/-! Kernel dependency checks for the Chvátal Phase-0 depth skeleton. -/

/-- info: 'Chvatal.chvatal_log2_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.chvatal_log2_lt

/-- info: 'Chvatal.chvatal41' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.chvatal41

/-- info: 'Chvatal.chvatal71' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.chvatal71

/-- info: 'Chvatal.totalDepth_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.totalDepth_eq
