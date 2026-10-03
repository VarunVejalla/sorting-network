import AKS.Paterson.Root
import AKS.Paterson.Accounting
import AKS.Paterson.Padding
import AKS.Separator.PatersonPartial

/-! # Kernel axiom audit for the refined Paterson milestones -/

/-- info: 'Paterson.partialNetwork_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.partialNetwork_depth_le

/-- info: 'Paterson.partialNetwork_left_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.partialNetwork_left_refinement

/-- info: 'Paterson.partialNetwork_right_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.partialNetwork_right_refinement

/-- info: 'Paterson.Bags.parallel_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.parallel_depth_le

/-- info: 'Paterson.Bags.bagSeparator_filters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.bagSeparator_filters

/-- info: 'Paterson.Bags.interior_parallel_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.interior_parallel_step

/-- info: 'Paterson.Bags.subtree_intrusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.subtree_intrusion

/-- info: 'Paterson.Bags.fast_scheduled_routing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.fast_scheduled_routing

/-- info: 'Paterson.Bags.deep_half_strangers_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.deep_half_strangers_zero

/-- info: 'Paterson.Bags.root_sort_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.root_sort_depth_le

/-- info: 'Paterson.Bags.idealStageCount_converges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.idealStageCount_converges

/-- info: 'Paterson.Bags.proposed_depth_le_7000' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.proposed_depth_le_7000

/-- info: 'Paterson.padded_initial_separator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.padded_initial_separator

/-- info: 'Paterson.padded_final_separator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.padded_final_separator
