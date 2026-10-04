import AKS.Separator.PatersonRun
import AKS.Paterson.CoarsePrefixCount

/-! # Kernel axiom audit for mixed stages and root split groundwork -/

/-- info: 'Paterson.Bags.scheduledCompare_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.scheduledCompare_preserves

/-- info: 'Paterson.Bags.comparisonRun_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.comparisonRun_depth_le

/-- info: 'Paterson.Bags.comparisonRun_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.comparisonRun_invariant

/-- info: 'Paterson.Bags.allocated_upper_region_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.allocated_upper_region_budget

/-- info: 'Paterson.Bags.upperRegisters_complement_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.upperRegisters_complement_count

/-- info: 'Paterson.Bags.upperRegisters_dvd64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.upperRegisters_dvd64

/-- info: 'Paterson.Bags.deepErrors_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.deepErrors_bound

/-- info: 'Paterson.Bags.deepErrors_one_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.deepErrors_one_empty

/-- info: 'Paterson.Bags.upper_deep_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.upper_deep_complete

/-- info: 'Paterson.Bags.assigned_deep_prefix_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.assigned_deep_prefix_card

/-- info: 'Paterson.Bags.deep_prefix_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.deep_prefix_agreement

/-- info: 'Paterson.Bags.sorted_network_bin_wrong_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.sorted_network_bin_wrong_bound

/-- info: 'Paterson.Bags.allocated_remaining_prefix_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.allocated_remaining_prefix_discrepancy

/-- info: 'Paterson.Bags.coarse_prefix_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.coarse_prefix_count

/-- info: 'Paterson.Bags.allocated_coarse_prefix_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.allocated_coarse_prefix_capacity

/-- info: 'Paterson.Bags.allocated_actual_prefix_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.allocated_actual_prefix_discrepancy
