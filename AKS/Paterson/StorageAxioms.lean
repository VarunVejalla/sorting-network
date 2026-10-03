import AKS.Paterson.AllocationInitial
import AKS.Paterson.PartialBoundary
import AKS.Paterson.AllocatedPartialBalance

/-! # Kernel axiom audit for storage-aware Paterson scheduling -/

/-- info: 'Paterson.partialNetwork_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.partialNetwork_supported

/-- info: 'Paterson.Bags.StoredPlacement.route_cold_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.StoredPlacement.route_cold_card

/-- info: 'Paterson.Bags.StoredPlacement.compare_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.StoredPlacement.compare_depth_le

/-- info: 'Paterson.Bags.StoredPlacement.compare_cold_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.StoredPlacement.compare_cold_exec

/-- info: 'Paterson.Bags.StoredPlacement.route_regs_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.StoredPlacement.route_regs_of_pos

/-- info: 'Paterson.Bags.StoredPlacement.route_root_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.StoredPlacement.route_root_regs

/-- info: 'Paterson.Bags.StoredPlacement.subtree_intrusion_stored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.StoredPlacement.subtree_intrusion_stored

/-- info: 'Paterson.Bags.coherent_cohort_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.coherent_cohort_balance

/-- info: 'Paterson.Bags.fast_partial_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.fast_partial_fresh

/-- info: 'Paterson.Bags.partial_tail_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.partial_tail_arithmetic

/-- info: 'Paterson.Bags.fast_clipped_routing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.fast_clipped_routing

/-- info: 'Paterson.Bags.fast_virtual_fringe_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.fast_virtual_fringe_coverage

/-- info: 'Paterson.Bags.allocationStep_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.allocationStep_preserves

/-- info: 'Paterson.Bags.scheduledInitial_allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.scheduledInitial_allocation

/-- info: 'Paterson.Bags.allocationRun_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.allocationRun_invariant

/-- info: 'Paterson.Bags.allocated_subtree_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.allocated_subtree_card

/-- info: 'Paterson.Bags.allocated_parent_coherence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.allocated_parent_coherence

/-- info: 'Paterson.Bags.allocated_full_cohort_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.allocated_full_cohort_balance

/-- info: 'Paterson.Bags.allocated_partial_available' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.allocated_partial_available

/-- info: 'Paterson.Bags.allocated_partial_fresh_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.allocated_partial_fresh_budget

/-- info: 'Paterson.Bags.allocated_partial_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Paterson.Bags.allocated_partial_support
