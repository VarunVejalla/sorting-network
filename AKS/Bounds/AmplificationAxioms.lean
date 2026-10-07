import AKS.Sort.RepairInterface
import AKS.Sort.RepairBarrier
import AKS.Bounds.ConditionalLimit
import AKS.Bounds.DyadicLimit

/-! Focused trust audit for the conditional amplification research modules. -/

/-- info: 'SortingRepair.rankLocal_of_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingRepair.rankLocal_of_sorts
/-- info: 'SortingRepair.pivotal_card_le_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingRepair.pivotal_card_le_depth
/-- info: 'SortingRepair.disjoint_changes_le_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingRepair.disjoint_changes_le_depth
/-- info: 'SortingRepair.support_rank_cover_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingRepair.support_rank_cover_cut
/-- info: 'SortingRepair.binary_cut_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingRepair.binary_cut_bound
/-- info: 'SortingRepair.layer_product_barrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingRepair.layer_product_barrier
/-- info: 'SortingRepair.no_uniform_small_repair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingRepair.no_uniform_small_repair
/-- info: 'SortingDepth.exists_dyadic_depth_limit_of_bounded_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.exists_dyadic_depth_limit_of_bounded_defect
/-- info: 'SortingDepth.depth_limit_of_dyadic_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.depth_limit_of_dyadic_limit
/-- info: 'SortingDepth.exists_depth_limit_of_bounded_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.exists_depth_limit_of_bounded_defect
/-- info: 'SortingDepth.liminf_eq_limsup_of_bounded_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.liminf_eq_limsup_of_bounded_defect
