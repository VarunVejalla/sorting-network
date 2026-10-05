import AKS.Bounds.KahaleAsymptotic
import AKS.Kahale.CertificateCompatibility
import AKS.Kahale.JointPotential
import AKS.Kahale.UnionCoupling
import AKS.Kahale.ActiveWidth

/-! Kernel dependency checks for the Kahale lower bound. -/

/-- info: 'Kahale.wire_rank_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.wire_rank_interval
/-- info: 'Kahale.certificateHeights_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.certificateHeights_correct
/-- info: 'Kahale.yao_binomial_constraint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.yao_binomial_constraint
/-- info: 'Kahale.greedyLayers_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.greedyLayers_exec
/-- info: 'Kahale.sorting_network_fibonacci_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.sorting_network_fibonacci_bound
/-- info: 'SortingDepth.minimum_logarithmic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.minimum_logarithmic_bound
/-- info: 'SortingDepth.liminf_minimum_div_logb_ge_kahale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.liminf_minimum_div_logb_ge_kahale
/-- info: 'SortingDepth.eventually_minimum_depth_ge_kahale_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.eventually_minimum_depth_ge_kahale_logb

/-- info: 'Kahale.zero_certificate_max_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.zero_certificate_max_append
/-- info: 'Kahale.one_certificate_iff_hits_zero_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.one_certificate_iff_hits_zero_family
/-- info: 'Kahale.sorts_iff_certificates_intersect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.sorts_iff_certificates_intersect
/-- info: 'Kahale.sorts_iff_certificate_card_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.sorts_iff_certificate_card_bounds

/-- info: 'Kahale.joint_product_scalar_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.joint_product_scalar_bound
/-- info: 'Kahale.identical_joint_statistics_different_updates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.identical_joint_statistics_different_updates
/-- info: 'Kahale.joint_product_factor_two_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.joint_product_factor_two_attained
/-- info: 'Kahale.active_comparator_union_cost_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.active_comparator_union_cost_coupling
/-- info: 'Kahale.active_final_comparator_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.active_final_comparator_adjacent
/-- info: 'Kahale.active_comparator_width_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.active_comparator_width_le
