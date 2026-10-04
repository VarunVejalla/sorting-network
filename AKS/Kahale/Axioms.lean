import AKS.Bounds.KahaleAsymptotic

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
