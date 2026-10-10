import AKS.Bounds.KahaleAsymptotic

/-! Kernel dependency checks for the standalone Kahale lower bound. -/

/-- info: 'Kahale.sorting_network_fibonacci_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.sorting_network_fibonacci_bound
/-- info: 'SortingDepth.minimum_logarithmic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.minimum_logarithmic_bound
/-- info: 'SortingDepth.liminf_minimum_div_logb_ge_kahale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.liminf_minimum_div_logb_ge_kahale
/-- info: 'SortingDepth.eventually_minimum_depth_ge_kahale_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SortingDepth.eventually_minimum_depth_ge_kahale_logb
