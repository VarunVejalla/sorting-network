import FrontierIntegerSchedule

/-! UB-23 count/ownership endpoints. These guards check the complete flow
schedule, including initialization, recurrence, and the terminal count target.
They make no claim about a rank invariant or a sorting-depth coefficient. -/

/-- info: 'Tapered945.candidate_integer_schedule_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tapered945.candidate_integer_schedule_invariant

/-- info: 'Tapered945.candidate_integer_schedule_routed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tapered945.candidate_integer_schedule_routed

/-- info: 'Tapered945.candidate_six_stage_integer_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tapered945.candidate_six_stage_integer_cycle

/-- info: 'Tapered945.candidate_integer_terminal_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Tapered945.candidate_integer_terminal_counts
