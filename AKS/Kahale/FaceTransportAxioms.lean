import AKS.Kahale.FaceTransport

/-- info: 'Kahale.pairAxis_min_transport' depends on axioms: [propext] -/
#guard_msgs in #print axioms Kahale.pairAxis_min_transport
/-- info: 'Kahale.pairAxis_transport_balance' depends on axioms: [propext] -/
#guard_msgs in #print axioms Kahale.pairAxis_transport_balance
/-- info: 'Kahale.pairAxis_gate_kills' depends on axioms: [propext] -/
#guard_msgs in #print axioms Kahale.pairAxis_gate_kills
/-- info: 'Kahale.facePairMatrix_min_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Kahale.facePairMatrix_min_transport
/-- info: 'Kahale.facePairMatrix_transport_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.facePairMatrix_transport_balance
/-- info: 'Kahale.facePairMatrix_gate_kills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.facePairMatrix_gate_kills
/-- info: 'Kahale.facePairMatrix_max_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Kahale.facePairMatrix_max_transport
/-- info: 'Kahale.facePairMatrix_untouched' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Kahale.facePairMatrix_untouched
