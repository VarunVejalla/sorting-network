import PacketRepair64
import PacketGenMerge
import PacketRebinning
import PacketHalfProfile

/-- info: 'Chvatal.PacketAlignment.sum_receiver_selected_errors_le_source_pieces' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sum_receiver_selected_errors_le_source_pieces

/-- info: 'Chvatal.PacketAlignment.sum_receiver_profile_errors_le_source_count_errors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sum_receiver_profile_errors_le_source_count_errors

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSelection_pairwise_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSelection_pairwise_disjoint

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_profile_error_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_profile_error_sum_le

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSelection_receiverSource' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSelection_receiverSource

/-- info: 'Chvatal.PacketAlignment.wireFlowReceiverNeighborBags_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowReceiverNeighborBags_mem

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSelection_eq_empty_of_not_neighbor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSelection_eq_empty_of_not_neighbor

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSelection_receiverSum_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSelection_receiverSum_eq

/-- info: 'Chvatal.PacketAlignment.wireFlowReceiver_selected_count_eq_register' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowReceiver_selected_count_eq_register

/-- info: 'Chvatal.PacketAlignment.wireFlowReceiver_register_count_error_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowReceiver_register_count_error_actual

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_receiver_signed_error_eq_register' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_receiver_signed_error_eq_register

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_register_error_sum_le_source_count_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_register_error_sum_le_source_count_error

/-- info: 'Chvatal.PacketAlignment.profileIntervalMean_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileIntervalMean_bounds

/-- info: 'Chvatal.PacketAlignment.wireFlowReceiverSelectedIdealMean_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowReceiverSelectedIdealMean_bounds

/-- info: 'Chvatal.PacketAlignment.profileIntervalMean_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileIntervalMean_between

/-- info: 'Chvatal.PacketAlignment.profileIntervalMean_mono_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileIntervalMean_mono_mean

/-- info: 'Chvatal.PacketAlignment.wireFlowReceiverSelectedIdealMean_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowReceiverSelectedIdealMean_mono

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_register_error_sum_le_source_count_error_multi' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_register_error_sum_le_source_count_error_multi

/-- info: 'Chvatal.PacketAlignment.realTarget_has_integer_fraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.realTarget_has_integer_fraction

/-- info: 'Chvatal.PacketAlignment.profileInterval_partition_L1_exact_allow_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileInterval_partition_L1_exact_allow_endpoint

/-- info: 'Chvatal.PacketAlignment.oddEvenMergeNet_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.oddEvenMergeNet_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.oddEvenMergeNet64_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.oddEvenMergeNet64_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.oddEvenMergeNet64_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.oddEvenMergeNet64_depth_le

/-- info: 'Chvatal.PacketAlignment.oddEvenMergeNet64_scatter_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.oddEvenMergeNet64_scatter_sorts

/-- info: 'Chvatal.PacketAlignment.oddEvenMergeNet64_scatter_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.oddEvenMergeNet64_scatter_depth_le

/-- info: 'Chvatal.PacketAlignment.repairOrderedHalfPair_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.repairOrderedHalfPair_sorts

/-- info: 'Chvatal.PacketAlignment.rankInterval_endpoint_repair_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.rankInterval_endpoint_repair_exists

/-- info: 'Chvatal.PacketAlignment.upFringe_endpoint_repair_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.upFringe_endpoint_repair_exists

/-- info: 'Chvatal.PacketAlignment.parallelHalfPairRepair_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.parallelHalfPairRepair_depth_le

/-- info: 'Chvatal.PacketAlignment.parallelHalfPairRepair_sorts_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.parallelHalfPairRepair_sorts_pair

/-- info: 'Chvatal.PacketAlignment.genScatter_exec_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.genScatter_exec_inside

/-- info: 'Chvatal.PacketAlignment.genScatter_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.genScatter_depth

/-- info: 'Chvatal.PacketAlignment.genMerge128_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.genMerge128_sorts

/-- info: 'Chvatal.PacketAlignment.genMerge128_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.genMerge128_depth_le

/-- info: 'Chvatal.PacketAlignment.genMerge128_dealt_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.genMerge128_dealt_counts

/-- info: 'Chvatal.PacketAlignment.genPacketPair_lanes_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.genPacketPair_lanes_sorted

/-- info: 'Chvatal.PacketAlignment.dealEmbeddings_partition' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.dealEmbeddings_partition

/-- info: 'Chvatal.PacketAlignment.genMerge_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.genMerge_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.genMerge_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.genMerge_depth_le

/-- info: 'Chvatal.PacketAlignment.genSorted_dealt_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.genSorted_dealt_counts

/-- info: 'Chvatal.PacketAlignment.genSorted_threshold_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.genSorted_threshold_counts

/-- info: 'Chvatal.PacketAlignment.halfRebin_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.halfRebin_sum

/-- info: 'Chvatal.PacketAlignment.halfRebin_positive_spill_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.halfRebin_positive_spill_le

/-- info: 'Chvatal.PacketAlignment.halfRebin_centered_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.halfRebin_centered_energy_le

/-- info: 'Chvatal.PacketAlignment.senderRepair_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.senderRepair_exists

/-- info: 'Chvatal.PacketAlignment.sorted_bool_halves_trueCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sorted_bool_halves_trueCount

/-- info: 'Chvatal.PacketAlignment.scheduled_senderRepair_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.scheduled_senderRepair_exists

/-- info: 'Chvatal.PacketAlignment.senderRepair_rebin_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.senderRepair_rebin_count

/-- info: 'Chvatal.PacketAlignment.senderRepair_count_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.senderRepair_count_exists

/-- info: 'Chvatal.PacketAlignment.senderRepair_count_at_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.senderRepair_count_at_threshold

/-- info: 'Chvatal.PacketAlignment.profileCell_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileCell_L1_exact

/-- info: 'Chvatal.PacketAlignment.profileCellMean_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileCellMean_L1_exact

/-- info: 'Chvatal.PacketAlignment.profileCellMean_cohort_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileCellMean_cohort_L1_exact

/-- info: 'Chvatal.PacketAlignment.profileCellMean_cohort_L1_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileCellMean_cohort_L1_sq

/-- info: 'Chvatal.PacketAlignment.sortedPackets_cellProfile_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sortedPackets_cellProfile_L1_exact

/-- info: 'Chvatal.PacketAlignment.sortedPackets_cellProfile_L1_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sortedPackets_cellProfile_L1_sq

/-- info: 'Chvatal.PacketAlignment.sortedPackets_halfProfile_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sortedPackets_halfProfile_L1_exact

/-- info: 'Chvatal.PacketAlignment.sortedPackets_halfProfile_L1_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sortedPackets_halfProfile_L1_sq

/-- info: 'Chvatal.PacketAlignment.sortedBool_rankInterval_trueCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sortedBool_rankInterval_trueCount

/-- info: 'Chvatal.PacketAlignment.profileInterval_change_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileInterval_change_le

/-- info: 'Chvatal.PacketAlignment.profileInterval_partition_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileInterval_partition_L1_exact

/-- info: 'Chvatal.PacketAlignment.sortedPackets_intervalPartition_L1_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sortedPackets_intervalPartition_L1_exact

/-- info: 'Chvatal.PacketAlignment.sortedPackets_intervalPartition_L1_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sortedPackets_intervalPartition_L1_sq

/-- info: 'Chvatal.PacketAlignment.sortedPackets_individualIntervalPartitions_L1_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sortedPackets_individualIntervalPartitions_L1_exact

/-- info: 'Chvatal.PacketAlignment.sortedPackets_individualIntervalPartitions_L1_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sortedPackets_individualIntervalPartitions_L1_sq

/-- info: 'Chvatal.PacketAlignment.trueCountOn_blockOf_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.trueCountOn_blockOf_profile

/-- info: 'Chvatal.PacketAlignment.sortedWireBags_intervalPartition_L1_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sortedWireBags_intervalPartition_L1_exact

/-- info: 'Chvatal.PacketAlignment.sortedSenderOutgoing_profile_error_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sortedSenderOutgoing_profile_error_exact

/-- info: 'Chvatal.PacketAlignment.senderOutgoingPieces_are_WireFlow_ports' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.senderOutgoingPieces_are_WireFlow_ports

/-- info: 'Chvatal.PacketAlignment.selectedSenderOutgoing_profile_error_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.selectedSenderOutgoing_profile_error_le

/-- info: 'Chvatal.PacketAlignment.sortedSenderOutgoing_profile_error_exact_var' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.sortedSenderOutgoing_profile_error_exact_var

/-- info: 'Chvatal.PacketAlignment.selectedSenderOutgoing_profile_error_le_var' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.selectedSenderOutgoing_profile_error_le_var

/-- info: 'Chvatal.PacketAlignment.selectedSenderOutgoing_count_error_le_var' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.selectedSenderOutgoing_count_error_le_var

/-- info: 'Chvatal.PacketAlignment.wireFlowReceiver_count_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowReceiver_count_error_le

/-- info: 'Chvatal.PacketAlignment.wireFlowReceiver_count_error_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowReceiver_count_error_actual
