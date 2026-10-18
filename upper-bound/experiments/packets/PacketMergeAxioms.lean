import PacketRepair64
import PacketGenMerge
import PacketInduction
import PacketRebinning
import PacketHalfProfile
import PacketReceiverOverlap
import PacketUnequalMerge
import PacketMergeTree
import PacketMergeTreeGen

/-- info: 'Chvatal.PacketAlignment.bitonicSort4096OnSupport_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.bitonicSort4096OnSupport_depth_le

/-- info: 'Chvatal.PacketAlignment.bitonicSort4096OnSupport_rankSorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.bitonicSort4096OnSupport_rankSorted

/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryMatching_4096Block_physicalSort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryMatching_4096Block_physicalSort

/-- info: 'Chvatal.PacketAlignment.packetEmbedding_eq_supportOrderEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetEmbedding_eq_supportOrderEmbedding

/-- info: 'Chvatal.PacketAlignment.dealEvenEmbedding_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.dealEvenEmbedding_strictMono
/-- info: 'Chvatal.PacketAlignment.dealOddEmbedding_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.dealOddEmbedding_strictMono

/-- info: 'Chvatal.PacketAlignment.dealEmbeddings_interleave_of_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.dealEmbeddings_interleave_of_strictMono

/-- info: 'Chvatal.PacketAlignment.dealEmbeddings_crossOrdered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.dealEmbeddings_crossOrdered

/-- info: 'Chvatal.PacketAlignment.joinPacketEmbedding_crossOrdered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.joinPacketEmbedding_crossOrdered

/-- info: 'Chvatal.PacketAlignment.dealtJoinedPackets_crossOrdered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.dealtJoinedPackets_crossOrdered

/-- info: 'Chvatal.PacketAlignment.adjacentPacketMatching_dealtBlocks_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.adjacentPacketMatching_dealtBlocks_ordered

/-- info: 'Chvatal.PacketAlignment.adjacentPacketMatching_dealt_mem_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.adjacentPacketMatching_dealt_mem_output

/-- info: 'Chvatal.PacketAlignment.adjacentPacketMatching_outputBlocks_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.adjacentPacketMatching_outputBlocks_ordered

/-- info: 'Chvatal.PacketAlignment.adjacentPacketMatchingOutputBlock_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.adjacentPacketMatchingOutputBlock_contract
/-- info: 'Chvatal.PacketAlignment.joinPacketEmbedding_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.joinPacketEmbedding_strictMono
/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRound_output_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRound_output_strictMono
/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRound_withSingletons_output_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRound_withSingletons_output_strictMono

/-- info: 'Chvatal.PacketAlignment.parallelDownSetEndpointRepair_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.parallelDownSetEndpointRepair_exists

/-- info: 'Chvatal.PacketAlignment.parallelDownSetEndpointRepair_packetLayout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.parallelDownSetEndpointRepair_packetLayout

/-- info: 'Chvatal.PacketAlignment.downSetEndpoint_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.downSetEndpoint_partition

/-- info: 'Chvatal.PacketAlignment.flowA7_scheduled_parent_endpoint_repair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_scheduled_parent_endpoint_repair

/-- info: 'Chvatal.PacketAlignment.flowA7_scheduled_parent_endpoint_packetLayout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_scheduled_parent_endpoint_packetLayout

/-- info: 'Chvatal.PacketAlignment.parallelUpFringeEndpointRepair_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.parallelUpFringeEndpointRepair_exists

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_child_up_endpoint_repair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_child_up_endpoint_repair

/-- info: 'Chvatal.PacketAlignment.scheduled_bag_size_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.scheduled_bag_size_form

/-- info: 'Chvatal.PacketAlignment.flowA7_scheduled_bag_size_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_scheduled_bag_size_form

/-- info: 'Chvatal.PacketAlignment.flowA7_scheduled_packet_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_scheduled_packet_factorization

/-- info: 'Chvatal.PacketAlignment.floorCeilAverage_centered_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.floorCeilAverage_centered_energy_le

/-- info: 'Chvatal.PacketAlignment.genMerge128_dealt_centered_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genMerge128_dealt_centered_energy_le

/-- info: 'Chvatal.PacketAlignment.floorCeilAverage_energy_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.floorCeilAverage_energy_drop

/-- info: 'Chvatal.PacketAlignment.floorCeilAverage_energy_drop_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.floorCeilAverage_energy_drop_ge

/-- info: 'Chvatal.PacketAlignment.genMerge128_dealt_energy_drop_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genMerge128_dealt_energy_drop_ge

/-- info: 'Chvatal.PacketAlignment.genMerge128_dealt_energy_drop_ge_targetAverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genMerge128_dealt_energy_drop_ge_targetAverage

/-- info: 'Chvatal.PacketAlignment.mergeDealMatching_energy_drop_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.mergeDealMatching_energy_drop_ge

/-- info: 'Chvatal.PacketAlignment.floorCeilAverage_energy_drop_ge_targetAverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.floorCeilAverage_energy_drop_ge_targetAverage

/-- info: 'Chvatal.PacketAlignment.mergeDealMatching_energy_drop_ge_targetAverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.mergeDealMatching_energy_drop_ge_targetAverage

/-- info: 'Chvatal.PacketAlignment.senderRankCut_fringe_mean_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.senderRankCut_fringe_mean_sum_le

/-- info: 'Chvatal.PacketAlignment.senderRankCut_middle_mean_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.senderRankCut_middle_mean_sum_le

/-- info: 'Chvatal.PacketAlignment.senderOutgoingPiece_card_eq_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.senderOutgoingPiece_card_eq_interval

/-- info: 'Chvatal.PacketAlignment.senderOutgoingPiece_profile_error_le_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.senderOutgoingPiece_profile_error_le_capacity

/-- info: 'Chvatal.PacketAlignment.senderOutgoing_fringe_profile_error_sum_le_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.senderOutgoing_fringe_profile_error_sum_le_up

/-- info: 'Chvatal.PacketAlignment.senderOutgoing_middle_profile_error_sum_le_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.senderOutgoing_middle_profile_error_sum_le_down

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_low_frontier_error_sum_le_up' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_low_frontier_error_sum_le_up

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_high_frontier_error_sum_le_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_high_frontier_error_sum_le_down

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_root_fringe_error_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_root_fringe_error_eq_zero

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_leaf_middle_error_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_leaf_middle_error_eq_zero

/-- info: 'Chvatal.PacketAlignment.flowDown7_d_sub_one_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowDown7_d_sub_one_eq_zero

/-- info: 'Chvatal.PacketAlignment.flowUp7_level_one_le_capacity_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowUp7_level_one_le_capacity_scale

/-- info: 'Chvatal.PacketAlignment.flowUp7_level_one_time_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowUp7_level_one_time_sum_le

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_level_one_bags_card_le_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_level_one_bags_card_le_64

/-- info: 'Chvatal.PacketAlignment.flowUp7_level_one_aggregate_time_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowUp7_level_one_aggregate_time_sum_le

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_high_frontier_error_sum_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_high_frontier_error_sum_eq_zero

/-- info: 'Chvatal.PacketAlignment.profileIntervalMean_partition_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.profileIntervalMean_partition_sum

/-- info: 'Chvatal.PacketAlignment.profileIntervalMean_partition_sum_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.profileIntervalMean_partition_sum_interval

/-- info: 'Chvatal.PacketAlignment.profileIntervalMean_partition_sum_4096_grid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.profileIntervalMean_partition_sum_4096_grid

/-- info: 'Chvatal.PacketAlignment.blockOf_inter_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.blockOf_inter_eq

/-- info: 'Chvatal.PacketAlignment.senderOutgoingPiece_inter_portMacroGroup_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.senderOutgoingPiece_inter_portMacroGroup_eq

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

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSelection_active_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSelection_active_cover

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSelection_active_union_eq_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSelection_active_union_eq_range

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSelection_active_sum_eq_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSelection_active_sum_eq_range

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSelection_active_union_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSelection_active_union_low

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSelection_active_union_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSelection_active_union_high

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSelection_active_union_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSelection_active_union_complete

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSelection_active_sum_eq_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSelection_active_sum_eq_union

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSelection_active_sum_eq_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSelection_active_sum_eq_low

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSelection_active_sum_eq_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSelection_active_sum_eq_high

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSenderPieceMean_active_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSenderPieceMean_active_sum_eq

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerSenderPieceMean_active_sum_eq_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayerSenderPieceMean_active_sum_eq_target

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

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_selectedPiece_image_subset_register' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_selectedPiece_image_subset_register

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_selectedPiece_subset_nextWireSet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_selectedPiece_subset_nextWireSet

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_pieceOwner_iff_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_pieceOwner_iff_selected

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_selectedPiece_owner_eq_pieceOwner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_selectedPiece_owner_eq_pieceOwner

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerPieceOwner_profileCount_eq_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayerPieceOwner_profileCount_eq_selected

/-- info: 'Chvatal.PacketAlignment.wireFlowLayerPieceOwner_profileMean_eq_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowLayerPieceOwner_profileMean_eq_selected

/-- info: 'Chvatal.PacketAlignment.wireFlowReceiver_register_count_error_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.wireFlowReceiver_register_count_error_actual

/-- info: 'Chvatal.PacketAlignment.wireFlowReceiver_register_count_error_reencoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowReceiver_register_count_error_reencoded

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

/-- info: 'Chvatal.PacketAlignment.wireFlowReceiverSelectedIdealMean_has_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowReceiverSelectedIdealMean_has_code

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_selected_means_have_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_selected_means_have_codes

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_selected_means_have_monotone_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_selected_means_have_monotone_codes

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

/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_reencoded_profile_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_reencoded_profile_recurrence

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

/-- info: 'Chvatal.PacketAlignment.halfRebin_eq_self_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.halfRebin_eq_self_of_le

/-- info: 'Chvatal.PacketAlignment.halfRebin_centered_energy_eq_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.halfRebin_centered_energy_eq_of_le

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

/-- info: 'Chvatal.PacketAlignment.halfRebin_centered_energy_drop_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.halfRebin_centered_energy_drop_exact

/-- info: 'Chvatal.PacketAlignment.senderRepair_centered_energy_drop_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.senderRepair_centered_energy_drop_exact

/-- info: 'Chvatal.PacketAlignment.senderRepair_lowCount_count_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.senderRepair_lowCount_count_identity

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

/-- info: 'Chvatal.PacketAlignment.profileInterval_restrict_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileInterval_restrict_cell

/-- info: 'Chvatal.PacketAlignment.profileIntervalMean_restrict_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileIntervalMean_restrict_cell

/-- info: 'Chvatal.PacketAlignment.profileIntervalMean_restrict_cell_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileIntervalMean_restrict_cell_local

/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_merge_wholeBlock_owner_L2_le_of_overlap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_merge_wholeBlock_owner_L2_le_of_overlap

/-- info: 'Chvatal.PacketAlignment.packetFamily64_transpose_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64_transpose_merge

/-- info: 'Chvatal.PacketAlignment.receiverChildFamilies_transpose_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.receiverChildFamilies_transpose_merge

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_childCohorts_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_childCohorts_merge

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_childCohorts_parentPartition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_childCohorts_parentPartition

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_macroSource_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_macroSource_partition

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_macroSource_commonBatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_macroSource_commonBatch

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_macroSource_outputPartition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_macroSource_outputPartition

/-- info: 'Chvatal.PacketAlignment.flowA7_root_receiver_packetAssembly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_root_receiver_packetAssembly

/-- info: 'Chvatal.PacketAlignment.flowA7_root_receiver_fullBlocksBatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_root_receiver_fullBlocksBatch

/-- info: 'Chvatal.PacketAlignment.flowA7_topReceiver_wireSet_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_topReceiver_wireSet_empty

/-- info: 'Chvatal.PacketAlignment.profileInterval_packetwise_vs_aggregate_counterexample' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.profileInterval_packetwise_vs_aggregate_counterexample

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

/-- info: 'Chvatal.PacketAlignment.upSetEndpoint_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.upSetEndpoint_partition

/-- info: 'Chvatal.PacketAlignment.parallelUpFringeEndpointRepair_packetLayout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.parallelUpFringeEndpointRepair_packetLayout

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_child_up_packetLayout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_child_up_packetLayout

/-- info: 'Chvatal.PacketAlignment.parallelSourcePortPacketLayout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.parallelSourcePortPacketLayout

/-- info: 'Chvatal.PacketAlignment.flowA7_scheduled_source_port_packetLayout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.flowA7_scheduled_source_port_packetLayout

/-- info: 'Chvatal.PacketAlignment.flowA7_source_port_packetLayout_register' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.flowA7_source_port_packetLayout_register

/-- info: 'Chvatal.PacketAlignment.genPacketRound_dealt_lanes_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketRound_dealt_lanes_sorted

/-- info: 'Chvatal.PacketAlignment.genPacketRound_dealt_supports_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketRound_dealt_supports_disjoint

/-- info: 'Chvatal.PacketAlignment.genPacketRound_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketRound_depth_le

/-- info: 'Chvatal.PacketAlignment.genPacketRound_exec_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketRound_exec_inside

/-- info: 'Chvatal.PacketAlignment.genPacketRound_exec_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketRound_exec_outside

/-- info: 'Chvatal.PacketAlignment.genPacketRound_outputPackets_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketRound_outputPackets_sorted

/-- info: 'Chvatal.PacketAlignment.genPacketRound_outputPackets_support' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketRound_outputPackets_support

/-- info: 'Chvatal.PacketAlignment.genPacketRound_outputPackets_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketRound_outputPackets_disjoint

/-- info: 'Chvatal.PacketAlignment.joinPacketEmbedding_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.joinPacketEmbedding_range

/-- info: 'Chvatal.PacketAlignment.genJoinMatching_edges_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genJoinMatching_edges_disjoint

/-- info: 'Chvatal.PacketAlignment.genJoinMatching_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genJoinMatching_disjoint

/-- info: 'Chvatal.PacketAlignment.genJoinMatching_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genJoinMatching_nodup

/-- info: 'Chvatal.PacketAlignment.genJoinMatching_round_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genJoinMatching_round_depth_le

/-- info: 'Chvatal.PacketAlignment.genJoinMatching_round_outputPackets_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genJoinMatching_round_outputPackets_sorted

/-- info: 'Chvatal.PacketAlignment.genJoinMatching_round_outputPackets_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genJoinMatching_round_outputPackets_disjoint

/-- info: 'Chvatal.PacketAlignment.genJoinMatching_round_outputPackets_support' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genJoinMatching_round_outputPackets_support

/-- info: 'Chvatal.PacketAlignment.genIndexedPairSupports_edges_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPairSupports_edges_disjoint

/-- info: 'Chvatal.PacketAlignment.genIndexedPairSupports_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPairSupports_disjoint

/-- info: 'Chvatal.PacketAlignment.genIndexedPairSupports_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPairSupports_nodup

/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRound_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRound_depth_le

/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRound_output_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRound_output_sorted

/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRound_output_support' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRound_output_support

/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRound_output_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRound_output_disjoint

/-- info: 'Chvatal.PacketAlignment.adjacentPacketMatching_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.adjacentPacketMatching_nodup

/-- info: 'Chvatal.PacketAlignment.adjacentPacketMatching_noFixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.adjacentPacketMatching_noFixed

/-- info: 'Chvatal.PacketAlignment.adjacentPacketMatching_vertexDisjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.adjacentPacketMatching_vertexDisjoint

/-- info: 'Chvatal.PacketAlignment.adjacentPacketMatching_covers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.adjacentPacketMatching_covers

/-- info: 'Chvatal.PacketAlignment.flowA7_sourcePortRepairNet_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_sourcePortRepairNet_depth_le

/-- info: 'Chvatal.PacketAlignment.flowA7_sourcePortRepairNetAt_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_sourcePortRepairNetAt_depth_le

/-- info: 'Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_depth_le

/-- info: 'Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_transport

/-- info: 'Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_layout

/-- info: 'Chvatal.PacketAlignment.PacketSortedOn_orderEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.PacketSortedOn_orderEmb

/-- info: 'Chvatal.PacketAlignment.PacketSortedOn_orderEmb_of_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.PacketSortedOn_orderEmb_of_card_eq
/-- info: 'Chvatal.PacketAlignment.rankSortedOn_packetEmbedding_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.rankSortedOn_packetEmbedding_range
/-- info: 'Chvatal.PacketAlignment.packetSortedOn_of_rankAlignedFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetSortedOn_of_rankAlignedFamily

/-- info: 'Chvatal.PacketAlignment.rankIn_univ_eq_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.rankIn_univ_eq_val

/-- info: 'Chvatal.PacketAlignment.blockOf_register_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.blockOf_register_image

/-- info: 'Chvatal.PacketAlignment.downSetRepairPacket_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.downSetRepairPacket_union

/-- info: 'Chvatal.PacketAlignment.downSetRepairPacket_pairwise_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.downSetRepairPacket_pairwise_disjoint

/-- info: 'Chvatal.PacketAlignment.downSetRepairPacket_card_eq_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.downSetRepairPacket_card_eq_64

/-- info: 'Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_downCutFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_downCutFamily

/-- info: 'Chvatal.PacketAlignment.upSetRepairPacket_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.upSetRepairPacket_union

/-- info: 'Chvatal.PacketAlignment.upSetRepairPacket_pairwise_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.upSetRepairPacket_pairwise_disjoint

/-- info: 'Chvatal.PacketAlignment.upSetRepairPacket_card_eq_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.upSetRepairPacket_card_eq_64

/-- info: 'Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_upSetFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_upSetFamily

/-- info: 'Chvatal.PacketAlignment.sourcePortRepairPacket_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.sourcePortRepairPacket_union

/-- info: 'Chvatal.PacketAlignment.sourcePortRepairPacket_pairwise_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.sourcePortRepairPacket_pairwise_disjoint

/-- info: 'Chvatal.PacketAlignment.sourcePortRepairPacket_card_eq_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.sourcePortRepairPacket_card_eq_64

/-- info: 'Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_sourcePackets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_sourcePackets

/-- info: 'Chvatal.PacketAlignment.receiverPacketFamily_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.receiverPacketFamily_union

/-- info: 'Chvatal.PacketAlignment.receiverPacketFamily_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.receiverPacketFamily_sorted

/-- info: 'Chvatal.PacketAlignment.receiverPacketFamily_pairwise_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.receiverPacketFamily_pairwise_disjoint

/-- info: 'Chvatal.PacketAlignment.receiverPacketFamily_card_eq_64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.receiverPacketFamily_card_eq_64

/-- info: 'Chvatal.PacketAlignment.receiverPacketFamily_wireSets_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.receiverPacketFamily_wireSets_union

/-- info: 'Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_noRepair_packetCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_noRepair_packetCells

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_packetAssembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_packetAssembly

/-- info: 'Chvatal.PacketAlignment.alignedUpRepairPacket_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.alignedUpRepairPacket_union

/-- info: 'Chvatal.PacketAlignment.alignedUpRepairPacket_pairwise_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.alignedUpRepairPacket_pairwise_disjoint

/-- info: 'Chvatal.PacketAlignment.alignedUpRepairPacket_card_eq_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.alignedUpRepairPacket_card_eq_64

/-- info: 'Chvatal.PacketAlignment.alignedUpRepairPacket_sorted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.alignedUpRepairPacket_sorted

/-- info: 'Chvatal.PacketAlignment.alignedDownRepairPacket_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.alignedDownRepairPacket_union

/-- info: 'Chvatal.PacketAlignment.alignedDownRepairPacket_pairwise_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.alignedDownRepairPacket_pairwise_disjoint

/-- info: 'Chvatal.PacketAlignment.alignedDownRepairPacket_card_eq_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.alignedDownRepairPacket_card_eq_64

/-- info: 'Chvatal.PacketAlignment.alignedDownRepairPacket_sorted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.alignedDownRepairPacket_sorted

/-- info: 'Chvatal.PacketAlignment.rankPacketCell_eq_global' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.rankPacketCell_eq_global

/-- info: 'Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_alignedUpFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_alignedUpFamily

/-- info: 'Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_alignedDownCutFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_alignedDownCutFamily

/-- info: 'Chvatal.PacketAlignment.rankPacketCell_whole_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.rankPacketCell_whole_union

/-- info: 'Chvatal.PacketAlignment.rankPacketCell_whole_pairwise_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.rankPacketCell_whole_pairwise_disjoint

/-- info: 'Chvatal.PacketAlignment.rankPacketCell_whole_card_eq_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.rankPacketCell_whole_card_eq_64

/-- info: 'Chvatal.PacketAlignment.upSet_eq_self_of_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.upSet_eq_self_of_card_eq

/-- info: 'Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_zeroDownUpFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_sourcePortRepairStage_zeroDownUpFamily

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_aligned_packetAssembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_aligned_packetAssembly

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_packetAssembly_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_packetAssembly_fin

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_packetAssembly_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_packetAssembly_canonical

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_parentPort_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_parentPort_canonical

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_childPorts_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_childPorts_canonical

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_canonical

/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRound_canonicalOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRound_canonicalOutput

/-- info: 'Chvatal.PacketAlignment.canonicalPacketFamily_toEmbeddings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketFamily_toEmbeddings

/-- info: 'Chvatal.PacketAlignment.canonicalPacketFamily_fullBlocks_with_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketFamily_fullBlocks_with_tail

/-- info: 'Chvatal.PacketAlignment.canonicalStreamFamilies_fullBlocks_disjoint' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalStreamFamilies_fullBlocks_disjoint
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_regularTailPool_commonBatch' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_regularTailPool_commonBatch
/-- info: 'Chvatal.PacketAlignment.canonicalStreamAndExceptionPool_fullBlocks_batch' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalStreamAndExceptionPool_fullBlocks_batch
/-- info: 'Chvatal.PacketAlignment.canonicalStreamFullBlock_blocks_disjoint_exceptionPool' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalStreamFullBlock_blocks_disjoint_exceptionPool
/-- info: 'Chvatal.PacketAlignment.packetBlockListSupport_eq_outputChunks' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetBlockListSupport_eq_outputChunks
/-- info: 'Chvatal.PacketAlignment.canonicalStreamFamilies_fullBlocks_data' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalStreamFamilies_fullBlocks_data
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_regularFullBlocks' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_regularFullBlocks
/-- info: 'Chvatal.PacketAlignment.canonicalStreamFullBlock_exceptionPool' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalStreamFullBlock_exceptionPool
/-- info: 'Chvatal.PacketAlignment.canonicalStreamFullBlock_exceptionPool_partition' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalStreamFullBlock_exceptionPool_partition
/-- info: 'Chvatal.PacketAlignment.canonicalPacketFamily_fullBlocks_data' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketFamily_fullBlocks_data
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_regularTailPool' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_regularTailPool

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_embeddingFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_embeddingFamily

/-- info: 'Chvatal.PacketAlignment.canonicalPacketFamily_count_mul_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketFamily_count_mul_64

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_packetCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_packetCount

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_divisible64_batch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_divisible64_batch

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_residue63_batch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_residue63_batch

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_packetCount_block_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_packetCount_block_shape

/-- info: 'Chvatal.PacketAlignment.flowA7_terminal_packet_count_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_terminal_packet_count_shape

/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRound_unmatched_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRound_unmatched_unchanged

/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRound_output_support_incident' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRound_output_support_incident

/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRound_withSingletons_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRound_withSingletons_contract

/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRound_withSingletons_canonicalOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRound_withSingletons_canonicalOutput

/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRound_canonicalOutput_fixedCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRound_canonicalOutput_fixedCount
/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRound_withSingletons_canonicalOutput_fixedCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRound_withSingletons_canonicalOutput_fixedCount
/-- info: 'Chvatal.PacketAlignment.genIndexedPacketRounds_twoStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genIndexedPacketRounds_twoStep
/-- info: 'Chvatal.PacketAlignment.indexedPacketPerfectMatching_preservesState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.indexedPacketPerfectMatching_preservesState
/-- info: 'Chvatal.PacketAlignment.iterateIndexedPacketPerfectMatchings_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.iterateIndexedPacketPerfectMatchings_step
/-- info: 'Chvatal.PacketAlignment.indexedPacketMatching_preservesState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.indexedPacketMatching_preservesState
/-- info: 'Chvatal.PacketAlignment.indexedPacketMatching_preservesPhysicalState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.indexedPacketMatching_preservesPhysicalState

/-- info: 'Chvatal.PacketAlignment.interBlockBoundaryMatching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.interBlockBoundaryMatching

/-- info: 'Chvatal.PacketAlignment.interBlockBoundaryMatching_preservesPhysicalState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.interBlockBoundaryMatching_preservesPhysicalState

/-- info: 'Chvatal.PacketAlignment.adjacentPacketMatchingFlattenedOutput_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.adjacentPacketMatchingFlattenedOutput_contract

/-- info: 'Chvatal.PacketAlignment.adjacentThenBoundaryMatching_preservesPhysicalState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.adjacentThenBoundaryMatching_preservesPhysicalState
/-- info: 'Chvatal.PacketAlignment.interBlockBoundaryOutputBlock_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.interBlockBoundaryOutputBlock_contract
/-- info: 'Chvatal.PacketAlignment.interBlockBoundaryGroupedOutput_support_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.interBlockBoundaryGroupedOutput_support_eq
/-- info: 'Chvatal.PacketAlignment.interBlockBoundaryMatching_preservesGroupedPhysicalState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.interBlockBoundaryMatching_preservesGroupedPhysicalState
/-- info: 'Chvatal.PacketAlignment.interBlockBoundaryGroupedOutput_nextBoundaryEdge_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.interBlockBoundaryGroupedOutput_nextBoundaryEdge_ordered
/-- info: 'Chvatal.PacketAlignment.iterateIndexedOrderedPacketMatchings_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.iterateIndexedOrderedPacketMatchings_step
/-- info: 'Chvatal.PacketAlignment.iterateIndexedPacketMatchings_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.iterateIndexedPacketMatchings_step

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge128_physicalHalf_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge128_physicalHalf_counts

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge128_balanced_deal_vs_physical_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge128_balanced_deal_vs_physical_halves

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge128_balanced_inputs_shift_physical_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge128_balanced_inputs_shift_physical_profile

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge128_physicalHalf_doubledEnergy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge128_physicalHalf_doubledEnergy

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_physicalHalf_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_physicalHalf_counts

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_balanced_deal_vs_physical_halves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_balanced_deal_vs_physical_halves

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_physicalHalf_doubledEnergy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_physicalHalf_doubledEnergy

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_dealt_doubledEnergy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_dealt_doubledEnergy

/-- info: 'Chvatal.PacketAlignment.parityEnergy_le_twoRunInputEnergy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.parityEnergy_le_twoRunInputEnergy

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_dealt_energy_le_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_dealt_energy_le_input

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_parallel_dealt_energy_le_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_parallel_dealt_energy_le_input

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_monotone_parity_energy_le_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_monotone_parity_energy_le_input

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_monotone_parity_energy_eq_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_monotone_parity_energy_eq_residual

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_monotone_input_energy_eq_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_monotone_input_energy_eq_phase

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_monotone_energy_drop_eq_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_monotone_energy_drop_eq_phase

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_phase_drop_ge_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_phase_drop_ge_eight

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_phase_drop_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_phase_drop_eq_zero_iff

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_monotone_energy_drop_ge_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_monotone_energy_drop_ge_eight

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_monotone_energy_drop_ge_three_quarters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_monotone_energy_drop_ge_three_quarters

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_monotone_energy_drop_with_exception' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_monotone_energy_drop_with_exception

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_family_energy_drop_with_exception' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_family_energy_drop_with_exception

/-- info: 'Chvatal.PacketAlignment.canonicalPacketFamily_energy_drop_with_exception' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketFamily_energy_drop_with_exception

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_energy_drop_with_exception' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_energy_drop_with_exception

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_parity_rebin_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_parity_rebin_L1_exact

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_ownedParityProfile_rebin_L1_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_ownedParityProfile_rebin_L1_exact

/-- info: 'Chvatal.PacketAlignment.monotoneBool_eq_countSuffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.monotoneBool_eq_countSuffix

/-- info: 'Chvatal.PacketAlignment.boolTrueCount_countSuffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.boolTrueCount_countSuffix

/-- info: 'Chvatal.PacketAlignment.monotoneBits_assignedRankProfiles_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.monotoneBits_assignedRankProfiles_L1_exact
/-- info: 'Chvatal.PacketAlignment.monotoneBits_assignedRankProfiles_aggregate_L2_var' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.monotoneBits_assignedRankProfiles_aggregate_L2_var
/-- info: 'Chvatal.PacketAlignment.monotoneBits_assignedRankProfiles_aggregate_L2_var_allow_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.monotoneBits_assignedRankProfiles_aggregate_L2_var_allow_endpoint
/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_assignedParityProfiles_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_assignedParityProfiles_L1_exact

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_assignedParityProfiles_L2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_assignedParityProfiles_L2_le

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_assignedParity_signed_error_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_assignedParity_signed_error_eq

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_assignedParity_cohort_signed_error_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_assignedParity_cohort_signed_error_eq

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_assignedParity_cohort_L2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_assignedParity_cohort_L2_le

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_parityMean_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_parityMean_mono

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_parityMean_eq_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_parityMean_eq_code

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_parityCode_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_parityCode_valid

/-- info: 'Chvatal.PacketAlignment.canonicalPacketFamily_parity_rebin_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketFamily_parity_rebin_L1_exact

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_parity_rebin_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_parity_rebin_L1_exact


/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_family_active_drop_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_family_active_drop_lower_bound


/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_parallel_monotone_parity_energy_le_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_parallel_monotone_parity_energy_le_input

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_scatteredFamily_dealt_energy_le_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_scatteredFamily_dealt_energy_le_input

/-- info: 'Chvatal.PacketAlignment.oddEvenMerge64_rankSortedFamily_dealt_energy_le_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.oddEvenMerge64_rankSortedFamily_dealt_energy_le_input

/-- info: 'Chvatal.PacketAlignment.canonicalPacketFamily_dealt_energy_le_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketFamily_dealt_energy_le_input

/-- info: 'Chvatal.PacketAlignment.canonicalPacketFamily_parity_energy_le_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketFamily_parity_energy_le_input

/-- info: 'Chvatal.PacketAlignment.canonicalPacketFamily_parity_energy_eq_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketFamily_parity_energy_eq_residual

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_packetEnergy_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_packetEnergy_contraction

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_packetEnergy_contraction_multi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_packetEnergy_contraction_multi

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_parityEnergy_contraction_multi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_parityEnergy_contraction_multi

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_parityEnergy_exact_multi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_parityEnergy_exact_multi


/-- info: 'Chvatal.PacketAlignment.packetParityRankSupports_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetParityRankSupports_partition

/-- info: 'Chvatal.PacketAlignment.packetEmbeddingSupport_parity_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetEmbeddingSupport_parity_partition

/-- info: 'Chvatal.PacketAlignment.packetEvenRankEmbedding_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetEvenRankEmbedding_strictMono

/-- info: 'Chvatal.PacketAlignment.packetOddRankEmbedding_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetOddRankEmbedding_strictMono

/-- info: 'Chvatal.PacketAlignment.canonicalPacketParitySupports_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketParitySupports_partition

/-- info: 'Chvatal.PacketAlignment.canonicalPacketParityEmbeddings_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketParityEmbeddings_strictMono

/-- info: 'Chvatal.PacketAlignment.canonicalPacketParityEmbeddings_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketParityEmbeddings_disjoint

/-- info: 'Chvatal.PacketAlignment.canonicalPacketParityEmbeddings_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketParityEmbeddings_cover

/-- info: 'Chvatal.PacketAlignment.canonicalPacketParityEmbedding_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketParityEmbedding_mem

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_parityOwnerCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_parityOwnerCount
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_parityOwnerCount_intersection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_parityOwnerCount_intersection

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_repairedParent_alignedChildren_packetAssembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_repairedParent_alignedChildren_packetAssembly

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_alignedParent_repairedChildren_packetAssembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_alignedParent_repairedChildren_packetAssembly

/-- info: 'Chvatal.PacketAlignment.flowA7_zeroDownSet_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_zeroDownSet_empty

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_zeroParent_packetAssembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_zeroParent_packetAssembly

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_zeroDownChildren_packetAssembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_zeroDownChildren_packetAssembly

/-- info: 'Chvatal.PacketAlignment.stageNet_rankSortedOn_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.stageNet_rankSortedOn_image

/-- info: 'Chvatal.PacketAlignment.stageNet_rankSortedOn_image_of_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.stageNet_rankSortedOn_image_of_card_eq

/-- info: 'Chvatal.PacketAlignment.rankSortedOn_of_thresholds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.rankSortedOn_of_thresholds

/-- info: 'Chvatal.PacketAlignment.flowA7_sourcePortRepairNet_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_sourcePortRepairNet_layout

/-- info: 'Chvatal.PacketAlignment.flowA7_packet_count_block_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_packet_count_block_shape

/-- info: 'Chvatal.PacketAlignment.flowA7_packet_tail_fraction_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_packet_tail_fraction_le

/-- info: 'Chvatal.PacketAlignment.unequalCorrectedInterleave_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalCorrectedInterleave_sorted

/-- info: 'Chvatal.PacketAlignment.unequalCorrectionLayer_parallel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalCorrectionLayer_parallel

/-- info: 'Chvatal.PacketAlignment.unequalCorrectionLayer_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalCorrectionLayer_depth_le

/-- info: 'Chvatal.PacketAlignment.unequalInterleave_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalInterleave_odd

/-- info: 'Chvatal.PacketAlignment.unequalInterleave_even_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalInterleave_even_succ

/-- info: 'Chvatal.PacketAlignment.unequalCorrectionLayer_exec_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalCorrectionLayer_exec_odd

/-- info: 'Chvatal.PacketAlignment.unequalCorrectionLayer_exec_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalCorrectionLayer_exec_even

/-- info: 'Chvatal.PacketAlignment.unequal_cross_bounds_of_threshold_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequal_cross_bounds_of_threshold_gap

/-- info: 'Chvatal.PacketAlignment.unequalCorrectionLayer_exec_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalCorrectionLayer_exec_first

/-- info: 'Chvatal.PacketAlignment.unequalCorrectionLayer_exec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalCorrectionLayer_exec_eq

/-- info: 'Chvatal.PacketAlignment.unequalCorrectionLayer_sorts_of_threshold_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalCorrectionLayer_sorts_of_threshold_gap

/-- info: 'Chvatal.PacketAlignment.unequalSourceParityThresholdGap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalSourceParityThresholdGap

/-- info: 'Chvatal.PacketAlignment.unequalThresholdCount_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalThresholdCount_exec

/-- info: 'Chvatal.PacketAlignment.unequalThresholdGap_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalThresholdGap_exec

/-- info: 'Chvatal.PacketAlignment.unequalSourceParityThresholdGap_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalSourceParityThresholdGap_exec

/-- info: 'Chvatal.PacketAlignment.unequalThresholdCount_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalThresholdCount_cast

/-- info: 'Chvatal.PacketAlignment.unequalSourceParityThresholdGap_exec_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalSourceParityThresholdGap_exec_cast

/-- info: 'Chvatal.PacketAlignment.unequalParityMerge_step_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalParityMerge_step_sorts

/-- info: 'Chvatal.PacketAlignment.evenSourceParityThresholdGap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.evenSourceParityThresholdGap

/-- info: 'Chvatal.PacketAlignment.equal_cross_bounds_of_threshold_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.equal_cross_bounds_of_threshold_gap


/-- info: 'Chvatal.PacketAlignment.evenSourceParityThresholdGap_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.evenSourceParityThresholdGap_exec

/-- info: 'Chvatal.PacketAlignment.equalCorrectedInterleave_sorted_of_threshold_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.equalCorrectedInterleave_sorted_of_threshold_gap

/-- info: 'Chvatal.PacketAlignment.equalCorrectionLayer_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.equalCorrectionLayer_depth_le

/-- info: 'Chvatal.PacketAlignment.equalCorrectionLayer_exec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.equalCorrectionLayer_exec_eq

/-- info: 'Chvatal.PacketAlignment.equalCorrectionLayer_sorts_of_threshold_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.equalCorrectionLayer_sorts_of_threshold_gap

/-- info: 'Chvatal.PacketAlignment.evenParityMerge_step_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.evenParityMerge_step_sorts

/-- info: 'Chvatal.PacketAlignment.equalParityFront_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.equalParityFront_depth_le

/-- info: 'Chvatal.PacketAlignment.equalParityMergeNet_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.equalParityMergeNet_depth_le

/-- info: 'Chvatal.PacketAlignment.equalParityMergeNet_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.equalParityMergeNet_sorts

/-- info: 'Chvatal.PacketAlignment.equalParityMerge64_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.equalParityMerge64_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.equalParityMerge64_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.equalParityMerge64_depth_le

/-- info: 'Chvatal.PacketAlignment.standard64Merge_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.standard64Merge_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.standard64Merge_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.standard64Merge_depth_le
/-- info: 'Chvatal.PacketAlignment.standard64Merge_scatter_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.standard64Merge_scatter_sorts_two_runs
/-- info: 'Chvatal.PacketAlignment.standard64Merge_scatter_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.standard64Merge_scatter_depth_le

/-- info: 'Chvatal.PacketAlignment.unequalMerge3Net_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalMerge3Net_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.unequalMerge7Net_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalMerge7Net_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.unequalMerge15Net_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalMerge15Net_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.unequalMerge31Net_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalMerge31Net_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.unequalMerge63Net_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalMerge63Net_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.unequalMerge63Net_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalMerge63Net_depth_le

/-- info: 'Chvatal.PacketAlignment.equalParityMergeNet_sorts_two_even_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.equalParityMergeNet_sorts_two_even_runs

/-- info: 'Chvatal.PacketAlignment.unequalTail63Lift6_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalTail63Lift6_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.unequalTail63Lift6_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalTail63Lift6_depth_le

/-- info: 'Chvatal.PacketAlignment.unequalTail31Lift6_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalTail31Lift6_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.unequalTail31Lift6_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalTail31Lift6_depth_le

/-- info: 'Chvatal.PacketAlignment.unequalTail15Lift6_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalTail15Lift6_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.unequalTail15Lift6_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalTail15Lift6_depth_le

/-- info: 'Chvatal.PacketAlignment.unequalTail7Lift6_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalTail7Lift6_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.unequalTail7Lift6_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalTail7Lift6_depth_le

/-- info: 'Chvatal.PacketAlignment.unequalTail3Lift6_sorts_two_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalTail3Lift6_sorts_two_runs

/-- info: 'Chvatal.PacketAlignment.unequalTail3Lift6_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.unequalTail3Lift6_depth_le

/-- info: 'Chvatal.PacketAlignment.packetOddTree6_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetOddTree6_sorts

/-- info: 'Chvatal.PacketAlignment.packetOddTree6_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetOddTree6_depth_le

/-- info: 'Chvatal.PacketAlignment.PacketMergeTree.scatter_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.PacketMergeTree.scatter_sorts

/-- info: 'Chvatal.PacketAlignment.PacketMergeTree.scatter_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.PacketMergeTree.scatter_depth_le

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTree_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTree_sorts

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTree_depth_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTree_depth_eq

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTree_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTree_depth_le

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTreeOutputEmbedding_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTreeOutputEmbedding_disjoint

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTreeOutputEmbedding_covers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTreeOutputEmbedding_covers

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTreeOutputEmbedding_support_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTreeOutputEmbedding_support_iff

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTree_outputPacket_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTree_outputPacket_sorted

/-- info: 'Chvatal.PacketAlignment.genPacketGroup63Embedding_mem_packets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketGroup63Embedding_mem_packets

/-- info: 'Chvatal.PacketAlignment.genPacketGroup63Embedding_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketGroup63Embedding_strictMono

/-- info: 'Chvatal.PacketAlignment.genPacketGroup63Embedding_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketGroup63Embedding_strictMono

/-- info: 'Chvatal.PacketAlignment.genPacketGroup63Embedding_covers_packets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketGroup63Embedding_covers_packets

/-- info: 'Chvatal.PacketAlignment.PacketMergeTree.runsSorted_of_chunks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.PacketMergeTree.runsSorted_of_chunks

/-- info: 'Chvatal.PacketAlignment.packetOddTree6_runsSorted_of_packets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetOddTree6_runsSorted_of_packets

/-- info: 'Chvatal.PacketAlignment.packetOddTree6GroupNet_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetOddTree6GroupNet_sorts

/-- info: 'Chvatal.PacketAlignment.packetOddTree6GroupNet_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetOddTree6GroupNet_depth_le

/-- info: 'Chvatal.PacketAlignment.packetOddTree6GroupNet_outputPacket_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetOddTree6GroupNet_outputPacket_strictMono

/-- info: 'Chvatal.PacketAlignment.packetOddTree6GroupNet_outputPacket_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetOddTree6GroupNet_outputPacket_sorted

/-- info: 'Chvatal.PacketAlignment.genScatterBatch_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterBatch_depth_le

/-- info: 'Chvatal.PacketAlignment.genScatterBatch_comparator_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterBatch_comparator_endpoints

/-- info: 'Chvatal.PacketAlignment.genScatter_comparator_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatter_comparator_endpoints

/-- info: 'Chvatal.PacketAlignment.genScatterBatch_genScatter_comparators_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterBatch_genScatter_comparators_disjoint

/-- info: 'Chvatal.PacketAlignment.genScatterBatch_exec_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterBatch_exec_outside

/-- info: 'Chvatal.PacketAlignment.genScatterBatch_exec_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterBatch_exec_inside

/-- info: 'Chvatal.PacketAlignment.genDisjointAppend_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genDisjointAppend_depth_le

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTreeBatch_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTreeBatch_depth_le

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTreeBatch_outputPacket_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTreeBatch_outputPacket_sorted

/-- info: 'Chvatal.PacketAlignment.genMergeTreeFullTailBatch_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genMergeTreeFullTailBatch_depth_le

/-- info: 'Chvatal.PacketAlignment.packetFamily_residue63_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily_residue63_merge

/-- info: 'Chvatal.PacketAlignment.genMergeTreeFullTailBatch_outputPacket_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genMergeTreeFullTailBatch_outputPacket_sorted

/-- info: 'Chvatal.PacketAlignment.genMergeTreeFullTailBatch_output_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genMergeTreeFullTailBatch_output_support

/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockIndex_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockIndex_injective

/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockEmbedding_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockEmbedding_disjoint

/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_nodup

/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_disjoint

/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_merge_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_merge_depth_le

/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_merge_output_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_merge_output_sorted
/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_merge_output_blockSorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_merge_output_blockSorted
/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_merge_wholeBlock_owner_L2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_merge_wholeBlock_owner_L2_le
/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_merge_output_valuesOrdered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_merge_output_valuesOrdered
/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_merge_outputFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_merge_outputFamily

/-- info: 'Chvatal.PacketAlignment.packetFamily_divisible64_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily_divisible64_merge

/-- info: 'Chvatal.PacketAlignment.packetPowerTree6_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetPowerTree6_depth_le

/-- info: 'Chvatal.PacketAlignment.packetPowerTree6_runsSorted_of_packets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetPowerTree6_runsSorted_of_packets

/-- info: 'Chvatal.PacketAlignment.packetPowerTree6GroupNet_sorts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetPowerTree6GroupNet_sorts

/-- info: 'Chvatal.PacketAlignment.packetPowerTree6GroupNet_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetPowerTree6GroupNet_depth_le

/-- info: 'Chvatal.PacketAlignment.packetPowerTree6GroupNet_outputPacket_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetPowerTree6GroupNet_outputPacket_strictMono

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTreeOutputEmbedding_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTreeOutputEmbedding_ordered

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTreeOutputPackets_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTreeOutputPackets_ordered

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTreeOutputPackets_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTreeOutputPackets_disjoint

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTree_outputPackets_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTree_outputPackets_sorted
/-- info: 'Chvatal.PacketAlignment.genScatterMergeTree_outputPackets_valuesOrdered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTree_outputPackets_valuesOrdered

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTree_outputPhysicalPacketState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTree_outputPhysicalPacketState

/-- info: 'Chvatal.PacketAlignment.packetPowerTree6GroupNet_outputPackets_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetPowerTree6GroupNet_outputPackets_ordered

/-- info: 'Chvatal.PacketAlignment.packetPowerTree6GroupNet_outputPacket_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetPowerTree6GroupNet_outputPacket_sorted

/-- info: 'Chvatal.PacketAlignment.genPacketGroup64Embedding_mem_packets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketGroup64Embedding_mem_packets

/-- info: 'Chvatal.PacketAlignment.genPacketGroup64Embedding_covers_packets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genPacketGroup64Embedding_covers_packets

/-- info: 'Chvatal.PacketAlignment.boolTrueCount_genPacketGroup64Embedding_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.boolTrueCount_genPacketGroup64Embedding_sum

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTree_output_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTree_output_profile

/-- info: 'Chvatal.PacketAlignment.packetPowerTree6GroupNet_output_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetPowerTree6GroupNet_output_profile

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTree_output_threshold_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTree_output_threshold_profile
/-- info: 'Chvatal.PacketAlignment.genScatterMergeTree_output_threshold_profile_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTree_output_threshold_profile_L1_exact
/-- info: 'Chvatal.PacketAlignment.packetPowerTree6GroupNet_output_threshold_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetPowerTree6GroupNet_output_threshold_profile
/-- info: 'Chvatal.PacketAlignment.packetPowerTree6GroupNet_heterogeneous_profile_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetPowerTree6GroupNet_heterogeneous_profile_error_le
/-- info: 'Chvatal.PacketAlignment.packetPowerTree6GroupNet_heterogeneous_profile_error_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetPowerTree6GroupNet_heterogeneous_profile_error_exact
/-- info: 'Chvatal.PacketAlignment.packetPowerTree6GroupNet_heterogeneous_profile_energy_le_signed_sum_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetPowerTree6GroupNet_heterogeneous_profile_energy_le_signed_sum_sq
/-- info: 'Chvatal.PacketAlignment.packetPowerTree6GroupNet_heterogeneous_profile_energy_normalized_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetPowerTree6GroupNet_heterogeneous_profile_energy_normalized_le

/-- info: 'Chvatal.PacketAlignment.genScatterMergeTreeBatch_output_threshold_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTreeBatch_output_threshold_profile

/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_merge_output_threshold_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_merge_output_threshold_profile

/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_merge_heterogeneous_profile_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_merge_heterogeneous_profile_energy_le

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_divisible64_batch_profiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_divisible64_batch_profiles
/-- info: 'Chvatal.PacketAlignment.genScatterMergeTree_output_threshold_profile_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTree_output_threshold_profile_k

/-- info: 'Chvatal.PacketAlignment.genMergeTreeFullTailBatch_output_threshold_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genMergeTreeFullTailBatch_output_threshold_profile

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_residue63_batch_profiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_residue63_batch_profiles

/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_packetCount_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_packetCount_residue

/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_support
/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_residue63_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_residue63_support
/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_output_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_output_support
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_divisible64_batch_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_divisible64_batch_support
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_allCases_residue63_batch_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_allCases_residue63_batch_support
/-- info: 'Chvatal.PacketAlignment.monotoneCountDecomposition_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.monotoneCountDecomposition_L1_exact

/-- info: 'Chvatal.PacketAlignment.monotoneCountDecomposition_L2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.monotoneCountDecomposition_L2_le
/-- info: 'Chvatal.PacketAlignment.assignedRankProfiles_L1_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.assignedRankProfiles_L1_exact
/-- info: 'Chvatal.PacketAlignment.monotoneBlocks_assignedRankProfiles_L1_nonincrease' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.monotoneBlocks_assignedRankProfiles_L1_nonincrease
/-- info: 'Chvatal.PacketAlignment.assignedRankProfiles_aggregate_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.assignedRankProfiles_aggregate_L2
/-- info: 'Chvatal.PacketAlignment.assignedRankProfiles_aggregate_L2_var' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.assignedRankProfiles_aggregate_L2_var
/-- info: 'Chvatal.PacketAlignment.finiteErrorProfiles_aggregate_L2_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.finiteErrorProfiles_aggregate_L2_overlap
/-- info: 'Chvatal.PacketAlignment.flowDown7_levelTwo_timeSix_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowDown7_levelTwo_timeSix_eq
/-- info: 'Chvatal.PacketAlignment.flowDown7_levelTwo_timeSix_div4096_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowDown7_levelTwo_timeSix_div4096_eq
/-- info: 'Chvatal.PacketAlignment.not_three_partial_rankGroups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.not_three_partial_rankGroups
/-- info: 'Chvatal.PacketAlignment.partialRankGroupIndices_card_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.partialRankGroupIndices_card_le_two
/-- info: 'Chvatal.PacketAlignment.not_three_partial_rankIntervals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.not_three_partial_rankIntervals
/-- info: 'Chvatal.PacketAlignment.partialRankIntervalIndices_card_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.partialRankIntervalIndices_card_le_two
/-- info: 'Chvatal.PacketAlignment.wireSetOwner_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireSetOwner_mem
/-- info: 'Chvatal.PacketAlignment.wireSetOwner_eq_iff_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireSetOwner_eq_iff_mem
/-- info: 'Chvatal.PacketAlignment.assignedRankCount_wireSetPacketRankOwner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.assignedRankCount_wireSetPacketRankOwner
/-- info: 'Chvatal.PacketAlignment.packetRankOwner_trueCountOn_eq_of_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetRankOwner_trueCountOn_eq_of_partition

/-- info: 'Chvatal.PacketAlignment.packetRankOwner_trueCountOn_eq_of_local_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetRankOwner_trueCountOn_eq_of_local_partition
/-- info: 'Chvatal.PacketAlignment.packetRankOwner_trueCountOn_intersection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetRankOwner_trueCountOn_intersection
/-- info: 'Chvatal.PacketAlignment.natProfileInterp_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.natProfileInterp_between
/-- info: 'Chvatal.PacketAlignment.natProfileInterp_mono_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.natProfileInterp_mono_mean
/-- info: 'Chvatal.PacketAlignment.natProfileInterp_sum_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.natProfileInterp_sum_mono
/-- info: 'Chvatal.PacketAlignment.assignedRankCount_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.assignedRankCount_mono
/-- info: 'Chvatal.PacketAlignment.assignedRankInterp_sum_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.assignedRankInterp_sum_mono
/-- info: 'Chvatal.PacketAlignment.wireSetPacketRankInterp_sum_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireSetPacketRankInterp_sum_mono
/-- info: 'Chvatal.PacketAlignment.profileIntervalOwnerMean_eq_interp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.profileIntervalOwnerMean_eq_interp
/-- info: 'Chvatal.PacketAlignment.profileIntervalSelectedMean_eq_interp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.profileIntervalSelectedMean_eq_interp
/-- info: 'Chvatal.PacketAlignment.wireFlowReceiverSelectedIdealMean_eq_intervalProfile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowReceiverSelectedIdealMean_eq_intervalProfile
/-- info: 'Chvatal.PacketAlignment.packetized_source_errors_sq_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetized_source_errors_sq_sum_le
/-- info: 'Chvatal.PacketAlignment.packetized_merge_owner_errors_sq_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetized_merge_owner_errors_sq_sum_le
/-- info: 'Chvatal.PacketAlignment.packetized_source_errors_sq_sum_le_of_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetized_source_errors_sq_sum_le_of_degree
/-- info: 'Chvatal.PacketAlignment.packetized_merge_owner_errors_sq_sum_le_of_degree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Chvatal.PacketAlignment.packetized_merge_owner_errors_sq_sum_le_of_degree
/-- info: 'Chvatal.PacketAlignment.sum_receiver_selected_error_sq_le_source_pieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.sum_receiver_selected_error_sq_le_source_pieces
/-- info: 'Chvatal.PacketAlignment.sortedSenderOutgoing_profile_error_exact_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.sortedSenderOutgoing_profile_error_exact_one
/-- info: 'Chvatal.PacketAlignment.wireFlowReceiverNeighborSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowReceiverNeighborSum_eq
/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_profile_error_sq_sum_le_source_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_profile_error_sq_sum_le_source_energy
/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_register_error_sq_sum_le_source_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_register_error_sq_sum_le_source_energy
/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_register_error_sq_sum_le_source_energy_multi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_register_error_sq_sum_le_source_energy_multi
/-- info: 'Chvatal.PacketAlignment.wireFlowLayer_reencoded_profile_energy_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.wireFlowLayer_reencoded_profile_energy_recurrence
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryOutputBlock_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryOutputBlock_range
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryOutputBlock_support_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryOutputBlock_support_eq
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryOutputBlocks_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryOutputBlocks_ordered
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryOutputBlock_lane_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryOutputBlock_lane_contract
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_lane_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_lane_contract
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_ordered
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_disjoint_of_block_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_disjoint_of_block_ne
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryDealtOutputBlock_range' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryDealtOutputBlock_range
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryDealtOutputBlock_disjoint_singleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryDealtOutputBlock_disjoint_singleton
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryOutputBlock_pairwise_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryOutputBlock_pairwise_disjoint
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_disjoint
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_perm_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_perm_output
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_nodup
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryMatching_preservesGroupedPhysicalState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryMatching_preservesGroupedPhysicalState
/-- info: 'Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_nextWideBoundaryEdge_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.fourLaneBoundaryGroupedOutput_nextWideBoundaryEdge_ordered
/-- info: 'Chvatal.PacketAlignment.eightLaneBoundaryMatching_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.eightLaneBoundaryMatching_ordered
/-- info: 'Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_ordered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_ordered
/-- info: 'Chvatal.PacketAlignment.eightLaneBoundaryOutputBlock_lane_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.eightLaneBoundaryOutputBlock_lane_contract
/- 16-lane matching induction guards -/
/-- info: 'Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_at' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_at
/-- info: 'Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_nextWideBoundaryEdge_ordered' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_nextWideBoundaryEdge_ordered
/- 16-lane matching induction guards -/
/-- info: 'Chvatal.PacketAlignment.eightLaneBoundaryDealtOutputBlock_disjoint_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.eightLaneBoundaryDealtOutputBlock_disjoint_singleton
/-- info: 'Chvatal.PacketAlignment.eightLaneBoundaryOutputBlock_pairwise_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.eightLaneBoundaryOutputBlock_pairwise_disjoint
/-- info: 'Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_disjoint' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_disjoint
/-- info: 'Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_nodup' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_nodup
/-- info: 'Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_perm_output' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_perm_output
/-- info: 'Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_support_eq' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.eightLaneBoundaryGroupedOutput_support_eq
/-- info: 'Chvatal.PacketAlignment.eightLaneBoundaryMatching_preservesGroupedPhysicalState' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.eightLaneBoundaryMatching_preservesGroupedPhysicalState
/- Generic receiver batching interface guards. -/
/-- info: 'Chvatal.PacketAlignment.genScatterMergeTreeBatch_exec_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.genScatterMergeTreeBatch_exec_inside
/-- info: 'Chvatal.PacketAlignment.finiteReceiverMacroBatch_of_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.finiteReceiverMacroBatch_of_list

/- FlowA7 concrete global receiver batching guards. -/
/-- info: 'Chvatal.PacketAlignment.flowA7_receiverMacroData_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiverMacroData_exists
/-- info: 'Chvatal.PacketAlignment.flowA7_globalReceiverMacroBatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_globalReceiverMacroBatch
/-- info: 'Chvatal.PacketAlignment.packetFamily64Block_outputEmbedding_eq_sourcePacket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64Block_outputEmbedding_eq_sourcePacket
/-- info: 'Chvatal.PacketAlignment.downSetEndpointPair_not_rankBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.downSetEndpointPair_not_rankBlock
/-- info: 'Chvatal.PacketAlignment.downSetEndpointPair_not_receiverRankBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.downSetEndpointPair_not_receiverRankBlock
/-- info: 'Chvatal.PacketAlignment.rankPacketCell_macroGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.rankPacketCell_macroGroup
/-- info: 'Chvatal.PacketAlignment.rankIn_blockOf_eq_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.rankIn_blockOf_eq_sub
/-- info: 'Chvatal.PacketAlignment.blockOf_blockOf_eq_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.blockOf_blockOf_eq_shift
/-- info: 'Chvatal.PacketAlignment.rankPacketCell_macroGroup_in_rankInterval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.rankPacketCell_macroGroup_in_rankInterval
/-- info: 'Chvatal.PacketAlignment.rankPacketCell_stream_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.rankPacketCell_stream_contract
/-- info: 'Chvatal.PacketAlignment.flowA7_shiftedUp_regularStreams_contract' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_shiftedUp_regularStreams_contract
/-- info: 'Chvatal.PacketAlignment.flowA7_shiftedDown_interiorStream_contract' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_shiftedDown_interiorStream_contract
/-- info: 'Chvatal.PacketAlignment.flowA7_alignedUp_regularStreams_contract' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_alignedUp_regularStreams_contract
/-- info: 'Chvatal.PacketAlignment.flowA7_alignedDown_interiorStream_contract' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_alignedDown_interiorStream_contract
/-- info: 'Chvatal.PacketAlignment.shiftedSelector_exceptionPool_budget' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.shiftedSelector_exceptionPool_budget
/-- info: 'Chvatal.PacketAlignment.shiftedSelector_exceptionPool_index_card' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.shiftedSelector_exceptionPool_index_card
/-- info: 'Chvatal.PacketAlignment.canonicalExceptionPool_family' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalExceptionPool_family
/-- info: 'Chvatal.PacketAlignment.canonicalPacketFamily_residue_contract' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalPacketFamily_residue_contract
/-- info: 'Chvatal.PacketAlignment.canonicalStreamResidues_exceptionPool' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.canonicalStreamResidues_exceptionPool
/-- info: 'Chvatal.PacketAlignment.flowA7_shiftedDown_endpoint_contract' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_shiftedDown_endpoint_contract
/-- info: 'Chvatal.PacketAlignment.flowA7_shiftedUp_endpoint_contract' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_shiftedUp_endpoint_contract
/-- info: 'Chvatal.PacketAlignment.flowA7_shiftedUp_port_partition' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_shiftedUp_port_partition
/-- info: 'Chvatal.PacketAlignment.flowA7_alignedUp_port_partition' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_alignedUp_port_partition
/-- info: 'Chvatal.PacketAlignment.flowA7_zeroDownUp_port_partition' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_zeroDownUp_port_partition
/-- info: 'Chvatal.PacketAlignment.flowA7_shiftedDown_port_partition' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_shiftedDown_port_partition
/-- info: 'Chvatal.PacketAlignment.flowA7_alignedDown_port_partition' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_alignedDown_port_partition
/-- info: 'Chvatal.PacketAlignment.flowA7_zeroDown_port_partition' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_zeroDown_port_partition
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_parentPort_streamPartition' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_parentPort_streamPartition
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_childPorts_streamPartition' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_childPorts_streamPartition
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_regularStreams_bundle' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_regularStreams_bundle
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_exceptionPool' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_exceptionPool
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_exceptionPool_batch' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_exceptionPool_batch
/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockEmbedding_rankInterval_support' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockEmbedding_rankInterval_support
/-- info: 'Chvatal.PacketAlignment.packetFamily64BlockList_rankIntervals' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.packetFamily64BlockList_rankIntervals
/-- info: 'Chvatal.PacketAlignment.CanonicalPacketFullBlockProvenance.block_rankIntervals' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.CanonicalPacketFullBlockProvenance.block_rankIntervals
/-- info: 'Chvatal.PacketAlignment.CanonicalStreamFullBlockData.block_rankIntervals' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.CanonicalStreamFullBlockData.block_rankIntervals
/-- info: 'Chvatal.PacketAlignment.CanonicalStreamFullBlockData.rankCellStream_complete' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.CanonicalStreamFullBlockData.rankCellStream_complete
/-- info: 'Chvatal.PacketAlignment.CanonicalStreamFullBlockData.groupBlock_rankInterval' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.CanonicalStreamFullBlockData.groupBlock_rankInterval
/-- info: 'Chvatal.PacketAlignment.CanonicalStreamFullBlockData.rankIntervals_of_rankCellStreams' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.CanonicalStreamFullBlockData.rankIntervals_of_rankCellStreams
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_regularFullBlocks_rankIntervals' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_regularFullBlocks_rankIntervals
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_regular_partial_groups_bound' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_regular_partial_groups_bound
/-- info: 'Chvatal.PacketAlignment.flowA7_receiver_regular_partial_groups_sum_le_258' depends on axioms: [propext,
  Classical.choice,
  Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Chvatal.PacketAlignment.flowA7_receiver_regular_partial_groups_sum_le_258
