/-
  Compile-time checks that the Paterson development introduces no proof holes
  or additional axioms. This audit covers the halver existence results and
  the separator theorem for arities divisible by 32.
-/

import AKS.Halver.PatersonExistence
import AKS.Halver.PatersonEntropy
import AKS.Halver.PatersonCollapsedWitnesses
import AKS.Halver.PatersonTail
import AKS.Halver.PatersonSimultaneous
import AKS.Halver.PatersonJointTail
import AKS.Separator.PatersonInjective
import AKS.Separator.PatersonOddFinal
import AKS.Separator.PatersonCertificate
import AKS.Bags.PatersonNumerics

/-- info: 'Paterson.card_restricted_permutations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.card_restricted_permutations

/-- info: 'Paterson.restricted_matching_sequence_density_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.restricted_matching_sequence_density_le

/-- info: 'Paterson.isHalver_of_noSmallTraps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.isHalver_of_noSmallTraps

/-- info: 'Paterson.exists_halver_of_size_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.exists_halver_of_size_bound

/-- info: 'Paterson.log_choose_le_entropy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.log_choose_le_entropy

/-- info: 'Paterson.failure_term_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.failure_term_le

/-- info: 'Paterson.depthRatio_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.depthRatio_le

/-- info: 'Paterson.witness_failure_term_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.witness_failure_term_le

/-- info: 'Paterson.exists_halver_of_collapsed_tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.exists_halver_of_collapsed_tail_bound

/-- info: 'Paterson.collapsed_tail_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.collapsed_tail_lt_one

/-- info: 'Paterson.exists_paterson_halver_all_arities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.exists_paterson_halver_all_arities

/-- info: 'Paterson.exists_simultaneous_halver_of_trap_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.exists_simultaneous_halver_of_trap_covers

/-- info: 'Paterson.exists_paterson_first_level_halver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.exists_paterson_first_level_halver

/-- info: 'Paterson.exists_paterson_first_level_all_arities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.exists_paterson_first_level_all_arities

/-- info: 'Paterson.restricted_injective_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.restricted_injective_initial

/-- info: 'Paterson.restricted_injective_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.restricted_injective_final

/-- info: 'Paterson.exists_paterson_first_level_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.exists_paterson_first_level_supported

/-- info: 'Paterson.separatorNetwork_depth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.separatorNetwork_depth_le

/-- info: 'Paterson.supported_halving_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.supported_halving_step

/-- info: 'Paterson.separatorNetwork_supported_of_dvd32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.separatorNetwork_supported_of_dvd32

/-- info: 'Paterson.separatorNetwork_certificate_of_dvd32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.separatorNetwork_certificate_of_dvd32

/-- info: 'Paterson.oddInitialHalver_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.oddInitialHalver_injective

/-- info: 'Paterson.flip_exec_reverseDual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.flip_exec_reverseDual

/-- info: 'Paterson.flip_isEpsilonAlphaHalver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.flip_isEpsilonAlphaHalver

/-- info: 'Paterson.oddFinalHalver_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.oddFinalHalver_injective

/-- info: 'Paterson.separatorDepthBudget_le_989' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Paterson.separatorDepthBudget_le_989

/-- info: 'patersonAdjustedStageRatio_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms patersonAdjustedStageRatio_lt
