import D2FlowRankBridge
import D2CandidateQuotaLower

namespace Chvatal.D2CandidateTwoFrontBridge

open Chvatal.D2Reserve

/-- At every active ordinary candidate sender, the tolerant deficit gate and
the proved quota floor bound the one-sided prefix overrun by 31 units per
8192-capacity block. The remaining geometric question is whether these blocks
are exactly the physical fixed-core calls charged by the 448 transfer. -/
theorem candidate_sender_two_front_overrun_le_31_per_capacity_block
    {d i t G low : Nat}
    (hd : 7 ≤ d)
    (ha : active d (tfD2 d) i t)
    (hrole : d2ScheduleRole d i t = .topRise \/
      d2ScheduleRole d i t = .mid \/
      d2ScheduleRole d i t = .botDesc)
    (hdeficit : 4096 * G ≤ 23 * d2FlowCandidateCapacity d i t)
    (heven :
      d2FlowCandidateQuota d t i (d2ScheduleRole d i t) % 2 = 0) :
    ∃ blocks,
      d2FlowCandidateCapacity d i t = 8192 * blocks /\
      G - min G
        (low + d2FlowCandidateQuota d t i (d2ScheduleRole d i t) / 2) <=
        31 * blocks := by
  obtain ⟨blocks, hblocks⟩ :=
    d2FlowCandidateCapacity_eq_8192_mul hd ha
  have hquota := d2FlowCandidateQuota_lower_ordinary hd ha hrole
  have hhalf : d2FlowCandidateQuota d t i (d2ScheduleRole d i t) =
      2 * (d2FlowCandidateQuota d t i (d2ScheduleRole d i t) / 2) := by
    omega
  refine ⟨blocks, hblocks, ?_⟩
  exact d2FlowTwoFront_prefix_excess_le_tolerant_tiles
    G low (d2FlowCandidateQuota d t i (d2ScheduleRole d i t))
    (d2FlowCandidateCapacity d i t)
    (d2FlowCandidateQuota d t i (d2ScheduleRole d i t) / 2)
    blocks hblocks hhalf hdeficit hquota

end Chvatal.D2CandidateTwoFrontBridge
