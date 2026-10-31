import D2FlowRankBridge
import D2CandidateQuotaLower

namespace Chvatal.D2CandidateTwoFrontBridge

open Chvatal.D2Reserve

/-- At every active ordinary candidate sender, the tolerant deficit gate and
the quota floor bound overrun by 31 per 8192-capacity block. Since a physical
core tile has capacity 262144, this is 992 per physical tile, not 31. -/
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

/-- Under the stronger 1/512 deficit reserve, the same quota floor leaves at
most 32 units of overrun per actual 262144-wire physical core tile. Combined
with the local 448 transfer, this fits the 512-per-tile doubling budget. -/
theorem candidate_sender_strict_two_front_overrun_le_32_per_core_tile
    {d i t G low : Nat}
    (hd : 7 ≤ d)
    (ha : active d (tfD2 d) i t)
    (hrole : d2ScheduleRole d i t = .topRise ∨
      d2ScheduleRole d i t = .mid ∨ d2ScheduleRole d i t = .botDesc)
    (hdeficit : 512 * G ≤ d2FlowCandidateCapacity d i t)
    (heven :
      d2FlowCandidateQuota d t i (d2ScheduleRole d i t) % 2 = 0) :
    ∃ tiles,
      d2FlowCandidateCapacity d i t = 262144 * tiles ∧
      G - min G
        (low + d2FlowCandidateQuota d t i (d2ScheduleRole d i t) / 2) <=
        32 * tiles := by
  obtain ⟨tiles, htiles⟩ := d2FlowCandidateCapacity_eq_262144_mul hd ha
  have hquota := d2FlowCandidateQuota_lower_ordinary hd ha hrole
  have hhalf : d2FlowCandidateQuota d t i (d2ScheduleRole d i t) =
      2 * (d2FlowCandidateQuota d t i (d2ScheduleRole d i t) / 2) := by
    omega
  refine ⟨tiles, htiles, ?_⟩
  exact d2FlowTwoFront_prefix_excess_le_tiles
    G low (d2FlowCandidateQuota d t i (d2ScheduleRole d i t))
    (d2FlowCandidateCapacity d i t)
    (d2FlowCandidateQuota d t i (d2ScheduleRole d i t) / 2)
    tiles htiles hhalf hdeficit hquota

/-- The sharper screened deficit ratio `G/capacity <= 15/8192` exactly
matches half the candidate quota floor and leaves no ideal-prefix overrun. -/
theorem candidate_sender_two_front_overrun_zero_of_15over8192
    {d i t G low : Nat}
    (hd : 7 <= d)
    (ha : active d (tfD2 d) i t)
    (hrole : d2ScheduleRole d i t = .topRise \/
      d2ScheduleRole d i t = .mid \/ d2ScheduleRole d i t = .botDesc)
    (hdeficit : 8192 * G <= 15 * d2FlowCandidateCapacity d i t)
    (heven :
      d2FlowCandidateQuota d t i (d2ScheduleRole d i t) % 2 = 0) :
    G - min G
      (low + d2FlowCandidateQuota d t i (d2ScheduleRole d i t) / 2) = 0 := by
  have hquota := d2FlowCandidateQuota_lower_ordinary hd ha hrole
  have hhalf : d2FlowCandidateQuota d t i (d2ScheduleRole d i t) =
      2 * (d2FlowCandidateQuota d t i (d2ScheduleRole d i t) / 2) := by
    omega
  exact d2FlowTwoFront_prefix_excess_zero_of_15over8192
    G low (d2FlowCandidateQuota d t i (d2ScheduleRole d i t))
    (d2FlowCandidateCapacity d i t)
    (d2FlowCandidateQuota d t i (d2ScheduleRole d i t) / 2)
    hhalf hdeficit hquota

end Chvatal.D2CandidateTwoFrontBridge
