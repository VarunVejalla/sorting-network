import D2ScheduleReserve
open Chvatal.D2Reserve

theorem d2_topRise_child_quota_eq_parent_capacity
    {d i t : Nat} (ht : 4 <= t) (hd : 7 <= d)
    (ha : active d (tfD2 d) i t) :
    8 * d2FlowCandidateQuota d (t - 1) (i + 1) .topRise =
      d2FlowCandidateCapacity d i t := by
  let e := d2FlowCandidateCapacityExponent d i t
  have hne : Not (t = 1) := by omega
  have hparts : 2 <= t := by
    unfold active at ha
    simp only [if_neg hne] at ha
    exact ha.1
  have hbound : 2 * t + 11 <= 3 * d + 3 * i := by
    unfold active at ha
    simp only [if_neg hne] at ha
    omega
  have he20 : 20 <= e := by
    dsimp [e]
    exact d2FlowCandidateCapacityExponent_ge_twenty hd ha
  have hden : 2 * t + 4 <= 13 + 3 * d + 3 * i := by omega
  have hchildExp :
      d2FlowCandidateCapacityExponent d (i + 1) (t - 1) = e + 5 := by
    dsimp [d2FlowCandidateCapacityExponent, e]
    omega
  have hchildSub :
      d2FlowCandidateCapacityExponent d (i + 1) (t - 1) - 8 = e - 3 := by
    omega
  have hpow : 8 * 2 ^ (e - 3) = 2 ^ e := by
    have heq : e = (e - 3) + 3 := by omega
    rw [heq, pow_add]
    norm_num
    ring
  change 8 * 2 ^ (d2FlowCandidateCapacityExponent d (i + 1) (t - 1) - 8) =
    2 ^ d2FlowCandidateCapacityExponent d i t
  rw [hchildSub]
  exact hpow
