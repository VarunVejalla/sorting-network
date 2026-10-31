import D2Stage18Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

/-- The moving Stage-18 level-two middle quota is one sixteenth of the
Stage-16 level-two reserve inherited from the Stage-17 top-rise children.
The same arithmetic leaves enough capacity for the root allowance and both
endpoint reserves. -/
theorem d2FlowCandidateStage18_levelTwo_quota_arithmetic
    {d : Nat} (hd : 16 <= d) :
    16 * d2FlowCandidateQuota d 18 2 .mid =
      d2FlowCandidateQuota d 16 2 .mid /\
    256 * d2FlowCandidateQuota d 18 2 .mid <=
      d2FlowCandidateCapacity d 2 18 /\
    d2FlowCandidateCapacity d 2 18 <=
      128 * d2FlowCandidateQuota d 16 2 .mid /\
    d2FlowCandidateQuota d 18 2 .mid % 2 = 0 := by
  have he18 : d2FlowCandidateCapacityExponent d 2 18 = 3 * d - 21 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have he16 : d2FlowCandidateCapacityExponent d 2 16 = 3 * d - 17 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have hq18 : d2FlowCandidateQuota d 18 2 .mid =
      15 * 2 ^ (3 * d - 33) := by
    change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 2 18 - 12) = _
    rw [he18]
    congr 1 <;> omega
  have hq16 : d2FlowCandidateQuota d 16 2 .mid =
      15 * 2 ^ (3 * d - 29) := by
    change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 2 16 - 12) = _
    rw [he16]
    congr 1 <;> omega
  have hcap : d2FlowCandidateCapacity d 2 18 =
      2 ^ (3 * d - 21) := by
    change 2 ^ d2FlowCandidateCapacityExponent d 2 18 = _
    rw [he18]
  have hratio : 16 * d2FlowCandidateQuota d 18 2 .mid =
      d2FlowCandidateQuota d 16 2 .mid := by
    rw [hq18, hq16]
    have hexp : 4 + (3 * d - 33) = 3 * d - 29 := by omega
    rw [show (16 : Nat) = 2 ^ 4 by norm_num]
    rw [show 2 ^ 4 * (15 * 2 ^ (3 * d - 33)) =
      15 * (2 ^ 4 * 2 ^ (3 * d - 33)) by ring]
    rw [← pow_add, hexp]
  have hquotaCap : 256 * d2FlowCandidateQuota d 18 2 .mid <=
      d2FlowCandidateCapacity d 2 18 := by
    rw [hq18, hcap]
    have hexp : 8 + (3 * d - 33) = 3 * d - 25 := by omega
    have hcapExp : 3 * d - 21 = 4 + (3 * d - 25) := by omega
    rw [show 256 = 2 ^ 8 by norm_num]
    rw [show 2 ^ 8 * (15 * 2 ^ (3 * d - 33)) =
      15 * (2 ^ 8 * 2 ^ (3 * d - 33)) by ring]
    rw [← pow_add, hexp, hcapExp, pow_add]
    omega
  have hleft : d2FlowCandidateCapacity d 2 18 <=
      128 * d2FlowCandidateQuota d 16 2 .mid := by
    rw [hq16, hcap]
    have hexp : 7 + (3 * d - 29) = 3 * d - 22 := by omega
    have hcapExp : 3 * d - 21 = 1 + (3 * d - 22) := by omega
    rw [show 128 = 2 ^ 7 by norm_num]
    rw [show 2 ^ 7 * (15 * 2 ^ (3 * d - 29)) =
      15 * (2 ^ 7 * 2 ^ (3 * d - 29)) by ring]
    rw [← pow_add, hexp, hcapExp, pow_add]
    omega
  have heven : d2FlowCandidateQuota d 18 2 .mid % 2 = 0 := by
    rw [hq18]
    have hexp : 3 * d - 33 = (3 * d - 34) + 1 := by omega
    rw [hexp, pow_succ]
    omega
  exact ⟨hratio, hquotaCap, hleft, heven⟩

/-- Stage-17 level-three child reserves dominate the Stage-18 level-two
capacity by the exact factor 15/128. -/
theorem d2FlowCandidateStage18_levelTwo_child_reserve_relation
    {d : Nat} (hd : 16 <= d) :
    128 * d2FlowCandidateQuota d 17 3 .mid =
      15 * d2FlowCandidateCapacity d 2 18 := by
  have he17 : d2FlowCandidateCapacityExponent d 3 17 = 3 * d - 16 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have he18 : d2FlowCandidateCapacityExponent d 2 18 = 3 * d - 21 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have hq17 : d2FlowCandidateQuota d 17 3 .mid =
      15 * 2 ^ (3 * d - 28) := by
    change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 3 17 - 12) = _
    rw [he17]
    congr 1 <;> omega
  have hcap18 : d2FlowCandidateCapacity d 2 18 =
      2 ^ (3 * d - 21) := by
    change 2 ^ d2FlowCandidateCapacityExponent d 2 18 = _
    rw [he18]
  rw [hq17, hcap18]
  have hexp : 7 + (3 * d - 28) = 3 * d - 21 := by omega
  rw [show (128 : Nat) = 2 ^ 7 by norm_num]
  rw [show 2 ^ 7 * (15 * 2 ^ (3 * d - 28)) =
    15 * (2 ^ 7 * 2 ^ (3 * d - 28)) by ring]
  rw [← pow_add, hexp]

end Chvatal.D2Reserve
