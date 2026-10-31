import D2Stage14Arithmetic

namespace Chvatal.D2Reserve

theorem d2FlowStage14QuotaArithmeticProbe (childDepth : Nat) (hd : Nat.le 7 childDepth) :
    let d := childDepth + 7
    d2FlowCandidateQuota d 14 6 D2Role.botDesc =
        15 * 2 ^ (3 * childDepth + 8) ∧
    256 * d2FlowCandidateQuota d 14 6 D2Role.botDesc <=
        d2FlowCandidateCapacity d 6 14 ∧
    d2FlowCandidateQuota d 14 6 D2Role.botDesc % 2 = 0 := by
  let d := childDepth + 7
  have hdD : Nat.le 14 d := by omega
  have hcapacityNative : d2FlowCandidateCapacity d 6 14 =
      128 * (8192 * 8 ^ childDepth) := by
    simpa [d] using d2FlowCandidateStage14_levelSix_capacity_eq_nativeChild d hdD
  have hquota : d2FlowCandidateQuota d 14 6 .botDesc =
      15 * 2 ^ (3 * childDepth + 8) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent, d]
    congr 2
    omega
  have hnative : 8192 * 8 ^ childDepth =
      32 * 2 ^ (3 * childDepth + 8) := by
    calc
      8192 * 8 ^ childDepth = 2 ^ 13 * (2 ^ 3) ^ childDepth := by norm_num
      _ = 2 ^ 13 * 2 ^ (3 * childDepth) := by rw [pow_mul]
      _ = 2 ^ (13 + 3 * childDepth) := by rw [← pow_add]
      _ = 2 ^ (5 + (3 * childDepth + 8)) := by congr 1 <;> omega
      _ = 2 ^ 5 * 2 ^ (3 * childDepth + 8) := by rw [pow_add]
      _ = 32 * 2 ^ (3 * childDepth + 8) := by norm_num
  have hquotaTwice : 2 * d2FlowCandidateQuota d 14 6 .botDesc <=
      8192 * 8 ^ childDepth := by
    rw [hquota, hnative]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 14 6 .botDesc <=
      d2FlowCandidateCapacity d 6 14 := by
    rw [hcapacityNative]
    omega
  have hquotaEven : d2FlowCandidateQuota d 14 6 .botDesc % 2 = 0 := by
    have hexp : 3 * childDepth + 8 = (3 * childDepth + 7) + 1 := by omega
    rw [hquota, hexp, pow_succ]
    omega
  simpa [d] using And.intro hquota (And.intro hquotaCap hquotaEven)

end Chvatal.D2Reserve
