import D2Stage14Arithmetic

namespace Chvatal.D2Reserve

set_option maxHeartbeats 10000000

theorem d2FlowStage14QuotaProbe (childDepth : Nat) :
    d2FlowCandidateQuota (childDepth + 7) 14 6 D2Role.botDesc =
      15 * 2 ^ (3 * childDepth + 8) := by
  simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
  congr 2
  omega

end Chvatal.D2Reserve
