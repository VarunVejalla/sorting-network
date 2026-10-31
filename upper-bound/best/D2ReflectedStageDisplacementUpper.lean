import D2ReflectedStageBand

set_option maxRecDepth 4096

namespace Chvatal.D2ReflectedStageDisplacement

theorem rankMap_displacement_upper_832 (q : Wire) :
    (rankMap q).val <= q.val + 832 := by
  by_contra hbad
  have hlt : q.val + 832 < (rankMap q).val := by omega
  let k := q.val + 832 + 1
  have hk : k <= N := by
    have hr := (rankMap q).isLt
    dsimp [k]
    omega
  obtain ⟨a, b, hwidth, hab, haN, hbN, haK, hkB, hfalse, htrue⟩ :=
    threshold_band_brackets k hk
  have hgap : 64 * b - 64 * a <= 832 := by omega
  have hboundA : k <= 64 * a + 832 := by omega
  have hqA : q.val < 64 * a := by dsimp [k] at hboundA; omega
  have hout := hfalse q hqA
  change stageNet.exec (highThreshold k) q = false at hout
  have hp := congrFun (threshold_output_eq_rankMap k) q
  have hp' : stageNet.exec (highThreshold k) q = highThreshold k (rankMap q) := by
    simpa only [Function.comp_apply] using hp
  rw [hp'] at hout
  have hkR : k <= (rankMap q).val := by dsimp [k]; omega
  simp [highThreshold, hkR] at hout


end Chvatal.D2ReflectedStageDisplacement
