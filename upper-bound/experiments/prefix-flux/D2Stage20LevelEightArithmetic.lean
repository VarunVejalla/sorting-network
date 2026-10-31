import D2Stage20Frontier

namespace Chvatal.D2Reserve

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The level-eight Stage-20 capacity is exactly 128 times the native mass of
one level-nine child. Its bot-descending quota is even and fits together with
any root satisfying the regular-parent cap inside the eight-child native
mass. -/
theorem d2FlowCandidateStage20_levelEight_arithmetic
    (childDepth : Nat) (hd : 6 ≤ childDepth) :
    let d := childDepth + 10
    let native := 8192 * 8 ^ (childDepth + 1)
    let cap := d2FlowCandidateCapacity d 8 20
    let quota := d2FlowCandidateQuota d 20 8 .botDesc
    cap = 128 * native ∧
    256 * quota ≤ cap ∧
    quota % 2 = 0 ∧
    (∀ G, 512 * G ≤ cap → quota + G ≤ native) := by
  let d := childDepth + 10
  let native := 8192 * 8 ^ (childDepth + 1)
  let cap := d2FlowCandidateCapacity d 8 20
  let quota := d2FlowCandidateQuota d 20 8 .botDesc
  have hd16 : 16 ≤ d := by dsimp [d]; omega
  have hcapExp : d2FlowCandidateCapacityExponent d 8 20 = 3 * d - 7 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have hquotaExp : d2FlowCandidateCapacityExponent d 8 20 - 12 =
      3 * d - 19 := by rw [hcapExp]; omega
  have hnative : native = 2 ^ (3 * d - 14) := by
    dsimp [native]
    rw [show (8192 : Nat) = 2 ^ 13 by norm_num,
      show (8 : Nat) = 2 ^ 3 by norm_num]
    rw [← Nat.pow_mul, ← Nat.pow_add]
    congr 1 <;> dsimp [d] <;> omega
  have hcap : cap = 2 ^ (3 * d - 7) := by
    dsimp [cap, d2FlowCandidateCapacity]
    rw [hcapExp]
  have hquota : quota = 15 * 2 ^ (3 * d - 19) := by
    dsimp [quota, d2FlowCandidateQuota]
    rw [hquotaExp]
  have hcapNative : cap = 128 * native := by
    rw [hcap, hnative]
    have he : 3 * d - 7 = 7 + (3 * d - 14) := by omega
    rw [he, pow_add]
    norm_num
  have hquotaCap : 256 * quota ≤ cap := by
    rw [hquota, hcap]
    have he : 3 * d - 7 = 12 + (3 * d - 19) := by omega
    rw [he, pow_add]
    norm_num
    nlinarith [Nat.zero_le (2 ^ (3 * d - 19))]
  have heven : quota % 2 = 0 := by
    rw [hquota]
    have he : 3 * d - 19 = (3 * d - 20) + 1 := by omega
    rw [he, pow_succ]
    omega
  have hbudget : ∀ G, 512 * G ≤ cap → quota + G ≤ native := by
    intro G hG
    rw [hcapNative] at hG
    rw [hquota]
    nlinarith [Nat.zero_le native, Nat.zero_le (2 ^ (3 * d - 19))]
  dsimp [d, native, cap, quota]
  exact ⟨hcapNative, hquotaCap, heven, hbudget⟩

end Chvatal.D2Reserve
