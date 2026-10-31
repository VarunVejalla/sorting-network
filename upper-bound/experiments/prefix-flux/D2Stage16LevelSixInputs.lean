import D2Stage15LevelSevenRootFull
import D2Stage16LevelSixRootCap
import D2Stage16LevelSixBalance
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 5000000

private theorem d2FlowCandidateActive_stage16_tail_false
    {d i : Nat} (hd : 14 <= d) (hi : 7 <= i) :
    d2FlowCandidateActive d 16 i = false := by
  classical
  have hiff := d2FlowCandidateActive_stage16_iff (d := d) (i := i) hd
  cases h : d2FlowCandidateActive d 16 i with
  | false => rfl
  | true =>
      have hlevels := hiff.mp h
      by_cases h14 : d = 14
      · simp [h14] at hlevels
        omega
      · simp [h14] at hlevels
        omega

/-- The actual Stage-15 output at every level-six node satisfies the full
recursive input contract for Stage 16. Its level-seven children are full at
the root, while Stage 16 is inactive below level six. -/
theorem d2FlowCandidateRun_stage16_levelSix_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r : Fin 8) :
    let d := childDepth + 7
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 16) j) k) m) l) q) r
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
      (d2FlowCandidateQuota d 16)
      (fun x => d2FlowCandidateCapacity d x 16) 6 tree := by
  obtain ⟨height, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : childDepth ≠ 0)
  let childDepth := height + 1
  let d := childDepth + 7
  let run16 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 16
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild (d2FlowTreeChild run16 j) k) m) l) q) r
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hinactive : forall k, 7 <= k -> d2FlowCandidateActive d 16 k = false := by
    intro k hk
    exact d2FlowCandidateActive_stage16_tail_false hd14 hk
  have hchildren : forall s : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
        (d2FlowCandidateQuota d 16)
        (fun x => d2FlowCandidateCapacity d x 16) 7
        (d2FlowTreeChild tree s) := by
    intro s
    exact d2FlowStageInvInputs_all_inactive
      (scale := 8192) (active := d2FlowCandidateActive d 16)
      (role := d2FlowCandidateRole d 16) (quota := d2FlowCandidateQuota d 16)
      (cap := fun x => d2FlowCandidateCapacity d x 16)
      (d2FlowTreeChild tree s) (by
        intro k hk
        exact hinactive k (by omega))
  have hbalance := d2FlowCandidateRun_stage16_levelSix_balanced
    childDepth hd j k m l q r
  have hrootcap := d2FlowCandidateRun_stage16_levelSix_root_cap
    childDepth hd j k m l q r
  have hquota := d2FlowCandidateStage16_levelSix_quota_gates hd14
  have hrootfull : forall s : Fin 8,
      d2FlowTreeRootDeficit (d2FlowTreeChild tree s) =
        8192 * 8 ^ childDepth := by
    intro s
    have h := d2FlowCandidateRun_stage15_levelSeven_root_full
      (height := height) (by omega) j k m l q r s
    simpa [d, run16, tree, childDepth] using h
  have htotal : d2FlowTotal (fun s : Fin 8 =>
      d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) =
        8 * (8192 * 8 ^ childDepth) := by
    unfold d2FlowTotal
    calc
      Finset.univ.sum (fun s : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) =
        Finset.univ.sum (fun _ : Fin 8 => 8192 * 8 ^ childDepth) := by
          apply Finset.sum_congr rfl
          intro s hs
          exact hrootfull s
      _ = 8 * (8192 * 8 ^ childDepth) := by simp
  have hcapMass : d2FlowCandidateCapacity d 6 16 =
      8 * (8192 * 8 ^ childDepth) := by
    dsimp [d, d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    rw [show 13 + 3 * (childDepth + 7) + 18 - 36 =
      3 * childDepth + 16 by omega]
    have hpow : 8 ^ childDepth = 2 ^ (3 * childDepth) := by
      rw [show 8 = 2 ^ 3 by norm_num, ← pow_mul]
    rw [hpow, show 8192 = 2 ^ 13 by norm_num]
    rw [show 3 * childDepth + 16 = (3 * childDepth + 13) + 3 by omega]
    rw [pow_add]
    ring
  have halloc : d2FlowCandidateQuota d 16 6 .botDesc <=
      d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) -
        d2FlowTreeRootDeficit tree := by
    have hq := hquota.1
    have hg := hrootcap
    rw [hcapMass] at hq hg
    have hroot : 64 * d2FlowTreeRootDeficit tree <=
        8192 * 8 ^ childDepth := by nlinarith
    have hqsmall : 32 * d2FlowCandidateQuota d 16 6 .botDesc <=
        8192 * 8 ^ childDepth := by nlinarith
    have hsumineq : d2FlowCandidateQuota d 16 6 .botDesc +
        d2FlowTreeRootDeficit tree <= 8 * (8192 * 8 ^ childDepth) := by
      nlinarith
    rw [htotal]
    omega
  have hleft : d2FlowCandidateCapacity d 6 16 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    rw [hrootfull, hcapMass]
    omega
  have hright : d2FlowCandidateCapacity d 6 16 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    rw [hrootfull, hcapMass]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 16 6 .botDesc <=
      d2FlowCandidateCapacity d 6 16 := hquota.1
  have heven : d2FlowCandidateQuota d 16 6 .botDesc % 2 = 0 := hquota.2
  have hcontract := d2FlowStageInvInputs_botDesc_of_contract
    (scale := 8192) (i := 6) (h := childDepth) tree
    (by simpa [d] using (show d2FlowCandidateActive d 16 6 = true from
      (d2FlowCandidateActive_stage16_iff hd14).2 (by
        by_cases h14 : d = 14 <;> simp [h14])))
    (d2FlowCandidateRole_stage16_bottom hd14)
    hchildren hbalance hrootcap hquotaCap halloc heven hleft hright
  simpa [d, run16, tree] using hcontract

end Chvatal.D2Reserve
