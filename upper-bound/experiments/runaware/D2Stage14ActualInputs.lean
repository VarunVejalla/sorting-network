import D2Stage14Contract

namespace Chvatal.D2Reserve

set_option maxHeartbeats 10000000

/-- The complete recursive input contract at every actual Stage-14
level-six node. -/
theorem d2FlowCandidateStage14_actual_levelSix_inputs
    (childDepth : Nat) (hd : 7 ≤ childDepth) :
    ∀ j k m l q r,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive (childDepth + 7) 14)
        (d2FlowCandidateRole (childDepth + 7) 14)
        (d2FlowCandidateQuota (childDepth + 7) 14)
        (fun x => d2FlowCandidateCapacity (childDepth + 7) x 14) 6
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowCandidateRun (childDepth + 7)
                      (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j) k) m) l) q) r) := by
  intro j k m l q r
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run := d2FlowCandidateRun d initial 14
  let path : D2FlowPath 6 := .cons j (.cons k (.cons m (.cons l (.cons q (.cons r .nil)))))
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run j) k) m) l) q) r
  have htf : 14 ≤ tfD2 d := by unfold tfD2; omega
  have hstar14 : alphaStar d 14 = 0 := by
    unfold alphaStar
    have h : 39 ≤ 3 * d := by omega
    simp [h]
  have hstar15 : alphaStar d 15 = 0 := by
    unfold alphaStar
    have h : 41 ≤ 3 * d := by omega
    simp [h]
  have ha14 : alpha d 14 = 0 := by
    simp [alpha, hstar14, ceilParity]
  have ha15 : alpha d 15 = 1 := by
    simp [alpha, hstar15, ceilParity]
  have ho14 : omega 14 = 6 := by norm_num [omega, ceilParity]
  have ho15 : omega 15 = 7 := by norm_num [omega, ceilParity]
  have hactive6 : d2FlowCandidateActive d 14 6 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hrole6 : d2FlowCandidateRole d 14 6 = .botDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha14, ho14, ho15]
  have hrecursive : ∀ s : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 14) (d2FlowCandidateRole d 14)
        (d2FlowCandidateQuota d 14) (fun x => d2FlowCandidateCapacity d x 14)
        7 (d2FlowTreeChild tree s) := by
    intro s
    exact d2FlowCandidateStage14_inactive_inputs (d := d) (by omega) (by omega)
      (d2FlowTreeChild tree s)
  have hbalance := d2FlowCandidateStage14_actual_levelSix_balanced
    childDepth hd j k m l q r
  change (d2FlowTreeRootData tree).2.1 + (d2FlowTreeRootData tree).2.2 =
      d2FlowTreeRootDeficit tree at hbalance
  have hdeficit := d2FlowCandidateStage14_actual_levelSix_deficit_bound
    childDepth hd j k m l q r
  change 512 * d2FlowTreeRootDeficit tree ≤
      d2FlowCandidateCapacity d 6 14 at hdeficit
  have hreserve := d2FlowCandidateStage14_actual_levelSix_endpoint_reserves
    childDepth hd path
  have hreserve' :
      d2FlowCandidateCapacity d 6 14 ≤
          128 * d2FlowTreeRootDeficit (d2FlowTreeChild tree ⟨0, by omega⟩) ∧
      d2FlowCandidateCapacity d 6 14 ≤
          128 * d2FlowTreeRootDeficit (d2FlowTreeChild tree ⟨7, by omega⟩) := by
    change d2FlowCandidateCapacity (childDepth + 7) 6 14 ≤
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeAtPath 6
              (d2FlowCandidateRun (childDepth + 7)
                (d2FlowTreeInitial 8192 (childDepth + 7)) 14)
              (.cons j (.cons k (.cons m (.cons l (.cons q (.cons r .nil)))))))
            ⟨0, by omega⟩) ∧
      d2FlowCandidateCapacity (childDepth + 7) 6 14 ≤
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeAtPath 6
              (d2FlowCandidateRun (childDepth + 7)
                (d2FlowTreeInitial 8192 (childDepth + 7)) 14)
              (.cons j (.cons k (.cons m (.cons l (.cons q (.cons r .nil)))))))
            ⟨7, by omega⟩) at hreserve
    exact hreserve
  have hcapacityNative : d2FlowCandidateCapacity d 6 14 =
      128 * (8192 * 8 ^ childDepth) := by
    simpa [d] using d2FlowCandidateStage14_levelSix_capacity_eq_nativeChild d (by omega)
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
  have hquotaLe : d2FlowCandidateQuota d 14 6 .botDesc ≤
      8192 * 8 ^ childDepth := by
    rw [hquota, hnative]
    omega
  have hquotaTwice : 2 * d2FlowCandidateQuota d 14 6 .botDesc ≤
      8192 * 8 ^ childDepth := by
    rw [hquota, hnative]
    omega
  have hquotaCap : 256 * d2FlowCandidateQuota d 14 6 .botDesc ≤
      d2FlowCandidateCapacity d 6 14 := by
    rw [hcapacityNative]
    nlinarith [hquotaTwice]
  have hquotaEven : d2FlowCandidateQuota d 14 6 .botDesc % 2 = 0 := by
    rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * childDepth + 8 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  have htreePath : tree = d2FlowTreeAtPath 6
      (d2FlowCandidateRun d initial 14) path := by
    rfl
  have htotal : d2FlowTotal
      (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) =
        8 * (8192 * 8 ^ childDepth) := by
    have hconst : (fun s : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) =
        fun _ => 8192 * 8 ^ childDepth := by
      funext s
      rw [htreePath,
        d2FlowCandidateLevelSix_children_preserved childDepth hd path s,
        d2FlowTreeFull_root_deficit]
    simp [d2FlowTotal, hconst]
  have hGle : d2FlowTreeRootDeficit tree ≤ 8192 * 8 ^ childDepth := by
    rw [← hcapacityNative] at hdeficit
    omega
  have halloc : d2FlowCandidateQuota d 14 6 .botDesc ≤
      d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) -
        d2FlowTreeRootDeficit tree := by
    rw [htotal]
    omega
  have hquotaCapRole : 256 * d2FlowCandidateQuota d 14 6
      (d2FlowCandidateRole d 14 6) ≤ d2FlowCandidateCapacity d 6 14 := by
    simpa [hrole6] using hquotaCap
  have hquotaEvenRole : d2FlowCandidateQuota d 14 6
      (d2FlowCandidateRole d 14 6) % 2 = 0 := by
    simpa [hrole6] using hquotaEven
  exact d2FlowStageInvInputs_botDesc_of_contract 8192 6 tree hactive6 hrole6
    hrecursive hbalance hdeficit hquotaCapRole halloc hquotaEvenRole
    hreserve'.1 hreserve'.2

end Chvatal.D2Reserve
