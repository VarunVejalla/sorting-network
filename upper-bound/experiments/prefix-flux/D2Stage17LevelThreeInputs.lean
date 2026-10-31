import D2Stage16LevelTwoInputs
import D2Stage16LevelFourInputs
import D2Stage16LevelSixInputs
import D2Stage15PreservesInv
import D2Stage17LevelFourInputs
import D2Stage17Frontier
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- Every actual Stage-17 level-three middle sender satisfies its complete
recursive input contract. Its Stage-16 level-two parent provides the root
cap and balance; Stage-16 level-four cuts provide child-root reserves. -/
theorem d2FlowCandidateRun_stage17_levelThree_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m : Fin 8) :
    let d := childDepth + 7
    let run17 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 17
    let tree := d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild run17 j) k) m
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
      (d2FlowCandidateQuota d 17)
      (fun x => d2FlowCandidateCapacity d x 17) 3 tree := by
  classical
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run16 := d2FlowCandidateRun d initial 16
  let run17 := d2FlowCandidateRun d initial 17
  let parent := d2FlowTreeChild (d2FlowTreeChild run16 j) k
  let source := d2FlowTreeChild parent m
  let tree := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild run17 j) k) m
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hactive17_3 : d2FlowCandidateActive d 17 3 = true := by
    apply (d2FlowCandidateActive_stage17_iff hd14).2
    exact Or.inr (Or.inl rfl)
  have hrole17_3 : d2FlowCandidateRole d 17 3 = .mid :=
    d2FlowCandidateRole_stage17_mid3 hd14
  have hactive16_2 : d2FlowCandidateActive d 16 2 = true := by
    apply (d2FlowCandidateActive_stage16_iff hd14).2
    by_cases h14 : d = 14 <;> simp [h14]
  have hrole16_2 : d2FlowCandidateRole d 16 2 =
      if d = 14 then .topRise else .mid := by
    by_cases h14 : d = 14
    · have h := d2FlowCandidateRole_stage16_top (d := d) hd14
      rw [h14] at h
      simpa [h14] using h
    · have h := d2FlowCandidateRole_stage16_internal_mid
        (d := d) (i := 2) (by omega) (Or.inl rfl)
      simpa [h14] using h
  have hregular16_2 : d2FlowCandidateRole d 16 2 = .topRise \/
      d2FlowCandidateRole d 16 2 = .mid \/
      d2FlowCandidateRole d 16 2 = .botDesc := by
    rw [hrole16_2]
    by_cases h14 : d = 14 <;> simp [h14]
  have hinvRun16 : d2FlowTreeInv 8192 run16 := by
    simpa [d, initial, run16] using
      d2FlowCandidateStage15_preserves_inv childDepth hd
  have hparentInv : d2FlowTreeInv 8192 parent := by
    exact d2FlowTreeInv_grandchild (h := childDepth + 5)
      run16 hinvRun16 j k
  have hparentInputs := d2FlowCandidateRun_stage16_levelTwo_inputs
    childDepth hd j k
  have hparentInputs' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
      (d2FlowCandidateQuota d 16)
      (fun x => d2FlowCandidateCapacity d x 16) 2 parent := by
    simpa [d, initial, run16, parent] using hparentInputs
  have hrun17 : run17 = d2FlowCandidateStage d 16 run16 := by
    change d2FlowCandidateRun d initial 17 =
      d2FlowCandidateStage d 16 (d2FlowCandidateRun d initial 16)
    rw [d2FlowCandidateRun.eq_def]
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 16)
        (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
        (childDepth + 5) 2 parent) m := by
    change d2FlowTreeChild
        (d2FlowTreeChild (d2FlowTreeChild run17 j) k) m = _
    rw [hrun17]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path3_projection
      (active := d2FlowCandidateActive d 16)
      (role := d2FlowCandidateRole d 16)
      (quota := d2FlowCandidateQuota d 16)
      (h := childDepth + 4) (i := 0) run16 j k m
  have hchildBound := d2FlowStage_regular_child_g_bound_of_tree_inputs
    (active := d2FlowCandidateActive d 16)
    (role := d2FlowCandidateRole d 16)
    (quota := d2FlowCandidateQuota d 16)
    (cap := fun x => d2FlowCandidateCapacity d x 16)
    (stageDepth := childDepth + 4) (i := 2) parent
    hactive16_2 hregular16_2 hparentInv hparentInputs'
  have hcapShift : d2FlowCandidateCapacity d 3 17 =
      2 * d2FlowCandidateCapacity d 2 16 :=
    d2FlowCandidateCapacity_succ_level_next_stage d 2 16 (by omega)
  have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
      d2FlowCandidateCapacity d 3 17 := by
    have hc := hchildBound m
    rw [htreeEq, hcapShift]
    simpa using hc
  have hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree := by
    cases hnode : parent with
    | node G low high children =>
        have hb := d2FlowStage_regular_child_balanced
          (active := d2FlowCandidateActive d 16)
          (role := d2FlowCandidateRole d 16)
          (quota := d2FlowCandidateQuota d 16)
          (h := childDepth + 4) (i := 2)
          (G := G) (low := low) (high := high) children
          hactive16_2 hregular16_2 m
        simpa [htreeEq, hnode] using hb
  have hactive16_3 : d2FlowCandidateActive d 16 3 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hlevels := (d2FlowCandidateActive_stage16_iff hd14).mp ht
    by_cases h14 : d = 14 <;> simp [h14] at hlevels <;> omega
  have hactive16_4 : d2FlowCandidateActive d 16 4 = true := by
    apply (d2FlowCandidateActive_stage16_iff hd14).2
    by_cases h14 : d = 14 <;> simp [h14]
  have hrole16_4 : d2FlowCandidateRole d 16 4 = .mid := by
    by_cases h14 : d = 14
    · have hcd : childDepth = 7 := by dsimp [d] at h14; omega
      subst childDepth
      norm_num [d, d2FlowCandidateRole, d2ScheduleRole,
        alpha, alphaStar, ceilParity, omega]
    · exact d2FlowCandidateRole_stage16_internal_mid
        (i := 4) (by omega) (Or.inr rfl)
  have hq3floor : forall s : Fin 8,
      d2FlowCandidateQuota d 16 4 .mid <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s) := by
    intro s
    have hproject := d2FlowStage_path4_projection
      (active := d2FlowCandidateActive d 16)
      (role := d2FlowCandidateRole d 16)
      (quota := d2FlowCandidateQuota d 16)
      (h := childDepth + 3) (i := 0) run16 j k m s
    have hchildEq : d2FlowTreeChild tree s =
        d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 16)
            (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
            (childDepth + 4) 3
            source) s := by
      change d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild (d2FlowCandidateRun d initial 17) j) k) m) s = _
      rw [d2FlowCandidateRun.eq_def]
      simp only [d2FlowCandidateStage]
      exact hproject
    have hsourceFalse := hactive16_3
    cases hnode : source with
    | node G3 low3 high3 children3 =>
        have hstep := d2FlowStage_inactive_child
          (active := d2FlowCandidateActive d 16)
          (role := d2FlowCandidateRole d 16)
          (quota := d2FlowCandidateQuota d 16)
          (h := childDepth + 3) (i := 3)
          (G := G3) (low := low3) (high := high3) children3 hsourceFalse s
        have hchildStage : d2FlowTreeChild tree s =
            d2FlowStage (d2FlowCandidateActive d 16)
              (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
              (childDepth + 3) 4 (children3 s) := by
          calc
            d2FlowTreeChild tree s =
                d2FlowTreeChild
                  (d2FlowStage (d2FlowCandidateActive d 16)
                    (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
                  (childDepth + 4) 3 source) s := by
                      simpa [source, hnode] using hchildEq
            _ = d2FlowStage (d2FlowCandidateActive d 16)
                  (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
                  (childDepth + 3) 4 (children3 s) := by
                    simpa [hnode] using hstep
        cases hchild : children3 s with
        | node G4 low4 high4 children4 =>
            have hdef := d2FlowStage_active_node_deficit
              (active := d2FlowCandidateActive d 16)
              (role := d2FlowCandidateRole d 16)
              (quota := d2FlowCandidateQuota d 16)
              (h := childDepth + 2) (i := 4)
              (G := G4) (low := low4) (high := high4)
              children4 hactive16_4
            have hq := congrArg d2FlowTreeRootDeficit hchildStage
            rw [hchild] at hq
            rw [hq, hdef]
            simp [hrole16_4]
  have hquotaCap : 256 * d2FlowCandidateQuota d 17 3 .mid <=
      d2FlowCandidateCapacity d 3 17 := by
    have hactiveRaw : active d (tfD2 d) 3 17 := by
      have hm := d2FlowCandidateActive_matches_schedule
        (d := d) (i := 3) (t := 17) (by omega)
      rw [hactive17_3] at hm
      exact of_decide_eq_true hm.symm
    have hrSchedule : d2ScheduleRole d 3 17 = .mid := by
      have hm := d2FlowCandidateRole_matches_schedule
        (d := d) (i := 3) (t := 17) (by omega)
      exact hm.symm.trans hrole17_3
    have hregular : d2ScheduleRole d 3 17 = .topRise \/
        d2ScheduleRole d 3 17 = .mid \/
        d2ScheduleRole d 3 17 = .botDesc := Or.inr (Or.inl hrSchedule)
    have h := d2FlowCandidateQuota_le_capacity_div_256
      (by omega) hactiveRaw hregular
    simpa [hrSchedule] using h
  have heven : d2FlowCandidateQuota d 17 3 .mid % 2 = 0 := by
    have hactiveRaw : active d (tfD2 d) 3 17 := by
      have hm := d2FlowCandidateActive_matches_schedule
        (d := d) (i := 3) (t := 17) (by omega)
      rw [hactive17_3] at hm
      exact of_decide_eq_true hm.symm
    have hrSchedule : d2ScheduleRole d 3 17 = .mid := by
      have hm := d2FlowCandidateRole_matches_schedule
        (d := d) (i := 3) (t := 17) (by omega)
      exact hm.symm.trans hrole17_3
    have hregular : d2ScheduleRole d 3 17 = .topRise \/
        d2ScheduleRole d 3 17 = .mid \/
        d2ScheduleRole d 3 17 = .botDesc := Or.inr (Or.inl hrSchedule)
    have h := d2FlowCandidateQuota_even (by omega) hactiveRaw (by omega) hregular
    simpa [hrSchedule, d2FlowCandidateRole] using h
  have hq3relation : 128 * d2FlowCandidateQuota d 16 4 .mid =
      15 * d2FlowCandidateCapacity d 3 17 := by
    have hcap : d2FlowCandidateCapacity d 3 17 = 2 ^ (3 * d - 16) := by
      simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
      omega
    have hq : d2FlowCandidateQuota d 16 4 .mid =
        15 * 2 ^ (3 * d - 23) := by
      simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
      omega
    rw [hcap, hq]
    rw [show 3 * d - 16 = 7 + (3 * d - 23) by omega, pow_add]
    ring
  have hleft : d2FlowCandidateCapacity d 3 17 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    have hf := hq3floor (Fin.mk 0 (by omega))
    have hcq : d2FlowCandidateCapacity d 3 17 <=
        128 * d2FlowCandidateQuota d 16 4 .mid := by
      nlinarith [hq3relation]
    exact le_trans hcq (Nat.mul_le_mul_left 128 hf)
  have hright : d2FlowCandidateCapacity d 3 17 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    have hf := hq3floor (Fin.mk 7 (by omega))
    have hcq : d2FlowCandidateCapacity d 3 17 <=
        128 * d2FlowCandidateQuota d 16 4 .mid := by
      nlinarith [hq3relation]
    exact le_trans hcq (Nat.mul_le_mul_left 128 hf)
  have htotalLower : 8 * d2FlowCandidateQuota d 16 4 .mid <=
      d2FlowTotal (fun s : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
    change 8 * d2FlowCandidateQuota d 16 4 .mid <=
      Finset.univ.sum (fun s : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s))
    calc
      8 * d2FlowCandidateQuota d 16 4 .mid =
          Finset.univ.sum (fun _ : Fin 8 =>
            d2FlowCandidateQuota d 16 4 .mid) := by simp
      _ <= Finset.univ.sum (fun s : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
        apply Finset.sum_le_sum
        intro s hs
        exact hq3floor s
  have halloc : d2FlowCandidateQuota d 17 3 .mid <=
      d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) -
        d2FlowTreeRootDeficit tree := by
    have hbudget : d2FlowCandidateQuota d 17 3 .mid +
        d2FlowTreeRootDeficit tree <=
        8 * d2FlowCandidateQuota d 16 4 .mid := by
      nlinarith [hquotaCap, hrootcap, hq3relation]
    omega
  have hchildren : forall s : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
        (d2FlowCandidateQuota d 17)
        (fun x => d2FlowCandidateCapacity d x 17) 4
        (d2FlowTreeChild tree s) := by
    intro s
    exact d2FlowCandidateRun_stage17_levelFour_inputs
      childDepth hd j k m s
  have hcontract := d2FlowStageInvInputs_mid_of_contract
    (scale := 8192) (i := 3) tree hactive17_3 hrole17_3 hchildren
    hbalance hrootcap hquotaCap halloc heven hleft hright
  simpa [d, initial, run16, run17, tree] using hcontract

end Chvatal.D2Reserve
