import D2Stage16LevelFourInputs
import D2Stage17LevelSixInputs
import D2Stage17Frontier
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- The complete input contract at each actual Stage-17 level-five sender.
The Stage-16 level-four middle cut supplies balance and the root-cap gate;
its level-six bottom-descending quota supplies the endpoint reserve. -/
theorem d2FlowCandidateRun_stage17_levelFive_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q : Fin 8) :
    let d := childDepth + 7
    let run17 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 17
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run17 j) k) m) l) q
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
      (d2FlowCandidateQuota d 17)
      (fun x => d2FlowCandidateCapacity d x 17) 5 tree := by
  classical
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let run16 := d2FlowCandidateRun d initial 16
  let run17 := d2FlowCandidateRun d initial 17
  let path3 := d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run16 j) k) m
  let parent := d2FlowTreeChild path3 l
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild run17 j) k) m) l) q
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hactive17_5 : d2FlowCandidateActive d 17 5 = true := by
    apply (d2FlowCandidateActive_stage17_iff hd14).2
    exact Or.inr (Or.inr (Or.inl rfl))
  have hrole17_5 : d2FlowCandidateRole d 17 5 = .mid :=
    d2FlowCandidateRole_stage17_mid5 hd14
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
  have hregular16_4 : d2FlowCandidateRole d 16 4 = .topRise \/
      d2FlowCandidateRole d 16 4 = .mid \/
      d2FlowCandidateRole d 16 4 = .botDesc := Or.inr (Or.inl hrole16_4)
  have hinvRun16 : d2FlowTreeInv 8192 run16 := by
    simpa [d, initial, run16] using
      d2FlowCandidateStage15_preserves_inv childDepth hd
  have hinv2 : d2FlowTreeInv 8192
      (d2FlowTreeChild (d2FlowTreeChild run16 j) k) := by
    exact d2FlowTreeInv_grandchild (h := childDepth + 5)
      run16 hinvRun16 j k
  have hinv3 : d2FlowTreeInv 8192 path3 := by
    cases hnode : d2FlowTreeChild (d2FlowTreeChild run16 j) k with
    | node G low high children =>
        have hx := hinv2
        rw [hnode] at hx
        simp only [d2FlowTreeInv] at hx
        simpa [path3, hnode] using hx.2.2.2 m
  have hparentInv : d2FlowTreeInv 8192 parent := by
    cases hnode : path3 with
    | node G low high children =>
        have hx := hinv3
        rw [hnode] at hx
        simp only [d2FlowTreeInv] at hx
        simpa [parent, path3, hnode] using hx.2.2.2 l
  have hparentInputs := d2FlowCandidateRun_stage16_levelFour_inputs
    childDepth hd j k m l
  have hparentInputs' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
      (d2FlowCandidateQuota d 16)
      (fun x => d2FlowCandidateCapacity d x 16) 4 parent := by
    simpa [d, initial, run16, parent] using hparentInputs
  have hrun17 : run17 = d2FlowCandidateStage d 16 run16 := by
    change d2FlowCandidateRun d initial 17 =
      d2FlowCandidateStage d 16 (d2FlowCandidateRun d initial 16)
    rw [d2FlowCandidateRun.eq_def]
  have hpath4 : d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run17 j) k) m) l =
      d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 16)
          (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
          (childDepth + 4) 3 path3) l := by
    change d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run17 j) k) m) l = _
    rw [hrun17]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path4_projection
      (active := d2FlowCandidateActive d 16)
      (role := d2FlowCandidateRole d 16)
      (quota := d2FlowCandidateQuota d 16)
      (h := childDepth + 3) (i := 0) run16 j k m l
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 16)
        (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
        (childDepth + 3) 4 parent) q := by
    change d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild run17 j) k) m) l) q = _
    rw [hpath4]
    exact d2FlowStage_child_child_projection path3 l q
  have hchildBound := d2FlowStage_regular_child_g_bound_of_tree_inputs
    (active := d2FlowCandidateActive d 16)
    (role := d2FlowCandidateRole d 16)
    (quota := d2FlowCandidateQuota d 16)
    (cap := fun x => d2FlowCandidateCapacity d x 16)
    (stageDepth := childDepth + 2) (i := 4) parent
    hactive16_4 hregular16_4 hparentInv hparentInputs'
  have hcapShift : d2FlowCandidateCapacity d 5 17 =
      2 * d2FlowCandidateCapacity d 4 16 :=
    d2FlowCandidateCapacity_succ_level_next_stage d 4 16 (by omega)
  have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
      d2FlowCandidateCapacity d 5 17 := by
    have hc := hchildBound q
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
          (h := childDepth + 2) (i := 4)
          (G := G) (low := low) (high := high) children
          hactive16_4 hregular16_4 q
        simpa [htreeEq, hnode] using hb
  have hactive16_5 : d2FlowCandidateActive d 16 5 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hlevels := (d2FlowCandidateActive_stage16_iff hd14).mp ht
    by_cases h14 : d = 14 <;> simp [h14] at hlevels <;> omega
  have hactive16_6 : d2FlowCandidateActive d 16 6 = true := by
    apply (d2FlowCandidateActive_stage16_iff hd14).2
    by_cases h14 : d = 14 <;> simp [h14]
  have hrole16_6 : d2FlowCandidateRole d 16 6 = .botDesc :=
    d2FlowCandidateRole_stage16_bottom hd14
  have hq5floor : forall s : Fin 8,
      d2FlowCandidateQuota d 16 6 .botDesc <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s) := by
    intro s
    have hproject := d2FlowStage_path6_tree_projection
      (active := d2FlowCandidateActive d 16)
      (role := d2FlowCandidateRole d 16)
      (quota := d2FlowCandidateQuota d 16)
      (h := childDepth + 1) (i := 0) run16 j k m l q s
    have hchildEq : d2FlowTreeChild tree s =
        d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 16)
            (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
            (childDepth + 2) 5
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild run16 j) k) m) l) q)) s := by
      change d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild run17 j) k) m) l) q) s = _
      rw [hrun17]
      simp only [d2FlowCandidateStage]
      exact hproject
    let source := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run16 j) k) m) l) q
    have hsourceFalse : d2FlowCandidateActive d 16 5 = false := hactive16_5
    cases hsource : source with
    | node G5 low5 high5 children5 =>
        have hstep := d2FlowStage_inactive_child
          (active := d2FlowCandidateActive d 16)
          (role := d2FlowCandidateRole d 16)
          (quota := d2FlowCandidateQuota d 16)
          (h := childDepth + 1) (i := 5)
          (G := G5) (low := low5) (high := high5) children5 hsourceFalse s
        have hchildStage : d2FlowTreeChild tree s =
            d2FlowStage (d2FlowCandidateActive d 16)
              (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
              (childDepth + 1) 6 (children5 s) := by
          calc
            d2FlowTreeChild tree s =
                d2FlowTreeChild
                  (d2FlowStage (d2FlowCandidateActive d 16)
                    (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
                    (childDepth + 2) 5 source) s := by
                      simpa [source, hsource] using hchildEq
            _ = d2FlowStage (d2FlowCandidateActive d 16)
                  (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
                  (childDepth + 1) 6 (children5 s) := by
                    simpa [hsource] using hstep
        cases hchild : children5 s with
        | node G6 low6 high6 children6 =>
            have hdef := d2FlowStage_active_node_deficit
              (active := d2FlowCandidateActive d 16)
              (role := d2FlowCandidateRole d 16)
              (quota := d2FlowCandidateQuota d 16)
              (h := childDepth) (i := 6)
              (G := G6) (low := low6) (high := high6)
              children6 hactive16_6
            have hq := congrArg d2FlowTreeRootDeficit hchildStage
            rw [hchild] at hq
            rw [hq, hdef]
            simp [hrole16_6]
  have hquotaCap : 256 * d2FlowCandidateQuota d 17 5 .mid <=
      d2FlowCandidateCapacity d 5 17 := by
    have hactiveRaw : active d (tfD2 d) 5 17 := by
      have hm := d2FlowCandidateActive_matches_schedule
        (d := d) (i := 5) (t := 17) (by omega)
      rw [hactive17_5] at hm
      exact of_decide_eq_true hm.symm
    have hrSchedule : d2ScheduleRole d 5 17 = .mid := by
      have hm := d2FlowCandidateRole_matches_schedule
        (d := d) (i := 5) (t := 17) (by omega)
      exact hm.symm.trans hrole17_5
    have hregular : d2ScheduleRole d 5 17 = .topRise \/
        d2ScheduleRole d 5 17 = .mid \/
        d2ScheduleRole d 5 17 = .botDesc := Or.inr (Or.inl hrSchedule)
    have h := d2FlowCandidateQuota_le_capacity_div_256
      (by omega) hactiveRaw hregular
    simpa [hrSchedule] using h
  have heven : d2FlowCandidateQuota d 17 5 .mid % 2 = 0 := by
    have hactiveRaw : active d (tfD2 d) 5 17 := by
      have hm := d2FlowCandidateActive_matches_schedule
        (d := d) (i := 5) (t := 17) (by omega)
      rw [hactive17_5] at hm
      exact of_decide_eq_true hm.symm
    have hrSchedule : d2ScheduleRole d 5 17 = .mid := by
      have hm := d2FlowCandidateRole_matches_schedule
        (d := d) (i := 5) (t := 17) (by omega)
      exact hm.symm.trans hrole17_5
    have hregular : d2ScheduleRole d 5 17 = .topRise \/
        d2ScheduleRole d 5 17 = .mid \/
        d2ScheduleRole d 5 17 = .botDesc := Or.inr (Or.inl hrSchedule)
    have h := d2FlowCandidateQuota_even (by omega) hactiveRaw (by omega) hregular
    simpa [hrSchedule, d2FlowCandidateRole] using h
  have hq5relation : 128 * d2FlowCandidateQuota d 16 6 .botDesc =
      15 * d2FlowCandidateCapacity d 5 17 := by
    have hcap : d2FlowCandidateCapacity d 5 17 = 2 ^ (3 * d - 10) := by
      simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
      omega
    have hq : d2FlowCandidateQuota d 16 6 .botDesc =
        15 * 2 ^ (3 * d - 17) := by
      simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
      omega
    rw [hcap, hq]
    rw [show 3 * d - 10 = 7 + (3 * d - 17) by omega, pow_add]
    ring
  have hleft : d2FlowCandidateCapacity d 5 17 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    have hf := hq5floor (Fin.mk 0 (by omega))
    have hcq : d2FlowCandidateCapacity d 5 17 <=
        128 * d2FlowCandidateQuota d 16 6 .botDesc := by
      nlinarith [hq5relation]
    exact le_trans hcq (Nat.mul_le_mul_left 128 hf)
  have hright : d2FlowCandidateCapacity d 5 17 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    have hf := hq5floor (Fin.mk 7 (by omega))
    have hcq : d2FlowCandidateCapacity d 5 17 <=
        128 * d2FlowCandidateQuota d 16 6 .botDesc := by
      nlinarith [hq5relation]
    exact le_trans hcq (Nat.mul_le_mul_left 128 hf)
  have htotalLower : 8 * d2FlowCandidateQuota d 16 6 .botDesc <=
      d2FlowTotal (fun s : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
    change 8 * d2FlowCandidateQuota d 16 6 .botDesc <=
      Finset.univ.sum (fun s : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s))
    calc
      8 * d2FlowCandidateQuota d 16 6 .botDesc =
          Finset.univ.sum (fun _ : Fin 8 =>
            d2FlowCandidateQuota d 16 6 .botDesc) := by simp
      _ <= Finset.univ.sum (fun s : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
        apply Finset.sum_le_sum
        intro s hs
        exact hq5floor s
  have halloc : d2FlowCandidateQuota d 17 5 .mid <=
      d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) -
        d2FlowTreeRootDeficit tree := by
    have hbudget : d2FlowCandidateQuota d 17 5 .mid +
        d2FlowTreeRootDeficit tree <=
        8 * d2FlowCandidateQuota d 16 6 .botDesc := by
      nlinarith [hquotaCap, hrootcap, hq5relation]
    omega
  have hchildren : forall s : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
        (d2FlowCandidateQuota d 17)
        (fun x => d2FlowCandidateCapacity d x 17) 6
        (d2FlowTreeChild tree s) := by
    intro s
    exact d2FlowCandidateRun_stage17_levelSix_inputs
      childDepth hd j k m l q s
  have hcontract := d2FlowStageInvInputs_mid_of_contract
    (scale := 8192) (i := 5) tree hactive17_5 hrole17_5 hchildren
    hbalance hrootcap hquotaCap halloc heven hleft hright
  simpa [d, initial, run16, run17, tree] using hcontract

end Chvatal.D2Reserve
