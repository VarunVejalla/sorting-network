import D2CandidateQuotaLower
import D2Stage16LevelFourInputs
import D2Stage18Frontier

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 16000000
set_option maxRecDepth 4096

/-- The generic two-step reserve theorem supplies the actual endpoint gates
for Stage 18 level four from its Stage-16 visit, with the inactive Stage 17
step in between. This verifies the reusable recurrence on a real run. -/
theorem d2FlowCandidateRun_stage18_levelFour_endpoint_reserve_via_two_step
    (height : Nat) (hd : 6 <= height) (j k m l : Fin 8) :
    let d := height + 8
    let run18 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 18
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild run18 j) k) m) l
    d2FlowCandidateCapacity d 4 18 <=
      128 * d2FlowTreeRootDeficit (d2FlowTreeChild tree 0) /\
    d2FlowCandidateCapacity d 4 18 <=
      128 * d2FlowTreeRootDeficit (d2FlowTreeChild tree 7) := by
  classical
  let d := height + 8
  let initial := d2FlowTreeInitial 8192 d
  let run16 : D2FlowTree (height + 8) :=
    d2FlowCandidateRun d initial 16
  let run17 : D2FlowTree (height + 8) :=
    d2FlowCandidateRun d initial 17
  let run18 : D2FlowTree (height + 8) :=
    d2FlowCandidateRun d initial 18
  let parent16 := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild run16 j) k) m
  let tree16 := d2FlowTreeChild parent16 l
  let tree := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run18 j) k) m) l
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hactive16 : d2FlowCandidateActive d 16 4 = true := by
    rw [d2FlowCandidateActive_stage16_iff hd14]
    by_cases h14 : d = 14 <;> simp [h14]
  have hrole16 : d2FlowCandidateRole d 16 4 = .mid := by
    by_cases h14 : d = 14
    · have hh : height = 6 := by dsimp [d] at h14; omega
      subst height
      norm_num [d2FlowCandidateRole, d2ScheduleRole, alpha, alphaStar,
        ceilParity, omega]
    · exact d2FlowCandidateRole_stage16_internal_mid
        (i := 4) (by omega) (Or.inr rfl)
  have hactive18 : d2FlowCandidateActive d 18 4 = true := by
    apply (d2FlowCandidateActive_stage18_iff hd14).2
    by_cases hsmall : d <= 15 <;> simp [hsmall]
  have hrole18 : d2FlowCandidateRole d 18 4 = .mid :=
    d2FlowCandidateRole_stage18_mid46 hd14 4 (Or.inl rfl)
  have hactive18Raw : active d (tfD2 d) 4 18 := by
    have hm := d2FlowCandidateActive_matches_schedule
      (d := d) (i := 4) (t := 18) (by omega)
    rw [hactive18] at hm
    exact of_decide_eq_true hm.symm
  have hrole18Raw : d2ScheduleRole d 4 18 = .mid := by
    have hm := d2FlowCandidateRole_matches_schedule
      (d := d) (i := 4) (t := 18) (by omega)
    exact hm.symm.trans hrole18
  have hrole16Raw : d2ScheduleRole d 4 16 = .mid := by
    have hm := d2FlowCandidateRole_matches_schedule
      (d := d) (i := 4) (t := 16) (by omega)
    exact hm.symm.trans hrole16
  have hinputs16 : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
      (d2FlowCandidateQuota d 16)
      (fun x => d2FlowCandidateCapacity d x 16) 4 tree16 := by
    simpa [d, initial, run16, parent16, tree16] using
      d2FlowCandidateRun_stage16_levelFour_inputs (height + 1) (by omega)
        j k m l
  have hinvRun16 : d2FlowTreeInv 8192 run16 := by
    simpa [d, initial, run16] using
      d2FlowCandidateStage15_preserves_inv (height + 1) (by omega)
  have hinv2 : d2FlowTreeInv 8192
      (d2FlowTreeChild (d2FlowTreeChild run16 j) k) :=
    d2FlowTreeInv_grandchild run16 hinvRun16 j k
  have hinvTree16 : d2FlowTreeInv 8192 tree16 := by
    simpa [parent16, tree16] using
      d2FlowTreeInv_grandchild
        (d2FlowTreeChild (d2FlowTreeChild run16 j) k) hinv2 m l
  have hactive16_3 : d2FlowCandidateActive d 16 3 = false := by
    cases h : d2FlowCandidateActive d 16 3 with
    | false => rfl
    | true =>
        have hlevels := (d2FlowCandidateActive_stage16_iff hd14).mp h
        by_cases h14 : d = 14 <;> simp [h14] at hlevels
  cases hnode : tree16 with
  | node G low high children =>
      have hinputs := hinputs16
      rw [hnode] at hinputs
      simp only [d2FlowStageInvInputs] at hinputs
      rcases hinputs with ⟨_, hlocal⟩
      simp only [hactive16, if_pos, hrole16] at hlocal
      rcases hlocal with ⟨hbalance, hcontract⟩
      rcases hcontract with ⟨hdeficit, hquota, halloc, heven,
        hleft, hright⟩
      have hcover : G <= d2FlowTotal
          (fun q => d2FlowTreeRootDeficit (children q)) := by
        have hx := hinvTree16
        rw [hnode] at hx
        simp only [d2FlowTreeInv] at hx
        simpa [d2FlowTotal] using hx.2.1
      have hquotaRaw : 256 * d2FlowCandidateQuota d 16 4
          (d2ScheduleRole d 4 16) <= d2FlowCandidateCapacity d 4 16 := by
        simpa [hrole16Raw] using hquota
      have hallocRaw : d2FlowCandidateQuota d 16 4
          (d2ScheduleRole d 4 16) <=
          d2FlowTotal (fun q => d2FlowTreeRootDeficit (children q)) - G := by
        simpa [hrole16Raw] using halloc
      have hevenRaw : d2FlowCandidateQuota d 16 4
          (d2ScheduleRole d 4 16) % 2 = 0 := by
        simpa [hrole16Raw] using heven
      have hrun17 : run17 = d2FlowCandidateStage d 16 run16 := by
        change d2FlowCandidateRun d initial 17 =
          d2FlowCandidateStage d 16 (d2FlowCandidateRun d initial 16)
        rw [d2FlowCandidateRun.eq_def]
      have hrun18 : run18 = d2FlowCandidateStage d 17 run17 := by
        change d2FlowCandidateRun d initial 18 =
          d2FlowCandidateStage d 17 (d2FlowCandidateRun d initial 17)
        rw [d2FlowCandidateRun.eq_def]
      have hparent16_inactive : d2FlowCandidateActive d 16 3 = false :=
        hactive16_3
      have htree17 :
          d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run17 j) k) m) l =
          d2FlowStage (d2FlowCandidateActive d 16)
            (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
            (height + 3 + 1) 4 tree16 := by
        have hproj := d2FlowStage_path4_projection
          (active := d2FlowCandidateActive d 16)
          (role := d2FlowCandidateRole d 16)
          (quota := d2FlowCandidateQuota d 16)
          (h := height + 4) (i := 0) run16 j k m l
        cases hp : parent16 with
        | node Gp lp rp grandchildren =>
            have hchild := d2FlowStage_inactive_child
              (active := d2FlowCandidateActive d 16)
              (role := d2FlowCandidateRole d 16)
              (quota := d2FlowCandidateQuota d 16)
              (h := height + 3 + 1) (i := 3) (G := Gp)
              (low := lp) (high := rp) grandchildren hparent16_inactive l
            calc
              _ = d2FlowTreeChild
                    (d2FlowStage (d2FlowCandidateActive d 16)
                      (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
                      (height + 5) 3 parent16) l := by
                      rw [hrun17]
                      simpa [d2FlowCandidateStage] using hproj
              _ = _ := by simpa [parent16, tree16, hp] using hchild
      have hreserve := d2FlowCandidate_two_step_endpoint_reserve
        (d := d) (i := 4) (t := 18) (by omega) (by omega)
        (by unfold tfD2; omega) hactive18Raw
        (by simp [hrole18Raw]) (by simp [hrole16Raw])
        children hbalance hcover hdeficit hquotaRaw hallocRaw hevenRaw hleft hright
      have hproj18 (q : Fin 8) :
          d2FlowTreeRootDeficit (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild run18 j) k) m) l) q) =
          d2FlowTreeRootDeficit (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 17)
              (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
              (height + 3 + 1) 4
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild run17 j) k) m) l)) q) := by
        have hp := d2FlowStage_path5_projection
          (active := d2FlowCandidateActive d 17)
          (role := d2FlowCandidateRole d 17)
          (quota := d2FlowCandidateQuota d 17)
          (h := height + 3) (i := 0) run17 j k m l q
        calc
          _ = d2FlowTreeRootDeficit (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild
                        (d2FlowCandidateStage d 17 run17) j) k) m) l) q) := by
              rw [hrun18]
          _ = _ := by simpa only [d2FlowCandidateStage] using hp
      have hreserve' := by simpa [d] using hreserve
      constructor
      · rw [hproj18 0, htree17]
        simpa [d, hnode] using hreserve'.1
      · rw [hproj18 7, htree17]
        simpa [d, hnode] using hreserve'.2

end Chvatal.D2Reserve
