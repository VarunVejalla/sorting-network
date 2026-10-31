import D2Stage15LevelFiveContract
import D2Stage15LevelThreeRootCap
import D2Stage15ActualReserves
import D2Stage15Frontier
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- Assemble the complete Stage-15 input contract at each active level-three
sender. Stage 14 supplies its local balance and reserves; its active
level-two cut also accounts for the parent's deficit. The level-four
children are inactive and inherit the checked level-five contracts. -/
theorem d2FlowCandidateRun_stage15_levelThree_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k l : Fin 8) :
    let d := childDepth + 7
    let initial := d2FlowTreeInitial 8192 d
    let run15 := d2FlowCandidateRun d initial 15
    let tree := d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild run15 j) k) l
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
      (d2FlowCandidateQuota d 15)
      (fun i => d2FlowCandidateCapacity d i 15) 3 tree := by
  classical
  let d := childDepth + 7
  let run14 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  let run15 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 15
  let tree := d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run15 j) k) l
  have hd' : 14 <= d := by dsimp [d]; omega
  have hactive : d2FlowCandidateActive d 15 3 = true :=
    (d2FlowCandidateActive_stage15_at hd').2.1
  have hrole : d2FlowCandidateRole d 15 3 = .mid :=
    d2FlowCandidateRole_stage15_internal_mid hd' 3 (Or.inl rfl)
  have hchildren : forall m : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
        (d2FlowCandidateQuota d 15)
        (fun i => d2FlowCandidateCapacity d i 15) 4
        (d2FlowTreeChild tree m) := by
    intro m
    apply d2FlowStageInvInputs_inactive_of_children 8192 4
      (d2FlowTreeChild tree m)
    · have hfalse : d2FlowCandidateActive d 15 4 = false := by
        cases hvalue : d2FlowCandidateActive d 15 4 with
        | false => rfl
        | true =>
            have hlevel := d2FlowCandidateActive_stage15_level_bound hvalue
            rcases hlevel with h | h | h | h <;> omega
      exact hfalse
    · intro q
      exact d2FlowCandidateRun_stage15_levelFive_inputs
        childDepth hd j k l m q
  have hfront := d2FlowCandidateStage14_frontiers d (by omega)
  rcases hfront with ⟨_, _, hactive2, hrole2, _, _, _, _, _⟩
  let path2 := d2FlowTreeChild (d2FlowTreeChild run14 j) k
  have hlocal : (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 14)
          (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
          (childDepth + 5) 2 path2) l)).2.1 +
      (d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d 14)
          (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
          (childDepth + 5) 2 path2) l)).2.2 =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 14)
            (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
            (childDepth + 5) 2 path2) l) := by
    cases path2 with
    | node G low high children =>
        exact d2FlowStage_regular_child_balanced children hactive2
          (Or.inr (Or.inl hrole2)) l
  have hprojection := d2FlowCandidateRun_stage15_levelThree_path_eq_levelTwo_child
    childDepth hd j k l
  have htree : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 14)
        (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
        (childDepth + 5) 2 path2) l := by
    exact hprojection
  have hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree := by
    change (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree
    rw [htree]
    exact hlocal
  have hdeficit := d2FlowCandidateRun_stage15_levelThree_root_cap
    childDepth hd j k l
  have hquotaCap :
      256 * d2FlowCandidateQuota d 15 3 .mid <=
        d2FlowCandidateCapacity d 3 15 := by
    have hactiveRaw : active d (tfD2 d) 3 15 := by
      have hm := d2FlowCandidateActive_matches_schedule
        (d := d) (t := 15) (i := 3) (by omega)
      rw [hactive] at hm
      exact of_decide_eq_true hm.symm
    have hroleSchedule : d2ScheduleRole d 3 15 = .mid := by
      have hm := d2FlowCandidateRole_matches_schedule
        (d := d) (i := 3) (t := 15) (by omega)
      exact hm.symm.trans hrole
    have hregular : d2ScheduleRole d 3 15 = .topRise \/
        d2ScheduleRole d 3 15 = .mid \/
        d2ScheduleRole d 3 15 = .botDesc := Or.inr (Or.inl hroleSchedule)
    have hbound := d2FlowCandidateQuota_le_capacity_div_256
      (by omega) hactiveRaw hregular
    simpa [hroleSchedule] using hbound
  have heven : d2FlowCandidateQuota d 15 3 .mid % 2 = 0 := by
    have hactiveRaw : active d (tfD2 d) 3 15 := by
      have hm := d2FlowCandidateActive_matches_schedule
        (d := d) (t := 15) (i := 3) (by omega)
      rw [hactive] at hm
      exact of_decide_eq_true hm.symm
    have hroleSchedule : d2ScheduleRole d 3 15 = .mid := by
      have hm := d2FlowCandidateRole_matches_schedule
        (d := d) (i := 3) (t := 15) (by omega)
      exact hm.symm.trans hrole
    have hregular : d2ScheduleRole d 3 15 = .topRise \/
        d2ScheduleRole d 3 15 = .mid \/
        d2ScheduleRole d 3 15 = .botDesc := Or.inr (Or.inl hroleSchedule)
    have hbound := d2FlowCandidateQuota_even
      (by omega) hactiveRaw (by omega) hregular
    simpa [hroleSchedule, d2FlowCandidateRole] using hbound
  have halloc := d2FlowCandidateRun_stage15_levelThree_allocation
    childDepth hd j k l
  have hleft := d2FlowCandidateRun_stage15_levelThree_endpoint_reserve
    (childDepth + 2) (by omega) j k l ⟨0, by omega⟩
  have hright := d2FlowCandidateRun_stage15_levelThree_endpoint_reserve
    (childDepth + 2) (by omega) j k l ⟨7, by omega⟩
  exact d2FlowStageInvInputs_mid_of_contract 8192 3 tree
    hactive hrole hchildren hbalance hdeficit hquotaCap halloc heven
    hleft hright

end Chvatal.D2Reserve
