import D2Stage15LevelFiveInputs
import D2Stage15Frontier
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- Assemble the complete recursive input contract at every actual
level-five Stage-15 middle sender. Its level-six children are inactive and
their level-seven children satisfy the checked bottom-rise contract. -/
theorem d2FlowCandidateRun_stage15_levelFive_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q : Fin 8) :
    let d := childDepth + 7
    let initial := d2FlowTreeInitial 8192 d
    let run15 := d2FlowCandidateRun d initial 15
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run15 j) k) m) l) q
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
      (d2FlowCandidateQuota d 15)
      (fun i => d2FlowCandidateCapacity d i 15) 5 tree := by
  classical
  let d := childDepth + 7
  let run15 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 15
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild run15 j) k) m) l) q
  have hd' : 14 <= d := by dsimp [d]; omega
  have hactive : d2FlowCandidateActive d 15 5 = true :=
    (d2FlowCandidateActive_stage15_at hd').2.2.1
  have hrole : d2FlowCandidateRole d 15 5 = .mid :=
    d2FlowCandidateRole_stage15_internal_mid hd' 5 (Or.inr rfl)
  have hchildren : forall r : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 15) (d2FlowCandidateRole d 15)
        (d2FlowCandidateQuota d 15)
        (fun i => d2FlowCandidateCapacity d i 15) 6
        (d2FlowTreeChild tree r) := by
    intro r
    apply d2FlowStageInvInputs_inactive_of_children 8192 6
      (d2FlowTreeChild tree r)
    · have hfalse : d2FlowCandidateActive d 15 6 = false := by
        cases hvalue : d2FlowCandidateActive d 15 6 with
        | false => rfl
        | true =>
            have hlevel := d2FlowCandidateActive_stage15_level_bound hvalue
            rcases hlevel with h | h | h | h <;> omega
      exact hfalse
    · intro s
      exact d2FlowCandidateRun_stage15_levelSeven_inputs
        childDepth hd j k m l q r s
  have hbalance := d2FlowCandidateRun_stage15_levelFive_balanced
    childDepth hd j k m l q
  have hdeficit := d2FlowCandidateRun_stage15_levelFive_root_cap
    childDepth hd j k m l q
  have hactiveRaw : active d (tfD2 d) 5 15 := by
    have hm := d2FlowCandidateActive_matches_schedule
      (d := d) (t := 15) (i := 5) (by omega)
    rw [hactive] at hm
    exact of_decide_eq_true hm.symm
  have hroleSchedule : d2ScheduleRole d 5 15 = .mid := by
    have hm := d2FlowCandidateRole_matches_schedule
      (d := d) (i := 5) (t := 15) (by omega)
    exact hm.symm.trans hrole
  have hregular : d2ScheduleRole d 5 15 = .topRise \/
      d2ScheduleRole d 5 15 = .mid \/
      d2ScheduleRole d 5 15 = .botDesc := Or.inr (Or.inl hroleSchedule)
  have hquotaCap : 256 * d2FlowCandidateQuota d 15 5 .mid <=
      d2FlowCandidateCapacity d 5 15 := by
    have hb := d2FlowCandidateQuota_le_capacity_div_256
      (by omega) hactiveRaw hregular
    simpa [hroleSchedule] using hb
  have heven : d2FlowCandidateQuota d 15 5 .mid % 2 = 0 := by
    have hb := d2FlowCandidateQuota_even
      (by omega) hactiveRaw (by omega) hregular
    simpa [hroleSchedule, d2FlowCandidateRole] using hb
  have halloc := d2FlowCandidateRun_stage15_levelFive_allocation
    childDepth hd j k m l q
  have hleft := d2FlowCandidateRun_stage15_levelFive_endpoint_reserve
    childDepth (by omega) j k m l q ⟨0, by omega⟩
  have hright := d2FlowCandidateRun_stage15_levelFive_endpoint_reserve
    childDepth (by omega) j k m l q ⟨7, by omega⟩
  exact d2FlowStageInvInputs_mid_of_contract 8192 5 tree
    hactive hrole hchildren hbalance hdeficit hquotaCap halloc heven
    hleft hright

end Chvatal.D2Reserve
