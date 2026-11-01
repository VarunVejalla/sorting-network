import D2AffineCoreAllStages
import D2CandidateTwoFrontBridge

namespace Chvatal.D2Reserve

open Chvatal.D2CandidateTwoFrontBridge

/-- Every active ordinary sender in the all-stage candidate flow tree has
zero ideal-prefix overrun above its two-front child reserves. This composes
the all-time affine profile with the candidate quota lower bound. It is an
abstract flow statement; it does not identify Boolean tile masses or tags. -/
theorem d2FlowCandidateRun_active_ordinary_two_front_overrun_zero_atPath
    {h i t : Nat} (hd : 7 <= (h + 1) + i) (ht : 0 < t)
    (path : D2FlowPath i)
    (ha : d2FlowCandidateActive ((h + 1) + i) t i = true)
    (hr : d2FlowCandidateRole ((h + 1) + i) t i = .topRise ∨
      d2FlowCandidateRole ((h + 1) + i) t i = .mid ∨
      d2FlowCandidateRole ((h + 1) + i) t i = .botDesc)
    (G low high : Nat) (children : Fin 8 -> D2FlowTree h)
    (hnode : d2FlowTreeAtPath i
      (d2FlowCandidateRun ((h + 1) + i)
        (d2FlowTreeInitial 8192 ((h + 1) + i)) t) path =
        .node G low high children) :
    G - min G
      (low + d2FlowCandidateQuota ((h + 1) + i) t i
        (d2FlowCandidateRole ((h + 1) + i) t i) / 2) = 0 := by
  classical
  let d := (h + 1) + i
  let run := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t
  let node := d2FlowTreeAtPath i run path
  have hcoreAll := d2FlowCandidateRun_affine_core_and_inv_all d hd t
  have hcore := hcoreAll.1
  change d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive d t k)
      (fun k => d2FlowCandidateRole d t k)
      (fun k => d2FlowCandidateCapacity d k t) 0 run at hcore
  have hlocal := d2FlowCandidateRun_core_provider_affine_atPath
    (h := h + 1) (i := i) (t := t) hd ht path hcore
  have hlocal' : d2FlowStageAffineInputs
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) i node := by
    simpa [d, run, node] using hlocal
  have hactiveSchedule : active d (tfD2 d) i t := by
    have haD : d2FlowCandidateActive d t i = true := by simpa [d] using ha
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (t := t) (i := i) ht
    rw [hmatch] at haD
    exact of_decide_eq_true haD
  have haD : d2FlowCandidateActive d t i = true := by simpa [d] using ha
  have hrD : d2FlowCandidateRole d t i = .topRise ∨
      d2FlowCandidateRole d t i = .mid ∨
      d2FlowCandidateRole d t i = .botDesc := by simpa [d] using hr
  have hroleSchedule : d2ScheduleRole d i t = .topRise ∨
      d2ScheduleRole d i t = .mid ∨ d2ScheduleRole d i t = .botDesc := by
    simpa [d, d2FlowCandidateRole, Nat.ne_of_gt ht] using hr
  have hroleEq : d2FlowCandidateRole d t i = d2ScheduleRole d i t :=
    d2FlowCandidateRole_matches_schedule ht
  have hlocalNode : d2FlowStageAffineInputs
      (d2FlowCandidateActive d t) (d2FlowCandidateRole d t)
      (d2FlowCandidateQuota d t)
      (fun k => d2FlowCandidateCapacity d k t) i
      (D2FlowTree.node G low high children) := by
    simpa [d, run, node, hnode] using hlocal'
  have hfields := d2FlowStageAffineInputs_ordinary_fields children
    hlocalNode haD hrD
  rcases hfields with ⟨_, _, heven, _, _, _, _, hprofile⟩
  have hdeficit : 8192 * G <= 15 * d2FlowCandidateCapacity d i t := by
    rcases hprofile with hzero | hstrong
    · rcases hzero with ⟨hGzero, _⟩
      simp [hGzero]
    · omega
  have hevenSchedule : d2FlowCandidateQuota d t i (d2ScheduleRole d i t) % 2 = 0 := by
    rw [← hroleEq]
    exact heven
  have hover := candidate_sender_two_front_overrun_zero_of_15over8192
    (d := d) (i := i) (t := t) (G := G) (low := low)
    (by omega) hactiveSchedule hroleSchedule hdeficit hevenSchedule
  rw [hroleEq.symm] at hover
  simpa [d] using hover

end Chvatal.D2Reserve
