import D2Stage18Frontier

namespace Chvatal.D2Reserve

theorem d2FlowCandidateStage19_alpha {d : Nat} (hd : 14 <= d) :
    alpha d 19 = (if d <= 15 then 3 else 1) :=
  d2FlowCandidateStage18_alpha_next hd

theorem d2FlowCandidateStage19_alpha_next {d : Nat} (hd : 14 <= d) :
    alpha d 20 = if d = 14 then 4 else if d <= 16 then 2 else 0 := by
  by_cases h14 : d = 14
  · subst d
    norm_num [alpha, alphaStar, ceilParity]
  · by_cases h15 : d = 15
    · subst d
      norm_num [alpha, alphaStar, ceilParity]
    · by_cases h16 : d = 16
      · subst d
        norm_num [alpha, alphaStar, ceilParity]
      · have h17 : 51 <= 3 * d := by omega
        have hgt : 16 < d := by omega
        have hnot16 : ¬ d <= 16 := by omega
        simp [alpha, alphaStar, ceilParity, h17, h14, hnot16]

theorem d2FlowCandidateStage19_omega : omega 19 = 7 :=
  d2FlowCandidateStage18_omega_next

theorem d2FlowCandidateStage19_omega_next : omega 20 = 8 := by
  norm_num [omega, ceilParity]

/-- Stage 19 activates the odd bands through level seven. The top startup
band is level three at depths 14-15, then level one. -/
theorem d2FlowCandidateActive_stage19_iff {d i : Nat} (hd : 14 <= d) :
    d2FlowCandidateActive d 19 i = true <->
      (if d <= 15 then i = 3 \/ i = 5 \/ i = 7
       else i = 1 \/ i = 3 \/ i = 5 \/ i = 7) := by
  classical
  have hactive : active d (tfD2 d) i 19 <->
      (if d <= 15 then i = 3 \/ i = 5 \/ i = 7
       else i = 1 \/ i = 3 \/ i = 5 \/ i = 7) := by
    have htf : 19 <= tfD2 d := by unfold tfD2; omega
    rw [active_iff_frontiers (d := d) (tf := tfD2 d) (i := i)
      (t := 19) (by omega)]
    rw [d2FlowCandidateStage19_alpha hd,
      d2FlowCandidateStage19_omega]
    by_cases hsmall : d <= 15
    · simp [hsmall]
      omega
    · simp [hsmall]
      omega
  rw [d2FlowCandidateActive_matches_schedule
    (d := d) (i := i) (t := 19) (by omega)]
  constructor
  · intro h
    exact hactive.mp (of_decide_eq_true h)
  · intro h
    apply decide_eq_true
    exact hactive.mpr h

theorem d2FlowCandidateRole_stage19_top {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateRole d 19 (if d <= 15 then 3 else 1) =
      (if d = 14 then .topDesc else if d = 16 then .topDesc else .topRise) := by
  have htop : (if d <= 15 then 3 else 1) = alpha d 19 := by
    rw [d2FlowCandidateStage19_alpha hd]
  rw [d2FlowCandidateRole_matches_schedule
    (d := d) (i := if d <= 15 then 3 else 1) (t := 19) (by omega)]
  rw [d2ScheduleRole, if_pos htop]
  rw [d2FlowCandidateStage19_alpha hd,
    d2FlowCandidateStage19_alpha_next hd]
  by_cases h14 : d = 14
  · simp [h14]
  · by_cases h15 : d = 15
    · simp [h14, h15]
    · by_cases h16 : d = 16
      · simp [h14, h15, h16]
      · have hgt : 16 < d := by omega
        have hnot16 : ¬ d <= 16 := by omega
        have hnot15 : ¬ d <= 15 := by omega
        simp [hnot16, hnot15, h14, h16]

theorem d2FlowCandidateRole_stage19_mid {d : Nat} (hd : 14 <= d)
    (hi : (if d <= 15 then 3 else 1) < i) (hbot : i < 7) :
    d2FlowCandidateRole d 19 i = .mid := by
  have htop : i ≠ alpha d 19 := by
    rw [d2FlowCandidateStage19_alpha hd]
    exact Nat.ne_of_gt hi
  have hbottom : i ≠ omega 19 := by
    rw [d2FlowCandidateStage19_omega]
    omega
  rw [d2FlowCandidateRole_matches_schedule
    (d := d) (i := i) (t := 19) (by omega)]
  simp [d2ScheduleRole, htop, hbottom]

theorem d2FlowCandidateRole_stage19_bottom {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateRole d 19 7 = .botDesc := by
  have htop : (7 : Nat) ≠ alpha d 19 := by
    rw [d2FlowCandidateStage19_alpha hd]
    by_cases hsmall : d <= 15 <;> simp [hsmall]
  rw [d2FlowCandidateRole_matches_schedule (d := d) (i := 7) (t := 19) (by omega)]
  simp [d2ScheduleRole, htop, d2FlowCandidateStage19_omega,
    d2FlowCandidateStage19_omega_next]

end Chvatal.D2Reserve
