import D2Stage19Frontier

namespace Chvatal.D2Reserve

theorem d2FlowCandidateStage20_alpha {d : Nat} (hd : 16 <= d) :
    alpha d 20 = (if d = 16 then 2 else 0) := by
  have hd14 : 14 <= d := by omega
  rw [d2FlowCandidateStage19_alpha_next hd14]
  by_cases h16 : d = 16
  · subst d
    norm_num
  · have hnot14 : d ≠ 14 := by omega
    have hnotle16 : ¬ d ≤ 16 := by omega
    simp [h16, hnot14, hnotle16]

theorem d2FlowCandidateStage20_alpha_next {d : Nat} (hd : 16 <= d) :
    alpha d 21 = (if d = 16 then 3 else 1) := by
  by_cases h16 : d = 16
  · subst d
    norm_num [alpha, alphaStar, ceilParity]
  · by_cases h17 : d = 17
    · subst d
      norm_num [alpha, alphaStar, ceilParity]
    · have h18 : 18 <= d := by omega
      have hzero : 53 <= 3 * d := by omega
      simp [alpha, alphaStar, ceilParity, hzero, h16, h17]

theorem d2FlowCandidateStage20_omega : omega 20 = 8 :=
  d2FlowCandidateStage19_omega_next

theorem d2FlowCandidateStage20_omega_next : omega 21 = 9 := by
  norm_num [omega, ceilParity]

/-- For d >= 16, Stage 20 activates the even bands through level eight;
level two is the startup top only at d=16, and level zero is active from
d=17 onward. -/
theorem d2FlowCandidateActive_stage20_iff {d i : Nat} (hd : 16 <= d) :
    d2FlowCandidateActive d 20 i = true <->
      (if d = 16 then i = 2 ∨ i = 4 ∨ i = 6 ∨ i = 8
       else i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 6 ∨ i = 8) := by
  classical
  have hactive : active d (tfD2 d) i 20 <->
      (if d = 16 then i = 2 ∨ i = 4 ∨ i = 6 ∨ i = 8
       else i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 6 ∨ i = 8) := by
    have htf : 20 < tfD2 d := by unfold tfD2; omega
    rw [active_iff_frontiers (d := d) (tf := tfD2 d) (i := i)
      (t := 20) (by omega)]
    rw [d2FlowCandidateStage20_alpha hd,
      d2FlowCandidateStage20_omega]
    by_cases h16 : d = 16 <;> simp [h16, tfD2] <;> omega
  rw [d2FlowCandidateActive_matches_schedule
    (d := d) (i := i) (t := 20) (by omega)]
  constructor
  · intro h
    exact hactive.mp (of_decide_eq_true h)
  · intro h
    apply decide_eq_true
    exact hactive.mpr h

theorem d2FlowCandidateRole_stage20_top {d : Nat} (hd : 16 <= d) :
    d2FlowCandidateRole d 20 (if d = 16 then 2 else 0) = .topDesc := by
  have htop : (if d = 16 then 2 else 0) = alpha d 20 := by
    rw [d2FlowCandidateStage20_alpha hd]
  have hmove : alpha d 20 < alpha d 21 := by
    rw [d2FlowCandidateStage20_alpha hd,
      d2FlowCandidateStage20_alpha_next hd]
    by_cases h16 : d = 16 <;> simp [h16]
  rw [d2FlowCandidateRole_matches_schedule
    (d := d) (i := if d = 16 then 2 else 0) (t := 20) (by omega)]
  simp [d2ScheduleRole, htop, hmove]

theorem d2FlowCandidateRole_stage20_mid {d i : Nat} (hd : 16 <= d)
    (hi : (if d = 16 then 2 else 0) < i) (hbot : i < 8) :
    d2FlowCandidateRole d 20 i = .mid := by
  have htop : i ≠ alpha d 20 := by
    rw [d2FlowCandidateStage20_alpha hd]
    by_cases h16 : d = 16
    · simp [h16] at hi ⊢
      omega
    · simp [h16] at hi ⊢
      omega
  have hbottom : i ≠ omega 20 := by
    rw [d2FlowCandidateStage20_omega]
    omega
  rw [d2FlowCandidateRole_matches_schedule
    (d := d) (i := i) (t := 20) (by omega)]
  simp [d2ScheduleRole, htop, hbottom]

theorem d2FlowCandidateRole_stage20_bottom {d : Nat} (hd : 16 <= d) :
    d2FlowCandidateRole d 20 8 = .botDesc := by
  have htop : (8 : Nat) ≠ alpha d 20 := by
    rw [d2FlowCandidateStage20_alpha hd]
    by_cases h16 : d = 16 <;> simp [h16]
  have hbottom : omega 20 = (8 : Nat) := by
    exact d2FlowCandidateStage20_omega
  have hmove : omega 20 < omega 21 := by
    rw [d2FlowCandidateStage20_omega,
      d2FlowCandidateStage20_omega_next]
    omega
  rw [d2FlowCandidateRole_matches_schedule
    (d := d) (i := 8) (t := 20) (by omega)]
  simp [d2ScheduleRole, htop, hbottom,
    d2FlowCandidateStage20_omega_next]

end Chvatal.D2Reserve
