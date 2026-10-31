import D2Stage15Frontier

namespace Chvatal.D2Reserve

set_option linter.constructorNameAsVariable false

theorem d2FlowCandidateStage16_alpha
    {d : Nat} (hd : 14 <= d) :
    alpha d 16 = (if d = 14 then 2 else 0) := by
  by_cases h14 : d = 14
  · subst d
    norm_num [alpha, alphaStar, ceilParity]
  · have hd15 : 15 <= d := by omega
    have hzero : 2 * 16 + 11 <= 3 * d := by omega
    simp [alpha, alphaStar, hzero, ceilParity, h14]

theorem d2FlowCandidateStage16_alpha_next
    {d : Nat} (hd : 14 <= d) : alpha d 17 = 1 := by
  by_cases h14 : d = 14
  · subst d
    norm_num [alpha, alphaStar, ceilParity]
  · have hd15 : 15 <= d := by omega
    have hzero : 2 * 17 + 11 <= 3 * d := by omega
    simp [alpha, alphaStar, hzero, ceilParity]

theorem d2FlowCandidateStage16_omega : omega 16 = 6 := by
  norm_num [omega, ceilParity]

theorem d2FlowCandidateStage16_omega_next : omega 17 = 7 := by
  norm_num [omega, ceilParity]

/-- At Stage 16 the active frontier is the even band 0,2,4,6, except at
the minimum depth 14 where its top endpoint is level two. -/
theorem d2FlowCandidateActive_stage16_iff
    {d i : Nat} (hd : 14 <= d) :
    d2FlowCandidateActive d 16 i = true <->
      (if d = 14 then i = 2 \/ i = 4 \/ i = 6
       else i = 0 \/ i = 2 \/ i = 4 \/ i = 6) := by
  classical
  constructor
  · intro ha
    have hm := d2FlowCandidateActive_matches_schedule
      (d := d) (i := i) (t := 16) (by omega)
    rw [ha] at hm
    have hprop : active d (tfD2 d) i 16 := of_decide_eq_true hm.symm
    unfold active at hprop
    simp only [if_neg (by decide : (16 : Nat) ≠ 1)] at hprop
    rcases hprop with ⟨_, _, hpar, hlow, hup⟩
    have hi8 : i < 8 := by omega
    have hparEven : i % 2 = 0 := by simpa using hpar
    have hlevels : i = 0 \/ i = 2 \/ i = 4 \/ i = 6 := by omega
    by_cases h14 : d = 14
    · rcases hlevels with h | h | h | h
      · subst i
        omega
      · simpa [h14, h]
      · simpa [h14, h]
      · simpa [h14, h]
    · simpa [h14] using hlevels
  · intro hi
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (i := i) (t := 16) (by omega)
    rw [hmatch]
    apply decide_eq_true
    have hprop : active d (tfD2 d) i 16 := by
      unfold active
      simp only [if_neg (by decide : (16 : Nat) ≠ 1)]
      have htf : 16 <= tfD2 d := by unfold tfD2; omega
      by_cases h14 : d = 14
      · simp [h14] at hi
        rcases hi with h | h | h <;> subst i
        all_goals exact ⟨by omega, htf, by norm_num, by omega, by omega⟩
      · simp [h14] at hi
        rcases hi with h | h | h | h <;> subst i
        all_goals exact ⟨by omega, htf, by norm_num, by omega, by omega⟩
    exact hprop

theorem d2FlowCandidateRole_stage16_top
    {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateRole d 16 (if d = 14 then 2 else 0) =
      (if d = 14 then .topRise else .topDesc) := by
  by_cases h14 : d = 14
  · subst d
    change d2FlowCandidateRole 14 16 2 = D2Role.topRise
    rw [d2FlowCandidateRole_matches_schedule (d := 14) (t := 16) (i := 2) (by omega)]
    norm_num [d2ScheduleRole, alpha, alphaStar, ceilParity, omega]
  · have hzero16 : 2 * 16 + 11 <= 3 * d := by omega
    have hzero17 : 2 * 17 + 11 <= 3 * d := by omega
    simp only [if_neg h14]
    rw [d2FlowCandidateRole_matches_schedule (d := d) (t := 16) (i := 0) (by omega)]
    simp [d2ScheduleRole, alpha, alphaStar, ceilParity, omega, hzero16, hzero17, h14]

theorem d2FlowCandidateRole_stage16_internal_mid
    {d i : Nat} (hd : 15 <= d) (hi : i = 2 \/ i = 4) :
    d2FlowCandidateRole d 16 i = .mid := by
  have hzero16 : 2 * 16 + 11 <= 3 * d := by omega
  have hzero17 : 2 * 17 + 11 <= 3 * d := by omega
  rcases hi with rfl | rfl
  · rw [d2FlowCandidateRole_matches_schedule (d := d) (t := 16) (i := 2) (by omega)]
    simp [d2ScheduleRole, alpha, alphaStar, ceilParity, omega, hzero16, hzero17]
  · rw [d2FlowCandidateRole_matches_schedule (d := d) (t := 16) (i := 4) (by omega)]
    simp [d2ScheduleRole, alpha, alphaStar, ceilParity, omega, hzero16, hzero17]

theorem d2FlowCandidateRole_stage16_bottom
    {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateRole d 16 6 = .botDesc := by
  by_cases h14 : d = 14
  · subst d
    rw [d2FlowCandidateRole_matches_schedule (d := 14) (t := 16) (i := 6) (by omega)]
    norm_num [d2ScheduleRole, alpha, alphaStar, ceilParity, omega]
  · have hzero16 : 2 * 16 + 11 <= 3 * d := by omega
    have hzero17 : 2 * 17 + 11 <= 3 * d := by omega
    rw [d2FlowCandidateRole_matches_schedule (d := d) (t := 16) (i := 6) (by omega)]
    simp [d2ScheduleRole, alpha, alphaStar, ceilParity, omega, hzero16, hzero17, h14]

end Chvatal.D2Reserve
