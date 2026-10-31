import D2Stage17Frontier

namespace Chvatal.D2Reserve

theorem d2FlowCandidateStage18_alpha {d : Nat} (hd : 14 <= d) :
    alpha d 18 = (if d <= 15 then 2 else 0) :=
  d2FlowCandidateStage17_alpha_next hd

theorem d2FlowCandidateStage18_alpha_next {d : Nat} (hd : 14 <= d) :
    alpha d 19 = (if d <= 15 then 3 else 1) := by
  by_cases h14 : d = 14
  · subst d
    norm_num [alpha, alphaStar, ceilParity]
  · by_cases h15 : d = 15
    · subst d
      norm_num [alpha, alphaStar, ceilParity]
    · by_cases h16 : d = 16
      · subst d
        norm_num [alpha, alphaStar, ceilParity]
      · have h17 : 49 <= 3 * d := by omega
        simp [alpha, alphaStar, ceilParity, h17]
        omega

theorem d2FlowCandidateStage18_omega : omega 18 = 8 :=
  d2FlowCandidateStage17_omega_next

theorem d2FlowCandidateStage18_omega_next : omega 19 = 7 := by
  norm_num [omega, ceilParity]

/-- Stage 18 activates the even bands through level eight; at depths 14 and
15 the top level is the startup band two. -/
theorem d2FlowCandidateActive_stage18_iff {d i : Nat} (hd : 14 <= d) :
    d2FlowCandidateActive d 18 i = true <->
      (if d <= 15 then i = 2 \/ i = 4 \/ i = 6 \/ i = 8
       else i = 0 \/ i = 2 \/ i = 4 \/ i = 6 \/ i = 8) := by
  classical
  constructor
  · intro ha
    have hm := d2FlowCandidateActive_matches_schedule
      (d := d) (i := i) (t := 18) (by omega)
    rw [ha] at hm
    have hp : active d (tfD2 d) i 18 := of_decide_eq_true hm.symm
    unfold active at hp
    simp only [if_neg (by decide : (18 : Nat) ≠ 1)] at hp
    have hpar : i % 2 = 0 := by simpa using hp.2.2.1
    have hlo : 3 * i + 3 * d >= 47 := hp.2.2.2.1
    have hup : 3 * i < 26 := hp.2.2.2.2
    have hlevels : i = 0 \/ i = 2 \/ i = 4 \/ i = 6 \/ i = 8 := by omega
    by_cases hsmall : d <= 15
    · rcases hlevels with h | h | h | h | h
      · subst i
        simp at hlo
        omega
      · subst i; simp [hsmall]
      · subst i; simp [hsmall]
      · subst i; simp [hsmall]
      · subst i; simp [hsmall]
    · simpa [hsmall] using hlevels
  · intro hi
    have hm := d2FlowCandidateActive_matches_schedule
      (d := d) (i := i) (t := 18) (by omega)
    rw [hm]
    apply decide_eq_true
    have hprop : active d (tfD2 d) i 18 := by
      unfold active
      simp only [if_neg (by decide : (18 : Nat) ≠ 1)]
      have htf : 18 <= tfD2 d := by unfold tfD2; omega
      by_cases hsmall : d <= 15
      · simp [hsmall] at hi
        rcases hi with h | h | h | h <;> subst i
        all_goals exact ⟨by omega, htf, by norm_num, by omega, by omega⟩
      · simp [hsmall] at hi
        rcases hi with h | h | h | h | h <;> subst i
        all_goals exact ⟨by omega, htf, by norm_num, by omega, by omega⟩
    exact hprop

theorem d2FlowCandidateRole_stage18_top {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateRole d 18 (if d <= 15 then 2 else 0) = .topDesc := by
  have hmove : alpha d 18 < alpha d 19 := by
    rw [d2FlowCandidateStage18_alpha hd,
      d2FlowCandidateStage18_alpha_next hd]
    by_cases hsmall : d <= 15 <;> simp [hsmall]
  have htop : (if d <= 15 then 2 else 0) = alpha d 18 := by
    rw [d2FlowCandidateStage18_alpha hd]
  rw [d2FlowCandidateRole_matches_schedule
    (d := d) (i := if d <= 15 then 2 else 0) (t := 18) (by omega)]
  simp [d2ScheduleRole, htop, hmove]

theorem d2FlowCandidateRole_stage18_mid46 {d : Nat} (hd : 14 <= d)
    (i : Nat) (hi : i = 4 \/ i = 6) :
    d2FlowCandidateRole d 18 i = .mid := by
  have htop : i ≠ alpha d 18 := by
    rw [d2FlowCandidateStage18_alpha hd]
    rcases hi with rfl | rfl <;> by_cases hsmall : d <= 15 <;> simp [hsmall]
  have hbot : i ≠ omega 18 := by
    rw [d2FlowCandidateStage18_omega]
    rcases hi with rfl | rfl <;> omega
  rw [d2FlowCandidateRole_matches_schedule (d := d) (i := i) (t := 18) (by omega)]
  simp [d2ScheduleRole, htop, hbot]

theorem d2FlowCandidateRole_stage18_mid2 {d : Nat} (hd : 16 <= d) :
    d2FlowCandidateRole d 18 2 = .mid := by
  have hd14 : 14 <= d := by omega
  have htop : (2 : Nat) ≠ alpha d 18 := by
    rw [d2FlowCandidateStage18_alpha hd14]
    simp [show ¬ d <= 15 by omega]
  have hbot : (2 : Nat) ≠ omega 18 := by rw [d2FlowCandidateStage18_omega]; omega
  rw [d2FlowCandidateRole_matches_schedule (d := d) (i := 2) (t := 18) (by omega)]
  simp [d2ScheduleRole, htop, hbot]

theorem d2FlowCandidateRole_stage18_bottom {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateRole d 18 8 = .botRise := by
  have htop : (8 : Nat) ≠ alpha d 18 := by
    rw [d2FlowCandidateStage18_alpha hd]
    by_cases hsmall : d <= 15 <;> simp [hsmall]
  rw [d2FlowCandidateRole_matches_schedule (d := d) (i := 8) (t := 18) (by omega)]
  simp [d2ScheduleRole, htop, d2FlowCandidateStage18_omega,
    d2FlowCandidateStage18_omega_next]

end Chvatal.D2Reserve
