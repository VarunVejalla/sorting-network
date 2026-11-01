import D2ScheduleReserve
namespace Chvatal.D2Reserve
set_option linter.unusedVariables false

theorem alpha_at_tf_values {d : Nat} (hd : 7 <= d) :
    alpha d (tfD2 d) = d - 4 /\
    alpha d (tfD2 d - 2) = d - 6 := by
  have htime2 : tfD2 d - 2 = 3 * d - 16 := by
    unfold tfD2
    omega
  have hn1 : ¬ (2 * (3 * d - 14) + 11 <= 3 * d) := by omega
  have hs1 : alphaStar d (3 * d - 14) = d - 5 := by
    unfold alphaStar
    rw [if_neg hn1]
    omega
  have hs2 : alphaStar d (3 * d - 16) = d - 7 := by
    by_cases h7 : d = 7
    · subst d
      norm_num [alphaStar]
    · have hn2 : ¬ (2 * (3 * d - 16) + 11 <= 3 * d) := by omega
      unfold alphaStar
      rw [if_neg hn2]
      omega
  have hp1 : (d - 5) % 2 ≠ (3 * d - 14) % 2 := by omega
  have hp2 : (d - 7) % 2 ≠ (3 * d - 16) % 2 := by omega
  constructor
  · rw [show tfD2 d = 3 * d - 14 by rfl]
    have ht0 : 3 * d - 14 ≠ 0 := by omega
    have ht1 : 3 * d - 14 ≠ 1 := by omega
    rw [show alpha d (3 * d - 14) = ceilParity (alphaStar d (3 * d - 14)) (3 * d - 14) by
      simp [alpha, ht0, ht1]]
    rw [hs1]
    simp [ceilParity, hp1]
    omega
  · rw [htime2]
    have ht0 : 3 * d - 16 ≠ 0 := by omega
    have ht1 : 3 * d - 16 ≠ 1 := by omega
    rw [show alpha d (3 * d - 16) = ceilParity (alphaStar d (3 * d - 16)) (3 * d - 16) by
      simp [alpha, ht0, ht1]]
    rw [hs2]
    simp [ceilParity, hp2]
    omega

/-- At the terminal stage, a regular active node remains active two stages
earlier; that predecessor cannot be top-descending. -/
theorem active_regular_prev_two_role_cases_at_tf {d i : Nat}
    (hd : 7 <= d) (ha : active d (tfD2 d) i (tfD2 d))
    (hrole : d2ScheduleRole d i (tfD2 d) = .topRise \/
      d2ScheduleRole d i (tfD2 d) = .mid \/
      d2ScheduleRole d i (tfD2 d) = .botDesc) :
    active d (tfD2 d) i (tfD2 d - 2) /\
      (d2ScheduleRole d i (tfD2 d - 2) = .topRise \/
       d2ScheduleRole d i (tfD2 d - 2) = .mid \/
       d2ScheduleRole d i (tfD2 d - 2) = .botDesc \/
       d2ScheduleRole d i (tfD2 d - 2) = .botRise) := by
  have htv := alpha_at_tf_values hd
  have hfront := (active_iff_frontiers (d := d) (tf := tfD2 d)
    (i := i) (t := tfD2 d) (by unfold tfD2; omega)).1 ha
  have hi : i = d - 4 := by
    have hmeet := frontiers_meet_at_tf hd
    have how : omega (tfD2 d) = d - 4 := hmeet.symm.trans htv.1
    omega
  have hnotBot : Not (botRiseBoundary i (tfD2 d)) := by
    unfold botRiseBoundary
    rw [hi]
    unfold tfD2
    omega
  have hprev := active_prev_two_of_not_botRise (by unfold tfD2; omega) ha hnotBot
  have hprevAlpha : alpha d (tfD2 d - 2) = d - 6 := htv.2
  have hnotTop : Not (d2ScheduleRole d i (tfD2 d - 2) = .topDesc) := by
    intro hp
    have heq : i = alpha d (tfD2 d - 2) := by
      unfold d2ScheduleRole at hp
      by_cases hbound : i = alpha d (tfD2 d - 2)
      · exact hbound
      · by_cases hbot : i = omega (tfD2 d - 2)
        · have hneq : omega (tfD2 d - 2) ≠ alpha d (tfD2 d - 2) := by
            rw [← hbot, hi, hprevAlpha]
            omega
          simp [hbound, hbot, hneq] at hp
          split_ifs at hp <;> cases hp
        · simp [hbound, hbot] at hp
    rw [hi, hprevAlpha] at heq
    omega
  refine ⟨hprev, ?_⟩
  cases hr : d2ScheduleRole d i (tfD2 d - 2) with
  | topDesc => exact False.elim (hnotTop hr)
  | topRise => exact Or.inl (by simpa [hr])
  | mid => exact Or.inr (Or.inl (by simpa [hr]))
  | botDesc => exact Or.inr (Or.inr (Or.inl (by simpa [hr])))
  | botRise => exact Or.inr (Or.inr (Or.inr (by simpa [hr])))

/-- Two-visit role classification including the terminal stage. -/
theorem active_regular_prev_two_role_cases_le {d i t : Nat}
    (hd : 7 <= d) (ht : 4 <= t) (htf : t <= tfD2 d)
    (ha : active d (tfD2 d) i t)
    (hrole : d2ScheduleRole d i t = .topRise \/
      d2ScheduleRole d i t = .mid \/ d2ScheduleRole d i t = .botDesc) :
    active d (tfD2 d) i (t - 2) /\
      (d2ScheduleRole d i (t - 2) = .topRise \/
       d2ScheduleRole d i (t - 2) = .mid \/
       d2ScheduleRole d i (t - 2) = .botDesc \/
       d2ScheduleRole d i (t - 2) = .botRise) := by
  by_cases hlt : t < tfD2 d
  · exact active_regular_prev_two_role_cases hd ht hlt ha hrole
  · have heq : t = tfD2 d := by omega
    subst t
    exact active_regular_prev_two_role_cases_at_tf hd ha hrole
end Chvatal.D2Reserve
