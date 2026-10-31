import D2ScheduleReserve

namespace Chvatal.D2Reserve

/-- At the first stage after the Stage-14 bootstrap, precisely the four odd
levels through seven are active. -/
theorem d2FlowCandidateActive_stage15_level_bound
    {d i : Nat} :
    d2FlowCandidateActive d 15 i = true ->
      i = 1 \/ i = 3 \/ i = 5 \/ i = 7 := by
  classical
  have hmatch := d2FlowCandidateActive_matches_schedule
    (d := d) (i := i) (t := 15) (by omega)
  intro h
  rw [hmatch] at h
  simp only [decide_eq_true_eq] at h
  simp only [active, if_neg (by decide : ¬ ((15 : Nat) = 1))] at h
  rcases h with ⟨_, htf, hpar, hlow, hhigh⟩
  norm_num at hpar hlow hhigh
  omega

/-- Each of the four possible Stage-15 active levels is actually present. -/
theorem d2FlowCandidateActive_stage15_at
    {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateActive d 15 1 = true /\
      d2FlowCandidateActive d 15 3 = true /\
      d2FlowCandidateActive d 15 5 = true /\
      d2FlowCandidateActive d 15 7 = true := by
  classical
  have htf : 15 <= tfD2 d := by unfold tfD2; omega
  have hact : forall i, (i = 1 \/ i = 3 \/ i = 5 \/ i = 7) ->
      active d (tfD2 d) i 15 := by
    intro i hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals
      unfold active
      simp only [if_neg (by decide : ¬ ((15 : Nat) = 1))]
      refine ⟨by omega, htf, by norm_num, by omega, by omega⟩
  have hbool (i : Nat) (hi : i = 1 \/ i = 3 \/ i = 5 \/ i = 7) :
      d2FlowCandidateActive d 15 i = true := by
    rw [d2FlowCandidateActive_matches_schedule
      (d := d) (i := i) (t := 15) (by omega)]
    exact decide_eq_true (hact i hi)
  exact ⟨hbool 1 (Or.inl rfl), hbool 3 (Or.inr (Or.inl rfl)),
    hbool 5 (Or.inr (Or.inr (Or.inl rfl))),
    hbool 7 (Or.inr (Or.inr (Or.inr rfl)) )⟩

theorem d2FlowCandidateActive_stage15_iff
    {d i : Nat} (hd : 14 <= d) :
    d2FlowCandidateActive d 15 i = true <->
      i = 1 \/ i = 3 \/ i = 5 \/ i = 7 := by
  constructor
  · exact d2FlowCandidateActive_stage15_level_bound
  · intro hi
    rcases d2FlowCandidateActive_stage15_at hd with
      ⟨h1, h3, h5, h7⟩
    rcases hi with rfl | rfl | rfl | rfl
    · exact h1
    · exact h3
    · exact h5
    · exact h7

theorem d2FlowCandidateRole_stage15_internal_mid
    {d : Nat} (hd : 14 <= d) (i : Nat)
    (hi : i = 3 \/ i = 5) :
    d2FlowCandidateRole d 15 i = .mid := by
  have halpha : alpha d 15 = 1 := by
    unfold alpha alphaStar
    have hzero : 2 * 15 + 11 <= 3 * d := by omega
    simp [hzero, ceilParity]
  have homega : omega 15 = 7 := by
    norm_num [omega, ceilParity]
  rw [d2FlowCandidateRole_matches_schedule (by omega)]
  rcases hi with rfl | rfl <;> simp [d2ScheduleRole, halpha, homega]

theorem d2FlowCandidateRole_stage15_bottom
    {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateRole d 15 7 = .botRise := by
  have htop : alpha d 15 = 1 := by
    unfold alpha alphaStar
    have hzero : 2 * 15 + 11 <= 3 * d := by omega
    simp [hzero, ceilParity]
  have hbot : omega 15 = 7 := by
    norm_num [omega, ceilParity]
  have hnext : omega 16 = 6 := by
    norm_num [omega, ceilParity]
  rw [d2FlowCandidateRole_matches_schedule (by omega)]
  simp [d2ScheduleRole, htop, hbot, hnext]

theorem d2FlowCandidateRole_stage15_top
    {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateRole d 15 1 = if d = 14 then .topDesc else .topRise := by
  have htop : alpha d 15 = 1 := by
    unfold alpha alphaStar
    have hzero : 2 * 15 + 11 <= 3 * d := by omega
    simp [hzero, ceilParity]
  have hnext : alpha d 16 = if d = 14 then 2 else 0 := by
    by_cases hd14 : d = 14
    · subst d
      norm_num [alpha, alphaStar, ceilParity]
    · have hd15 : 15 <= d := by omega
      have hzero : 2 * 16 + 11 <= 3 * d := by omega
      simp [alpha, alphaStar, ceilParity, hzero, hd14]
  rw [d2FlowCandidateRole_matches_schedule (by omega)]
  by_cases h14 : d = 14
  · subst d
    norm_num [d2ScheduleRole, alpha, alphaStar, ceilParity, omega]
  · have htopd : alpha d 15 = 1 := htop
    have hnextd : alpha d 16 = 0 := by simpa [h14] using hnext
    simp [d2ScheduleRole, htopd, hnextd, h14]

/-- The stage/level shift from a Stage-14 sender to the corresponding
Stage-15 parent reserve multiplies capacity by 32. -/
theorem d2FlowCandidateCapacity_stage14_child_eq_32_stage15_parent
    {d i : Nat} (hd : 14 <= d) :
    d2FlowCandidateCapacity d (i + 1) 14 =
      32 * d2FlowCandidateCapacity d i 15 := by
  have hexp : d2FlowCandidateCapacityExponent d (i + 1) 14 =
      d2FlowCandidateCapacityExponent d i 15 + 5 := by
    unfold d2FlowCandidateCapacityExponent
    omega
  rw [d2FlowCandidateCapacity, d2FlowCandidateCapacity, hexp, pow_add]
  norm_num
  ring

/-- At the active ordinary levels 4 and 6 of Stage 14, the scheduled quota
is exactly `15/4096` of that sender's capacity. -/
theorem d2FlowCandidateStage14_quota_exact_ratio
    {d i : Nat} (hd : 14 <= d)
    {r : D2Role} (hr : r = .mid \/ r = .botDesc) :
    4096 * d2FlowCandidateQuota d 14 (i + 1) r =
      15 * d2FlowCandidateCapacity d (i + 1) 14 := by
  have he : 12 <= d2FlowCandidateCapacityExponent d (i + 1) 14 := by
    unfold d2FlowCandidateCapacityExponent
    omega
  let e := d2FlowCandidateCapacityExponent d (i + 1) 14
  have hpow : 2 ^ 12 * 2 ^ (e - 12) = 2 ^ e := by
    calc
      2 ^ 12 * 2 ^ (e - 12) = 2 ^ (12 + (e - 12)) := by rw [pow_add]
      _ = 2 ^ e := by rw [show 12 + (e - 12) = e by omega]
  rcases hr with rfl | rfl
  all_goals
    simp only [d2FlowCandidateQuota, d2FlowCandidateCapacity]
    change 4096 * (15 * 2 ^ (e - 12)) = 15 * 2 ^ e
    calc
      4096 * (15 * 2 ^ (e - 12)) = 15 * (2 ^ 12 * 2 ^ (e - 12)) := by
        norm_num
        ring
      _ = 15 * 2 ^ e := by rw [hpow]

/-- The quota added by that Stage-14 sender is more than enough to furnish
the `1/128` endpoint reserve at the corresponding Stage-15 parent. -/
theorem d2FlowCandidateStage14_quota_funds_stage15_parent_reserve
    {d i G : Nat} (hd : 14 <= d)
    {r : D2Role} (hr : r = .mid \/ r = .botDesc) :
    d2FlowCandidateCapacity d i 15 <=
      128 * (G + d2FlowCandidateQuota d 14 (i + 1) r) := by
  have hscale := d2FlowCandidateCapacity_stage14_child_eq_32_stage15_parent
    (i := i) hd
  have hquota := d2FlowCandidateStage14_quota_exact_ratio
    (i := i) hd hr
  nlinarith

/-- The preceding scale calculation applies to the actual local Stage-14
tree transition: an active mid or bottom-descending sender's updated root
deficit furnishes the endpoint reserve needed one level above at Stage 15. -/
theorem d2FlowCandidateStage14_sender_output_funds_stage15_reserve
    {d i h G low high : Nat} (hd : 14 <= d)
    {r : D2Role} (hr : r = .mid \/ r = .botDesc)
    (children : Fin 8 -> D2FlowTree h)
    (hactive : d2FlowCandidateActive d 14 (i + 1) = true)
    (hrole : d2FlowCandidateRole d 14 (i + 1) = r) :
    d2FlowCandidateCapacity d i 15 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowStage (d2FlowCandidateActive d 14)
          (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
          (h + 1) (i + 1) (.node G low high children)) := by
  have hfund := d2FlowCandidateStage14_quota_funds_stage15_parent_reserve
    (d := d) (i := i) (G := G) hd hr
  have hpost := d2FlowStage_active_node_deficit
    (active := d2FlowCandidateActive d 14)
    (role := d2FlowCandidateRole d 14)
    (quota := d2FlowCandidateQuota d 14)
    (h := h) (i := i + 1) (G := G) (low := low) (high := high)
    children hactive
  have hpost' : d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive d 14)
        (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
        (h + 1) (i + 1) (.node G low high children)) =
      G + d2FlowCandidateQuota d 14 (i + 1) r := by
    rcases hr with hrmid | hrdesc
    · have hrole' : d2FlowCandidateRole d 14 (i + 1) = .mid :=
        hrole.trans hrmid
      simpa [hrole', hrmid] using hpost
    · have hrole' : d2FlowCandidateRole d 14 (i + 1) = .botDesc :=
        hrole.trans hrdesc
      simpa [hrole', hrdesc] using hpost
  nlinarith

/-- The actual Stage-14 children of Stage-15's middle senders are active
ordinary senders: level four is mid and level six is bottom-descending. -/
theorem d2FlowCandidateStage14_reserve_sender_roles
    {d : Nat} (hd : 14 <= d) :
    d2FlowCandidateActive d 14 4 = true /\
      d2FlowCandidateRole d 14 4 = .mid /\
      d2FlowCandidateActive d 14 6 = true /\
      d2FlowCandidateRole d 14 6 = .botDesc := by
  classical
  have htf : 14 <= tfD2 d := by unfold tfD2; omega
  have hAlpha14 : alpha d 14 = 0 := by
    unfold alpha alphaStar
    have hzero : 2 * 14 + 11 <= 3 * d := by omega
    simp [hzero, ceilParity]
  have hAlpha15 : alpha d 15 = 1 := by
    unfold alpha alphaStar
    have hzero : 2 * 15 + 11 <= 3 * d := by omega
    simp [hzero, ceilParity]
  have hOmega14 : omega 14 = 6 := by norm_num [omega, ceilParity]
  have hOmega15 : omega 15 = 7 := by norm_num [omega, ceilParity]
  have hactive (i : Nat) (hi : i = 4 \/ i = 6) :
      d2FlowCandidateActive d 14 i = true := by
    have hprop : active d (tfD2 d) i 14 := by
      unfold active
      simp only [if_neg (by decide : ¬ ((14 : Nat) = 1))]
      rcases hi with rfl | rfl
      all_goals
        refine ⟨by omega, htf, by norm_num, by omega, by omega⟩
    rw [d2FlowCandidateActive_matches_schedule
      (d := d) (i := i) (t := 14) (by omega)]
    exact decide_eq_true hprop
  have hrole4 : d2FlowCandidateRole d 14 4 = .mid := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, hAlpha14, hOmega14]
  have hrole6 : d2FlowCandidateRole d 14 6 = .botDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, hAlpha14, hOmega14, hOmega15]
  exact ⟨hactive 4 (Or.inl rfl), hrole4,
    hactive 6 (Or.inr rfl), hrole6⟩

/-- For the concrete Stage-14 schedule, the post-update level-four root
supplies the left/right reserve required at a Stage-15 level-three sender. -/
theorem d2FlowCandidateStage14_levelFour_funds_stage15_levelThree_reserve
    {d h G low high : Nat} (hd : 14 <= d)
    (children : Fin 8 -> D2FlowTree h) :
    d2FlowCandidateCapacity d 3 15 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowStage (d2FlowCandidateActive d 14)
          (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
          (h + 1) 4 (.node G low high children)) := by
  rcases d2FlowCandidateStage14_reserve_sender_roles hd with
    ⟨_, hrole4, _, _⟩
  exact d2FlowCandidateStage14_sender_output_funds_stage15_reserve
    (d := d) (i := 3) (h := h) (G := G) (low := low) (high := high)
    hd (r := .mid) (Or.inl rfl) children
    (d2FlowCandidateStage14_reserve_sender_roles hd).1 hrole4

/-- Likewise, the post-update level-six root supplies the endpoint reserve
required at a Stage-15 level-five sender. -/
theorem d2FlowCandidateStage14_levelSix_funds_stage15_levelFive_reserve
    {d h G low high : Nat} (hd : 14 <= d)
    (children : Fin 8 -> D2FlowTree h) :
    d2FlowCandidateCapacity d 5 15 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowStage (d2FlowCandidateActive d 14)
          (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
          (h + 1) 6 (.node G low high children)) := by
  rcases d2FlowCandidateStage14_reserve_sender_roles hd with
    ⟨_, _, _, hrole6⟩
  exact d2FlowCandidateStage14_sender_output_funds_stage15_reserve
    (d := d) (i := 5) (h := h) (G := G) (low := low) (high := high)
    hd (r := .botDesc) (Or.inr rfl) children
    (d2FlowCandidateStage14_reserve_sender_roles hd).2.2.1 hrole6

end Chvatal.D2Reserve
