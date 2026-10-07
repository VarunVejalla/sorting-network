module

/-
  # Chvátal §3 integer flow table (DCS-TR-294 pp. 7–9)

  Between times `t` and `t+1` each node on level `i` sends `flowUp` wires to its parent
  (the fringe blocks `F₁ ∪ F₂`) and `flowDown` wires to each of its `br` children
  (a block `B_j`). Formulas (`c = capacity`, `Q = A²·br²`, `k = br`), for `2 ≤ t < tf`:
  * `i = α t`, top descends (`α t < α (t+1)`): `π = 0`, `τ = c/k`;
  * `i = α t`, top rises: `π = ν c/(A k)`, `τ = (A k − ν) c/(A k²)`;
  * `α t < i < ω t`: `π = (A ν k − 1) c/Q`, `τ = (A k − ν) c/(A k²)`;
  * `i = ω t`, bottom descends: `π = (A ν k − 1) c/Q`, `τ = a(ω t + 1, t + 1)`;
  * `i = ω t`, bottom rises: `π = a(ω t, t)`, `τ = 0`.
  These identities were verified with exact rational arithmetic for `d = 14, 15, 20, 30`.
-/

public import AKS.Chvatal.Scheduler

@[expose] public section

namespace Chvatal

/-- Wires a node on level `i` sends to its parent between times `t` and `t+1`. -/
def flowUp (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d) (i t : Nat) : Rat :=
  if ¬(t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2) then 0
  else if i = sched.alpha t then
    (if sched.alpha t < sched.alpha (t + 1) then 0
     else p.nu * capacity p d i t / (p.A * (p.br : Rat)))
  else if i = sched.omega t then
    (if sched.omega t < sched.omega (t + 1) then
      (p.A * p.nu * (p.br : Rat) - 1) * capacity p d i t / capacityRatio p
     else allocation p d sched i t)
  else (p.A * p.nu * (p.br : Rat) - 1) * capacity p d i t / capacityRatio p

/-- Wires a node on level `i` sends to each of its `br` children between `t` and `t+1`. -/
def flowDown (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d) (i t : Nat) : Rat :=
  if ¬(t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2) then 0
  else if i = sched.alpha t then
    (if sched.alpha t < sched.alpha (t + 1) then capacity p d i t / (p.br : Rat)
     else (p.A * (p.br : Rat) - p.nu) * capacity p d i t / (p.A * (p.br : Rat) ^ 2))
  else if i = sched.omega t then
    (if sched.omega t < sched.omega (t + 1) then
      allocation p d sched (sched.omega t + 1) (t + 1)
     else 0)
  else (p.A * (p.br : Rat) - p.nu) * capacity p d i t / (p.A * (p.br : Rat) ^ 2)

/-- **B1 (send identity).** Every node sends out exactly its wires:
    `a(i,t) = π(i,t) + br · τ(i,t)` for `2 ≤ t`, `t + 1 < tf`, given `α s < ω s` for
    `2 ≤ s < tf`. -/
theorem allocation_eq_flowUp_add_flowDown (p : ScheduleParams) (d : Nat)
    (sched : LevelSchedule p d)
    (hlt : ∀ s, 2 ≤ s → s < sched.tf → sched.alpha s < sched.omega s)
    (t : Nat) (ht2 : 2 ≤ t) (ht : t + 1 < sched.tf) (i : Nat) :
    allocation p d sched i t =
      flowUp p d sched i t + (p.br : Rat) * flowDown p d sched i t := by
  by_cases hactive : t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2
  swap
  · rw [allocation_inactive p d sched i t hactive]
    simp [flowUp, flowDown, hactive]
  have h_alloc : ¬¬(t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2) :=
    not_not.mpr hactive
  have hA := p.A_pos
  have hbr := p.br_cast_pos
  have hnu := p.hnu_pos
  have hc := capacity_pos p d i t
  have hQ : capacityRatio p = p.A ^ 2 * (p.br : Rat) ^ 2 := rfl
  by_cases hα : i = sched.alpha t
  · have hal : allocation p d sched i t = capacity p d i t := by
      unfold allocation; rw [if_pos hactive, if_pos hα]
    by_cases hstep : sched.alpha t < sched.alpha (t + 1)
    · simp only [flowUp, flowDown, if_neg h_alloc, if_pos hα, if_pos hstep]
      rw [hal]; field_simp; simp
    · simp only [flowUp, flowDown, if_neg h_alloc, if_pos hα, if_neg hstep]
      rw [hal]; field_simp; ring
  by_cases hω : i = sched.omega t
  · have hal : allocation p d sched i t =
        (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ i - capacity p d i t / capacityRatio p := by
      unfold allocation; rw [if_pos hactive, if_neg hα, if_pos hω]
    by_cases hstep : sched.omega t < sched.omega (t + 1)
    · have hsucc : sched.omega (t + 1) = sched.omega t + 1 := by
        have h1 := sched.omega_step t (by omega)
        have h2 := sched.omega_parity (t + 1) (by omega)
        have h3 := sched.omega_parity t hactive.1
        omega
      have hα1 : sched.alpha (t + 1) < sched.omega t + 1 := by
        have := hlt (t + 1) (by omega) ht
        omega
      have hact1 : t + 1 ≤ sched.tf ∧ sched.alpha (t + 1) ≤ sched.omega t + 1 ∧
          sched.omega t + 1 ≤ sched.omega (t + 1) ∧ (sched.omega t + 1) % 2 = (t + 1) % 2 := by
        have h3 := sched.omega_parity t hactive.1
        refine ⟨by omega, by omega, by omega, by omega⟩
      have hal1 : allocation p d sched (sched.omega t + 1) (t + 1) =
          (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ (sched.omega t + 1) -
            capacity p d (sched.omega t + 1) (t + 1) / capacityRatio p := by
        unfold allocation
        rw [if_pos hact1, if_neg (by omega), if_pos hsucc.symm]
      have hcap1 : capacity p d (sched.omega t + 1) (t + 1) =
          p.nu * (p.A * capacity p d (sched.omega t) t) := by
        rw [capacity_succ_stage, capacity_succ_level]
      simp only [flowUp, flowDown, if_neg h_alloc, if_neg hα, if_pos hω, if_pos hstep]
      rw [hal, hal1, hcap1, hω]
      simp only [Nat.cast_pow] at *
      rw [hQ]
      field_simp
      ring
    · simp only [flowUp, flowDown, if_neg h_alloc, if_neg hα, if_pos hω, if_neg hstep]
      ring
  · have hal : allocation p d sched i t = (1 - 1 / capacityRatio p) * capacity p d i t := by
      unfold allocation; rw [if_pos hactive, if_neg hα, if_neg hω]
    simp only [flowUp, flowDown, if_neg h_alloc, if_neg hα, if_neg hω]
    rw [hal, hQ]
    field_simp
    ring

/-! ## Role lemmas (for the conservation proof) -/

section Roles

variable (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d)

theorem flowDown_inactive {i t : Nat}
    (h : ¬(t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2)) :
    flowDown p d sched i t = 0 := by simp [flowDown, h]

theorem flowUp_inactive {i t : Nat}
    (h : ¬(t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2)) :
    flowUp p d sched i t = 0 := by simp [flowUp, h]

/-- Interior-type child send (also valid for a rising top and for a descending bottom). -/
theorem flowDown_mid {i t : Nat}
    (h : t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2)
    (hα : i = sched.alpha t → ¬ sched.alpha t < sched.alpha (t + 1))
    (hω : i ≠ sched.omega t) :
    flowDown p d sched i t =
      (p.A * (p.br : Rat) - p.nu) * capacity p d i t / (p.A * (p.br : Rat) ^ 2) := by
  by_cases hi : i = sched.alpha t
  · simp only [flowDown, if_neg (not_not.mpr h), if_pos hi, if_neg (hα hi)]
  · simp only [flowDown, if_neg (not_not.mpr h), if_neg hi, if_neg hω]

theorem flowDown_top_desc {i t : Nat}
    (h : t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2)
    (hα : i = sched.alpha t) (hs : sched.alpha t < sched.alpha (t + 1)) :
    flowDown p d sched i t = capacity p d i t / (p.br : Rat) := by
  simp only [flowDown, if_neg (not_not.mpr h), if_pos hα, if_pos hs]

theorem flowDown_bot_desc {i t : Nat}
    (h : t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2)
    (hα : i ≠ sched.alpha t) (hω : i = sched.omega t)
    (hs : sched.omega t < sched.omega (t + 1)) :
    flowDown p d sched i t = allocation p d sched (sched.omega t + 1) (t + 1) := by
  simp only [flowDown, if_neg (not_not.mpr h), if_neg hα, if_pos hω, if_pos hs]

theorem flowDown_bot_rise {i t : Nat}
    (h : t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2)
    (hα : i ≠ sched.alpha t) (hω : i = sched.omega t)
    (hs : ¬ sched.omega t < sched.omega (t + 1)) :
    flowDown p d sched i t = 0 := by
  simp only [flowDown, if_neg (not_not.mpr h), if_neg hα, if_pos hω, if_neg hs]

/-- Interior-type parent send (also valid for a descending bottom). -/
theorem flowUp_mid {i t : Nat}
    (h : t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2)
    (hα : i ≠ sched.alpha t)
    (hω : i = sched.omega t → sched.omega t < sched.omega (t + 1)) :
    flowUp p d sched i t =
      (p.A * p.nu * (p.br : Rat) - 1) * capacity p d i t / capacityRatio p := by
  by_cases hi : i = sched.omega t
  · simp only [flowUp, if_neg (not_not.mpr h), if_neg hα, if_pos hi, if_pos (hω hi)]
  · simp only [flowUp, if_neg (not_not.mpr h), if_neg hα, if_neg hi]

theorem flowUp_top_desc {i t : Nat}
    (h : t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2)
    (hα : i = sched.alpha t) (hs : sched.alpha t < sched.alpha (t + 1)) :
    flowUp p d sched i t = 0 := by
  simp only [flowUp, if_neg (not_not.mpr h), if_pos hα, if_pos hs]

theorem flowUp_top_rise {i t : Nat}
    (h : t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2)
    (hα : i = sched.alpha t) (hs : ¬ sched.alpha t < sched.alpha (t + 1)) :
    flowUp p d sched i t = p.nu * capacity p d i t / (p.A * (p.br : Rat)) := by
  simp only [flowUp, if_neg (not_not.mpr h), if_pos hα, if_neg hs]

theorem flowUp_bot_rise {i t : Nat}
    (h : t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2)
    (hα : i ≠ sched.alpha t) (hω : i = sched.omega t)
    (hs : ¬ sched.omega t < sched.omega (t + 1)) :
    flowUp p d sched i t = allocation p d sched i t := by
  simp only [flowUp, if_neg (not_not.mpr h), if_neg hα, if_pos hω, if_neg hs]

theorem alloc_top {i t : Nat}
    (h : t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2)
    (hα : i = sched.alpha t) :
    allocation p d sched i t = capacity p d i t := by
  unfold allocation; rw [if_pos h, if_pos hα]

theorem alloc_bot {i t : Nat}
    (h : t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2)
    (hα : i ≠ sched.alpha t) (hω : i = sched.omega t) :
    allocation p d sched i t =
      (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ i - capacity p d i t / capacityRatio p := by
  unfold allocation; rw [if_pos h, if_neg hα, if_pos hω]

theorem alloc_mid {i t : Nat}
    (h : t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2)
    (hα : i ≠ sched.alpha t) (hω : i ≠ sched.omega t) :
    allocation p d sched i t = (1 - 1 / capacityRatio p) * capacity p d i t := by
  unfold allocation; rw [if_pos h, if_neg hα, if_neg hω]

end Roles

/-! ## B2: cross-time conservation -/

theorem capacity_pred (p : ScheduleParams) (d : Nat) {i : Nat} (hi : 1 ≤ i) (t : Nat) :
    capacity p d i t = p.A * capacity p d (i - 1) t := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simpa using capacity_succ_level p d j t

set_option maxHeartbeats 4000000 in
/-- **B2 (conservation).** Wires arriving at a node at time `t+1` are exactly those its parent
    sent down plus those its `br` children sent up. -/
theorem flow_conservation (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d)
    (hlt : ∀ s, 2 ≤ s → s < sched.tf → sched.alpha s < sched.omega s)
    (hend : sched.alpha sched.tf = sched.omega sched.tf)
    (hmeet : capacity p d (sched.alpha sched.tf) sched.tf =
      (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ (sched.alpha sched.tf))
    (t : Nat) (ht2 : 2 ≤ t) (ht : t + 1 ≤ sched.tf) (i : Nat) :
    allocation p d sched i (t + 1) =
      (if 1 ≤ i then flowDown p d sched (i - 1) t else 0) +
        (p.br : Rat) * flowUp p d sched (i + 1) t := by
  have hαp := sched.alpha_parity t (by omega)
  have hαp1 := sched.alpha_parity (t + 1) ht
  have hωp := sched.omega_parity t (by omega)
  have hωp1 := sched.omega_parity (t + 1) ht
  have hαs := sched.alpha_step t ht
  have hωs := sched.omega_step t ht
  have hαω : sched.alpha t < sched.omega t := hlt t ht2 (by omega)
  have hlt1 : t + 1 < sched.tf → sched.alpha (t + 1) < sched.omega (t + 1) :=
    fun h => hlt (t + 1) (by omega) h
  have hfin : t + 1 = sched.tf → sched.alpha (t + 1) = sched.omega (t + 1) := by
    intro h; rw [h]; exact hend
  have hA := p.A_pos
  have hbr := p.br_cast_pos
  have hnu := p.hnu_pos
  have hQ : capacityRatio p = p.A ^ 2 * (p.br : Rat) ^ 2 := rfl
  by_cases hAct : t + 1 ≤ sched.tf ∧ sched.alpha (t + 1) ≤ i ∧ i ≤ sched.omega (t + 1) ∧
      i % 2 = (t + 1) % 2
  swap
  · -- inactive node: nothing arrives
    rw [allocation_inactive p d sched i (t + 1) hAct]
    have hpar : (if 1 ≤ i then flowDown p d sched (i - 1) t else 0) = 0 := by
      split_ifs with h1
      · by_cases hpa : t ≤ sched.tf ∧ sched.alpha t ≤ i - 1 ∧ i - 1 ≤ sched.omega t ∧
            (i - 1) % 2 = t % 2
        swap
        · exact flowDown_inactive p d sched hpa
        · by_cases hpω : i - 1 = sched.omega t
          · exact flowDown_bot_rise p d sched hpa (by omega) hpω (by omega)
          · exfalso; omega
      · rfl
    have hchild : flowUp p d sched (i + 1) t = 0 := by
      by_cases hqa : t ≤ sched.tf ∧ sched.alpha t ≤ i + 1 ∧ i + 1 ≤ sched.omega t ∧
          (i + 1) % 2 = t % 2
      swap
      · exact flowUp_inactive p d sched hqa
      · by_cases hqα : i + 1 = sched.alpha t
        · exact flowUp_top_desc p d sched hqa hqα (by omega)
        · exfalso; omega
    rw [hpar, hchild]; simp
  have hAct' := hAct
  obtain ⟨hAt, hAl, hAo, hAp⟩ := hAct
  by_cases hfinal : t + 1 = sched.tf
  · -- the step into the meeting time
    have hmα := hfin hfinal
    clear hfin hlt1 hlt
    have hi : i = sched.alpha t + 1 := by omega
    have hω2 : sched.omega t = sched.alpha t + 2 := by omega
    have hLHS : allocation p d sched i (t + 1) = capacity p d i (t + 1) :=
      alloc_top p d sched hAct' (by omega)
    have hp1 : 1 ≤ i := by omega
    rw [if_pos hp1]
    have hpA : t ≤ sched.tf ∧ sched.alpha t ≤ i - 1 ∧ i - 1 ≤ sched.omega t ∧
        (i - 1) % 2 = t % 2 := by omega
    have hpar : flowDown p d sched (i - 1) t = capacity p d (i - 1) t / (p.br : Rat) :=
      flowDown_top_desc p d sched hpA (by omega) (by omega)
    have hqA : t ≤ sched.tf ∧ sched.alpha t ≤ i + 1 ∧ i + 1 ≤ sched.omega t ∧
        (i + 1) % 2 = t % 2 := by omega
    have hchild : flowUp p d sched (i + 1) t = allocation p d sched (i + 1) t :=
      flowUp_bot_rise p d sched hqA (by omega) (by omega) (by omega)
    have hqal := alloc_bot p d sched hqA (by omega) (by omega)
    have h1 := capacity_pred p d hp1 t
    have h2 := capacity_succ_level p d i t
    have hM : capacity p d i (t + 1) = (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ i := by
      have hm := hmeet
      rw [← hfinal] at hm
      have hia : sched.alpha (t + 1) = i := by omega
      rw [hia] at hm
      exact hm
    rw [hLHS, hpar, hchild, hqal, hM, h2, h1, hQ, pow_succ]
    field_simp
    ring
  · have hα'ω' := hlt1 (lt_of_le_of_ne ht hfinal)
    clear hfin hlt1 hlt
    by_cases hiα : i = sched.alpha (t + 1)
    · have hLHS : allocation p d sched i (t + 1) = capacity p d i (t + 1) :=
        alloc_top p d sched hAct' hiα
      rcases (by omega : sched.alpha (t + 1) = sched.alpha t + 1 ∨
          sched.alpha t = sched.alpha (t + 1) + 1) with hd | hr
      · -- top descends
        have hp1 : 1 ≤ i := by omega
        rw [if_pos hp1]
        have hpA : t ≤ sched.tf ∧ sched.alpha t ≤ i - 1 ∧ i - 1 ≤ sched.omega t ∧
            (i - 1) % 2 = t % 2 := by omega
        have hpar := flowDown_top_desc p d sched hpA (by omega) (by omega)
        have hqA : t ≤ sched.tf ∧ sched.alpha t ≤ i + 1 ∧ i + 1 ≤ sched.omega t ∧
            (i + 1) % 2 = t % 2 := by omega
        have hchild := flowUp_mid p d sched hqA (by omega) (by omega)
        have h1 := capacity_pred p d hp1 t
        have h2 := capacity_succ_level p d i t
        have h3 := capacity_succ_stage p d i t
        rw [hLHS, hpar, hchild, h3, h2, h1, hQ]
        field_simp
        ring
      · -- top rises
        have hpar0 : (if 1 ≤ i then flowDown p d sched (i - 1) t else 0) = 0 := by
          split_ifs with h1
          · exact flowDown_inactive p d sched (by omega)
          · rfl
        have hqA : t ≤ sched.tf ∧ sched.alpha t ≤ i + 1 ∧ i + 1 ≤ sched.omega t ∧
            (i + 1) % 2 = t % 2 := by omega
        have hchild := flowUp_top_rise p d sched hqA (by omega) (by omega)
        have h2 := capacity_succ_level p d i t
        have h3 := capacity_succ_stage p d i t
        rw [hLHS, hpar0, hchild, h3, h2]
        field_simp
        ring
    · by_cases hiω : i = sched.omega (t + 1)
      · rcases (by omega : sched.omega (t + 1) = sched.omega t + 1 ∨
            sched.omega t = sched.omega (t + 1) + 1) with hd | hr
        · -- bottom descends
          have hp1 : 1 ≤ i := by omega
          rw [if_pos hp1]
          have hpA : t ≤ sched.tf ∧ sched.alpha t ≤ i - 1 ∧ i - 1 ≤ sched.omega t ∧
              (i - 1) % 2 = t % 2 := by omega
          have hpar := flowDown_bot_desc p d sched hpA (by omega) (by omega) (by omega)
          have hchild : flowUp p d sched (i + 1) t = 0 :=
            flowUp_inactive p d sched (by omega)
          have hii : sched.omega t + 1 = i := by omega
          rw [hpar, hchild, hii]; simp
        · -- bottom rises
          have hp1 : 1 ≤ i := by omega
          rw [if_pos hp1]
          have hpA : t ≤ sched.tf ∧ sched.alpha t ≤ i - 1 ∧ i - 1 ≤ sched.omega t ∧
              (i - 1) % 2 = t % 2 := by omega
          have hpar := flowDown_mid p d sched hpA (by omega) (by omega)
          have hqA : t ≤ sched.tf ∧ sched.alpha t ≤ i + 1 ∧ i + 1 ≤ sched.omega t ∧
              (i + 1) % 2 = t % 2 := by omega
          have hchild := flowUp_bot_rise p d sched hqA (by omega) (by omega) (by omega)
          have hqal := alloc_bot p d sched hqA (by omega) (by omega)
          have hLHS := alloc_bot p d sched hAct' hiα hiω
          have h1 := capacity_pred p d hp1 t
          have h2 := capacity_succ_level p d i t
          have h3 := capacity_succ_stage p d i t
          rw [hLHS, hpar, hchild, hqal, h3, h2, h1, hQ, pow_succ]
          field_simp
          ring
      · -- interior node
        have hp1 : 1 ≤ i := by omega
        rw [if_pos hp1]
        have hpA : t ≤ sched.tf ∧ sched.alpha t ≤ i - 1 ∧ i - 1 ≤ sched.omega t ∧
            (i - 1) % 2 = t % 2 := by omega
        have hpar := flowDown_mid p d sched hpA (by omega) (by omega)
        have hqA : t ≤ sched.tf ∧ sched.alpha t ≤ i + 1 ∧ i + 1 ≤ sched.omega t ∧
            (i + 1) % 2 = t % 2 := by omega
        have hchild := flowUp_mid p d sched hqA (by omega) (by omega)
        have hLHS := alloc_mid p d sched hAct' hiα hiω
        have h1 := capacity_pred p d hp1 t
        have h2 := capacity_succ_level p d i t
        have h3 := capacity_succ_stage p d i t
        rw [hLHS, hpar, hchild, h3, h2, h1, hQ]
        field_simp
        ring

end Chvatal
