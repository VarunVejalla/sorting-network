module

public import AKS.Chvatal.Schedule7

@[expose] public section

/-! # Chvátal §3 integer flow table (DCS-TR-294 pp. 7–9)

Between times `t` and `t+1` a node on level `i` sends `flowUp` wires to its parent and
`flowDown` wires to each of its `br` children. With `c = capacity`, `Q = A²·br²`, `k = br`,
for `2 ≤ t < tf`: top descending `π = 0, τ = c/k`; top rising `π = ν c/(A k)`,
`τ = (A k − ν) c/(A k²)`; interior `π = (A ν k − 1) c/Q`, same `τ`; bottom descending
`π` as interior, `τ = a(ω t + 1, t + 1)`; bottom rising `π = a(ω t, t)`, `τ = 0`. -/

namespace Chvatal

/-- Wires a node on level `i` sends to its parent between times `t` and `t+1`. -/
def flowUp (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d) (i t : Nat) : Rat :=
  if ¬Active sched i t then 0
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
  if ¬Active sched i t then 0
  else if i = sched.alpha t then
    (if sched.alpha t < sched.alpha (t + 1) then capacity p d i t / (p.br : Rat)
     else (p.A * (p.br : Rat) - p.nu) * capacity p d i t / (p.A * (p.br : Rat) ^ 2))
  else if i = sched.omega t then
    (if sched.omega t < sched.omega (t + 1) then
      allocation p d sched (sched.omega t + 1) (t + 1)
     else 0)
  else (p.A * (p.br : Rat) - p.nu) * capacity p d i t / (p.A * (p.br : Rat) ^ 2)

section Roles

variable (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d)

theorem flowDown_inactive {i t : Nat} (h : ¬Active sched i t) :
    flowDown p d sched i t = 0 := by simp only [flowDown, if_pos h]

theorem flowUp_inactive {i t : Nat} (h : ¬Active sched i t) :
    flowUp p d sched i t = 0 := by simp only [flowUp, if_pos h]

/-- Interior-type child send (also valid for a rising top and for a descending bottom). -/
theorem flowDown_mid {i t : Nat} (h : Active sched i t)
    (hα : i = sched.alpha t → ¬ sched.alpha t < sched.alpha (t + 1))
    (hω : i ≠ sched.omega t) :
    flowDown p d sched i t =
      (p.A * (p.br : Rat) - p.nu) * capacity p d i t / (p.A * (p.br : Rat) ^ 2) := by
  by_cases hi : i = sched.alpha t
  · simp only [flowDown, if_neg (not_not.mpr h), if_pos hi, if_neg (hα hi)]
  · simp only [flowDown, if_neg (not_not.mpr h), if_neg hi, if_neg hω]

theorem flowDown_top_desc {i t : Nat} (h : Active sched i t)
    (hα : i = sched.alpha t) (hs : sched.alpha t < sched.alpha (t + 1)) :
    flowDown p d sched i t = capacity p d i t / (p.br : Rat) := by
  simp only [flowDown, if_neg (not_not.mpr h), if_pos hα, if_pos hs]

theorem flowDown_bot_desc {i t : Nat} (h : Active sched i t)
    (hα : i ≠ sched.alpha t) (hω : i = sched.omega t)
    (hs : sched.omega t < sched.omega (t + 1)) :
    flowDown p d sched i t = allocation p d sched (sched.omega t + 1) (t + 1) := by
  simp only [flowDown, if_neg (not_not.mpr h), if_neg hα, if_pos hω, if_pos hs]

theorem flowDown_bot_rise {i t : Nat} (h : Active sched i t)
    (hα : i ≠ sched.alpha t) (hω : i = sched.omega t)
    (hs : ¬ sched.omega t < sched.omega (t + 1)) :
    flowDown p d sched i t = 0 := by
  simp only [flowDown, if_neg (not_not.mpr h), if_neg hα, if_pos hω, if_neg hs]

/-- Interior-type parent send (also valid for a descending bottom). -/
theorem flowUp_mid {i t : Nat} (h : Active sched i t) (hα : i ≠ sched.alpha t)
    (hω : i = sched.omega t → sched.omega t < sched.omega (t + 1)) :
    flowUp p d sched i t =
      (p.A * p.nu * (p.br : Rat) - 1) * capacity p d i t / capacityRatio p := by
  by_cases hi : i = sched.omega t
  · simp only [flowUp, if_neg (not_not.mpr h), if_neg hα, if_pos hi, if_pos (hω hi)]
  · simp only [flowUp, if_neg (not_not.mpr h), if_neg hα, if_neg hi]

theorem flowUp_top_desc {i t : Nat} (h : Active sched i t)
    (hα : i = sched.alpha t) (hs : sched.alpha t < sched.alpha (t + 1)) :
    flowUp p d sched i t = 0 := by
  simp only [flowUp, if_neg (not_not.mpr h), if_pos hα, if_pos hs]

theorem flowUp_top_rise {i t : Nat} (h : Active sched i t)
    (hα : i = sched.alpha t) (hs : ¬ sched.alpha t < sched.alpha (t + 1)) :
    flowUp p d sched i t = p.nu * capacity p d i t / (p.A * (p.br : Rat)) := by
  simp only [flowUp, if_neg (not_not.mpr h), if_pos hα, if_neg hs]

theorem flowUp_bot_rise {i t : Nat} (h : Active sched i t)
    (hα : i ≠ sched.alpha t) (hω : i = sched.omega t)
    (hs : ¬ sched.omega t < sched.omega (t + 1)) :
    flowUp p d sched i t = allocation p d sched i t := by
  simp only [flowUp, if_neg (not_not.mpr h), if_neg hα, if_pos hω, if_neg hs]

end Roles

/-- Prove an `Active` goal from the schedule facts in context. -/
local macro "act" : tactic => `(tactic| (unfold Active; omega))

/-- **B1 (send identity).** Every node sends out exactly its wires:
    `a(i,t) = π(i,t) + br · τ(i,t)` for `2 ≤ t`, `t + 1 ≤ tf`. -/
theorem allocation_eq_flowUp_add_flowDown (p : ScheduleParams) (d : Nat)
    (sched : LevelSchedule p d)
    (hlt : ∀ s, 2 ≤ s → s < sched.tf → sched.alpha s < sched.omega s)
    (hend : sched.alpha sched.tf = sched.omega sched.tf)
    (t : Nat) (ht2 : 2 ≤ t) (ht : t + 1 ≤ sched.tf) (i : Nat) :
    allocation p d sched i t =
      flowUp p d sched i t + (p.br : Rat) * flowDown p d sched i t := by
  by_cases hact : Active sched i t
  swap
  · rw [allocation_inactive p d sched i t hact, flowUp_inactive p d sched hact,
      flowDown_inactive p d sched hact]; simp
  have hA := p.A_pos
  have hbr := p.br_cast_pos
  have hnu := p.hnu_pos
  have hc := capacity_pos p d i t
  have hQ : capacityRatio p = p.A ^ 2 * (p.br : Rat) ^ 2 := rfl
  have hαω := hlt t ht2 (by omega)
  have hαp := sched.alpha_parity t hact.1
  by_cases hα : i = sched.alpha t
  · have hal := alloc_top p d sched hact hα
    by_cases hstep : sched.alpha t < sched.alpha (t + 1)
    · rw [flowUp_top_desc p d sched hact hα hstep, flowDown_top_desc p d sched hact hα hstep, hal]
      field_simp; simp
    · rw [flowUp_top_rise p d sched hact hα hstep, flowDown_mid p d sched hact (fun _ => hstep)
        (by omega), hal]
      field_simp; ring
  by_cases hω : i = sched.omega t
  · have hal := alloc_bot p d sched hact hα hω
    by_cases hstep : sched.omega t < sched.omega (t + 1)
    · have hsucc : sched.omega (t + 1) = sched.omega t + 1 := by
        have h1 := sched.omega_step t ht
        have h2 := sched.omega_parity (t + 1) ht
        have h3 := sched.omega_parity t hact.1
        omega
      have hα1 : sched.alpha (t + 1) < sched.omega t + 1 := by
        have h5 := sched.alpha_step t ht
        by_cases hfin : t + 1 = sched.tf
        · rw [← hfin] at hend
          omega
        · have := hlt (t + 1) (by omega) (lt_of_le_of_ne ht hfin)
          omega
      have hact1 : Active sched (sched.omega t + 1) (t + 1) := by
        have h3 := sched.omega_parity t hact.1
        act
      have hal1 := alloc_bot p d sched hact1 (by omega) hsucc.symm
      have hcap1 : capacity p d (sched.omega t + 1) (t + 1) =
          p.nu * (p.A * capacity p d (sched.omega t) t) := by
        rw [capacity_succ_stage, capacity_succ_level]
      rw [flowUp_mid p d sched hact hα (fun _ => hstep),
        flowDown_bot_desc p d sched hact hα hω hstep, hal, hal1, hcap1, hω]
      simp only [Nat.cast_pow] at *
      rw [hQ]
      field_simp
      ring
    · rw [flowUp_bot_rise p d sched hact hα hω hstep, flowDown_bot_rise p d sched hact hα hω hstep]
      ring
  · rw [alloc_mid p d sched hact hα hω, flowUp_mid p d sched hact hα (fun h => absurd h hω),
      flowDown_mid p d sched hact (fun h => absurd h hα) hω, hQ]
    field_simp
    ring

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
  have hA := p.A_pos
  have hbr := p.br_cast_pos
  have hnu := p.hnu_pos
  have hQ : capacityRatio p = p.A ^ 2 * (p.br : Rat) ^ 2 := rfl
  by_cases hAct : Active sched i (t + 1)
  swap
  · rw [allocation_inactive p d sched i (t + 1) hAct]
    have hpar : (if 1 ≤ i then flowDown p d sched (i - 1) t else 0) = 0 := by
      split_ifs with h1
      · by_cases hpa : Active sched (i - 1) t
        swap
        · exact flowDown_inactive p d sched hpa
        · exact flowDown_bot_rise p d sched hpa (by omega) (by omega) (by omega)
      · rfl
    have hchild : flowUp p d sched (i + 1) t = 0 := by
      by_cases hqa : Active sched (i + 1) t
      swap
      · exact flowUp_inactive p d sched hqa
      · exact flowUp_top_desc p d sched hqa (by omega) (by omega)
    rw [hpar, hchild]; simp
  have hAct' := hAct
  obtain ⟨hAt, hAl, hAo, hAp⟩ := hAct
  have h2 := capacity_succ_level p d i t
  have h3 := capacity_succ_stage p d i t
  have hrw : 1 ≤ i → capacity p d i t = p.A * capacity p d (i - 1) t := fun h => capacity_pred p d h t
  by_cases hfinal : t + 1 = sched.tf
  · have hmα : sched.alpha (t + 1) = sched.omega (t + 1) := by rw [hfinal]; exact hend
    have hp1 : 1 ≤ i := by omega
    have hpA : Active sched (i - 1) t := by act
    have hqA : Active sched (i + 1) t := by act
    have hM : capacity p d i (t + 1) = (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ i := by
      have hm := hmeet
      rw [← hfinal, show sched.alpha (t + 1) = i by omega] at hm
      exact hm
    rw [if_pos hp1, alloc_top p d sched hAct' (by omega),
      flowDown_top_desc p d sched hpA (by omega) (by omega),
      flowUp_bot_rise p d sched hqA (by omega) (by omega) (by omega),
      alloc_bot p d sched hqA (by omega) (by omega), hM, h2, hrw hp1, hQ, pow_succ]
    field_simp
    ring
  · have hα'ω' := hlt (t + 1) (by omega) (lt_of_le_of_ne ht hfinal)
    by_cases hiα : i = sched.alpha (t + 1)
    · have hLHS := alloc_top p d sched hAct' hiα
      have hqA : Active sched (i + 1) t := by act
      rcases (by omega : sched.alpha (t + 1) = sched.alpha t + 1 ∨
          sched.alpha t = sched.alpha (t + 1) + 1) with hd | hr
      · have hp1 : 1 ≤ i := by omega
        have hpA : Active sched (i - 1) t := by act
        rw [if_pos hp1, hLHS, flowDown_top_desc p d sched hpA (by omega) (by omega),
          flowUp_mid p d sched hqA (by omega) (by omega), h3, h2, hrw hp1, hQ]
        field_simp
        ring
      · have hpar0 : (if 1 ≤ i then flowDown p d sched (i - 1) t else 0) = 0 := by
          split_ifs
          · exact flowDown_inactive p d sched (by act)
          · rfl
        rw [hpar0, hLHS, flowUp_top_rise p d sched hqA (by omega) (by omega), h3, h2]
        field_simp
        ring
    · have hp1 : 1 ≤ i := by omega
      have hpA : Active sched (i - 1) t := by act
      rw [if_pos hp1]
      by_cases hiω : i = sched.omega (t + 1)
      · rcases (by omega : sched.omega (t + 1) = sched.omega t + 1 ∨
            sched.omega t = sched.omega (t + 1) + 1) with hd | hr
        · rw [flowDown_bot_desc p d sched hpA (by omega) (by omega) (by omega),
            flowUp_inactive p d sched (by act), show sched.omega t + 1 = i by omega]
          simp
        · have hqA : Active sched (i + 1) t := by act
          rw [alloc_bot p d sched hAct' hiα hiω, flowDown_mid p d sched hpA (by omega) (by omega),
            flowUp_bot_rise p d sched hqA (by omega) (by omega) (by omega),
            alloc_bot p d sched hqA (by omega) (by omega), h3, h2, hrw hp1, hQ, pow_succ]
          field_simp
          ring
      · have hqA : Active sched (i + 1) t := by act
        rw [alloc_mid p d sched hAct' hiα hiω, flowDown_mid p d sched hpA (by omega) (by omega),
          flowUp_mid p d sched hqA (by omega) (by omega), h3, h2, hrw hp1, hQ]
        field_simp
        ring

/-! ## Specialization to params7 (§7) -/

/-- Paper's claim that top and bottom are apart before `t_f`. -/
theorem alpha7_lt_omega7 (d : Nat) (hd : 7 ≤ d) (s : Nat) (hs : 2 ≤ s)
    (hlt : s < tf7 d) : alpha7 d s < omega7 d s := by
  rw [alpha7_of_ge_two d s hs, omega7_of_ge_two d s hs]
  have htf : s + 20 < 3 * d := by unfold tf7 at hlt; omega
  unfold ceilParity alphaStarLower omegaStarLower
  split_ifs <;> omega

theorem alpha7_tf_eq_omega7_tf (d : Nat) (hd : 7 ≤ d) :
    alpha7 d (tf7 d) = omega7 d (tf7 d) := by
  have h1 := levelSchedule7_alpha_tf d hd
  have h2 := levelSchedule7_omega_tf d hd
  simp only [levelSchedule7] at h1 h2
  rw [h1, h2]

/-- Meeting identity `capacity = N / br^(meet level)` at `params7`. -/
theorem capacity_meet7_div (d : Nat) (hd : 7 ≤ d) :
    capacity params7 d (meetLevel7 d) (tf7 d) =
      (((64 : Nat) ^ d : Nat) : Rat) / (64 : Rat) ^ (meetLevel7 d) := by
  rw [capacity_meet7 d hd]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 7 := ⟨d - 7, by omega⟩
  have hm : meetLevel7 (e + 7) = e + 1 := by unfold meetLevel7; omega
  rw [hm]
  push_cast
  rw [show e + 7 = (e + 1) + 6 by omega, pow_add]
  have : (64 : Rat) ^ (e + 1) ≠ 0 := by positivity
  field_simp

theorem flow_conservation_params7 (d : Nat) (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t + 1 ≤ tf7 d) (i : Nat) :
    allocation params7 d (levelSchedule7 d hd) i (t + 1) =
      (if 1 ≤ i then flowDown params7 d (levelSchedule7 d hd) (i - 1) t else 0) +
        (params7.br : Rat) * flowUp params7 d (levelSchedule7 d hd) (i + 1) t := by
  refine flow_conservation params7 d (levelSchedule7 d hd) ?_ ?_ ?_ t ht2 ht i
  · intro s hs hlt
    exact alpha7_lt_omega7 d hd s hs hlt
  · exact alpha7_tf_eq_omega7_tf d hd
  · have h1 := levelSchedule7_alpha_tf d hd
    rw [h1]
    have := capacity_meet7_div d hd
    simpa [levelSchedule7, params7] using this

theorem flow_send_params7 (d : Nat) (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t)
    (ht : t + 1 ≤ tf7 d) (i : Nat) :
    allocation params7 d (levelSchedule7 d hd) i t =
      flowUp params7 d (levelSchedule7 d hd) i t +
        (params7.br : Rat) * flowDown params7 d (levelSchedule7 d hd) i t :=
  allocation_eq_flowUp_add_flowDown params7 d (levelSchedule7 d hd)
    (fun s hs hlt => alpha7_lt_omega7 d hd s hs hlt)
    (alpha7_tf_eq_omega7_tf d hd) t ht2 ht i

end Chvatal
