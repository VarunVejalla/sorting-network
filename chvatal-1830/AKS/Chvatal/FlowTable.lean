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
def flowUp (d : Nat) (i t : Nat) : Rat :=
  if ¬Active d i t then 0
  else if i = alpha7 d t then
    (if alpha7 d t < alpha7 d (t + 1) then 0
     else (1 / 64 : Rat) * capacity d i t / (4096 * 64 : Rat))
  else if i = omega7 d t then
    (if omega7 d t < omega7 d (t + 1) then
      (4095 : Rat) * capacity d i t / capacityRatio
     else allocation d i t)
  else (4095 : Rat) * capacity d i t / capacityRatio

/-- Wires a node on level `i` sends to each of its `br` children between `t` and `t+1`. -/
def flowDown (d : Nat) (i t : Nat) : Rat :=
  if ¬Active d i t then 0
  else if i = alpha7 d t then
    (if alpha7 d t < alpha7 d (t + 1) then capacity d i t / (64 : Rat)
     else (4096 * 64 - 1 / 64 : Rat) * capacity d i t / (4096 * 64 ^ 2 : Rat))
  else if i = omega7 d t then
    (if omega7 d t < omega7 d (t + 1) then
      allocation d (omega7 d t + 1) (t + 1)
     else 0)
  else (4096 * 64 - 1 / 64 : Rat) * capacity d i t / (4096 * 64 ^ 2 : Rat)

section Roles

variable (d : Nat) theorem flowDown_inactive {i t : Nat} (h : ¬Active d i t) :
    flowDown d i t = 0 := by simp only [flowDown, if_pos h]

theorem flowUp_inactive {i t : Nat} (h : ¬Active d i t) :
    flowUp d i t = 0 := by simp only [flowUp, if_pos h]

/-- Interior-type child send (also valid for a rising top and for a descending bottom). -/
theorem flowDown_mid {i t : Nat} (h : Active d i t)
    (hα : i = alpha7 d t → ¬ alpha7 d t < alpha7 d (t + 1))
    (hω : i ≠ omega7 d t) :
    flowDown d i t =
      (4096 * 64 - 1 / 64 : Rat) * capacity d i t / (4096 * 64 ^ 2 : Rat) := by
  by_cases hi : i = alpha7 d t
  · simp only [flowDown, if_neg (not_not.mpr h), if_pos hi, if_neg (hα hi)]
  · simp only [flowDown, if_neg (not_not.mpr h), if_neg hi, if_neg hω]

theorem flowDown_top_desc {i t : Nat} (h : Active d i t)
    (hα : i = alpha7 d t) (hs : alpha7 d t < alpha7 d (t + 1)) :
    flowDown d i t = capacity d i t / (64 : Rat) := by
  simp only [flowDown, if_neg (not_not.mpr h), if_pos hα, if_pos hs]

theorem flowDown_bot_desc {i t : Nat} (h : Active d i t)
    (hα : i ≠ alpha7 d t) (hω : i = omega7 d t)
    (hs : omega7 d t < omega7 d (t + 1)) :
    flowDown d i t = allocation d (omega7 d t + 1) (t + 1) := by
  simp only [flowDown, if_neg (not_not.mpr h), if_neg hα, if_pos hω, if_pos hs]

theorem flowDown_bot_rise {i t : Nat} (h : Active d i t)
    (hα : i ≠ alpha7 d t) (hω : i = omega7 d t)
    (hs : ¬ omega7 d t < omega7 d (t + 1)) :
    flowDown d i t = 0 := by
  simp only [flowDown, if_neg (not_not.mpr h), if_neg hα, if_pos hω, if_neg hs]

/-- Interior-type parent send (also valid for a descending bottom). -/
theorem flowUp_mid {i t : Nat} (h : Active d i t) (hα : i ≠ alpha7 d t)
    (hω : i = omega7 d t → omega7 d t < omega7 d (t + 1)) :
    flowUp d i t =
      (4095 : Rat) * capacity d i t / capacityRatio := by
  by_cases hi : i = omega7 d t
  · simp only [flowUp, if_neg (not_not.mpr h), if_neg hα, if_pos hi, if_pos (hω hi)]
  · simp only [flowUp, if_neg (not_not.mpr h), if_neg hα, if_neg hi]

theorem flowUp_top_desc {i t : Nat} (h : Active d i t)
    (hα : i = alpha7 d t) (hs : alpha7 d t < alpha7 d (t + 1)) :
    flowUp d i t = 0 := by
  simp only [flowUp, if_neg (not_not.mpr h), if_pos hα, if_pos hs]

theorem flowUp_top_rise {i t : Nat} (h : Active d i t)
    (hα : i = alpha7 d t) (hs : ¬ alpha7 d t < alpha7 d (t + 1)) :
    flowUp d i t = (1 / 64 : Rat) * capacity d i t / (4096 * 64 : Rat) := by
  simp only [flowUp, if_neg (not_not.mpr h), if_pos hα, if_neg hs]

theorem flowUp_bot_rise {i t : Nat} (h : Active d i t)
    (hα : i ≠ alpha7 d t) (hω : i = omega7 d t)
    (hs : ¬ omega7 d t < omega7 d (t + 1)) :
    flowUp d i t = allocation d i t := by
  simp only [flowUp, if_neg (not_not.mpr h), if_neg hα, if_pos hω, if_neg hs]

end Roles

/-- Prove an `Active` goal from the schedule facts in context. -/
local macro "act" : tactic => `(tactic| (unfold Active; omega))

/-- **B1 (send identity).** Every node sends out exactly its wires:
    `a(i,t) = π(i,t) + br · τ(i,t)` for `2 ≤ t`, `t + 1 ≤ tf`. -/
theorem flow_send7 (d : Nat) (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t + 1 ≤ tf7 d)
    (i : Nat) :
    allocation d i t = flowUp d i t + (64 : Rat) * flowDown d i t := by
  have hlt := alpha7_lt_omega7 d hd
  have hend := alpha7_tf_eq_omega7_tf d hd
  by_cases hact : Active d i t
  swap
  · rw [allocation_inactive d i t hact, flowUp_inactive d hact,
      flowDown_inactive d hact]; simp
  have hc := capacity_pos d i t
  have hQ : capacityRatio = (4096 : Rat) ^ 2 * (64 : Rat) ^ 2 := rfl
  have hαω := hlt t ht2 (by omega)
  have hαp := alpha7_parity d t
  by_cases hα : i = alpha7 d t
  · have hal := alloc_top d hact hα
    by_cases hstep : alpha7 d t < alpha7 d (t + 1)
    · rw [flowUp_top_desc d hact hα hstep, flowDown_top_desc d hact hα hstep, hal]
      field_simp; simp
    · rw [flowUp_top_rise d hact hα hstep, flowDown_mid d hact (fun _ => hstep)
        (by omega), hal]
      field_simp; ring
  by_cases hω : i = omega7 d t
  · have hal := alloc_bot d hact hα hω
    by_cases hstep : omega7 d t < omega7 d (t + 1)
    · have hsucc : omega7 d (t + 1) = omega7 d t + 1 := by
        have h1 := omega7_step d t hd ht
        have h2 := omega7_parity d (t + 1)
        have h3 := omega7_parity d t
        omega
      have hα1 : alpha7 d (t + 1) < omega7 d t + 1 := by
        have h5 := alpha7_step d t hd ht
        by_cases hfin : t + 1 = tf7 d
        · rw [← hfin] at hend
          omega
        · have := hlt (t + 1) (by omega) (lt_of_le_of_ne ht hfin)
          omega
      have hact1 : Active d (omega7 d t + 1) (t + 1) := by
        have h3 := omega7_parity d t
        act
      have hal1 := alloc_bot d hact1 (by omega) hsucc.symm
      have hcap1 : capacity d (omega7 d t + 1) (t + 1) =
          (1 / 64 : Rat) * ((4096 : Rat) * capacity d (omega7 d t) t) := by
        rw [capacity_succ_stage, capacity_succ_level]
      rw [flowUp_mid d hact hα (fun _ => hstep),
        flowDown_bot_desc d hact hα hω hstep, hal, hal1, hcap1, hω]
      simp only [Nat.cast_pow] at *
      rw [hQ]
      field_simp
      ring
    · rw [flowUp_bot_rise d hact hα hω hstep, flowDown_bot_rise d hact hα hω hstep]
      ring
  · rw [alloc_mid d hact hα hω, flowUp_mid d hact hα (fun h => absurd h hω),
      flowDown_mid d hact (fun h => absurd h hα) hω, hQ]
    field_simp
    ring

theorem capacity_pred (d : Nat) {i : Nat} (hi : 1 ≤ i) (t : Nat) :
    capacity d i t = (4096 : Rat) * capacity d (i - 1) t := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simpa using capacity_succ_level d j t

set_option maxHeartbeats 4000000 in
/-- **B2 (conservation).** Wires arriving at a node at time `t+1` are exactly those its parent
    sent down plus those its `br` children sent up. -/
theorem flow_conservation7 (d : Nat) (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t + 1 ≤ tf7 d)
    (i : Nat) :
    allocation d i (t + 1) =
      (if 1 ≤ i then flowDown d (i - 1) t else 0) +
        (64 : Rat) * flowUp d (i + 1) t := by
  have hlt := alpha7_lt_omega7 d hd
  have hend := alpha7_tf_eq_omega7_tf d hd
  have hmeet : capacity d (alpha7 d (tf7 d)) (tf7 d) =
      ((64 ^ d : Nat) : Rat) / (64 : Rat) ^ (alpha7 d (tf7 d)) := by
    rw [alpha7_tf d hd]; exact capacity_meet7_div d hd
  have hαp := alpha7_parity d t
  have hαp1 := alpha7_parity d (t + 1)
  have hωp := omega7_parity d t
  have hωp1 := omega7_parity d (t + 1)
  have hαs := alpha7_step d t hd ht
  have hωs := omega7_step d t hd ht
  have hαω : alpha7 d t < omega7 d t := hlt t ht2 (by omega)
  have hQ : capacityRatio = (4096 : Rat) ^ 2 * (64 : Rat) ^ 2 := rfl
  by_cases hAct : Active d i (t + 1)
  swap
  · rw [allocation_inactive d i (t + 1) hAct]
    have hpar : (if 1 ≤ i then flowDown d (i - 1) t else 0) = 0 := by
      split_ifs with h1
      · by_cases hpa : Active d (i - 1) t
        swap
        · exact flowDown_inactive d hpa
        · exact flowDown_bot_rise d hpa (by omega) (by omega) (by omega)
      · rfl
    have hchild : flowUp d (i + 1) t = 0 := by
      by_cases hqa : Active d (i + 1) t
      swap
      · exact flowUp_inactive d hqa
      · exact flowUp_top_desc d hqa (by omega) (by omega)
    rw [hpar, hchild]; simp
  have hAct' := hAct
  obtain ⟨hAt, hAl, hAo, hAp⟩ := hAct
  have h2 := capacity_succ_level d i t
  have h3 := capacity_succ_stage d i t
  have hrw : 1 ≤ i → capacity d i t = (4096 : Rat) * capacity d (i - 1) t := fun h => capacity_pred d h t
  by_cases hfinal : t + 1 = tf7 d
  · have hmα : alpha7 d (t + 1) = omega7 d (t + 1) := by rw [hfinal]; exact hend
    have hp1 : 1 ≤ i := by omega
    have hpA : Active d (i - 1) t := by act
    have hqA : Active d (i + 1) t := by act
    have hM : capacity d i (t + 1) = ((64 ^ d : Nat) : Rat) / (64 : Rat) ^ i := by
      have hm := hmeet
      rw [← hfinal, show alpha7 d (t + 1) = i by omega] at hm
      exact hm
    rw [if_pos hp1, alloc_top d hAct' (by omega),
      flowDown_top_desc d hpA (by omega) (by omega),
      flowUp_bot_rise d hqA (by omega) (by omega) (by omega),
      alloc_bot d hqA (by omega) (by omega), hM, h2, hrw hp1, hQ, pow_succ]
    field_simp
    ring
  · have hα'ω' := hlt (t + 1) (by omega) (lt_of_le_of_ne ht hfinal)
    by_cases hiα : i = alpha7 d (t + 1)
    · have hLHS := alloc_top d hAct' hiα
      have hqA : Active d (i + 1) t := by act
      rcases (by omega : alpha7 d (t + 1) = alpha7 d t + 1 ∨
          alpha7 d t = alpha7 d (t + 1) + 1) with hd | hr
      · have hp1 : 1 ≤ i := by omega
        have hpA : Active d (i - 1) t := by act
        rw [if_pos hp1, hLHS, flowDown_top_desc d hpA (by omega) (by omega),
          flowUp_mid d hqA (by omega) (by omega), h3, h2, hrw hp1, hQ]
        field_simp
        ring
      · have hpar0 : (if 1 ≤ i then flowDown d (i - 1) t else 0) = 0 := by
          split_ifs
          · exact flowDown_inactive d (by act)
          · rfl
        rw [hpar0, hLHS, flowUp_top_rise d hqA (by omega) (by omega), h3, h2]
        field_simp
        ring
    · have hp1 : 1 ≤ i := by omega
      have hpA : Active d (i - 1) t := by act
      rw [if_pos hp1]
      by_cases hiω : i = omega7 d (t + 1)
      · rcases (by omega : omega7 d (t + 1) = omega7 d t + 1 ∨
            omega7 d t = omega7 d (t + 1) + 1) with hd | hr
        · rw [flowDown_bot_desc d hpA (by omega) (by omega) (by omega),
            flowUp_inactive d (by act), show omega7 d t + 1 = i by omega]
          simp
        · have hqA : Active d (i + 1) t := by act
          rw [alloc_bot d hAct' hiα hiω, flowDown_mid d hpA (by omega) (by omega),
            flowUp_bot_rise d hqA (by omega) (by omega) (by omega),
            alloc_bot d hqA (by omega) (by omega), h3, h2, hrw hp1, hQ, pow_succ]
          field_simp
          ring
      · have hqA : Active d (i + 1) t := by act
        rw [alloc_mid d hAct' hiα hiω, flowDown_mid d hpA (by omega) (by omega),
          flowUp_mid d hqA (by omega) (by omega), h3, h2, hrw hp1, hQ]
        field_simp
        ring

end Chvatal
