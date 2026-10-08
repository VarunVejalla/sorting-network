module

/-
  # Chvátal §3 flow table at the §7 parameters (DCS-TR-294 pp. 7–9, §7)

  Discharges the three schedule hypotheses of `flow_conservation` for
  `levelSchedule7 d hd` (`d ≥ 7`): strict separation `α < ω` before `tf`,
  equality at `tf`, and the meeting capacity identity.
-/

public import AKS.Chvatal.FlowTable
public import AKS.Chvatal.Schedule7

@[expose] public section

namespace Chvatal

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
