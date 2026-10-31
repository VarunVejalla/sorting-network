import D2ScheduleReserve

namespace Chvatal.D2TerminalSchedule

open Chvatal.D2Reserve

/-- At the final active stage `tfD2 d`, the activity inequalities leave only
the single level `d-4`. -/
theorem final_active_level {d i : Nat} (hd : 7 <= d)
    (ha : active d (tfD2 d) i (tfD2 d)) : i = d - 4 := by
  have htf : 2 <= tfD2 d := by unfold tfD2; omega
  have htfne : tfD2 d ≠ 1 := by unfold tfD2; omega
  unfold active at ha
  simp only [if_neg htfne] at ha
  rcases ha with ⟨_, _, hpar, hlow, hhigh⟩
  unfold tfD2 at hpar hlow hhigh
  omega

/-- The terminal active level really is present for every candidate depth. -/
theorem final_level_active (d : Nat) (hd : 7 <= d) :
    active d (tfD2 d) (d - 4) (tfD2 d) := by
  have htf : 2 <= tfD2 d := by unfold tfD2; omega
  have htfne : tfD2 d ≠ 1 := by unfold tfD2; omega
  unfold active
  simp only [if_neg htfne]
  unfold tfD2
  omega

/-- The scaled capacity exponent at every terminal active sender is exactly
25, independent of the input depth. -/
theorem final_active_capacity_exponent {d i : Nat} (hd : 7 <= d)
    (ha : active d (tfD2 d) i (tfD2 d)) :
    d2FlowCandidateCapacityExponent d i (tfD2 d) = 25 := by
  rw [final_active_level hd ha]
  unfold d2FlowCandidateCapacityExponent tfD2
  omega

/-- The corresponding unscaled/native D2 capacity is4096 wires. -/
theorem final_active_native_capacity {d i : Nat} (hd : 7 <= d)
    (ha : active d (tfD2 d) i (tfD2 d)) :
    capacityD2 d i (tfD2 d) = 4096 := by
  have hscaled := d2FlowCandidateCapacity_eq
    (d := d) (i := i) (t := tfD2 d) hd ha
  have hexp := final_active_capacity_exponent hd ha
  have hcap : d2FlowCandidateCapacity d i (tfD2 d) = 2 ^ 25 := by
    simp [d2FlowCandidateCapacity, hexp]
  rw [hcap] at hscaled
  norm_num at hscaled
  nlinarith

/-- Thus a physical integer rank error under the proposed `1/512` terminal
budget is at most8 keys per threshold. This does not itself repair outsiders
between distinct terminal bags. -/
theorem final_active_rank_error_le_eight {d i error : Nat}
    (hd : 7 <= d)
    (ha : active d (tfD2 d) i (tfD2 d))
    (herr : 512 * error <= capacityD2 d i (tfD2 d)) :
    error <= 8 := by
  rw [final_active_native_capacity hd ha] at herr
  have herr' : (error : Rat) ≤ 8 := by nlinarith
  exact_mod_cast herr'

end Chvatal.D2TerminalSchedule
