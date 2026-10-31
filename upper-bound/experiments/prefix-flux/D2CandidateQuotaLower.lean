import D2TwoStageEndpointReserve

namespace Chvatal.D2Reserve

/-- Every ordinary candidate sender receives at least the schedule's
`15/4096` quota fraction of its integer capacity. The top-rise quota is
slightly larger (`1/256`); middle and bottom-descending quotas attain the
fraction exactly. -/
theorem d2FlowCandidateQuota_lower_ordinary {d i t : Nat}
    (hd : 7 ≤ d) (ha : active d (tfD2 d) i t)
    (hrole : d2ScheduleRole d i t = .topRise ∨
      d2ScheduleRole d i t = .mid ∨ d2ScheduleRole d i t = .botDesc) :
    15 * d2FlowCandidateCapacity d i t ≤
      4096 * d2FlowCandidateQuota d t i (d2ScheduleRole d i t) := by
  have he := d2FlowCandidateCapacityExponent_ge_twenty hd ha
  cases hr : d2ScheduleRole d i t with
  | topDesc => simp [hr] at hrole
  | topRise =>
      have hexp : d2FlowCandidateCapacityExponent d i t =
          (d2FlowCandidateCapacityExponent d i t - 8) + 8 := by omega
      simp only [d2FlowCandidateCapacity, d2FlowCandidateQuota]
      have hpow : 4096 * 2 ^ (d2FlowCandidateCapacityExponent d i t - 8) =
          16 * 2 ^ d2FlowCandidateCapacityExponent d i t := by
        rw [show 4096 = 2 ^ 12 by norm_num, ← pow_add,
          show 12 + (d2FlowCandidateCapacityExponent d i t - 8) =
            d2FlowCandidateCapacityExponent d i t + 4 by omega,
          pow_add]
        norm_num
        ring
      have hpos : 0 < 2 ^ d2FlowCandidateCapacityExponent d i t :=
        pow_pos (by norm_num) _
      nlinarith [hpow, hpos]
  | mid =>
      simp only [d2FlowCandidateCapacity, d2FlowCandidateQuota]
      have hexp : 12 + (d2FlowCandidateCapacityExponent d i t - 12) =
          d2FlowCandidateCapacityExponent d i t := by omega
      have hpow : 4096 * 2 ^ (d2FlowCandidateCapacityExponent d i t - 12) =
          2 ^ d2FlowCandidateCapacityExponent d i t := by
        rw [show 4096 = 2 ^ 12 by norm_num, ← pow_add, hexp]
      have hscaled : 4096 * (15 * 2 ^
          (d2FlowCandidateCapacityExponent d i t - 12)) =
          15 * 2 ^ d2FlowCandidateCapacityExponent d i t := by
        calc
          _ = 15 * (4096 * 2 ^
              (d2FlowCandidateCapacityExponent d i t - 12)) := by ring
          _ = _ := by rw [hpow]
      rw [hscaled]
  | botDesc =>
      simp only [d2FlowCandidateCapacity, d2FlowCandidateQuota]
      have hexp : 12 + (d2FlowCandidateCapacityExponent d i t - 12) =
          d2FlowCandidateCapacityExponent d i t := by omega
      have hpow : 4096 * 2 ^ (d2FlowCandidateCapacityExponent d i t - 12) =
          2 ^ d2FlowCandidateCapacityExponent d i t := by
        rw [show 4096 = 2 ^ 12 by norm_num, ← pow_add, hexp]
      have hscaled : 4096 * (15 * 2 ^
          (d2FlowCandidateCapacityExponent d i t - 12)) =
          15 * 2 ^ d2FlowCandidateCapacityExponent d i t := by
        calc
          _ = 15 * (4096 * 2 ^
              (d2FlowCandidateCapacityExponent d i t - 12)) := by ring
          _ = _ := by rw [hpow]
      rw [hscaled]
  | botRise => simp [hr] at hrole

/-- Every active ordinary sender capacity contains an integral number of
8192-unit flow-capacity blocks. This is the arithmetic normalization used by
the two-front overrun estimate; it does not identify these blocks with
physical core invocations. -/
theorem d2FlowCandidateCapacity_eq_8192_mul {d i t : Nat}
    (hd : 7 ≤ d) (ha : active d (tfD2 d) i t) :
    ∃ blocks, d2FlowCandidateCapacity d i t = 8192 * blocks := by
  have he := d2FlowCandidateCapacityExponent_ge_twenty hd ha
  let e := d2FlowCandidateCapacityExponent d i t
  refine ⟨2 ^ (e - 13), ?_⟩
  have heq : e = 13 + (e - 13) := by dsimp [e]; omega
  change 2 ^ e = 8192 * 2 ^ (e - 13)
  rw [heq, Nat.pow_add]
  norm_num

/-- The integer candidate capacity, like its rational schedule counterpart,
drops by exactly sixteen at the same level over two stages. -/
theorem d2FlowCandidateCapacity_two_stage_ratio {d i t : Nat}
    (ht : 2 ≤ t) (hscale : 2 * t + 4 ≤ 13 + 3 * d + 3 * i) :
    d2FlowCandidateCapacity d i (t - 2) =
      16 * d2FlowCandidateCapacity d i t := by
  have hsub : t - 2 + 2 = t := Nat.sub_add_cancel ht
  have hexp : d2FlowCandidateCapacityExponent d i (t - 2) =
      d2FlowCandidateCapacityExponent d i t + 4 := by
    simp only [d2FlowCandidateCapacityExponent]
    have hscaleOld : 2 * (t - 2) + 4 ≤ 13 + 3 * d + 3 * i := by omega
    omega
  rw [d2FlowCandidateCapacity, hexp, pow_add]
  norm_num [d2FlowCandidateCapacity]
  ring

/-- Candidate-schedule form of the ordinary two-step reserve induction. If
the current ordinary visit has an ordinary predecessor two stages earlier,
its checked input reserves and quota gates imply the capacity-sized endpoint
reserves needed now. The intervening same-level stage is inactive by parity. -/
theorem d2FlowCandidate_two_step_endpoint_reserve
    {d i t G low high : Nat}
    (hd : 7 ≤ d) (ht : 4 ≤ t) (htf : t < tfD2 d)
    (hactive : active d (tfD2 d) i t)
    (hrole : d2ScheduleRole d i t = .topRise ∨
      d2ScheduleRole d i t = .mid ∨ d2ScheduleRole d i t = .botDesc)
    (hprevRole : d2ScheduleRole d i (t - 2) = .topRise ∨
      d2ScheduleRole d i (t - 2) = .mid ∨
      d2ScheduleRole d i (t - 2) = .botDesc)
    (children : Fin 8 → D2FlowTree h)
    (hbalance : low + high = G)
    (hcover : G ≤ d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdeficit : 512 * G ≤ d2FlowCandidateCapacity d i (t - 2))
    (hquota : 256 * d2FlowCandidateQuota d (t - 2) i
      (d2ScheduleRole d i (t - 2)) ≤ d2FlowCandidateCapacity d i (t - 2))
    (halloc : d2FlowCandidateQuota d (t - 2) i
      (d2ScheduleRole d i (t - 2)) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (heven : d2FlowCandidateQuota d (t - 2) i
      (d2ScheduleRole d i (t - 2)) % 2 = 0)
    (hleft : d2FlowCandidateCapacity d i (t - 2) ≤
      128 * d2FlowTreeRootDeficit (children 0))
    (hright : d2FlowCandidateCapacity d i (t - 2) ≤
      128 * d2FlowTreeRootDeficit (children 7)) :
    d2FlowCandidateCapacity d i t ≤ 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d (t - 1))
          (d2FlowCandidateRole d (t - 1))
          (d2FlowCandidateQuota d (t - 1)) (h + 1) i
          (d2FlowStage (d2FlowCandidateActive d (t - 2))
            (d2FlowCandidateRole d (t - 2))
            (d2FlowCandidateQuota d (t - 2)) (h + 1) i
            (.node G low high children))) 0) ∧
    d2FlowCandidateCapacity d i t ≤ 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage (d2FlowCandidateActive d (t - 1))
          (d2FlowCandidateRole d (t - 1))
          (d2FlowCandidateQuota d (t - 1)) (h + 1) i
          (d2FlowStage (d2FlowCandidateActive d (t - 2))
            (d2FlowCandidateRole d (t - 2))
            (d2FlowCandidateQuota d (t - 2)) (h + 1) i
            (.node G low high children))) 7) := by
  classical
  have hprev := active_regular_prev_two_role_cases hd ht htf hactive hrole
  have hprevActive : active d (tfD2 d) i (t - 2) := hprev.1
  have hprevBool : d2FlowCandidateActive d (t - 2) i = true := by
    rw [d2FlowCandidateActive_matches_schedule (d := d) (i := i)
      (t := t - 2) (by omega)]
    exact decide_eq_true hprevActive
  have hnotInter : ¬ active d (tfD2 d) i (t - 1) :=
    active_level_inactive_previous_stage (by omega) hactive
  have hinterBool : d2FlowCandidateActive d (t - 1) i = false := by
    rw [d2FlowCandidateActive_matches_schedule (d := d) (i := i)
      (t := t - 1) (by omega)]
    simp [hnotInter]
  have hcap : d2FlowCandidateCapacity d i (t - 2) =
      16 * d2FlowCandidateCapacity d i t :=
    d2FlowCandidateCapacity_two_stage_ratio (by omega)
      (by
        have he := d2FlowCandidateCapacityExponent_ge_twenty hd hactive
        unfold d2FlowCandidateCapacityExponent at he
        omega)
  have hquotaLower : 15 * d2FlowCandidateCapacity d i (t - 2) ≤
      4096 * d2FlowCandidateQuota d (t - 2) i
        (d2ScheduleRole d i (t - 2)) := by
    simpa [d2FlowCandidateRole, (show t - 2 ≠ 0 by omega)] using
      d2FlowCandidateQuota_lower_ordinary hd hprevActive hprevRole
  have hprevRole' : d2FlowCandidateRole d (t - 2) i = .topRise ∨
      d2FlowCandidateRole d (t - 2) i = .mid ∨
      d2FlowCandidateRole d (t - 2) i = .botDesc := by
    simpa [d2FlowCandidateRole, (show t - 2 ≠ 0 by omega)] using hprevRole
  have hquota' : 256 * d2FlowCandidateQuota d (t - 2) i
      (d2FlowCandidateRole d (t - 2) i) ≤
      d2FlowCandidateCapacity d i (t - 2) := by
    simpa [d2FlowCandidateRole, (show t - 2 ≠ 0 by omega)] using hquota
  have halloc' : d2FlowCandidateQuota d (t - 2) i
      (d2FlowCandidateRole d (t - 2) i) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    simpa [d2FlowCandidateRole, (show t - 2 ≠ 0 by omega)] using halloc
  have heven' : d2FlowCandidateQuota d (t - 2) i
      (d2FlowCandidateRole d (t - 2) i) % 2 = 0 := by
    simpa [d2FlowCandidateRole, (show t - 2 ≠ 0 by omega)] using heven
  have hquotaLower' : 15 * d2FlowCandidateCapacity d i (t - 2) ≤
      4096 * d2FlowCandidateQuota d (t - 2) i
        (d2FlowCandidateRole d (t - 2) i) := by
    simpa [d2FlowCandidateRole, (show t - 2 ≠ 0 by omega)] using hquotaLower
  have hreserve := d2FlowStage_regular_two_step_endpoint_reserve
    (active := d2FlowCandidateActive d (t - 2))
    (nextActive := d2FlowCandidateActive d (t - 1))
    (role := d2FlowCandidateRole d (t - 2))
    (nextRole := d2FlowCandidateRole d (t - 1))
    (quota := d2FlowCandidateQuota d (t - 2))
    (nextQuota := d2FlowCandidateQuota d (t - 1))
    (oldCap := d2FlowCandidateCapacity d i (t - 2))
    (newCap := d2FlowCandidateCapacity d i t)
    children hprevBool hprevRole'
    hbalance hcover hdeficit hquota' halloc' heven' hleft hright hinterBool
    hcap hquotaLower'
  simpa using hreserve

end Chvatal.D2Reserve
