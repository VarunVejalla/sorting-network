import D2CandidateQuotaLower

namespace Chvatal.D2Reserve

set_option maxHeartbeats 8000000

/-- At the ordinary visit two stages after a bottom-rise boundary, the native
size of each child is exactly one 128th of the sender's scheduled capacity. -/
theorem d2FlowCandidateCapacity_eq_128_native_child
    {d i t : Nat} (hlevel : i + 1 ≤ d) (hboundary : 3 * i = t + 4) :
    d2FlowCandidateCapacity d i t =
      128 * (8192 * 8 ^ (d - (i + 1))) := by
  have hsub : d - (i + 1) + (i + 1) = d := Nat.sub_add_cancel hlevel
  have hexp : d2FlowCandidateCapacityExponent d i t =
      20 + 3 * (d - (i + 1)) := by
    unfold d2FlowCandidateCapacityExponent
    omega
  rw [d2FlowCandidateCapacity, hexp]
  rw [show (128 : Nat) = 2 ^ 7 by norm_num,
    show (8192 : Nat) = 2 ^ 13 by norm_num,
    show (8 : Nat) = 2 ^ 3 by norm_num]
  calc
    2 ^ (20 + 3 * (d - (i + 1))) =
        2 ^ 20 * 2 ^ (3 * (d - (i + 1))) := by rw [pow_add]
    _ = 2 ^ 7 * (2 ^ 13 * (2 ^ 3) ^ (d - (i + 1))) := by
      rw [← pow_mul]
      ring

/-- A bottom-rise predecessor forces the exact frontier equation needed by
the native-child reserve calculation. -/
theorem d2FlowCandidate_botRise_prev_two_boundary
    {d i t : Nat} (ht : 4 ≤ t)
    (hprev : d2ScheduleRole d i (t - 2) = .botRise) :
    3 * i = t + 4 := by
  have h := d2ScheduleRole_botRise_boundary (by omega : 2 ≤ t - 2) hprev
  omega

/-- Schedule-level form of the exceptional reserve scale: if the visit two
stages earlier was `botRise`, current capacity is 128 native child sizes. -/
theorem d2FlowCandidate_botRise_prev_two_native_capacity
    {d i t : Nat} (ht : 4 ≤ t) (hlevel : i + 1 ≤ d)
    (hprev : d2ScheduleRole d i (t - 2) = .botRise) :
    d2FlowCandidateCapacity d i t =
      128 * (8192 * 8 ^ (d - (i + 1))) := by
  exact d2FlowCandidateCapacity_eq_128_native_child hlevel
    (d2FlowCandidate_botRise_prev_two_boundary ht hprev)

/-- The exceptional two-step reserve base: a `botRise` leaves inactive child
roots intact, then an inactive same-level step cannot decrease them. -/
theorem d2FlowStage_botRise_two_step_native_endpoint_reserve
    {h i G low high native cap : Nat}
    {active nextActive : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true) (hr : role i = .botRise)
    (hchildInactive : active (i + 1) = false)
    (hnextInactive : nextActive i = false)
    (hcap : cap = 128 * native)
    (hleft : native ≤ d2FlowTreeRootDeficit (children 0))
    (hright : native ≤ d2FlowTreeRootDeficit (children 7)) :
    cap ≤ 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage nextActive role quota (h + 1) i
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children))) 0) ∧
    cap ≤ 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage nextActive role quota (h + 1) i
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children))) 7) := by
  have hbotLeft := d2FlowStage_botRise_child_root_deficit
    (active := active) (role := role) (quota := quota) (h := h) (i := i)
    (G := G) (low := low) (high := high) children ha hr hchildInactive 0
  have hbotRight := d2FlowStage_botRise_child_root_deficit
    (active := active) (role := role) (quota := quota) (h := h) (i := i)
    (G := G) (low := low) (high := high) children ha hr hchildInactive 7
  have hfirstLeft : native ≤ d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) 0) := by
    rw [hbotLeft]
    exact hleft
  have hfirstRight : native ≤ d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) 7) := by
    rw [hbotRight]
    exact hright
  have hretained := d2FlowStage_inactive_preserves_endpoint_halves
    (active := nextActive) (role := role) (quota := quota) hnextInactive
    (d2FlowStage active role quota (h + 1) i
      (.node G low high children)) native hfirstLeft hfirstRight
  constructor
  case left =>
    calc
      cap = 128 * native := hcap
      _ ≤ 128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage nextActive role quota (h + 1) i
              (d2FlowStage active role quota (h + 1) i
                (.node G low high children))) 0) :=
        Nat.mul_le_mul_left 128 hretained.1
  case right =>
    calc
      cap = 128 * native := hcap
      _ ≤ 128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage nextActive role quota (h + 1) i
              (d2FlowStage active role quota (h + 1) i
                (.node G low high children))) 7) :=
        Nat.mul_le_mul_left 128 hretained.2

/-- Arbitrary-path trace adapter for a child root that is untouched throughout
a stage interval. This is the bridge from schedule history to concrete
recursive-tree snapshots, independent of the chosen path depth. -/
theorem d2FlowTreePathHistory_child_root_preserved
    {h n : Nat} (initial : D2FlowTree (h + 1 + n))
    (path : D2FlowPath n) (i : Nat)
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat) (j : Fin 8) (step : Nat)
    (hpreserves : ∀ k, k < step →
      active k
          ((d2FlowTreePathContext n initial path i active role quota overwrite).level + 1) = false ∧
        (active k
            (d2FlowTreePathContext n initial path i active role quota overwrite).level = false ∨
          role k
            (d2FlowTreePathContext n initial path i active role quota overwrite).level = .botRise)) :
    d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreePathHistory n initial path i active role quota overwrite step) j) =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreePathContext n initial path i active role quota overwrite).initial j) := by
  let ctx := d2FlowTreePathContext n initial path i active role quota overwrite
  let childActive := fun k => active k (ctx.level + 1)
  let parentActive := fun k => active k ctx.level
  let parentRole := fun k => role k ctx.level
  let childPort := fun k =>
    (d2FlowStagePort (active k) (role k) (quota k) h (ctx.level + 1)
      (d2FlowTreeChild
        (d2FlowTreeRunWithParentOverwrites ctx.initial ctx.level active role quota
          ctx.overwrite k) j) : Rat) / 8192
  let cutDeficit := fun k =>
    (d2FlowTreeParentCutAt (i := ctx.level)
      (d2FlowTreeRunWithParentOverwrites ctx.initial ctx.level active role quota
        ctx.overwrite k) (role k) (quota k) j : Rat) / 8192
  have htrace := d2FlowTreePathHistory_child_trace
    initial path i active role quota overwrite j step
  have hstable := d2ChildDeficitTrace_eq_of_preserves
    ((d2FlowTreeRootDeficit (d2FlowTreeChild ctx.initial j) : Rat) / 8192)
    childActive childPort parentActive parentRole cutDeficit 0 step (by
      intro k hk
      have h := hpreserves k hk
      simpa [ctx, childActive, parentActive, parentRole] using h)
  have htrace' :
      (d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreePathHistory n initial path i active role quota overwrite step) j) : Rat) / 8192 =
      d2ChildDeficitTrace
        ((d2FlowTreeRootDeficit (d2FlowTreeChild ctx.initial j) : Rat) / 8192)
        childActive childPort parentActive parentRole cutDeficit step := by
    simpa [ctx, childActive, childPort, parentActive, parentRole, cutDeficit] using htrace
  have hstable' :
      d2ChildDeficitTrace
        ((d2FlowTreeRootDeficit (d2FlowTreeChild ctx.initial j) : Rat) / 8192)
        childActive childPort parentActive parentRole cutDeficit step =
      (d2FlowTreeRootDeficit (d2FlowTreeChild ctx.initial j) : Rat) / 8192 := by
    calc
      d2ChildDeficitTrace
          ((d2FlowTreeRootDeficit (d2FlowTreeChild ctx.initial j) : Rat) / 8192)
          childActive childPort parentActive parentRole cutDeficit step =
        d2ChildDeficitTrace
          ((d2FlowTreeRootDeficit (d2FlowTreeChild ctx.initial j) : Rat) / 8192)
          childActive childPort parentActive parentRole cutDeficit (0 + step) := by
            rw [Nat.zero_add]
      _ = d2ChildDeficitTrace
          ((d2FlowTreeRootDeficit (d2FlowTreeChild ctx.initial j) : Rat) / 8192)
          childActive childPort parentActive parentRole cutDeficit 0 := hstable
      _ = _ := by simp [d2ChildDeficitTrace]
  have hrat :
      (d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreePathHistory n initial path i active role quota overwrite step) j) : Rat) / 8192 =
      (d2FlowTreeRootDeficit
        (d2FlowTreeChild ctx.initial j) : Rat) / 8192 := by
    rw [htrace', hstable']
  have hmul := congrArg (fun x : Rat => x * 8192) hrat
  norm_num at hmul
  exact_mod_cast hmul

end Chvatal.D2Reserve
