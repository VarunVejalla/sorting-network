import D2Stage14Arithmetic

namespace Chvatal.D2Reserve

set_option maxHeartbeats 10000000

theorem d2FlowStage_regular_child_g_bound_of_cover
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat}
    {h i G low high c : Nat} (children : Fin 8 -> D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc)
    (hbalance : low + high = G)
    (hcover : G <= d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)))
    (hpiAlloc : quota i (role i) <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (hG : 512 * G <= c)
    (hquota : 256 * quota i (role i) <= c)
    (heven : quota i (role i) % 2 = 0)
    (hleftReserve : c <= 128 *
      d2FlowTreeRootDeficit (children ⟨0, by omega⟩))
    (hrightReserve : c <= 128 *
      d2FlowTreeRootDeficit (children ⟨7, by omega⟩)) :
    forall j, 512 * d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j) <= 2 * c := by
  let sizes : Fin 8 -> Nat := fun j => d2FlowTreeRootDeficit (children j)
  let positions : Fin 8 -> Nat := d2FlowPosition sizes
  let total : Nat := d2FlowTotal sizes
  have hconserve : (total - G) + G = total :=
    Nat.sub_add_cancel (by simpa [total, sizes] using hcover)
  have hquotaEven : quota i (role i) = 2 * (quota i (role i) / 2) := by omega
  have halloc : quota i (role i) <= total - G := by
    simpa [total, sizes] using hpiAlloc
  have hlow : low <= G := by omega
  have hhigh : high <= G := by omega
  have hpositions := d2FlowPositions_contiguous sizes
  have hbound := d2_ordinary_update_preserves_child_g_bound sizes positions
    hbalance hconserve halloc hquotaEven hG hlow hhigh hquota
    (by simpa [sizes] using hleftReserve)
    (by simpa [sizes] using hrightReserve)
    (by simpa [positions, sizes] using hpositions.1)
    (by simpa [positions, sizes] using hpositions.2.1)
    (by simpa [positions, sizes, total] using hpositions.2.2)
  intro j
  rw [d2FlowStage_regular_child_deficit children ha hr j]
  simp only [d2FlowCutChild_deficit_eq_update]
  simpa [sizes, positions, total] using hbound j

/-- The Stage-14 level-four mid sender has enough capacity for its quota,
and its `1/512` deficit allowance absorbs a Stage-13 level-three deficit
plus half of that sender's outgoing quota. This is the tight arithmetic
needed when Stage-13's balanced level-three sender writes an endpoint. -/
theorem d2FlowCandidateStage14_levelFour_mid_budgets
    (d : Nat) (hd : 14 <= d) :
    let oldCap := d2FlowCandidateCapacity d 3 13
    let cap := d2FlowCandidateCapacity d 4 14
    let oldQuota := d2FlowCandidateQuota d 13 3 .mid
    let quota := d2FlowCandidateQuota d 14 4 .mid
    cap = 2 * oldCap /\
      quota = 2 * oldQuota /\
      256 * quota <= cap /\
      (forall G, 512 * G <= oldCap ->
        512 * (G + oldQuota / 2) <= cap) := by
  dsimp only
  have hOldCap : d2FlowCandidateCapacity d 3 13 = 2 ^ (3 * d - 8) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hCap : d2FlowCandidateCapacity d 4 14 = 2 ^ (3 * d - 7) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hOldQuota : d2FlowCandidateQuota d 13 3 .mid =
      15 * 2 ^ (3 * d - 20) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hQuota : d2FlowCandidateQuota d 14 4 .mid =
      15 * 2 ^ (3 * d - 19) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hCapScale : 2 ^ (3 * d - 7) = 2 * 2 ^ (3 * d - 8) := by
    rw [show 3 * d - 7 = 1 + (3 * d - 8) by omega, pow_add]
    norm_num
  have hQuotaScale : 15 * 2 ^ (3 * d - 19) =
      2 * (15 * 2 ^ (3 * d - 20)) := by
    rw [show 3 * d - 19 = 1 + (3 * d - 20) by omega, pow_add]
    ring
  have hQuotaCap :
      256 * (15 * 2 ^ (3 * d - 19)) <= 2 ^ (3 * d - 7) := by
    rw [show 3 * d - 7 = 12 + (3 * d - 19) by omega, pow_add]
    omega
  have hOldQuotaCap :
      256 * (15 * 2 ^ (3 * d - 20)) <= 2 ^ (3 * d - 8) := by
    rw [show 3 * d - 8 = 12 + (3 * d - 20) by omega, pow_add]
    omega
  have hOldQuotaEven :
      (15 * 2 ^ (3 * d - 20)) % 2 = 0 := by
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 20 ≠ 0 by omega)
    rw [he, pow_succ]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hCap, hOldCap, hCapScale]
  · rw [hQuota, hOldQuota, hQuotaScale]
  · rw [hQuota, hCap]
    exact hQuotaCap
  · intro G hG
    rw [hCap, hOldQuota]
    have hG' : 512 * G <= 2 ^ (3 * d - 8) := by
      rw [hOldCap] at hG
      exact hG
    have hsum :
        512 * G + 256 * (15 * 2 ^ (3 * d - 20)) <=
          2 * 2 ^ (3 * d - 8) := by
      omega
    have hidentity :
        512 * (G + (15 * 2 ^ (3 * d - 20)) / 2) =
          512 * G + 256 * (15 * 2 ^ (3 * d - 20)) := by
      omega
    rw [hidentity]
    calc
      _ <= 2 * 2 ^ (3 * d - 8) := hsum
      _ = 2 ^ (3 * d - 7) := hCapScale.symm

/-- One Stage-14 level-four endpoint reserve alone funds the node's root
deficit and its mid quota. The margin is `32 - 8 - 15 = 9` in units of
`capacity / 4096`. -/
theorem d2FlowCandidateStage14_levelFour_endpoint_funds_quota
    (d G child : Nat) (hd : 14 <= d)
    (hG : 512 * G <= d2FlowCandidateCapacity d 4 14)
    (hreserve : d2FlowCandidateCapacity d 4 14 <= 128 * child) :
    G + d2FlowCandidateQuota d 14 4 .mid <= child := by
  have hcap : d2FlowCandidateCapacity d 4 14 = 2 ^ (3 * d - 7) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 14 4 .mid =
      15 * 2 ^ (3 * d - 19) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hexp : 3 * d - 7 = 12 + (3 * d - 19) := by omega
  have hcapForm : d2FlowCandidateCapacity d 4 14 =
      4096 * 2 ^ (3 * d - 19) := by
    rw [hcap, hexp, pow_add]
    norm_num
  have hquotaIdentity : 4096 * d2FlowCandidateQuota d 14 4 .mid =
      15 * d2FlowCandidateCapacity d 4 14 := by
    rw [hquota, hcapForm]
    ring
  have hG' : 4096 * G <= 8 * d2FlowCandidateCapacity d 4 14 := by
    omega
  have hreserve' : 32 * d2FlowCandidateCapacity d 4 14 <= 4096 * child := by
    omega
  have hsum : 4096 * (G + d2FlowCandidateQuota d 14 4 .mid) <=
      4096 * child := by
    rw [Nat.mul_add, hquotaIdentity]
    nlinarith
  omega

/-- The endpoint reserve plus the sender deficit contract implies the full
aggregate allocation inequality: one child already covers root mass and quota. -/
theorem d2FlowCandidateStage14_levelFour_allocation_of_endpoint
    (d G : Nat) (children : Fin 8 -> Nat) (s : Fin 8) (hd : 14 <= d)
    (hG : 512 * G <= d2FlowCandidateCapacity d 4 14)
    (hreserve : d2FlowCandidateCapacity d 4 14 <= 128 * children s) :
    d2FlowCandidateQuota d 14 4 .mid <= d2FlowTotal children - G := by
  have hfund := d2FlowCandidateStage14_levelFour_endpoint_funds_quota
    d G (children s) hd hG hreserve
  have htotal := d2FlowSize_le_total children s
  omega

/-- A valid Stage-13 level-three mid input writes balanced level-four child
roots, and its child-deficit estimate is exactly strong enough for Stage 14's
twice-as-large level-four capacity. -/
theorem d2FlowCandidateStage14_levelFour_child_state_of_stage13_mid
    (d : Nat) (hd : 14 <= d) (h : Nat)
    (G low high : Nat) (children : Fin 8 -> D2FlowTree h)
    (hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 13)
      (d2FlowCandidateRole d 13)
      (d2FlowCandidateQuota d 13)
      (fun r => d2FlowCandidateCapacity d r 13) 3
      (.node G low high children)) :
    forall j : Fin 8,
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 13)
            (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
            (h + 1) 3 (.node G low high children)) j)).2.1 +
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 13)
            (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
            (h + 1) 3 (.node G low high children)) j)).2.2 =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 13)
            (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
            (h + 1) 3 (.node G low high children)) j) /\
      512 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 13)
            (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
            (h + 1) 3 (.node G low high children)) j) <=
        d2FlowCandidateCapacity d 4 14 := by
  rcases d2FlowCandidateStage13_frontiers d (by omega) with
    ⟨_, _, ha, hr, _, _, _⟩
  rcases d2FlowCandidateStage14_levelFour_mid_budgets d hd with
    ⟨hcapScale, _, _, _⟩
  have hlocal := hinputs
  simp only [d2FlowStageInvInputs, ha, if_true, hr] at hlocal
  rcases hlocal with ⟨_, hbalance, hG, hquota, halloc, heven, hleft, hright⟩
  have hquotaPos : 0 < d2FlowCandidateQuota d 13 3 .mid := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
  have hcover : G <= d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) := by omega
  have halloc' : d2FlowCandidateQuota d 13 3
      (d2FlowCandidateRole d 13 3) <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    simpa [hr] using halloc
  have hquota' : 256 * d2FlowCandidateQuota d 13 3
      (d2FlowCandidateRole d 13 3) <= d2FlowCandidateCapacity d 3 13 := by
    simpa [hr] using hquota
  have heven' : d2FlowCandidateQuota d 13 3
      (d2FlowCandidateRole d 13 3) % 2 = 0 := by
    simpa [hr] using heven
  intro j
  constructor
  · exact d2FlowStage_regular_child_balanced children ha
      (Or.inr (Or.inl hr)) j
  · have hg := d2FlowStage_regular_child_g_bound_of_cover
      (active := d2FlowCandidateActive d 13)
      (role := d2FlowCandidateRole d 13)
      (quota := d2FlowCandidateQuota d 13)
      children ha (Or.inr (Or.inl hr)) hbalance hcover halloc'
      hG hquota' heven' hleft hright j
    calc
      512 * d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 13)
              (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
              (h + 1) 3 (.node G low high children)) j) <=
          2 * d2FlowCandidateCapacity d 3 13 := hg
      _ = d2FlowCandidateCapacity d 4 14 := hcapScale.symm

/-- Stage 13's level-one top-rise cut writes level-two child roots whose
deficits fit Stage 14's twice-larger level-two capacity. -/
theorem d2FlowCandidateStage14_levelTwo_child_state_of_stage13_topRise
    (d : Nat) (hd : 14 <= d) (h : Nat)
    (G low high : Nat) (children : Fin 8 -> D2FlowTree h)
    (hinputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 13)
      (d2FlowCandidateRole d 13)
      (d2FlowCandidateQuota d 13)
      (fun r => d2FlowCandidateCapacity d r 13) 1
      (.node G low high children)) :
    forall j : Fin 8,
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 13)
            (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
            (h + 1) 1 (.node G low high children)) j)).2.1 +
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 13)
            (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
            (h + 1) 1 (.node G low high children)) j)).2.2 =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 13)
            (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
            (h + 1) 1 (.node G low high children)) j) /\
      512 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 13)
            (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
            (h + 1) 1 (.node G low high children)) j) <=
        d2FlowCandidateCapacity d 2 14 := by
  rcases d2FlowCandidateStage13_frontiers d (by omega) with
    ⟨hactive, hrole, _, _, _, _, _⟩
  have hlocal := hinputs
  simp only [d2FlowStageInvInputs, hactive, if_true, hrole] at hlocal
  rcases hlocal with ⟨_, hbalance, hG, hquota, halloc, heven, hleft, hright⟩
  have hquotaPos : 0 < d2FlowCandidateQuota d 13 1 .topRise := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
  have hcover : G <= d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) := by omega
  have hquota' : d2FlowCandidateQuota d 13 1
      (d2FlowCandidateRole d 13 1) <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    simpa [hrole] using halloc
  have hG' : 512 * G <= d2FlowCandidateCapacity d 1 13 := by
    simpa [hrole] using hG
  have hquotaCap : 256 * d2FlowCandidateQuota d 13 1
      (d2FlowCandidateRole d 13 1) <= d2FlowCandidateCapacity d 1 13 := by
    simpa [hrole] using hquota
  have heven' : d2FlowCandidateQuota d 13 1
      (d2FlowCandidateRole d 13 1) % 2 = 0 := by
    simpa [hrole] using heven
  have hcapScale : d2FlowCandidateCapacity d 2 14 =
      2 * d2FlowCandidateCapacity d 1 13 := by
    have hexp : d2FlowCandidateCapacityExponent d 2 14 =
        d2FlowCandidateCapacityExponent d 1 13 + 1 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    simp only [d2FlowCandidateCapacity]
    rw [hexp, pow_succ]
    omega
  intro j
  constructor
  · exact d2FlowStage_regular_child_balanced children hactive
      (Or.inl hrole) j
  · have hg := d2FlowStage_regular_child_g_bound_of_cover
      (active := d2FlowCandidateActive d 13)
      (role := d2FlowCandidateRole d 13)
      (quota := d2FlowCandidateQuota d 13)
      children hactive (Or.inl hrole) hbalance hcover hquota' hG'
      hquotaCap heven' hleft hright j
    calc
      512 * d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 13)
              (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
              (h + 1) 1 (.node G low high children)) j) <=
          2 * d2FlowCandidateCapacity d 1 13 := hg
      _ = d2FlowCandidateCapacity d 2 14 := hcapScale.symm

/-- The quota emitted by each active Stage-13 level-three mid sender is more
than enough to reserve the Stage-14 level-two capacity at its child root. -/
theorem d2FlowCandidateStage14_levelTwo_reserve_from_stage13_levelThree_quota
    (d : Nat) (hd : 14 <= d) :
    d2FlowCandidateCapacity d 2 14 <=
      128 * d2FlowCandidateQuota d 13 3 .mid := by
  have hcap : d2FlowCandidateCapacity d 2 14 = 2 ^ (3 * d - 13) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 13 3 .mid =
      15 * 2 ^ (3 * d - 20) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hexp : 3 * d - 13 = 7 + (3 * d - 20) := by omega
  rw [hcap, hquota, hexp, pow_add]
  norm_num

/-- Exact level-two Stage-14 capacity and mid quota formulas, including the
quota cap and parity conditions used by the recursive sender contract. -/
theorem d2FlowCandidateStage14_levelTwo_parameters
    (d : Nat) (hd : 14 <= d) :
    d2FlowCandidateCapacity d 2 14 = 2 ^ (3 * d - 13) /\
      d2FlowCandidateQuota d 14 2 .mid = 15 * 2 ^ (3 * d - 25) /\
      256 * d2FlowCandidateQuota d 14 2 .mid <=
        d2FlowCandidateCapacity d 2 14 /\
      d2FlowCandidateQuota d 14 2 .mid % 2 = 0 := by
  have hcap : d2FlowCandidateCapacity d 2 14 = 2 ^ (3 * d - 13) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 14 2 .mid =
      15 * 2 ^ (3 * d - 25) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  refine ⟨hcap, hquota, ?_, ?_⟩
  · rw [hcap, hquota]
    have hexp : 3 * d - 13 = 12 + (3 * d - 25) := by omega
    rw [hexp, pow_add]
    omega
  · rw [hquota]
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero
      (show 3 * d - 25 ≠ 0 by omega)
    rw [he, pow_succ]
    omega

/-- One reserved endpoint pays a level-two Stage-14 mid sender's old root
deficit and outgoing quota. -/
theorem d2FlowCandidateStage14_levelTwo_endpoint_funds_quota
    (d G child : Nat) (hd : 14 <= d)
    (hG : 512 * G <= d2FlowCandidateCapacity d 2 14)
    (hreserve : d2FlowCandidateCapacity d 2 14 <= 128 * child) :
    G + d2FlowCandidateQuota d 14 2 .mid <= child := by
  rcases d2FlowCandidateStage14_levelTwo_parameters d hd with
    ⟨hcap, hquota, _, _⟩
  let unit := 2 ^ (3 * d - 25)
  have hexp : 3 * d - 13 = 12 + (3 * d - 25) := by omega
  have hpower : 2 ^ (3 * d - 13) = 4096 * unit := by
    rw [hexp, pow_add]
    norm_num [unit]
  have hcapForm : d2FlowCandidateCapacity d 2 14 = 4096 * unit := by
    rw [hcap, hpower]
  have hG' : 512 * G <= 4096 * unit := by
    rw [← hcapForm]
    exact hG
  have hreserve' : 4096 * unit <= 128 * child := by
    rw [← hcapForm]
    exact hreserve
  rw [hquota]
  nlinarith

/-- A single level-two endpoint reserve is sufficient for the aggregate
allocation clause. -/
theorem d2FlowCandidateStage14_levelTwo_allocation_of_endpoint
    (d G : Nat) (children : Fin 8 -> Nat) (s : Fin 8) (hd : 14 <= d)
    (hG : 512 * G <= d2FlowCandidateCapacity d 2 14)
    (hreserve : d2FlowCandidateCapacity d 2 14 <= 128 * children s) :
    d2FlowCandidateQuota d 14 2 .mid <= d2FlowTotal children - G := by
  have hfund := d2FlowCandidateStage14_levelTwo_endpoint_funds_quota
    d G (children s) hd hG hreserve
  have htotal := d2FlowSize_le_total children s
  omega

end Chvatal.D2Reserve
