import D2Stage14Contract
import D2Stage15Frontier
import D2Stage15LevelSevenBalance

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv

set_option maxHeartbeats 3000000

set_option linter.unusedVariables false

/-- Assemble the ordinary top-rise input gate from its local numeric fields.
This constructor is intended for the first active Stage-15 sender. -/
theorem d2FlowStageInvInputs_topRise_of_contract
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    (scale i : Nat) {h : Nat} (tree : D2FlowTree (h + 1))
    (hactive : active i = true) (hrole : role i = .topRise)
    (hchildren : forall s : Fin 8,
      d2FlowStageInvInputs scale active role quota cap (i + 1)
        (d2FlowTreeChild tree s))
    (hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree)
    (hdeficit : 512 * d2FlowTreeRootDeficit tree <= cap i)
    (hquotaCap : 256 * quota i .topRise <= cap i)
    (halloc : quota i .topRise <=
      d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) -
        d2FlowTreeRootDeficit tree)
    (heven : quota i .topRise % 2 = 0)
    (hleft : cap i <= 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild tree (Fin.mk 0 (by omega))))
    (hright : cap i <= 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild tree (Fin.mk 7 (by omega)))) :
    d2FlowStageInvInputs scale active role quota cap i tree := by
  cases tree with
  | node G low high children =>
      have hb : low + high = G := by
        simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hbalance
      have hd : 512 * G <= cap i := by
        simpa [d2FlowTreeRootDeficit] using hdeficit
      have ha : quota i .topRise <=
          d2FlowTotal (fun s => d2FlowTreeRootDeficit (children s)) - G := by
        simpa [d2FlowTreeChild, d2FlowTreeRootDeficit] using halloc
      have hl : cap i <= 128 * d2FlowTreeRootDeficit
          (children (Fin.mk 0 (by omega))) := by
        simpa [d2FlowTreeChild] using hleft
      have hr : cap i <= 128 * d2FlowTreeRootDeficit
          (children (Fin.mk 7 (by omega))) := by
        simpa [d2FlowTreeChild] using hright
      simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
      exact ⟨hchildren, hb, hd, hquotaCap, ha, heven, hl, hr⟩

/-- At Stage 15 level one, eight Stage-14 level-two middle quotas cover both
the next top-rise quota and its endpoint-reserve requirement. -/
theorem d2FlowCandidateStage15_levelOne_quota_arithmetic
    {d : Nat} (hd : 14 <= d) :
    let c := d2FlowCandidateCapacity d 1 15
    let q14 := d2FlowCandidateQuota d 14 2 .mid
    let q15 := d2FlowCandidateQuota d 15 1 .topRise
    256 * q15 = c /\
      128 * q14 = 15 * c /\
      q15 <= 8 * q14 /\
      c <= 128 * q14 /\
      q15 % 2 = 0 := by
  let c := d2FlowCandidateCapacity d 1 15
  let q14 := d2FlowCandidateQuota d 14 2 .mid
  let q15 := d2FlowCandidateQuota d 15 1 .topRise
  have hcap := d2FlowCandidateCapacity_stage14_child_eq_32_stage15_parent
    (d := d) (i := 1) hd
  have hquota14 := d2FlowCandidateStage14_quota_exact_ratio
    (d := d) (i := 1) hd (r := .mid) (Or.inl rfl)
  have hscale : d2FlowCandidateCapacity d 2 14 = 32 * c := by
    simpa [c] using hcap
  have h128q14 : 128 * q14 = 15 * c := by
    dsimp [q14] at hquota14
    dsimp [q14]
    nlinarith [hquota14, hscale]
  have hexp : d2FlowCandidateCapacityExponent d 1 15 = 3 * d - 18 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  have hbig : 9 <= d2FlowCandidateCapacityExponent d 1 15 := by
    rw [hexp]
    omega
  have hpow : 256 * q15 = c := by
    have hsub : 8 + (d2FlowCandidateCapacityExponent d 1 15 - 8) =
        d2FlowCandidateCapacityExponent d 1 15 := by omega
    dsimp [q15, d2FlowCandidateQuota, c, d2FlowCandidateCapacity]
    calc
      256 * 2 ^ (d2FlowCandidateCapacityExponent d 1 15 - 8) =
          2 ^ 8 * 2 ^ (d2FlowCandidateCapacityExponent d 1 15 - 8) := by norm_num
      _ = 2 ^ d2FlowCandidateCapacityExponent d 1 15 := by
        rw [← pow_add, hsub]
      _ = 2 ^ d2FlowCandidateCapacityExponent d 1 15 := rfl
  have heven : q15 % 2 = 0 := by
    have hsub : d2FlowCandidateCapacityExponent d 1 15 - 8 =
        (d2FlowCandidateCapacityExponent d 1 15 - 9) + 1 := by omega
    dsimp [q15, d2FlowCandidateQuota]
    rw [hsub, pow_succ]
    omega
  have hcover : q15 <= 8 * q14 := by
    nlinarith [hpow, h128q14]
  have hreserve : c <= 128 * q14 := by
    nlinarith [h128q14]
  dsimp [c, q14, q15]
  exact ⟨hpow, h128q14, hcover, hreserve, heven⟩

/-- Every level-two child below an actual Stage-15 level-one sender has at
least the fresh Stage-14 level-two middle quota. The two-level projection
isolates that Stage-14 cut; its role adds the quota to the old nonnegative
deficit. -/
theorem d2FlowCandidateRun_stage15_levelOne_child_floor
    (childDepth : Nat) (hd : 7 <= childDepth) (j k : Fin 8) :
    d2FlowCandidateQuota (childDepth + 7) 14 2 .mid <=
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowCandidateRun (childDepth + 7)
              (d2FlowTreeInitial 8192 (childDepth + 7)) 15) j) k) := by
  let d := childDepth + 7
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  have hrun : d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 15 =
      d2FlowCandidateStage d 14 before := by rfl
  have hfront := d2FlowCandidateStage14_frontiers d (by dsimp [d]; omega)
  rcases hfront with ⟨_, _, hactive2, hrole2, _, _, _, _, _⟩
  have hinactive1 : d2FlowCandidateActive d 14 1 = false := by
    classical
    rw [d2FlowCandidateActive_matches_schedule
      (d := d) (i := 1) (t := 14) (by omega)]
    simp only [decide_eq_false_iff_not, active,
      if_neg (by decide : ¬ ((14 : Nat) = 1))]
    omega
  rw [hrun]
  simp only [d2FlowCandidateStage]
  change D2FlowTree (childDepth + 7) at before
  cases hroot : before with
  | node G low high children =>
      have hproject := d2FlowStage_child_child_of_inactive
        (active := d2FlowCandidateActive d 14)
        (role := d2FlowCandidateRole d 14)
        (quota := d2FlowCandidateQuota d 14)
        (h := childDepth + 5) (i := 0) (G := G) (low := low) (high := high)
        children hinactive1 j k
      cases hnode : d2FlowTreeChild (children j) k with
      | node G' low' high' grandchildren =>
          have hpost := d2FlowStage_active_node_deficit
            (active := d2FlowCandidateActive d 14)
            (role := d2FlowCandidateRole d 14)
            (quota := d2FlowCandidateQuota d 14)
            (h := childDepth + 4) (i := 2)
            (G := G') (low := low') (high := high') grandchildren hactive2
          have hresult : d2FlowTreeRootDeficit
              (d2FlowStage (d2FlowCandidateActive d 14)
                (d2FlowCandidateRole d 14) (d2FlowCandidateQuota d 14)
                (childDepth + 5) 2 (.node G' low' high' grandchildren)) =
              G' + d2FlowCandidateQuota d 14 2 .mid := by
            simpa [hrole2] using hpost
          rw [hproject, hnode, hresult]
          dsimp [d]
          omega

/-- Stage 14's root top-descending cut clears every level-one child's root
data, providing the zero-deficit and balance fields at Stage 15 level one. -/
theorem d2FlowCandidateRun_stage15_levelOne_child_rootdata_zero
    (childDepth : Nat) (hd : 7 <= childDepth) (j : Fin 8) :
    d2FlowTreeRootData
      (d2FlowTreeChild
        (d2FlowCandidateRun (childDepth + 7)
          (d2FlowTreeInitial 8192 (childDepth + 7)) 15) j) = (0, 0, 0) := by
  let d := childDepth + 7
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 14
  have hrun : d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 15 =
      d2FlowCandidateStage d 14 before := by rfl
  have hfront := d2FlowCandidateStage14_frontiers d (by dsimp [d]; omega)
  rcases hfront with ⟨hactive0, hrole0, _, _, _, _, _, _, _⟩
  rw [hrun]
  simp only [d2FlowCandidateStage]
  change D2FlowTree (childDepth + 7) at before
  cases hroot : before with
  | node G low high children =>
      have hzero := d2FlowStage_topDesc_child_rootdata
        (active := d2FlowCandidateActive d 14)
        (role := d2FlowCandidateRole d 14)
        (quota := d2FlowCandidateQuota d 14)
        (h := childDepth + 6) (i := 0)
        (G := G) (low := low) (high := high) children hactive0 hrole0 j
      simpa [hroot] using hzero

end Chvatal.D2Reserve
