import D2Stage20LevelFourInputs
import D2Stage19LevelOneInputs
import D2Stage19PreservesInv
import D2Stage18PreservesInv
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

private theorem d2FlowTreeInv_child_stage20t
    {scale h : Nat} (tree : D2FlowTree (h + 1))
    (hinv : d2FlowTreeInv scale tree) (j : Fin 8) :
    d2FlowTreeInv scale (d2FlowTreeChild tree j) := by
  cases tree with
  | node G low high children =>
      have hx := hinv
      simp only [d2FlowTreeInv] at hx
      simpa using hx.2.2.2 j

/-- The actual Stage-20 level-two sender contract, including the depth-16
top-descending startup case. From depth 17 the level-two middle sender uses
Stage 19's level-three quota as its endpoint floor. -/
theorem d2FlowCandidateRun_stage20_levelTwo_inputs
    (childDepth : Nat) (hd : 6 <= childDepth)
    (j k : Fin 8) :
    let d := childDepth + 10
    let run20 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 20
    let tree := d2FlowTreeChild (d2FlowTreeChild run20 j) k
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 20) (d2FlowCandidateRole d 20)
      (d2FlowCandidateQuota d 20)
      (fun x => d2FlowCandidateCapacity d x 20) 2 tree := by
  classical
  let d := childDepth + 10
  let initial := d2FlowTreeInitial 8192 d
  let run19 := d2FlowCandidateRun d initial 19
  let run20 := d2FlowCandidateRun d initial 20
  let parent := d2FlowTreeChild run19 j
  let tree := d2FlowTreeChild (d2FlowTreeChild run20 j) k
  have hd16 : 16 <= d := by dsimp [d]; omega
  have hd14 : 14 <= d := by omega
  have hactive20 : d2FlowCandidateActive d 20 2 = true := by
    apply (d2FlowCandidateActive_stage20_iff hd16).2
    by_cases h16 : d = 16 <;> simp [h16]
  have hrole20 : d2FlowCandidateRole d 20 2 =
      (if d = 16 then .topDesc else .mid) := by
    by_cases h16 : d = 16
    · have hcd : childDepth = 6 := by dsimp [d] at h16; omega
      have ht := d2FlowCandidateRole_stage20_top (d := 16) (by omega)
      simpa [d, hcd] using ht
    · have hlarge : 17 <= d := by omega
      have htop : d ≠ 16 := h16
      have hrole := d2FlowCandidateRole_stage20_mid
        (d := d) (i := 2) hd16 (by simp [h16]) (by omega)
      simpa [h16] using hrole
  have hactive19 : d2FlowCandidateActive d 19 1 = true := by
    apply (d2FlowCandidateActive_stage19_iff hd14).2
    by_cases hsmall : d <= 15 <;> simp [hsmall] <;> omega
  have hrole19 : d2FlowCandidateRole d 19 1 =
      (if d = 16 then .topDesc else .topRise) := by
    have ht := d2FlowCandidateRole_stage19_top hd14
    have hnotSmall : ¬ d <= 15 := by omega
    have htop : (if d <= 15 then 3 else 1) = 1 := by simp [hnotSmall]
    rw [htop] at ht
    have hnot14 : d ≠ 14 := by omega
    simpa [hnot14] using ht
  have hinv19 : d2FlowTreeInv 8192 run19 := by
    simpa [d, initial, run19] using
      d2FlowCandidateStage18_preserves_inv (childDepth + 3) (by omega)
  have hinv20 : d2FlowTreeInv 8192 run20 := by
    simpa [d, initial, run20] using
      d2FlowCandidateStage19_preserves_inv (childDepth + 1) (by omega)
  have hinvParent : d2FlowTreeInv 8192 parent := by
    simpa [parent] using d2FlowTreeInv_child_stage20t run19 hinv19 j
  have hparentInputs := d2FlowCandidateRun_stage19_levelOne_inputs
    (childDepth + 1) (by omega) j
  have hparentInputs' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 19) (d2FlowCandidateRole d 19)
      (d2FlowCandidateQuota d 19)
      (fun x => d2FlowCandidateCapacity d x 19) 1 parent := by
    simpa [d, initial, run19, parent] using hparentInputs
  have hrun20 : run20 = d2FlowCandidateStage d 19 run19 := by
    change d2FlowCandidateRun d initial 20 =
      d2FlowCandidateStage d 19 (d2FlowCandidateRun d initial 19)
    rw [d2FlowCandidateRun.eq_def]
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 19)
        (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
        (childDepth + 9) 1 parent) k := by
    dsimp only [tree]
    rw [hrun20]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_child_child_projection
      (active := d2FlowCandidateActive d 19)
      (role := d2FlowCandidateRole d 19)
      (quota := d2FlowCandidateQuota d 19)
      (h := childDepth + 8) (i := 0) run19 j k
  have hchildren : ∀ s : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 20) (d2FlowCandidateRole d 20)
        (d2FlowCandidateQuota d 20)
        (fun x => d2FlowCandidateCapacity d x 20) 3
        (d2FlowTreeChild tree s) := by
    intro s
    have hfalse3 : d2FlowCandidateActive d 20 3 = false := by
      cases h : d2FlowCandidateActive d 20 3 with
      | false => rfl
      | true =>
          have hs := (d2FlowCandidateActive_stage20_iff (d := d) (i := 3) hd16).mp h
          by_cases h16 : d = 16 <;> simp [h16] at hs <;> omega
    apply d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 20)
      (role := d2FlowCandidateRole d 20)
      (quota := d2FlowCandidateQuota d 20)
      (cap := fun x => d2FlowCandidateCapacity d x 20) 8192 3
      (d2FlowTreeChild tree s) hfalse3
    intro v
    simpa [d, initial, run20, tree] using
      d2FlowCandidateRun_stage20_levelFour_inputs childDepth hd j k s v
  by_cases hstartup : d = 16
  · have hrole20top : d2FlowCandidateRole d 20 2 = .topDesc := by
      simpa [hstartup] using hrole20
    have hzero : d2FlowTreeRootDeficit tree = 0 := by
      rw [htreeEq]
      cases hp : parent with
      | node G low high children =>
          have hz := d2FlowStage_topDesc_child_rootdata
            (active := d2FlowCandidateActive d 19)
            (role := d2FlowCandidateRole d 19)
            (quota := d2FlowCandidateQuota d 19)
            (h := childDepth + 8) (i := 1) (G := G)
            (low := low) (high := high) children hactive19
            (by simpa [hstartup] using hrole19) k
          have hG : d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 19)
                  (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
                  (childDepth + 9) 1 (.node G low high children)) k) = 0 := by
            have hp' := congrArg Prod.fst hz
            cases ht : d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 19)
                  (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
                  (childDepth + 8 + 1) 1 (.node G low high children)) k with
            | node Gk lowk highk childrenk =>
                have hGk : Gk = 0 := by
                  simpa [ht, d2FlowTreeRootData] using hp'
                simpa [ht, d2FlowTreeRootDeficit] using hGk
          simpa [hp] using hG
    have hcontract := d2FlowStageInvInputs_topDesc_of_contract
      (scale := 8192) (i := 2) tree hactive20 hrole20top hchildren
      (by
        have hinv := d2FlowTreeInv_grandchild run20 hinv20 j k
        exact d2FlowTreeInv_root_balance_of_zero tree hinv (by omega) hzero)
      hzero
    simpa [d, initial, run20, tree] using hcontract
  · have hlarge : 17 <= d := by omega
    have hrole20mid : d2FlowCandidateRole d 20 2 = .mid := by
      simpa [hstartup] using hrole20
    have hrole19rise : d2FlowCandidateRole d 19 1 = .topRise := by
      simpa [hstartup] using hrole19
    have hregular : d2FlowCandidateRole d 19 1 = .topRise \/
        d2FlowCandidateRole d 19 1 = .mid \/
        d2FlowCandidateRole d 19 1 = .botDesc := Or.inl hrole19rise
    have hchildBound := d2FlowStage_regular_child_g_bound_of_tree_inputs
      (active := d2FlowCandidateActive d 19)
      (role := d2FlowCandidateRole d 19)
      (quota := d2FlowCandidateQuota d 19)
      (cap := fun x => d2FlowCandidateCapacity d x 19)
      (stageDepth := childDepth + 8) (i := 1) parent
      hactive19 hregular hinvParent hparentInputs'
    have hcapShift : d2FlowCandidateCapacity d 2 20 =
        2 * d2FlowCandidateCapacity d 1 19 :=
      d2FlowCandidateCapacity_succ_level_next_stage d 1 19 (by omega)
    have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
        d2FlowCandidateCapacity d 2 20 := by
      have hc := hchildBound k
      rw [htreeEq, hcapShift]
      exact hc
    have hbalance : (d2FlowTreeRootData tree).2.1 +
        (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree := by
      cases hp : parent with
      | node G low high children =>
          have hb := d2FlowStage_regular_child_balanced
            (active := d2FlowCandidateActive d 19)
            (role := d2FlowCandidateRole d 19)
            (quota := d2FlowCandidateQuota d 19)
            (h := childDepth + 8) (i := 1) (G := G)
            (low := low) (high := high) children hactive19
            hregular k
          simpa [htreeEq, hp] using hb
    have hquotaCap : 256 * d2FlowCandidateQuota d 20 2 .mid <=
        d2FlowCandidateCapacity d 2 20 := by
      have hmatch := d2FlowCandidateActive_matches_schedule
        (d := d) (i := 2) (t := 20) (by omega)
      rw [hactive20] at hmatch
      have hschedActive : active d (tfD2 d) 2 20 := of_decide_eq_true hmatch.symm
      have hschedRole : d2ScheduleRole d 2 20 = .mid := by
        simpa [d2FlowCandidateRole] using hrole20mid
      have hq := d2FlowCandidateQuota_le_capacity_div_256
        (by omega) hschedActive (Or.inr (Or.inl hschedRole))
      simpa [hrole20mid, hschedRole] using hq
    have heven : d2FlowCandidateQuota d 20 2 .mid % 2 = 0 := by
      have hmatch := d2FlowCandidateActive_matches_schedule
        (d := d) (i := 2) (t := 20) (by omega)
      rw [hactive20] at hmatch
      have hschedActive : active d (tfD2 d) 2 20 := of_decide_eq_true hmatch.symm
      have hschedRole : d2ScheduleRole d 2 20 = .mid := by
        simpa [d2FlowCandidateRole] using hrole20mid
      have he := d2FlowCandidateQuota_even (by omega) hschedActive
        (by omega) (Or.inr (Or.inl hschedRole))
      simpa [hrole20mid] using he
    have hquotaFloor : d2FlowCandidateQuota d 19 3 .mid =
        15 * 2 ^ (3 * d - 32) := by
      change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 3 19 - 12) = _
      have he : d2FlowCandidateCapacityExponent d 3 19 = 3 * d - 20 := by
        simp [d2FlowCandidateCapacityExponent]
        omega
      rw [he]
      congr 1 <;> omega
    have hcapMass : d2FlowCandidateCapacity d 2 20 = 2 ^ (3 * d - 25) := by
      change 2 ^ d2FlowCandidateCapacityExponent d 2 20 = _
      have he : d2FlowCandidateCapacityExponent d 2 20 = 3 * d - 25 := by
        simp [d2FlowCandidateCapacityExponent]
        omega
      rw [he]
    have hfloor : ∀ s : Fin 8,
        d2FlowCandidateQuota d 19 3 .mid <=
          d2FlowTreeRootDeficit (d2FlowTreeChild tree s) := by
      intro s
      dsimp only [tree]
      have hproj : d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run20 j) k) s =
          d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 19)
              (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
              (childDepth + 8) 2
              (d2FlowTreeChild (d2FlowTreeChild run19 j) k)) s := by
        rw [hrun20]
        simp only [d2FlowCandidateStage]
        exact d2FlowStage_path3_projection
          (active := d2FlowCandidateActive d 19)
          (role := d2FlowCandidateRole d 19)
          (quota := d2FlowCandidateQuota d 19)
          (h := childDepth + 7) (i := 0) run19 j k s
      have hfalse2 : d2FlowCandidateActive d 19 2 = false := by
        cases h : d2FlowCandidateActive d 19 2 with
        | false => rfl
        | true =>
            have hs := (d2FlowCandidateActive_stage19_iff (i := 2) hd14).mp h
            by_cases hsmall : d <= 15 <;> simp [hsmall] at hs <;> omega
      cases hp : d2FlowTreeChild (d2FlowTreeChild run19 j) k with
      | node G2 low2 high2 children2 =>
          have hstep := d2FlowStage_inactive_child
            (active := d2FlowCandidateActive d 19)
            (role := d2FlowCandidateRole d 19)
            (quota := d2FlowCandidateQuota d 19)
            (h := childDepth + 7) (i := 2) (G := G2)
            (low := low2) (high := high2) children2 hfalse2 s
          cases hc : children2 s with
          | node G3 low3 high3 children3 =>
              have hactive3 : d2FlowCandidateActive d 19 3 = true := by
                apply (d2FlowCandidateActive_stage19_iff (i := 3) hd14).2
                by_cases hsmall : d <= 15 <;> simp [hsmall]
              have hrole3 : d2FlowCandidateRole d 19 3 = .mid :=
                d2FlowCandidateRole_stage19_mid hd14
                  (by by_cases hsmall : d <= 15 <;> simp [hsmall] <;> omega)
                  (by omega)
              have hdef := d2FlowStage_active_node_deficit
                (active := d2FlowCandidateActive d 19)
                (role := d2FlowCandidateRole d 19)
                (quota := d2FlowCandidateQuota d 19)
                (h := childDepth + 6) (i := 3) (G := G3)
                (low := low3) (high := high3) children3 hactive3
              have hDef' : d2FlowTreeRootDeficit
                  (d2FlowStage (d2FlowCandidateActive d 19)
                    (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
                    (childDepth + 7) 3 (children2 s)) =
                  G3 + d2FlowCandidateQuota d 19 3 .mid := by
                simpa [hc, hrole3] using hdef
              have hchildStage : d2FlowTreeChild
                  (d2FlowStage (d2FlowCandidateActive d 19)
                    (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
                    (childDepth + 8) 2 (.node G2 low2 high2 children2)) s =
                  d2FlowStage (d2FlowCandidateActive d 19)
                    (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
                    (childDepth + 7) 3 (children2 s) := by
                simpa using hstep
              rw [hproj, hp, hchildStage, hDef']
              omega
    have hleft : d2FlowCandidateCapacity d 2 20 <=
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
      rw [hcapMass]
      have hf := hfloor (Fin.mk 0 (by omega))
      rw [hquotaFloor] at hf
      have he : 3 * d - 25 = 7 + (3 * d - 32) := by omega
      rw [he, pow_add]
      rw [show (2 : Nat) ^ 7 = 128 by norm_num]
      nlinarith
    have hright : d2FlowCandidateCapacity d 2 20 <=
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
      rw [hcapMass]
      have hf := hfloor (Fin.mk 7 (by omega))
      rw [hquotaFloor] at hf
      have he : 3 * d - 25 = 7 + (3 * d - 32) := by omega
      rw [he, pow_add]
      rw [show (2 : Nat) ^ 7 = 128 by norm_num]
      nlinarith
    have htotal : 8 * d2FlowCandidateQuota d 19 3 .mid <=
        d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
      change 8 * d2FlowCandidateQuota d 19 3 .mid <=
        Finset.univ.sum (fun s : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeChild tree s))
      calc
        8 * d2FlowCandidateQuota d 19 3 .mid =
            Finset.univ.sum (fun _ : Fin 8 => d2FlowCandidateQuota d 19 3 .mid) := by simp
        _ <= Finset.univ.sum (fun s : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
          apply Finset.sum_le_sum
          intro s hs
          exact hfloor s
    have halloc : d2FlowCandidateQuota d 20 2 .mid <=
        d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) -
          d2FlowTreeRootDeficit tree := by
      have hbudget : d2FlowCandidateQuota d 20 2 .mid +
          d2FlowTreeRootDeficit tree <= 8 * d2FlowCandidateQuota d 19 3 .mid := by
        rw [hquotaFloor]
        have hG : 512 * d2FlowTreeRootDeficit tree <=
            d2FlowCandidateCapacity d 2 20 := hrootcap
        rw [hcapMass] at hG
        have hq : d2FlowCandidateQuota d 20 2 .mid =
            15 * 2 ^ (3 * d - 37) := by
          change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 2 20 - 12) = _
          rw [show d2FlowCandidateCapacityExponent d 2 20 = 3 * d - 25 by
            simp [d2FlowCandidateCapacityExponent]; omega]
          congr 1 <;> omega
        rw [hq]
        have hpow : 2 ^ (3 * d - 25) = 4096 * 2 ^ (3 * d - 37) := by
          have he : 3 * d - 25 = 12 + (3 * d - 37) := by omega
          rw [he, pow_add]
          norm_num
        have hpowFloor' : 2 ^ (3 * d - 32) = 32 * 2 ^ (3 * d - 37) := by
          have he : 3 * d - 32 = 5 + (3 * d - 37) := by omega
          rw [he, pow_add]
          norm_num
        rw [hpowFloor']
        rw [hpow] at hG
        nlinarith [Nat.zero_le (2 ^ (3 * d - 37))]
      omega
    have hcontract := d2FlowStageInvInputs_mid_of_contract
      (scale := 8192) (i := 2) tree hactive20 hrole20mid hchildren
      hbalance hrootcap hquotaCap halloc heven hleft hright
    simpa [d, initial, run20, tree] using hcontract

end Chvatal.D2Reserve
