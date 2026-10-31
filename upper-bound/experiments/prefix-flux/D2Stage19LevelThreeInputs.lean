import D2Stage19LevelThreeFloor
import D2Stage19LevelFiveInputs
import D2Stage18LevelTwoLateInputs
import D2Stage19Frontier
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- The full Stage-19 level-three middle-sender contract. Stage 18's level-two
regular cut supplies its cap and balance, and its level-four refresh quota
provides the endpoint and total-mass reserves. -/
theorem d2FlowCandidateRun_stage19_levelThree_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m : Fin 8) :
    let d := childDepth + 9
    let run19 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 19
    let tree := d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run19 j) k) m
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 19) (d2FlowCandidateRole d 19)
      (d2FlowCandidateQuota d 19)
      (fun x => d2FlowCandidateCapacity d x 19) 3 tree := by
  classical
  let d := childDepth + 9
  let initial := d2FlowTreeInitial 8192 d
  let run18 := d2FlowCandidateRun d initial 18
  let run19 := d2FlowCandidateRun d initial 19
  let parent := d2FlowTreeChild (d2FlowTreeChild run18 j) k
  let tree := d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run19 j) k) m
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hactive19 : d2FlowCandidateActive d 19 3 = true := by
    apply (d2FlowCandidateActive_stage19_iff hd14).2
    by_cases hsmall : d <= 15 <;> simp [hsmall] <;> omega
  have hrole19 : d2FlowCandidateRole d 19 3 = .mid := by
    apply d2FlowCandidateRole_stage19_mid hd14
    by_cases hsmall : d <= 15 <;> simp [hsmall] <;> omega
    all_goals omega
  have hactive18 : d2FlowCandidateActive d 18 2 = true := by
    have ht := d2FlowCandidateActive_stage18_iff (i := 2) hd14
    apply ht.mpr
    by_cases hsmall : d <= 15 <;> simp [hsmall] <;> omega
  have hrole18 : d2FlowCandidateRole d 18 2 = .mid :=
    d2FlowCandidateRole_stage18_mid2 (by dsimp [d]; omega)
  have hregular18 : d2FlowCandidateRole d 18 2 = .topRise \/
      d2FlowCandidateRole d 18 2 = .mid \/
      d2FlowCandidateRole d 18 2 = .botDesc := Or.inr (Or.inl hrole18)
  have hrunInv : d2FlowTreeInv 8192 run18 := by
    simpa [d, initial, run18] using
      d2FlowCandidateStage17_preserves_inv (childDepth + 2) (by omega)
  have hinvParent : d2FlowTreeInv 8192 parent :=
    d2FlowTreeInv_grandchild run18 hrunInv j k
  have hparentInputs := d2FlowCandidateRun_stage18_levelTwo_late_inputs
    (childDepth + 2) (by omega) j k
  have hparentInputs' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 2 parent := by
    simpa [d, initial, run18, parent] using hparentInputs
  have hrun19 : run19 = d2FlowCandidateStage d 18 run18 := by
    change d2FlowCandidateRun d initial 19 =
      d2FlowCandidateStage d 18 (d2FlowCandidateRun d initial 18)
    rw [d2FlowCandidateRun.eq_def]
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 18)
        (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
        (childDepth + 7) 2 parent) m := by
    dsimp only [tree]
    rw [hrun19]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path3_projection
      (active := d2FlowCandidateActive d 18)
      (role := d2FlowCandidateRole d 18)
      (quota := d2FlowCandidateQuota d 18)
      (h := childDepth + 6) (i := 0) run18 j k m
  have hchildBound := d2FlowStage_regular_child_g_bound_of_tree_inputs
    (active := d2FlowCandidateActive d 18)
    (role := d2FlowCandidateRole d 18)
    (quota := d2FlowCandidateQuota d 18)
    (cap := fun x => d2FlowCandidateCapacity d x 18)
    (stageDepth := childDepth + 6) (i := 2) parent
    hactive18 hregular18 hinvParent hparentInputs'
  have hcapShift : d2FlowCandidateCapacity d 3 19 =
      2 * d2FlowCandidateCapacity d 2 18 :=
    d2FlowCandidateCapacity_succ_level_next_stage d 2 18 (by omega)
  have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
      d2FlowCandidateCapacity d 3 19 := by
    have hc := hchildBound m
    rw [htreeEq, hcapShift]
    exact hc
  have hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree := by
    cases hp : parent with
    | node G low high children =>
        have hb := d2FlowStage_regular_child_balanced
          (active := d2FlowCandidateActive d 18)
          (role := d2FlowCandidateRole d 18)
          (quota := d2FlowCandidateQuota d 18)
          (h := childDepth + 6) (i := 2) (G := G)
          (low := low) (high := high) children hactive18
          hregular18 m
        simpa [htreeEq, hp] using hb
  have hquotaCap : 256 * d2FlowCandidateQuota d 19 3 .mid <=
      d2FlowCandidateCapacity d 3 19 := by
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (i := 3) (t := 19) (by omega)
    rw [hactive19] at hmatch
    have hschedActive : active d (tfD2 d) 3 19 := of_decide_eq_true hmatch.symm
    have hschedRole : d2ScheduleRole d 3 19 = .mid := by
      simpa [d2FlowCandidateRole] using hrole19
    have hq := d2FlowCandidateQuota_le_capacity_div_256
      (by omega) hschedActive (Or.inr (Or.inl hschedRole))
    simpa [hrole19, hschedRole] using hq
  have heven : d2FlowCandidateQuota d 19 3 .mid % 2 = 0 := by
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (i := 3) (t := 19) (by omega)
    rw [hactive19] at hmatch
    have hschedActive : active d (tfD2 d) 3 19 := of_decide_eq_true hmatch.symm
    have hschedRole : d2ScheduleRole d 3 19 = .mid := by
      simpa [d2FlowCandidateRole] using hrole19
    have he := d2FlowCandidateQuota_even (by omega) hschedActive
      (by omega) (Or.inr (Or.inl hschedRole))
    simpa [hrole19] using he
  have hfloor : ∀ r : Fin 8,
      d2FlowCandidateQuota d 18 4 .mid <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree r) := by
    intro r
    simpa [d, initial, run18, run19, tree] using
      d2FlowCandidateRun_stage19_levelThree_child_floor
        childDepth hd j k m r
  have hcapMass : d2FlowCandidateCapacity d 3 19 =
      2 ^ (3 * d - 20) := by
    change 2 ^ d2FlowCandidateCapacityExponent d 3 19 = _
    have he : d2FlowCandidateCapacityExponent d 3 19 = 3 * d - 20 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    rw [he]
  have hfloorValue : d2FlowCandidateQuota d 18 4 .mid =
      15 * 2 ^ (3 * d - 27) := by
    change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 4 18 - 12) = _
    have he : d2FlowCandidateCapacityExponent d 4 18 = 3 * d - 15 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    rw [he]
    congr 1 <;> omega
  have hleft : d2FlowCandidateCapacity d 3 19 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    have hf := hfloor (Fin.mk 0 (by omega))
    rw [hcapMass]
    have hf' : 15 * 2 ^ (3 * d - 27) <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
      simpa [hfloorValue] using hf
    have he : 3 * d - 20 = 7 + (3 * d - 27) := by omega
    rw [he, pow_add]
    norm_num at * <;> nlinarith
  have hright : d2FlowCandidateCapacity d 3 19 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    have hf := hfloor (Fin.mk 7 (by omega))
    rw [hcapMass]
    have hf' : 15 * 2 ^ (3 * d - 27) <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
      simpa [hfloorValue] using hf
    have he : 3 * d - 20 = 7 + (3 * d - 27) := by omega
    rw [he, pow_add]
    norm_num at * <;> nlinarith
  have htotal : 8 * d2FlowCandidateQuota d 18 4 .mid <=
      d2FlowTotal (fun r => d2FlowTreeRootDeficit (d2FlowTreeChild tree r)) := by
    change 8 * d2FlowCandidateQuota d 18 4 .mid <=
      Finset.univ.sum (fun r : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeChild tree r))
    calc
      8 * d2FlowCandidateQuota d 18 4 .mid =
          Finset.univ.sum (fun _ : Fin 8 => d2FlowCandidateQuota d 18 4 .mid) := by simp
      _ <= Finset.univ.sum (fun r : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeChild tree r)) := by
        apply Finset.sum_le_sum
        intro r hr
        exact hfloor r
  have halloc : d2FlowCandidateQuota d 19 3 .mid <=
      d2FlowTotal (fun r => d2FlowTreeRootDeficit (d2FlowTreeChild tree r)) -
        d2FlowTreeRootDeficit tree := by
    have hbudget : d2FlowCandidateQuota d 19 3 .mid +
        d2FlowTreeRootDeficit tree <= 8 * d2FlowCandidateQuota d 18 4 .mid := by
      have hq19 : d2FlowCandidateQuota d 19 3 .mid =
          15 * 2 ^ (3 * d - 32) := by
        change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 3 19 - 12) = _
        have he : d2FlowCandidateCapacityExponent d 3 19 = 3 * d - 20 := by
          simp [d2FlowCandidateCapacityExponent]
          omega
        rw [he]
        congr 1 <;> omega
      have hG : 512 * d2FlowTreeRootDeficit tree <=
          d2FlowCandidateCapacity d 3 19 := hrootcap
      have hpow : 2 ^ (3 * d - 27) = 32 * 2 ^ (3 * d - 32) := by
        have he : 3 * d - 27 = 5 + (3 * d - 32) := by omega
        rw [he, pow_add]
        norm_num
      have hcapPow : 2 ^ (3 * d - 20) = 4096 * 2 ^ (3 * d - 32) := by
        have he : 3 * d - 20 = 12 + (3 * d - 32) := by omega
        rw [he, pow_add]
        norm_num
      rw [hcapMass] at hG
      rw [hcapPow] at hG
      rw [hq19, hfloorValue, hpow]
      nlinarith [Nat.zero_le (2 ^ (3 * d - 32))]
    omega
  have hchildren : ∀ r : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 19) (d2FlowCandidateRole d 19)
        (d2FlowCandidateQuota d 19)
        (fun x => d2FlowCandidateCapacity d x 19) 4
        (d2FlowTreeChild tree r) := by
    intro r
    apply d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 19)
      (role := d2FlowCandidateRole d 19)
      (quota := d2FlowCandidateQuota d 19)
      (cap := fun x => d2FlowCandidateCapacity d x 19) 8192 4
      (d2FlowTreeChild tree r)
    · have hfalse : d2FlowCandidateActive d 19 4 = false := by
        cases h : d2FlowCandidateActive d 19 4 with
        | false => rfl
        | true =>
            have hs := (d2FlowCandidateActive_stage19_iff hd14).mp h
            by_cases hsmall : d <= 15 <;> simp [hsmall] at hs <;> omega
      exact hfalse
    · intro s
      exact d2FlowCandidateRun_stage19_levelFive_inputs
        childDepth hd j k m r s
  have hcontract := d2FlowStageInvInputs_mid_of_contract
    (scale := 8192) (i := 3) tree hactive19 hrole19 hchildren
    hbalance hrootcap hquotaCap halloc heven hleft hright
  simpa [d, initial, run19, tree] using hcontract

end Chvatal.D2Reserve
