import D2Stage20LevelSixInputs
import D2Stage19LevelThreeInputs
import D2Stage18PreservesInv
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

private theorem d2FlowTreeInv_child_stage20f
    {scale h : Nat} (tree : D2FlowTree (h + 1))
    (hinv : d2FlowTreeInv scale tree) (j : Fin 8) :
    d2FlowTreeInv scale (d2FlowTreeChild tree j) := by
  cases tree with
  | node G low high children =>
      have hx := hinv
      simp only [d2FlowTreeInv] at hx
      simpa using hx.2.2.2 j

/-- The actual Stage-20 level-four middle senders satisfy their input
contract. Stage 19's level-three regular cut supplies the root cap and balance;
each child receives the Stage-19 level-five quota floor, and Stage 20's
level-six theorem supplies the recursive child contracts. -/
theorem d2FlowCandidateRun_stage20_levelFour_inputs
    (childDepth : Nat) (hd : 6 <= childDepth)
    (j k m l : Fin 8) :
    let d := childDepth + 10
    let run20 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 20
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild run20 j) k) m) l
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 20) (d2FlowCandidateRole d 20)
      (d2FlowCandidateQuota d 20)
      (fun x => d2FlowCandidateCapacity d x 20) 4 tree := by
  classical
  let d := childDepth + 10
  let initial := d2FlowTreeInitial 8192 d
  let run19 := d2FlowCandidateRun d initial 19
  let run20 := d2FlowCandidateRun d initial 20
  let parent := d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run19 j) k) m
  let tree := d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run20 j) k) m) l
  have hd16 : 16 <= d := by dsimp [d]; omega
  have hd14 : 14 <= d := by omega
  have hactive20 : d2FlowCandidateActive d 20 4 = true := by
    apply (d2FlowCandidateActive_stage20_iff hd16).2
    by_cases h16 : d = 16 <;> simp [h16]
  have hrole20 : d2FlowCandidateRole d 20 4 = .mid := by
    apply d2FlowCandidateRole_stage20_mid hd16
    · by_cases h16 : d = 16 <;> simp [h16]
    · omega
  have hactive19 : d2FlowCandidateActive d 19 3 = true := by
    apply (d2FlowCandidateActive_stage19_iff hd14).2
    by_cases hsmall : d <= 15 <;> simp [hsmall] <;> omega
  have hrole19 : d2FlowCandidateRole d 19 3 = .mid := by
    apply d2FlowCandidateRole_stage19_mid hd14
    · by_cases hsmall : d <= 15 <;> simp [hsmall] <;> omega
    · omega
  have hregular19 : d2FlowCandidateRole d 19 3 = .topRise \/
      d2FlowCandidateRole d 19 3 = .mid \/
      d2FlowCandidateRole d 19 3 = .botDesc := Or.inr (Or.inl hrole19)
  have hinv19 : d2FlowTreeInv 8192 run19 := by
    simpa [d, initial, run19] using
      d2FlowCandidateStage18_preserves_inv (childDepth + 3) (by omega)
  have hinvParent : d2FlowTreeInv 8192 parent := by
    have h1 := d2FlowTreeInv_grandchild run19 hinv19 j k
    simpa [parent] using d2FlowTreeInv_child_stage20f
      (d2FlowTreeChild (d2FlowTreeChild run19 j) k) h1 m
  have hparentInputs := d2FlowCandidateRun_stage19_levelThree_inputs
    (childDepth + 1) (by omega) j k m
  have hparentInputs' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 19) (d2FlowCandidateRole d 19)
      (d2FlowCandidateQuota d 19)
      (fun x => d2FlowCandidateCapacity d x 19) 3 parent := by
    simpa [d, initial, run19, parent] using hparentInputs
  have hrun20 : run20 = d2FlowCandidateStage d 19 run19 := by
    change d2FlowCandidateRun d initial 20 =
      d2FlowCandidateStage d 19 (d2FlowCandidateRun d initial 19)
    rw [d2FlowCandidateRun.eq_def]
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 19)
        (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
        (childDepth + 7) 3 parent) l := by
    dsimp only [tree]
    rw [hrun20]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path4_projection
      (active := d2FlowCandidateActive d 19)
      (role := d2FlowCandidateRole d 19)
      (quota := d2FlowCandidateQuota d 19)
      (h := childDepth + 6) (i := 0) run19 j k m l
  have hchildBound := d2FlowStage_regular_child_g_bound_of_tree_inputs
    (active := d2FlowCandidateActive d 19)
    (role := d2FlowCandidateRole d 19)
    (quota := d2FlowCandidateQuota d 19)
    (cap := fun x => d2FlowCandidateCapacity d x 19)
    (stageDepth := childDepth + 6) (i := 3) parent
    hactive19 hregular19 hinvParent hparentInputs'
  have hcapShift : d2FlowCandidateCapacity d 4 20 =
      2 * d2FlowCandidateCapacity d 3 19 :=
    d2FlowCandidateCapacity_succ_level_next_stage d 3 19 (by omega)
  have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
      d2FlowCandidateCapacity d 4 20 := by
    have hc := hchildBound l
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
          (h := childDepth + 6) (i := 3) (G := G)
          (low := low) (high := high) children hactive19
          hregular19 l
        simpa [htreeEq, hp] using hb
  have hquotaCap : 256 * d2FlowCandidateQuota d 20 4 .mid <=
      d2FlowCandidateCapacity d 4 20 := by
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (i := 4) (t := 20) (by omega)
    rw [hactive20] at hmatch
    have hschedActive : active d (tfD2 d) 4 20 := of_decide_eq_true hmatch.symm
    have hschedRole : d2ScheduleRole d 4 20 = .mid := by
      simpa [d2FlowCandidateRole] using hrole20
    have hq := d2FlowCandidateQuota_le_capacity_div_256
      (by omega) hschedActive (Or.inr (Or.inl hschedRole))
    simpa [hrole20, hschedRole] using hq
  have heven : d2FlowCandidateQuota d 20 4 .mid % 2 = 0 := by
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (i := 4) (t := 20) (by omega)
    rw [hactive20] at hmatch
    have hschedActive : active d (tfD2 d) 4 20 := of_decide_eq_true hmatch.symm
    have hschedRole : d2ScheduleRole d 4 20 = .mid := by
      simpa [d2FlowCandidateRole] using hrole20
    have he := d2FlowCandidateQuota_even (by omega) hschedActive
      (by omega) (Or.inr (Or.inl hschedRole))
    simpa [hrole20] using he
  have hquotaFloor : d2FlowCandidateQuota d 19 5 .mid =
      15 * 2 ^ (3 * d - 26) := by
    change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 5 19 - 12) = _
    have he : d2FlowCandidateCapacityExponent d 5 19 = 3 * d - 14 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    rw [he]
    congr 1 <;> omega
  have hcapMass : d2FlowCandidateCapacity d 4 20 = 2 ^ (3 * d - 19) := by
    change 2 ^ d2FlowCandidateCapacityExponent d 4 20 = _
    have he : d2FlowCandidateCapacityExponent d 4 20 = 3 * d - 19 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    rw [he]
  have hfloor : ∀ v : Fin 8,
      d2FlowCandidateQuota d 19 5 .mid <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree v) := by
    intro v
    dsimp only [tree]
    let parent4 := d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run19 j) k) m) l
    have hproj : d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run20 j) k) m) l) v) =
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage (d2FlowCandidateActive d 19)
              (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
              (childDepth + 6) 4 parent4) v) := by
      rw [hrun20]
      simp only [d2FlowCandidateStage]
      exact d2FlowStage_path5_projection
        (active := d2FlowCandidateActive d 19)
        (role := d2FlowCandidateRole d 19)
        (quota := d2FlowCandidateQuota d 19)
        (h := childDepth + 5) (i := 0) run19 j k m l v
    have hfalse4 : d2FlowCandidateActive d 19 4 = false := by
      cases h : d2FlowCandidateActive d 19 4 with
      | false => rfl
      | true =>
          have hs := (d2FlowCandidateActive_stage19_iff (i := 4) hd14).mp h
          by_cases hsmall : d <= 15 <;> simp [hsmall] at hs <;> omega
    cases hp : parent4 with
    | node G4 low4 high4 children4 =>
        have hstep := d2FlowStage_inactive_child
          (active := d2FlowCandidateActive d 19)
          (role := d2FlowCandidateRole d 19)
          (quota := d2FlowCandidateQuota d 19)
          (h := childDepth + 5) (i := 4) (G := G4)
          (low := low4) (high := high4) children4 hfalse4 v
        cases hc : children4 v with
        | node G5 low5 high5 children5 =>
            have hactive5 : d2FlowCandidateActive d 19 5 = true := by
              apply (d2FlowCandidateActive_stage19_iff (i := 5) hd14).2
              by_cases hsmall : d <= 15 <;> simp [hsmall] <;> omega
            have hrole5 : d2FlowCandidateRole d 19 5 = .mid :=
              d2FlowCandidateRole_stage19_mid hd14
                (by by_cases hsmall : d <= 15 <;> simp [hsmall] <;> omega)
                (by omega)
            have hdef := d2FlowStage_active_node_deficit
              (active := d2FlowCandidateActive d 19)
              (role := d2FlowCandidateRole d 19)
              (quota := d2FlowCandidateQuota d 19)
              (h := childDepth + 4) (i := 5) (G := G5)
              (low := low5) (high := high5) children5 hactive5
            have hDef' : d2FlowTreeRootDeficit
                (d2FlowStage (d2FlowCandidateActive d 19)
                  (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
                  (childDepth + 5) 5 (children4 v)) =
                G5 + d2FlowCandidateQuota d 19 5 .mid := by
              simpa [hc, hrole5] using hdef
            have hchildStage : d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 19)
                  (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
                  (childDepth + 6) 4 (.node G4 low4 high4 children4)) v =
                d2FlowStage (d2FlowCandidateActive d 19)
                  (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
                  (childDepth + 5) 5 (children4 v) := by
              simpa using hstep
            rw [hproj, hp, hchildStage, hDef']
            omega
  have hleft : d2FlowCandidateCapacity d 4 20 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    rw [hcapMass]
    have hf := hfloor (Fin.mk 0 (by omega))
    rw [hquotaFloor] at hf
    have he : 3 * d - 19 = 7 + (3 * d - 26) := by omega
    rw [he, pow_add]
    rw [show (2 : Nat) ^ 7 = 128 by norm_num]
    nlinarith
  have hright : d2FlowCandidateCapacity d 4 20 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    rw [hcapMass]
    have hf := hfloor (Fin.mk 7 (by omega))
    rw [hquotaFloor] at hf
    have he : 3 * d - 19 = 7 + (3 * d - 26) := by omega
    rw [he, pow_add]
    rw [show (2 : Nat) ^ 7 = 128 by norm_num]
    nlinarith
  have htotal : 8 * d2FlowCandidateQuota d 19 5 .mid <=
      d2FlowTotal (fun v => d2FlowTreeRootDeficit (d2FlowTreeChild tree v)) := by
    change 8 * d2FlowCandidateQuota d 19 5 .mid <=
      Finset.univ.sum (fun v : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeChild tree v))
    calc
      8 * d2FlowCandidateQuota d 19 5 .mid =
          Finset.univ.sum (fun _ : Fin 8 => d2FlowCandidateQuota d 19 5 .mid) := by simp
      _ <= Finset.univ.sum (fun v : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeChild tree v)) := by
        apply Finset.sum_le_sum
        intro v hv
        exact hfloor v
  have halloc : d2FlowCandidateQuota d 20 4 .mid <=
      d2FlowTotal (fun v => d2FlowTreeRootDeficit (d2FlowTreeChild tree v)) -
        d2FlowTreeRootDeficit tree := by
    have hbudget : d2FlowCandidateQuota d 20 4 .mid +
        d2FlowTreeRootDeficit tree <= 8 * d2FlowCandidateQuota d 19 5 .mid := by
      rw [hquotaFloor]
      have hG : 512 * d2FlowTreeRootDeficit tree <=
          d2FlowCandidateCapacity d 4 20 := hrootcap
      rw [hcapMass] at hG
      have hq : d2FlowCandidateQuota d 20 4 .mid =
          15 * 2 ^ (3 * d - 31) := by
        change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 4 20 - 12) = _
        rw [show d2FlowCandidateCapacityExponent d 4 20 = 3 * d - 19 by
          simp [d2FlowCandidateCapacityExponent]; omega]
        congr 1 <;> omega
      rw [hq]
      have hpow : 2 ^ (3 * d - 19) = 4096 * 2 ^ (3 * d - 31) := by
        have he : 3 * d - 19 = 12 + (3 * d - 31) := by omega
        rw [he, pow_add]
        norm_num
      have hpowFloor : 2 ^ (3 * d - 26) = 32 * 2 ^ (3 * d - 31) := by
        have he : 3 * d - 26 = 5 + (3 * d - 31) := by omega
        rw [he, pow_add]
        norm_num
      rw [hpowFloor]
      rw [hpow] at hG
      nlinarith [Nat.zero_le (2 ^ (3 * d - 31))]
    omega
  have hchildren : ∀ v : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 20) (d2FlowCandidateRole d 20)
        (d2FlowCandidateQuota d 20)
        (fun x => d2FlowCandidateCapacity d x 20) 5
        (d2FlowTreeChild tree v) := by
    intro v
    have hfalse5 : d2FlowCandidateActive d 20 5 = false := by
      cases h : d2FlowCandidateActive d 20 5 with
      | false => rfl
      | true =>
          have hs := (d2FlowCandidateActive_stage20_iff (d := d) (i := 5) hd16).mp h
          by_cases h16 : d = 16 <;> simp [h16] at hs <;> omega
    apply d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 20)
      (role := d2FlowCandidateRole d 20)
      (quota := d2FlowCandidateQuota d 20)
      (cap := fun x => d2FlowCandidateCapacity d x 20) 8192 5
      (d2FlowTreeChild tree v) hfalse5
    intro w
    simpa [d, initial, run20, tree] using
      d2FlowCandidateRun_stage20_levelSix_inputs childDepth hd j k m l v w
  have hcontract := d2FlowStageInvInputs_mid_of_contract
    (scale := 8192) (i := 4) tree hactive20 hrole20 hchildren
    hbalance hrootcap hquotaCap halloc heven hleft hright
  simpa [d, initial, run20, tree] using hcontract

end Chvatal.D2Reserve
