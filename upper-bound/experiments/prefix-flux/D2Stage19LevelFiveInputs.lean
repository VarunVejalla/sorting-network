import D2Stage19LevelFiveFloor
import D2Stage18LevelFourInputs
import D2Stage19LevelSevenInputs
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

private theorem d2FlowStage_path5_tree_projection
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i : Nat}
    (tree : D2FlowTree (h + 5)) (j k m l q : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowStage active role quota (h + 5) i tree) j) k) m) l) q =
    d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) (i + 4)
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild tree j) k) m) l)) q := by
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]
  rw [d2FlowStage_child_child_projection]

/-- Stage 19's level-five middle-sender contract. The previous Stage-18
level-four regular cut bounds and balances its roots; the Stage-18 refresh
leaves a generous level-six quota reserve, and the Stage-19 level-seven
contract supplies all recursive child inputs. -/
theorem d2FlowCandidateRun_stage19_levelFive_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q : Fin 8) :
    let d := childDepth + 9
    let run19 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 19
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run19 j) k) m) l) q
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 19) (d2FlowCandidateRole d 19)
      (d2FlowCandidateQuota d 19)
      (fun x => d2FlowCandidateCapacity d x 19) 5 tree := by
  classical
  let d := childDepth + 9
  let initial := d2FlowTreeInitial 8192 d
  let run18 := d2FlowCandidateRun d initial 18
  let run19 := d2FlowCandidateRun d initial 19
  let parent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild run18 j) k) m) l
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild run19 j) k) m) l) q
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hactive19 : d2FlowCandidateActive d 19 5 = true := by
    apply (d2FlowCandidateActive_stage19_iff hd14).2
    by_cases hsmall : d <= 15 <;> simp [hsmall] <;> omega
  have hrole19 : d2FlowCandidateRole d 19 5 = .mid := by
    apply d2FlowCandidateRole_stage19_mid hd14
    by_cases hsmall : d <= 15 <;> simp [hsmall] <;> omega
    all_goals omega
  have hactive18 : d2FlowCandidateActive d 18 4 = true := by
    apply (d2FlowCandidateActive_stage18_iff hd14).2
    by_cases hsmall : d <= 15 <;> simp [hsmall]
  have hrole18 : d2FlowCandidateRole d 18 4 = .mid :=
    d2FlowCandidateRole_stage18_mid46 hd14 4 (Or.inl rfl)
  have hregular18 : d2FlowCandidateRole d 18 4 = .topRise \/
      d2FlowCandidateRole d 18 4 = .mid \/
      d2FlowCandidateRole d 18 4 = .botDesc := Or.inr (Or.inl hrole18)
  have hrunInv : d2FlowTreeInv 8192 run18 := by
    simpa [d, initial, run18] using
      d2FlowCandidateStage17_preserves_inv (childDepth + 2) (by omega)
  have hinvParent : d2FlowTreeInv 8192 parent := by
    have h2 := d2FlowTreeInv_grandchild (h := childDepth + 7)
      run18 hrunInv j k
    have h4 := d2FlowTreeInv_grandchild (h := childDepth + 5)
      (d2FlowTreeChild (d2FlowTreeChild run18 j) k) h2 m l
    simpa [parent] using h4
  have hparentInputs := d2FlowCandidateRun_stage18_levelFour_inputs
    (childDepth + 2) (by omega) j k m l
  have hparentInputs' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 4 parent := by
    simpa [d, initial, run18, parent] using hparentInputs
  have hrun19 : run19 = d2FlowCandidateStage d 18 run18 := by
    change d2FlowCandidateRun d initial 19 =
      d2FlowCandidateStage d 18 (d2FlowCandidateRun d initial 18)
    rw [d2FlowCandidateRun.eq_def]
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 18)
        (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
        (childDepth + 5) 4 parent) q := by
    dsimp only [tree]
    rw [hrun19]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path5_tree_projection
      (active := d2FlowCandidateActive d 18)
      (role := d2FlowCandidateRole d 18)
      (quota := d2FlowCandidateQuota d 18)
      (h := childDepth + 4) (i := 0) run18 j k m l q
  have hchildBound := d2FlowStage_regular_child_g_bound_of_tree_inputs
    (active := d2FlowCandidateActive d 18)
    (role := d2FlowCandidateRole d 18)
    (quota := d2FlowCandidateQuota d 18)
    (cap := fun x => d2FlowCandidateCapacity d x 18)
    (stageDepth := childDepth + 4) (i := 4) parent
    hactive18 hregular18 hinvParent hparentInputs'
  have hcapShift : d2FlowCandidateCapacity d 5 19 =
      2 * d2FlowCandidateCapacity d 4 18 :=
    d2FlowCandidateCapacity_succ_level_next_stage d 4 18 (by omega)
  have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
      d2FlowCandidateCapacity d 5 19 := by
    have hc := hchildBound q
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
          (h := childDepth + 4) (i := 4) (G := G)
          (low := low) (high := high) children hactive18
          hregular18 q
        simpa [htreeEq, hp] using hb
  have hquotaCap : 256 * d2FlowCandidateQuota d 19 5 .mid <=
      d2FlowCandidateCapacity d 5 19 := by
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (i := 5) (t := 19) (by omega)
    rw [hactive19] at hmatch
    have hschedActive : active d (tfD2 d) 5 19 := of_decide_eq_true hmatch.symm
    have hschedRole : d2ScheduleRole d 5 19 = .mid := by
      simpa [d2FlowCandidateRole] using hrole19
    have hq := d2FlowCandidateQuota_le_capacity_div_256
      (by omega) hschedActive (Or.inr (Or.inl hschedRole))
    simpa [hrole19, hschedRole] using hq
  have heven : d2FlowCandidateQuota d 19 5 .mid % 2 = 0 := by
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (i := 5) (t := 19) (by omega)
    rw [hactive19] at hmatch
    have hschedActive : active d (tfD2 d) 5 19 := of_decide_eq_true hmatch.symm
    have hschedRole : d2ScheduleRole d 5 19 = .mid := by
      simpa [d2FlowCandidateRole] using hrole19
    have he := d2FlowCandidateQuota_even (by omega) hschedActive
      (by omega) (Or.inr (Or.inl hschedRole))
    simpa [hrole19] using he
  have hfloor : ∀ r : Fin 8,
      d2FlowCandidateQuota d 18 6 .mid <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree r) := by
    intro r
    simpa [d, initial, run18, run19, tree] using
      d2FlowCandidateRun_stage19_levelFive_child_floor
        childDepth hd j k m l q r
  have hcapMass : d2FlowCandidateCapacity d 5 19 =
      2 ^ (3 * d - 14) := by
    change 2 ^ d2FlowCandidateCapacityExponent d 5 19 = _
    have he : d2FlowCandidateCapacityExponent d 5 19 = 3 * d - 14 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    rw [he]
  have hfloorValue : d2FlowCandidateQuota d 18 6 .mid =
      15 * 2 ^ (3 * d - 21) := by
    change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 6 18 - 12) = _
    have he : d2FlowCandidateCapacityExponent d 6 18 = 3 * d - 9 := by
      simp [d2FlowCandidateCapacityExponent]
      omega
    rw [he]
    congr 1 <;> omega
  have hleft : d2FlowCandidateCapacity d 5 19 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    have hf := hfloor (Fin.mk 0 (by omega))
    rw [hcapMass]
    have hf' : 15 * 2 ^ (3 * d - 21) <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
      simpa [hfloorValue] using hf
    have he : 3 * d - 14 = 7 + (3 * d - 21) := by omega
    rw [he, pow_add]
    norm_num at * <;> nlinarith
  have hright : d2FlowCandidateCapacity d 5 19 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    have hf := hfloor (Fin.mk 7 (by omega))
    rw [hcapMass]
    have hf' : 15 * 2 ^ (3 * d - 21) <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
      simpa [hfloorValue] using hf
    have he : 3 * d - 14 = 7 + (3 * d - 21) := by omega
    rw [he, pow_add]
    norm_num at * <;> nlinarith
  have htotal : 8 * d2FlowCandidateQuota d 18 6 .mid <=
      d2FlowTotal (fun r => d2FlowTreeRootDeficit (d2FlowTreeChild tree r)) := by
    change 8 * d2FlowCandidateQuota d 18 6 .mid <=
      Finset.univ.sum (fun r : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeChild tree r))
    calc
      8 * d2FlowCandidateQuota d 18 6 .mid =
          Finset.univ.sum (fun _ : Fin 8 => d2FlowCandidateQuota d 18 6 .mid) := by simp
      _ <= Finset.univ.sum (fun r : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeChild tree r)) := by
        apply Finset.sum_le_sum
        intro r hr
        exact hfloor r
  have halloc : d2FlowCandidateQuota d 19 5 .mid <=
      d2FlowTotal (fun r => d2FlowTreeRootDeficit (d2FlowTreeChild tree r)) -
        d2FlowTreeRootDeficit tree := by
    have hbudget : d2FlowCandidateQuota d 19 5 .mid +
        d2FlowTreeRootDeficit tree <= 8 * d2FlowCandidateQuota d 18 6 .mid := by
      have hq19 : d2FlowCandidateQuota d 19 5 .mid =
          15 * 2 ^ (3 * d - 26) := by
        change 15 * 2 ^ (d2FlowCandidateCapacityExponent d 5 19 - 12) = _
        have he : d2FlowCandidateCapacityExponent d 5 19 = 3 * d - 14 := by
          simp [d2FlowCandidateCapacityExponent]
          omega
        rw [he]
        congr 1 <;> omega
      have hG : 512 * d2FlowTreeRootDeficit tree <=
          d2FlowCandidateCapacity d 5 19 := hrootcap
      have hpow : 2 ^ (3 * d - 21) = 32 * 2 ^ (3 * d - 26) := by
        have he : 3 * d - 21 = 5 + (3 * d - 26) := by omega
        rw [he, pow_add]
        norm_num
      have hcapPow : 2 ^ (3 * d - 14) = 4096 * 2 ^ (3 * d - 26) := by
        have he : 3 * d - 14 = 12 + (3 * d - 26) := by omega
        rw [he, pow_add]
        norm_num
      rw [hcapMass] at hG
      rw [hcapPow] at hG
      rw [hq19, hfloorValue, hpow]
      nlinarith [Nat.zero_le (2 ^ (3 * d - 26))]
    omega
  have hchildren : ∀ r : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 19) (d2FlowCandidateRole d 19)
        (d2FlowCandidateQuota d 19)
        (fun x => d2FlowCandidateCapacity d x 19) 6
        (d2FlowTreeChild tree r) := by
    intro r
    apply d2FlowStageInvInputs_inactive_of_children
      (active := d2FlowCandidateActive d 19)
      (role := d2FlowCandidateRole d 19)
      (quota := d2FlowCandidateQuota d 19)
      (cap := fun x => d2FlowCandidateCapacity d x 19) 8192 6
      (d2FlowTreeChild tree r)
    · have hfalse : d2FlowCandidateActive d 19 6 = false := by
        cases h : d2FlowCandidateActive d 19 6 with
        | false => rfl
        | true =>
            have hs := (d2FlowCandidateActive_stage19_iff hd14).mp h
            by_cases hsmall : d <= 15 <;> simp [hsmall] at hs <;> omega
      exact hfalse
    · intro s
      exact d2FlowCandidateRun_stage19_levelSeven_inputs
        childDepth hd j k m l q r s
  have hcontract := d2FlowStageInvInputs_mid_of_contract
    (scale := 8192) (i := 5) tree hactive19 hrole19 hchildren
    hbalance hrootcap hquotaCap halloc heven hleft hright
  simpa [d, initial, run19, tree] using hcontract

end Chvatal.D2Reserve
