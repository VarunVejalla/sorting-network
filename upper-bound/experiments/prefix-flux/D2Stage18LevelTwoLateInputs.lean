import D2Stage18LevelThreeQuota
import D2Stage18LevelThreeInputs
import D2Stage17LevelOneStartupInputs
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

private theorem d2FlowTreeInv_child_stage18_two
    {h scale : Nat} (tree : D2FlowTree (h + 1))
    (hinv : d2FlowTreeInv scale tree) (j : Fin 8) :
    d2FlowTreeInv scale (d2FlowTreeChild tree j) := by
  cases tree with
  | node G low high children =>
      have hx := hinv
      simp only [d2FlowTreeInv] at hx
      simpa using hx.2.2.2 j

/-- The late-depth Stage-18 level-two middle sender receives its cap and
balance from the Stage-17 level-one top-rise cut. Its child-root reserves
come from the Stage-17 level-three middle quota. -/
theorem d2FlowCandidateRun_stage18_levelTwo_late_inputs
    (childDepth : Nat) (hd : 9 <= childDepth) (j k : Fin 8) :
    let d := childDepth + 7
    let run18 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 18
    let tree := d2FlowTreeChild (d2FlowTreeChild run18 j) k
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 2 tree := by
  classical
  obtain ⟨height, rfl⟩ : ∃ height, childDepth = height + 1 :=
    ⟨childDepth - 1, by omega⟩
  let childDepth := height + 1
  let d := height + 8
  let initial := d2FlowTreeInitial 8192 d
  let run17 := d2FlowCandidateRun d initial 17
  let run18 : D2FlowTree (height + 8) :=
    d2FlowCandidateRun (height + 8) (d2FlowTreeInitial 8192 (height + 8)) 18
  let parent := d2FlowTreeChild run17 j
  let tree := d2FlowTreeChild (d2FlowTreeChild run18 j) k
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hlate : 15 < d := by dsimp [d]; omega
  have hactive18_2 : d2FlowCandidateActive d 18 2 = true := by
    apply (d2FlowCandidateActive_stage18_iff hd14).2
    simp [show ¬ d <= 15 by omega]
  have hrole18_2 : d2FlowCandidateRole d 18 2 = .mid :=
    d2FlowCandidateRole_stage18_mid2 (by omega)
  have hinvRun17 : d2FlowTreeInv 8192 run17 := by
    simpa [d, initial, run17] using
      d2FlowCandidateStage16_preserves_inv childDepth (by omega)
  have hinvParent : d2FlowTreeInv 8192 parent :=
    d2FlowTreeInv_child_stage18_two run17 hinvRun17 j
  have hparentInputs := d2FlowCandidateRun_stage17_levelOne_inputs
    childDepth (by omega) j
  have hparentInputs' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
      (d2FlowCandidateQuota d 17)
      (fun x => d2FlowCandidateCapacity d x 17) 1 parent := by
    simpa [d, initial, run17, parent] using hparentInputs
  have hrun18 : run18 = d2FlowCandidateStage d 17 run17 := by
    change d2FlowCandidateRun d initial 18 =
      d2FlowCandidateStage d 17 (d2FlowCandidateRun d initial 17)
    rw [d2FlowCandidateRun.eq_def]
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 17)
        (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
        (height + 7) 1 parent) k := by
    change d2FlowTreeChild (d2FlowTreeChild run18 j) k = _
    rw [hrun18]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_child_child_projection
      (active := d2FlowCandidateActive d 17)
      (role := d2FlowCandidateRole d 17)
      (quota := d2FlowCandidateQuota d 17)
      (h := height + 6) (i := 0) run17 j k
  have hactive17_1 : d2FlowCandidateActive d 17 1 = true := by
    apply (d2FlowCandidateActive_stage17_iff hd14).2
    exact Or.inl rfl
  have hrole17_1 : d2FlowCandidateRole d 17 1 = .topRise := by
    rw [d2FlowCandidateRole_stage17_top hd14]
    simp [show ¬ d <= 15 by omega]
  have hregular17_1 : d2FlowCandidateRole d 17 1 = .topRise \/
      d2FlowCandidateRole d 17 1 = .mid \/
      d2FlowCandidateRole d 17 1 = .botDesc := Or.inl hrole17_1
  have hchildBound := d2FlowStage_regular_child_g_bound_of_tree_inputs
    (active := d2FlowCandidateActive d 17)
    (role := d2FlowCandidateRole d 17)
    (quota := d2FlowCandidateQuota d 17)
    (cap := fun x => d2FlowCandidateCapacity d x 17)
    (stageDepth := height + 6) (i := 1) parent
    hactive17_1 hregular17_1 hinvParent hparentInputs'
  have hcapShift : d2FlowCandidateCapacity d 2 18 =
      2 * d2FlowCandidateCapacity d 1 17 :=
    d2FlowCandidateCapacity_succ_level_next_stage d 1 17 (by omega)
  have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
      d2FlowCandidateCapacity d 2 18 := by
    have hc := hchildBound k
    rw [htreeEq, hcapShift]
    simpa using hc
  have hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree := by
    cases hp : parent with
    | node G low high children =>
        have hb := d2FlowStage_regular_child_balanced
          (active := d2FlowCandidateActive d 17)
          (role := d2FlowCandidateRole d 17)
          (quota := d2FlowCandidateQuota d 17)
          (h := height + 6) (i := 1) (G := G)
          (low := low) (high := high) children hactive17_1
          hregular17_1 k
        simpa [htreeEq, hp] using hb
  have harith := d2FlowCandidateStage18_levelTwo_quota_arithmetic
    (d := d) (by omega)
  have hquotaCap : 256 * d2FlowCandidateQuota d 18 2 .mid <=
      d2FlowCandidateCapacity d 2 18 := harith.2.1
  have heven : d2FlowCandidateQuota d 18 2 .mid % 2 = 0 :=
    harith.2.2.2
  have hrelation := d2FlowCandidateStage18_levelTwo_child_reserve_relation
    (d := d) (by omega)
  have hfloor : ∀ q : Fin 8,
      d2FlowCandidateQuota d 17 3 .mid <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree q) := by
    intro q
    simpa [d, initial, run17, run18, tree] using
      d2FlowCandidateRun_stage18_levelTwo_child_quota_floor
        childDepth (by omega) j k q
  have hleft : d2FlowCandidateCapacity d 2 18 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    have hf := hfloor (Fin.mk 0 (by omega))
    omega
  have hright : d2FlowCandidateCapacity d 2 18 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    have hf := hfloor (Fin.mk 7 (by omega))
    omega
  have htotal : 8 * d2FlowCandidateQuota d 17 3 .mid <=
      d2FlowTotal (fun q =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree q)) := by
    change 8 * d2FlowCandidateQuota d 17 3 .mid <=
      Finset.univ.sum (fun q : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree q))
    calc
      8 * d2FlowCandidateQuota d 17 3 .mid =
          Finset.univ.sum (fun _ : Fin 8 =>
            d2FlowCandidateQuota d 17 3 .mid) := by simp
      _ <= Finset.univ.sum (fun q : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree q)) := by
        apply Finset.sum_le_sum
        intro q hq
        exact hfloor q
  have halloc : d2FlowCandidateQuota d 18 2 .mid <=
      d2FlowTotal (fun q =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree q)) -
        d2FlowTreeRootDeficit tree := by
    have hbudget : d2FlowCandidateQuota d 18 2 .mid +
        d2FlowTreeRootDeficit tree <=
        8 * d2FlowCandidateQuota d 17 3 .mid := by
      nlinarith [hquotaCap, hrootcap, hrelation]
    omega
  have hchildren : ∀ q : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
        (d2FlowCandidateQuota d 18)
        (fun x => d2FlowCandidateCapacity d x 18) 3
        (d2FlowTreeChild tree q) := by
    intro q
    exact d2FlowCandidateRun_stage18_levelThree_inputs
      childDepth (by omega) j k q
  have hcontract := d2FlowStageInvInputs_mid_of_contract
    (scale := 8192) (i := 2) tree hactive18_2 hrole18_2
    hchildren hbalance hrootcap hquotaCap halloc heven hleft hright
  simpa [d, initial, run17, run18, tree] using hcontract

end Chvatal.D2Reserve
