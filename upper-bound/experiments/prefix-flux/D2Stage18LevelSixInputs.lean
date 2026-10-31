import D2Stage18LevelSixQuota
import D2Stage17LevelFiveInputs
import D2Stage17LevelOneStartupInputs
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

private theorem d2FlowTreeInv_child_stage18
    {h scale : Nat} (tree : D2FlowTree (h + 1))
    (hinv : d2FlowTreeInv scale tree) (j : Fin 8) :
    d2FlowTreeInv scale (d2FlowTreeChild tree j) := by
  cases tree with
  | node G low high children =>
      have hx := hinv
      simp only [d2FlowTreeInv] at hx
      simpa using hx.2.2.2 j

/-- The full Stage-18 level-six middle-sender contract. The preceding Stage-17
level-five cut provides its balance and root cap; Stage 17's level-seven
bottom-descending quota provides the eight child reserves and fresh mass. -/
theorem d2FlowCandidateRun_stage18_levelSix_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r : Fin 8) :
    let d := childDepth + 7
    let run18 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 18
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild run18 j) k) m) l) q) r
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
      (d2FlowCandidateQuota d 18)
      (fun x => d2FlowCandidateCapacity d x 18) 6 tree := by
  classical
  obtain ⟨height, rfl⟩ : ∃ height, childDepth = height + 1 :=
    ⟨childDepth - 1, by omega⟩
  let childDepth := height + 1
  let d := height + 8
  let initial := d2FlowTreeInitial 8192 d
  let run17 := d2FlowCandidateRun d initial 17
  let run18 : D2FlowTree (height + 8) :=
    d2FlowCandidateRun (height + 8) (d2FlowTreeInitial 8192 (height + 8)) 18
  let parent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild run17 j) k) m) l) q
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run18 j) k) m) l) q) r
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hactive18_6 : d2FlowCandidateActive d 18 6 = true := by
    apply (d2FlowCandidateActive_stage18_iff hd14).2
    by_cases hsmall : d <= 15 <;> simp [hsmall]
  have hrole18_6 : d2FlowCandidateRole d 18 6 = .mid := by
    by_cases hsmall : d <= 15
    · exact d2FlowCandidateRole_stage18_mid46 hd14 6 (Or.inr rfl)
    · exact d2FlowCandidateRole_stage18_mid46 hd14 6 (Or.inr rfl)
  have hinvRun17 : d2FlowTreeInv 8192 run17 := by
    simpa [d, initial, run17] using
      d2FlowCandidateStage16_preserves_inv childDepth (by omega)
  have hinvParent : d2FlowTreeInv 8192 parent := by
    have h1 := d2FlowTreeInv_child_stage18 run17 hinvRun17 j
    have h2 := d2FlowTreeInv_child_stage18
      (d2FlowTreeChild run17 j) h1 k
    have h3 := d2FlowTreeInv_child_stage18
      (d2FlowTreeChild (d2FlowTreeChild run17 j) k) h2 m
    have h4 := d2FlowTreeInv_child_stage18
      (d2FlowTreeChild (d2FlowTreeChild
        (d2FlowTreeChild run17 j) k) m) h3 l
    exact d2FlowTreeInv_child_stage18
      (d2FlowTreeChild (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowTreeChild run17 j) k) m) l) h4 q
  have hparentInputs := d2FlowCandidateRun_stage17_levelFive_inputs
    childDepth (by omega) j k m l q
  have hparentInputs' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
      (d2FlowCandidateQuota d 17)
      (fun x => d2FlowCandidateCapacity d x 17) 5 parent := by
    simpa [d, initial, run17, parent] using hparentInputs
  have hrun18 : run18 = d2FlowCandidateStage d 17 run17 := by
    change d2FlowCandidateRun d initial 18 =
      d2FlowCandidateStage d 17 (d2FlowCandidateRun d initial 17)
    rw [d2FlowCandidateRun.eq_def]
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 17)
        (d2FlowCandidateRole d 17) (d2FlowCandidateQuota d 17)
        (height + 3) 5 parent) r := by
    change d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run18 j) k) m) l) q) r = _
    rw [hrun18]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path6_tree_projection
      (active := d2FlowCandidateActive d 17)
      (role := d2FlowCandidateRole d 17)
      (quota := d2FlowCandidateQuota d 17)
      (h := height + 2) (i := 0) run17 j k m l q r
  have hactive17_5 : d2FlowCandidateActive d 17 5 = true := by
    apply (d2FlowCandidateActive_stage17_iff hd14).2
    exact Or.inr (Or.inr (Or.inl rfl))
  have hrole17_5 : d2FlowCandidateRole d 17 5 = .mid :=
    d2FlowCandidateRole_stage17_mid5 hd14
  have hregular17_5 : d2FlowCandidateRole d 17 5 = .topRise \/
      d2FlowCandidateRole d 17 5 = .mid \/
      d2FlowCandidateRole d 17 5 = .botDesc := Or.inr (Or.inl hrole17_5)
  have hchildBound := d2FlowStage_regular_child_g_bound_of_tree_inputs
    (active := d2FlowCandidateActive d 17)
    (role := d2FlowCandidateRole d 17)
    (quota := d2FlowCandidateQuota d 17)
    (cap := fun x => d2FlowCandidateCapacity d x 17)
    (stageDepth := height + 2) (i := 5) parent
    hactive17_5 hregular17_5 hinvParent hparentInputs'
  have hcapShift : d2FlowCandidateCapacity d 6 18 =
      2 * d2FlowCandidateCapacity d 5 17 :=
    d2FlowCandidateCapacity_succ_level_next_stage d 5 17 (by omega)
  have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
      d2FlowCandidateCapacity d 6 18 := by
    have hc := hchildBound r
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
          (h := height + 2) (i := 5) (G := G)
          (low := low) (high := high) children hactive17_5
          hregular17_5 r
        simpa [htreeEq, hp] using hb
  have harith := d2FlowCandidateStage18_levelSix_quota_arithmetic
    (d := d) (by omega)
  have hquotaCap : 256 * d2FlowCandidateQuota d 18 6 .mid <=
      d2FlowCandidateCapacity d 6 18 := harith.1
  have heven : d2FlowCandidateQuota d 18 6 .mid % 2 = 0 :=
    harith.2.2.2.2
  have hfloor : ∀ s : Fin 8,
      d2FlowCandidateQuota d 17 7 .botDesc <=
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s) := by
    intro s
    simpa [d, initial, run17, run18, tree] using
      d2FlowCandidateRun_stage18_levelSix_child_quota_floor
        childDepth (by omega) j k m l q r s
  have hleft : d2FlowCandidateCapacity d 6 18 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    have hf := hfloor (Fin.mk 0 (by omega))
    nlinarith [harith.2.2.2.1]
  have hright : d2FlowCandidateCapacity d 6 18 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    have hf := hfloor (Fin.mk 7 (by omega))
    nlinarith [harith.2.2.2.1]
  have htotal : 8 * d2FlowCandidateQuota d 17 7 .botDesc <=
      d2FlowTotal (fun s =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
    change 8 * d2FlowCandidateQuota d 17 7 .botDesc <=
      Finset.univ.sum (fun s : Fin 8 =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s))
    calc
      8 * d2FlowCandidateQuota d 17 7 .botDesc =
          Finset.univ.sum (fun _ : Fin 8 =>
            d2FlowCandidateQuota d 17 7 .botDesc) := by simp
      _ <= Finset.univ.sum (fun s : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) := by
        apply Finset.sum_le_sum
        intro s hs
        exact hfloor s
  have halloc : d2FlowCandidateQuota d 18 6 .mid <=
      d2FlowTotal (fun s =>
        d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) -
        d2FlowTreeRootDeficit tree := by
    have hbudget : d2FlowCandidateQuota d 18 6 .mid +
        d2FlowTreeRootDeficit tree <=
        8 * d2FlowCandidateQuota d 17 7 .botDesc := by
      nlinarith [hquotaCap, hrootcap, harith.2.2.1]
    omega
  have hchildren : ∀ s : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 18) (d2FlowCandidateRole d 18)
        (d2FlowCandidateQuota d 18)
        (fun x => d2FlowCandidateCapacity d x 18) 7
        (d2FlowTreeChild tree s) := by
    intro s
    exact d2FlowCandidateRun_stage18_levelSeven_inputs
      childDepth (by omega) j k m l q r s
  have hcontract := d2FlowStageInvInputs_mid_of_contract
    (scale := 8192) (i := 6) tree hactive18_6 hrole18_6
    hchildren hbalance hrootcap hquotaCap halloc heven hleft hright
  simpa [d, initial, run17, run18, tree] using hcontract

end Chvatal.D2Reserve
