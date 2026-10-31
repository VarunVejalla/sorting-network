import D2Stage20Frontier
import D2Stage20LevelEightArithmetic
import D2Stage19LevelSevenInputs
import D2Stage18LevelEightInputs
import D2Stage19PreservesInv
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

private theorem d2FlowTreeInv_child_stage20
    {h scale : Nat} (tree : D2FlowTree (h + 1))
    (hinv : d2FlowTreeInv scale tree) (j : Fin 8) :
    d2FlowTreeInv scale (d2FlowTreeChild tree j) := by
  cases tree with
  | node G low high children =>
      have hx := hinv
      simp only [d2FlowTreeInv] at hx
      simpa using hx.2.2.2 j

private theorem d2FlowStageInvInputs_inactive_tail_stage20
    {scale : Nat} {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {cap : Nat → Nat}
    (i : Nat) : ∀ {h : Nat} (tree : D2FlowTree h),
      (∀ t, i ≤ t → active t = false) →
      d2FlowStageInvInputs scale active role quota cap i tree := by
  intro h
  induction h generalizing i with
  | zero =>
      intro tree _
      cases tree
      simp [d2FlowStageInvInputs]
  | succ h ih =>
      intro tree hinactive
      cases tree with
      | node G low high children =>
          have hfalse : active i = false := hinactive i (Nat.le_refl i)
          simp only [d2FlowStageInvInputs, hfalse]
          refine ⟨?_, trivial⟩
          intro j
          exact ih (i + 1) (children j) (by
            intro t ht
            exact hinactive t (by omega))

/-- After the Stage-19 level-seven descending cut, every actual Stage-20
level-eight sender satisfies its bot-descending input contract. The root cap
is the exact next-level capacity shift; its level-nine children remain full
native subtrees. -/
theorem d2FlowCandidateRun_stage20_levelEight_inputs
    (childDepth : Nat) (hd : 6 ≤ childDepth)
    (j k m l q r s u : Fin 8) :
    let d := childDepth + 10
    let run20 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 20
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild run20 j) k) m) l) q) r) s) u
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 20) (d2FlowCandidateRole d 20)
      (d2FlowCandidateQuota d 20)
      (fun x => d2FlowCandidateCapacity d x 20) 8 tree := by
  classical
  let d := childDepth + 10
  let initial := d2FlowTreeInitial 8192 d
  let run19 := d2FlowCandidateRun d initial 19
  let run20 := d2FlowCandidateRun d initial 20
  let parent := d2FlowTreeChild (d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild
        (d2FlowTreeChild run19 j) k) m) l) q) r) s
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run20 j) k) m) l) q) r) s) u
  have hd16 : 16 ≤ d := by dsimp [d]; omega
  have hd14 : 14 ≤ d := by omega
  have hactive20 : d2FlowCandidateActive d 20 8 = true := by
    apply (d2FlowCandidateActive_stage20_iff hd16).2
    by_cases h16 : d = 16
    · simp [h16]
    · simp [h16]
  have hrole20 : d2FlowCandidateRole d 20 8 = .botDesc :=
    d2FlowCandidateRole_stage20_bottom hd16
  have hactive19 : d2FlowCandidateActive d 19 7 = true := by
    apply (d2FlowCandidateActive_stage19_iff hd14).2
    by_cases hsmall : d ≤ 15 <;> simp [hsmall] <;> omega
  have hrole19 : d2FlowCandidateRole d 19 7 = .botDesc :=
    d2FlowCandidateRole_stage19_bottom hd14
  have hregular19 : d2FlowCandidateRole d 19 7 = .topRise ∨
      d2FlowCandidateRole d 19 7 = .mid ∨
      d2FlowCandidateRole d 19 7 = .botDesc := Or.inr (Or.inr hrole19)
  have hinv19 : d2FlowTreeInv 8192 run19 := by
    simpa [d, initial, run19] using
      d2FlowCandidateStage18_preserves_inv (childDepth + 3) (by omega)
  have hinvParent : d2FlowTreeInv 8192 parent := by
    have h1 := d2FlowTreeInv_child_stage20 run19 hinv19 j
    have h2 := d2FlowTreeInv_child_stage20
      (d2FlowTreeChild run19 j) h1 k
    have h3 := d2FlowTreeInv_child_stage20
      (d2FlowTreeChild (d2FlowTreeChild run19 j) k) h2 m
    have h4 := d2FlowTreeInv_child_stage20
      (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run19 j) k) m) h3 l
    have h5 := d2FlowTreeInv_child_stage20
      (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild
        (d2FlowTreeChild run19 j) k) m) l) h4 q
    have h6 := d2FlowTreeInv_child_stage20
      (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowTreeChild run19 j) k) m) l) q) h5 r
    simpa [parent] using
      d2FlowTreeInv_child_stage20
        (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild
          (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run19 j) k) m) l) q) r)
        h6 s
  have hparentInputs := d2FlowCandidateRun_stage19_levelSeven_inputs
    (childDepth + 1) (by omega) j k m l q r s
  have hparentInputs' : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 19) (d2FlowCandidateRole d 19)
      (d2FlowCandidateQuota d 19)
      (fun x => d2FlowCandidateCapacity d x 19) 7 parent := by
    simpa [d, initial, run19, parent] using hparentInputs
  have hrun20 : run20 = d2FlowCandidateStage d 19 run19 := by
    change d2FlowCandidateRun d initial 20 =
      d2FlowCandidateStage d 19 (d2FlowCandidateRun d initial 19)
    rw [d2FlowCandidateRun.eq_def]
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 19)
        (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
        (childDepth + 3) 7 parent) u := by
    dsimp only [tree]
    rw [hrun20]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path8_projection
      (active := d2FlowCandidateActive d 19)
      (role := d2FlowCandidateRole d 19)
      (quota := d2FlowCandidateQuota d 19)
      (h := childDepth + 2) (i := 0) run19 j k m l q r s u
  have hchildBound := d2FlowStage_regular_child_g_bound_of_tree_inputs
    (active := d2FlowCandidateActive d 19)
    (role := d2FlowCandidateRole d 19)
    (quota := d2FlowCandidateQuota d 19)
    (cap := fun x => d2FlowCandidateCapacity d x 19)
    (stageDepth := childDepth + 2) (i := 7) parent
    hactive19 hregular19 hinvParent hparentInputs'
  have hcapShift : d2FlowCandidateCapacity d 8 20 =
      2 * d2FlowCandidateCapacity d 7 19 :=
    d2FlowCandidateCapacity_succ_level_next_stage d 7 19 (by omega)
  have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
      d2FlowCandidateCapacity d 8 20 := by
    have hc := hchildBound u
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
          (h := childDepth + 2) (i := 7) (G := G)
          (low := low) (high := high) children hactive19
          hregular19 u
        simpa [htreeEq, hp] using hb
  have hquotaCap : 256 * d2FlowCandidateQuota d 20 8 .botDesc <=
      d2FlowCandidateCapacity d 8 20 := by
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (i := 8) (t := 20) (by omega)
    rw [hactive20] at hmatch
    have hschedActive : active d (tfD2 d) 8 20 := of_decide_eq_true hmatch.symm
    have hschedRole : d2ScheduleRole d 8 20 = .botDesc := by
      simpa [d2FlowCandidateRole] using hrole20
    have hq := d2FlowCandidateQuota_le_capacity_div_256
      (by omega) hschedActive (Or.inr (Or.inr hschedRole))
    simpa [hrole20, hschedRole] using hq
  have heven : d2FlowCandidateQuota d 20 8 .botDesc % 2 = 0 := by
    have hmatch := d2FlowCandidateActive_matches_schedule
      (d := d) (i := 8) (t := 20) (by omega)
    rw [hactive20] at hmatch
    have hschedActive : active d (tfD2 d) 8 20 := of_decide_eq_true hmatch.symm
    have hschedRole : d2ScheduleRole d 8 20 = .botDesc := by
      simpa [d2FlowCandidateRole] using hrole20
    have he := d2FlowCandidateQuota_even (by omega) hschedActive
      (by omega) (Or.inr (Or.inr hschedRole))
    simpa [hrole20] using he
  let tree19eight := d2FlowTreeChild (d2FlowTreeChild
    (d2FlowTreeChild (d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowTreeChild run19 j) k) m) l) q) r) s) u
  have hInv8 : d2FlowTreeInv 8192 tree19eight := by
    have h1 := d2FlowTreeInv_child_stage20 run19 hinv19 j
    have h2 := d2FlowTreeInv_child_stage20 (d2FlowTreeChild run19 j) h1 k
    have h3 := d2FlowTreeInv_child_stage20 (d2FlowTreeChild
      (d2FlowTreeChild run19 j) k) h2 m
    have h4 := d2FlowTreeInv_child_stage20 (d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild run19 j) k) m) h3 l
    have h5 := d2FlowTreeInv_child_stage20 (d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run19 j) k) m) l) h4 q
    have h6 := d2FlowTreeInv_child_stage20 (d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild
        (d2FlowTreeChild run19 j) k) m) l) q) h5 r
    have h7 := d2FlowTreeInv_child_stage20 (d2FlowTreeChild
      (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowTreeChild run19 j) k) m) l) q) r) h6 s
    simpa [tree19eight] using d2FlowTreeInv_child_stage20
      (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild
        (d2FlowTreeChild (d2FlowTreeChild (d2FlowTreeChild run19 j) k) m) l) q) r) s) h7 u
  have hfull8 : d2FlowTreeRootDeficit tree19eight =
      8192 * 8 ^ (childDepth + 2) := by
    simpa [tree19eight, d, initial, run19] using
      d2FlowCandidateRun_stage19_levelEight_root_full
        (childDepth + 1) (by omega) j k m l q r s u
  have hchildrenFull : ∀ v : Fin 8,
      d2FlowTreeRootDeficit (d2FlowTreeChild tree19eight v) =
        8192 * 8 ^ (childDepth + 1) := by
    cases ht : tree19eight with
    | node G low high children =>
        have hinvNode : d2FlowTreeInv 8192 (.node G low high children) := by
          simpa [ht] using hInv8
        have hG : G = 8192 * 8 ^ (childDepth + 2) := by
          simpa [ht, d2FlowTreeRootDeficit] using hfull8
        intro v
        have hv := d2FlowTreeInv_native_node_children children hinvNode hG v
        simpa [ht, d2FlowTreeChild, d2FlowTreeRootDeficit] using hv
  have hchild9Unchanged : ∀ v : Fin 8,
      d2FlowTreeRootDeficit (d2FlowTreeChild tree v) =
      d2FlowTreeRootDeficit (d2FlowTreeChild tree19eight v) := by
    intro v
    rw [htreeEq]
    cases hp : parent with
    | node G7 low7 high7 children7 =>
        have hdecomp := d2FlowStage_child_decomposes
          (active := d2FlowCandidateActive d 19)
          (role := d2FlowCandidateRole d 19)
          (quota := d2FlowCandidateQuota d 19)
          (h := childDepth + 2) (i := 7) (G := G7)
          (low := low7) (high := high7) children7 u
        rw [hdecomp]
        rw [d2FlowTreeChild_setRoot]
        have hinactive8 : d2FlowCandidateActive d 19 8 = false := by
          have hs := (d2FlowCandidateActive_stage19_iff (i := 8) hd14)
          cases hh : d2FlowCandidateActive d 19 8 with
          | false => rfl
          | true => have hlevels := hs.mp hh; by_cases hsmall : d ≤ 15 <;> simp [hsmall] at hlevels <;> omega
        cases hc : children7 u with
        | node G8 low8 high8 children8 =>
            have hstep := d2FlowStage_inactive_child
              (active := d2FlowCandidateActive d 19)
              (role := d2FlowCandidateRole d 19)
              (quota := d2FlowCandidateQuota d 19)
              (h := childDepth + 1) (i := 8)
              (G := G8) (low := low8) (high := high8)
              children8 hinactive8 v
            have hinactive9 : d2FlowCandidateActive d 19 9 = false := by
              have hs := (d2FlowCandidateActive_stage19_iff (i := 9) hd14)
              cases hh : d2FlowCandidateActive d 19 9 with
              | false => rfl
              | true => have hlevels := hs.mp hh; by_cases hsmall : d ≤ 15 <;> simp [hsmall] at hlevels <;> omega
            have hroot := d2FlowStage_root_deficit_of_inactive
              (active := d2FlowCandidateActive d 19)
              (role := d2FlowCandidateRole d 19)
              (quota := d2FlowCandidateQuota d 19)
              (h := childDepth + 1) (i := 9) (children8 v) hinactive9
            have hDef := congrArg d2FlowTreeRootDeficit hstep
            rw [hroot] at hDef
            have hdepth : childDepth + 1 + 1 = childDepth + 2 := by omega
            have hDef' : d2FlowTreeRootDeficit
                (d2FlowTreeChild
                  (d2FlowStage (d2FlowCandidateActive d 19)
                    (d2FlowCandidateRole d 19) (d2FlowCandidateQuota d 19)
                    (childDepth + 2) 8 (.node G8 low8 high8 children8)) v) =
                d2FlowTreeRootDeficit (children8 v) := by
              simpa only [hdepth] using hDef
            have hTree19 : tree19eight = d2FlowTreeChild parent u := by rfl
            have hOrig : d2FlowTreeRootDeficit
                (d2FlowTreeChild tree19eight v) =
                d2FlowTreeRootDeficit (children8 v) := by
              rw [hTree19, hp]
              change d2FlowTreeRootDeficit
                  (d2FlowTreeChild (children7 u) v) = _
              rw [hc]
              rfl
            exact hDef'.trans hOrig.symm
  have hcapMass : d2FlowCandidateCapacity d 8 20 =
      128 * (8192 * 8 ^ (childDepth + 1)) := by
    have harith := d2FlowCandidateStage20_levelEight_arithmetic childDepth hd
    simpa [d] using harith.1
  have hleft : d2FlowCandidateCapacity d 8 20 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    rw [hcapMass, hchild9Unchanged (Fin.mk 0 (by omega)), hchildrenFull]
  have hright : d2FlowCandidateCapacity d 8 20 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    rw [hcapMass, hchild9Unchanged (Fin.mk 7 (by omega)), hchildrenFull]
  have htotal : 8 * (8192 * 8 ^ (childDepth + 1)) <=
      d2FlowTotal (fun v => d2FlowTreeRootDeficit
        (d2FlowTreeChild tree v)) := by
    change 8 * (8192 * 8 ^ (childDepth + 1)) <=
      Finset.univ.sum (fun v : Fin 8 => d2FlowTreeRootDeficit (d2FlowTreeChild tree v))
    calc
      8 * (8192 * 8 ^ (childDepth + 1)) =
          Finset.univ.sum (fun _ : Fin 8 => 8192 * 8 ^ (childDepth + 1)) := by simp
      _ = Finset.univ.sum (fun v : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree v)) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hchild9Unchanged v, hchildrenFull v]
      _ ≤ Finset.univ.sum (fun v : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree v)) := le_rfl
  have halloc : d2FlowCandidateQuota d 20 8 .botDesc <=
      d2FlowTotal (fun v => d2FlowTreeRootDeficit
        (d2FlowTreeChild tree v)) - d2FlowTreeRootDeficit tree := by
    have hbudget : d2FlowCandidateQuota d 20 8 .botDesc +
        d2FlowTreeRootDeficit tree <= 8 * (8192 * 8 ^ (childDepth + 1)) := by
      have hG : 512 * d2FlowTreeRootDeficit tree <=
          d2FlowCandidateCapacity d 8 20 := hrootcap
      have hq : 256 * d2FlowCandidateQuota d 20 8 .botDesc <=
          d2FlowCandidateCapacity d 8 20 := hquotaCap
      rw [hcapMass] at hG hq
      nlinarith [Nat.zero_le (8192 * 8 ^ (childDepth + 1))]
    omega
  have hchildren : ∀ v : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 20) (d2FlowCandidateRole d 20)
        (d2FlowCandidateQuota d 20)
        (fun x => d2FlowCandidateCapacity d x 20) 9
        (d2FlowTreeChild tree v) := by
    intro v
    apply d2FlowStageInvInputs_inactive_tail_stage20
      (scale := 8192) (active := d2FlowCandidateActive d 20)
      (role := d2FlowCandidateRole d 20)
      (quota := d2FlowCandidateQuota d 20)
      (cap := fun x => d2FlowCandidateCapacity d x 20) 9
    intro t ht
    cases h : d2FlowCandidateActive d 20 t with
    | false => rfl
    | true =>
        have hs := (d2FlowCandidateActive_stage20_iff (d := d) (i := t) hd16).mp h
        by_cases h16 : d = 16 <;> simp [h16] at hs <;> omega
  have hcontract := d2FlowStageInvInputs_botDesc_of_contract
    (scale := 8192) (i := 8) tree hactive20 hrole20 hchildren
    hbalance hrootcap hquotaCap halloc heven hleft hright
  simpa [d, initial, run20, tree] using hcontract

end Chvatal.D2Reserve
