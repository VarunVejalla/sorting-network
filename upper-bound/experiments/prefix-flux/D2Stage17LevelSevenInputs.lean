import D2Stage17LevelSevenBalance
import D2Stage17LevelSevenQuota
import D2Stage16LevelSixInputs
import D2Stage15LevelSevenChildrenFull
import D2Stage15PreservesInv
import D2Stage14Contract

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowStageInvInputs
attribute [local irreducible] d2FlowCandidateRun
set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- The complete Stage-17 recursive input contract at every actual level-seven
sender. Stage-16's level-six cut supplies the root cap and balance; the
level-eight descendants retain the full native roots prepared at Stage 15. -/
theorem d2FlowCandidateRun_stage17_levelSeven_inputs
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r s : Fin 8) :
    let d := childDepth + 7
    let run17 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 17
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run17 j) k) m) l) q) r) s
    d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
      (d2FlowCandidateQuota d 17)
      (fun x => d2FlowCandidateCapacity d x 17) 7 tree := by
  obtain ⟨height, rfl⟩ : ∃ height, childDepth = height + 1 :=
    ⟨childDepth - 1, by omega⟩
  let childDepth := height + 1
  let d := height + 8
  let initial := d2FlowTreeInitial 8192 d
  let run16 := d2FlowCandidateRun d initial 16
  let run17 := d2FlowCandidateRun d initial 17
  let run15 := d2FlowCandidateRun d initial 15
  let path : D2FlowPath 7 :=
    .cons j (.cons k (.cons m (.cons l (.cons q (.cons r (.cons s .nil))))))
  let tree15 := d2FlowTreeAtPath 7 run15 path
  let pathParent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run16 j) k) m) l) q) r
  let tree := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild run17 j) k) m) l) q) r) s
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hdheight : 6 <= height := by omega
  have hactive17 : d2FlowCandidateActive d 17 7 = true := by
    apply (d2FlowCandidateActive_stage17_iff hd14).2
    exact Or.inr (Or.inr (Or.inr rfl))
  have hrole17 : d2FlowCandidateRole d 17 7 = .botDesc :=
    d2FlowCandidateRole_stage17_bottom hd14
  have hactive16 : d2FlowCandidateActive d 16 6 = true := by
    apply (d2FlowCandidateActive_stage16_iff hd14).2
    by_cases h14 : d = 14 <;> simp [h14]
  have hrole16 : d2FlowCandidateRole d 16 6 = .botDesc :=
    d2FlowCandidateRole_stage16_bottom hd14
  have hregular16 : d2FlowCandidateRole d 16 6 = .topRise \/
      d2FlowCandidateRole d 16 6 = .mid \/
      d2FlowCandidateRole d 16 6 = .botDesc :=
    Or.inr (Or.inr hrole16)
  have hfalse7 : d2FlowCandidateActive d 16 7 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hi := (d2FlowCandidateActive_stage16_iff hd14).mp ht
    by_cases h14 : d = 14 <;> simp [h14] at hi <;> omega
  have hfalse8 : d2FlowCandidateActive d 16 8 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hi := (d2FlowCandidateActive_stage16_iff hd14).mp ht
    by_cases h14 : d = 14 <;> simp [h14] at hi <;> omega
  have hactive15_7 : d2FlowCandidateActive d 15 7 = true :=
    (d2FlowCandidateActive_stage15_at hd14).2.2.2
  have hrole15_7 : d2FlowCandidateRole d 15 7 = .botRise :=
    d2FlowCandidateRole_stage15_bottom hd14
  have hfalse15_8 : d2FlowCandidateActive d 15 8 = false := by
    apply Bool.eq_false_of_not_eq_true
    intro ht
    have hi := d2FlowCandidateActive_stage15_level_bound ht
    rcases hi with h | h | h | h <;> omega
  have hinvRun16 : d2FlowTreeInv 8192 run16 := by
    simpa [d, initial, run16, childDepth] using
      d2FlowCandidateStage15_preserves_inv childDepth (by omega)
  let tree2 := d2FlowTreeChild (d2FlowTreeChild run16 j) k
  let tree4 := d2FlowTreeChild (d2FlowTreeChild tree2 m) l
  let tree6 := d2FlowTreeChild (d2FlowTreeChild tree4 q) r
  have hinv2 : d2FlowTreeInv 8192 tree2 := by
    exact d2FlowTreeInv_grandchild (h := height + 6) run16 hinvRun16 j k
  have hinv4 : d2FlowTreeInv 8192 tree4 := by
    exact d2FlowTreeInv_grandchild (h := height + 4) tree2 hinv2 m l
  have hinv6 : d2FlowTreeInv 8192 tree6 := by
    exact d2FlowTreeInv_grandchild (h := height + 2) tree4 hinv4 q r
  have hparentInputs : d2FlowStageInvInputs 8192
      (d2FlowCandidateActive d 16) (d2FlowCandidateRole d 16)
      (d2FlowCandidateQuota d 16)
      (fun x => d2FlowCandidateCapacity d x 16) 6 pathParent := by
    have h := d2FlowCandidateRun_stage16_levelSix_inputs
      childDepth (by omega) j k m l q r
    simpa [d, initial, run16, pathParent, childDepth] using h
  have hrun : d2FlowCandidateRun d initial 17 =
      d2FlowCandidateStage d 16 run16 := by
    rw [d2FlowCandidateRun.eq_def]
  have hrun15 : run16 = d2FlowCandidateStage d 15 run15 := by
    change d2FlowCandidateRun d initial 16 = d2FlowCandidateStage d 15 run15
    rw [d2FlowCandidateRun.eq_def]
  have htree16 : d2FlowTreeAtPath 7 run16 path =
      d2FlowStage (d2FlowCandidateActive d 15)
        (d2FlowCandidateRole d 15) (d2FlowCandidateQuota d 15)
        (height + 1) 7 tree15 := by
    change d2FlowTreeAtPath 7 run16 path =
      d2FlowStage (d2FlowCandidateActive d 15)
        (d2FlowCandidateRole d 15) (d2FlowCandidateQuota d 15)
        (height + 1) 7 tree15
    rw [hrun15]
    simp only [d2FlowCandidateStage]
    exact d2FlowStage_path7_tree_of_inactive_parent
      (active := d2FlowCandidateActive d 15)
      (role := d2FlowCandidateRole d 15)
      (quota := d2FlowCandidateQuota d 15)
      (h := height + 1) (i := 0) run15 j k m l q r s
      (by
        apply Bool.eq_false_of_not_eq_true
        intro ht
        have hi := d2FlowCandidateActive_stage15_level_bound ht
        rcases hi with h | h | h | h <;> omega)
  have htreeEq : tree = d2FlowTreeChild
      (d2FlowStage (d2FlowCandidateActive d 16)
        (d2FlowCandidateRole d 16) (d2FlowCandidateQuota d 16)
        (height + 2) 6 pathParent) s := by
    dsimp only [tree, run17]
    rw [hrun]
    simp only [d2FlowCandidateStage]
    rw [d2FlowStage_path7_child_projection]
  have hchildBound := d2FlowStage_regular_child_g_bound_of_tree_inputs
    (active := d2FlowCandidateActive d 16)
    (role := d2FlowCandidateRole d 16)
    (quota := d2FlowCandidateQuota d 16)
    (cap := fun x => d2FlowCandidateCapacity d x 16)
    (stageDepth := height + 1) (i := 6) pathParent
    hactive16 hregular16 hinv6 hparentInputs
  have hcapShift : d2FlowCandidateCapacity d 7 17 =
      2 * d2FlowCandidateCapacity d 6 16 :=
    d2FlowCandidateCapacity_succ_level_next_stage d 6 16 (by omega)
  have hrootcap : 512 * d2FlowTreeRootDeficit tree <=
      d2FlowCandidateCapacity d 7 17 := by
    have hc := hchildBound s
    rw [htreeEq, hcapShift]
    simpa using hc
  have hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree := by
    simpa [d, initial, run17, tree, childDepth] using
      d2FlowCandidateRun_stage17_levelSeven_balanced
        childDepth (by omega) j k m l q r s
  have hquotaGates := d2FlowCandidateStage17_levelSeven_quota_gates hd14
  have hquotaCap : 256 * d2FlowCandidateQuota d 17 7 .botDesc <=
      d2FlowCandidateCapacity d 7 17 := hquotaGates.1
  have heven : d2FlowCandidateQuota d 17 7 .botDesc % 2 = 0 := hquotaGates.2
  have hrootfull : forall u : Fin 8,
      d2FlowTreeRootDeficit (d2FlowTreeChild tree u) = 8192 * 8 ^ height := by
    intro u
    have hsource : d2FlowTreeChild tree15 u = d2FlowTreeFull 8192 height :=
      by simpa [tree15] using
        d2FlowCandidateRun_stage15_levelSeven_children_full height hdheight path u
    have hfull16 : d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowTreeAtPath 7 run16 path) u) =
          8192 * 8 ^ height := by
      rw [htree16]
      cases hnode : tree15 with
      | node G low high children =>
          have hb := d2FlowStage_botRise_child_root_deficit
            (active := d2FlowCandidateActive d 15)
            (role := d2FlowCandidateRole d 15)
            (quota := d2FlowCandidateQuota d 15)
            (h := height) (i := 7) (G := G) (low := low)
            (high := high) children hactive15_7 hrole15_7 hfalse15_8 u
          have hsrcG := congrArg d2FlowTreeRootDeficit hsource
          have hsrcG' : d2FlowTreeRootDeficit
              (d2FlowTreeChild (D2FlowTree.node G low high children) u) =
              d2FlowTreeRootDeficit (d2FlowTreeFull 8192 height) := by
            simpa [hnode] using hsrcG
          calc
            d2FlowTreeRootDeficit
                (d2FlowTreeChild
                  (d2FlowStage (d2FlowCandidateActive d 15)
                    (d2FlowCandidateRole d 15) (d2FlowCandidateQuota d 15)
                    (height + 1) 7 (D2FlowTree.node G low high children)) u) =
                d2FlowTreeRootDeficit
                  (d2FlowTreeChild (D2FlowTree.node G low high children) u) := hb
            _ = d2FlowTreeRootDeficit (d2FlowTreeFull 8192 height) := hsrcG'
            _ = 8192 * 8 ^ height := d2FlowTreeRootDeficit_full 8192 height
    have hunchanged : d2FlowTreeRootDeficit (d2FlowTreeChild tree u) =
        d2FlowTreeRootDeficit
          (d2FlowTreeChild (d2FlowTreeChild pathParent s) u) := by
      rw [htreeEq]
      cases hnode : pathParent with
      | node G low high children =>
          have hg := d2FlowStage_regular_child_grandchild_deficit
            (active := d2FlowCandidateActive d 16)
            (role := d2FlowCandidateRole d 16)
            (quota := d2FlowCandidateQuota d 16)
            (h := height) (i := 6) (G := G) (low := low)
            (high := high) children hactive16 hregular16 hfalse7 hfalse8 s u
          simpa [hnode] using hg
    have hpathTree : d2FlowTreeAtPath 7 run16 path =
        d2FlowTreeChild pathParent s := by
      simp [d2FlowTreeAtPath, path, pathParent]
    rw [hunchanged]
    simpa [hpathTree] using hfull16
  have htotal : d2FlowTotal (fun u : Fin 8 =>
      d2FlowTreeRootDeficit (d2FlowTreeChild tree u)) =
        8192 * 8 ^ (height + 1) := by
    unfold d2FlowTotal
    calc
      (Finset.univ.sum fun u : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree u)) =
        Finset.univ.sum (fun _ : Fin 8 => 8192 * 8 ^ height) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [hrootfull u]
      _ = 8 * (8192 * 8 ^ height) := by simp
      _ = 8192 * 8 ^ (height + 1) := by rw [Nat.pow_succ]; ring
  have hcapMass : d2FlowCandidateCapacity d 7 17 =
      16 * (8192 * 8 ^ (height + 1)) := by
    dsimp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent, d]
    rw [show 13 + 3 * (height + 8) + 3 * 7 - (2 * 17 + 4) =
      3 * height + 20 by omega]
    rw [show 16 = 2 ^ 4 by norm_num,
      show 8192 = 2 ^ 13 by norm_num,
      show 8 = 2 ^ 3 by norm_num]
    rw [show 3 * height + 20 = 4 + 13 + 3 * (height + 1) by omega]
    rw [pow_add, pow_add, pow_mul]
    ring_nf
  have halloc : d2FlowCandidateQuota d 17 7 .botDesc <=
      d2FlowTotal (fun u => d2FlowTreeRootDeficit (d2FlowTreeChild tree u)) -
        d2FlowTreeRootDeficit tree := by
    rw [htotal]
    have hc := hrootcap
    rw [hcapMass] at hc hquotaCap
    have hG : 32 * d2FlowTreeRootDeficit tree <=
        8192 * 8 ^ (height + 1) := by nlinarith
    have hq : 16 * d2FlowCandidateQuota d 17 7 .botDesc <=
        8192 * 8 ^ (height + 1) := by nlinarith
    have hsum : d2FlowCandidateQuota d 17 7 .botDesc +
        d2FlowTreeRootDeficit tree <= 8192 * 8 ^ (height + 1) := by omega
    omega
  have hleft : d2FlowCandidateCapacity d 7 17 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 0 (by omega))) := by
    rw [hcapMass, hrootfull]
    rw [Nat.pow_succ]
    nlinarith
  have hright : d2FlowCandidateCapacity d 7 17 <=
      128 * d2FlowTreeRootDeficit
        (d2FlowTreeChild tree (Fin.mk 7 (by omega))) := by
    rw [hcapMass, hrootfull]
    rw [Nat.pow_succ]
    nlinarith
  have hchildren : forall u : Fin 8,
      d2FlowStageInvInputs 8192
        (d2FlowCandidateActive d 17) (d2FlowCandidateRole d 17)
        (d2FlowCandidateQuota d 17)
        (fun x => d2FlowCandidateCapacity d x 17) 8
        (d2FlowTreeChild tree u) := by
    intro u
    exact d2FlowStageInvInputs_all_inactive
      (scale := 8192) (active := d2FlowCandidateActive d 17)
      (role := d2FlowCandidateRole d 17)
      (quota := d2FlowCandidateQuota d 17)
      (cap := fun x => d2FlowCandidateCapacity d x 17)
      (d2FlowTreeChild tree u) (by
        intro i hi
        apply Bool.eq_false_of_not_eq_true
        intro ht
        have hlevels := (d2FlowCandidateActive_stage17_iff hd14).mp ht
        rcases hlevels with h | h | h | h <;> omega)
  exact d2FlowStageInvInputs_botDesc_of_contract
    8192 7 tree hactive17 hrole17 hchildren hbalance hrootcap
    hquotaCap halloc heven hleft hright

end Chvatal.D2Reserve
