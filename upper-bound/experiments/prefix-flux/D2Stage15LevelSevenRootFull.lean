import D2Stage15LevelSevenChildrenFull
import D2Stage15LevelSevenBalance
import D2Stage14PreservesInv

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowTreeInv
attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- If the level-six sender is inactive, the level-seven subtree after the
stage is exactly its own recursive stage output. -/
theorem d2FlowStage_path7_tree_of_inactive_parent
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h i : Nat}
    (tree : D2FlowTree (h + 7))
    (j k m l q r s : Fin 8)
    (hinactive : active (i + 6) = false) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowStage active role quota (h + 7) i tree) j) k) m) l) q) r) s =
    d2FlowStage active role quota h (i + 7)
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild tree j) k) m) l) q) r) s) := by
  rw [d2FlowStage_path7_child_projection]
  cases htree : d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild tree j) k) m) l) q) r with
  | node G low high children =>
      rw [d2FlowStage_inactive_child
        (active := active) (role := role) (quota := quota)
        (i := i + 6) children hinactive s]
      rfl

/-- Stage 15's bottom-rise level-seven senders become fully native after the
cut: their children were full at their inputs and the bot-rise fills the root
to their total mass. This is the level-seven source for Stage 16 reserves. -/
theorem d2FlowCandidateRun_stage15_levelSeven_root_full
    (height : Nat) (hh : 6 <= height)
    (j k m l q r s : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowCandidateRun (height + 8)
                      (d2FlowTreeInitial 8192 (height + 8)) 16) j) k) m) l) q) r) s) =
      8192 * 8 ^ (height + 1) := by
  let d := height + 8
  let initial := d2FlowTreeInitial 8192 d
  let before := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 15
  let tree2 := d2FlowTreeChild (d2FlowTreeChild before j) k
  let tree4 := d2FlowTreeChild (d2FlowTreeChild tree2 m) l
  let tree6 := d2FlowTreeChild (d2FlowTreeChild tree4 q) r
  let tree7 := d2FlowTreeChild tree6 s
  let path : D2FlowPath 7 :=
    .cons j (.cons k (.cons m (.cons l (.cons q (.cons r (.cons s .nil))))))
  have hd : 14 <= d := by dsimp [d]; omega
  have hinvBefore : d2FlowTreeInv 8192 before := by
    simpa [d, before] using
      d2FlowCandidateStage14_preserves_inv (height + 1) (by omega)
  have hinv2 : d2FlowTreeInv 8192 tree2 := by
    change d2FlowTreeInv 8192
      (d2FlowTreeChild (d2FlowTreeChild before j) k)
    exact d2FlowTreeInv_grandchild (h := height + 6) before hinvBefore j k
  have hinv4 : d2FlowTreeInv 8192 tree4 := by
    change d2FlowTreeInv 8192
      (d2FlowTreeChild (d2FlowTreeChild tree2 m) l)
    exact d2FlowTreeInv_grandchild (h := height + 4) tree2 hinv2 m l
  have hinv6 : d2FlowTreeInv 8192 tree6 := by
    change d2FlowTreeInv 8192
      (d2FlowTreeChild (d2FlowTreeChild tree4 q) r)
    exact d2FlowTreeInv_grandchild (h := height + 2) tree4 hinv4 q r
  have hinv7 : d2FlowTreeInv 8192 tree7 := by
    cases htree6 : tree6 with
    | node G low high children =>
        have hnode := hinv6
        rw [htree6] at hnode
        simp only [d2FlowTreeInv] at hnode
        simpa [tree7, htree6] using hnode.2.2.2 s
  have hchildFull : forall u : Fin 8,
      d2FlowTreeRootDeficit (d2FlowTreeChild tree7 u) =
        8192 * 8 ^ height := by
    intro u
    have h := d2FlowCandidateRun_stage15_levelSeven_children_full
      height hh path u
    change d2FlowTreeChild tree7 u = d2FlowTreeFull 8192 height at h
    have hr := congrArg d2FlowTreeRootDeficit h
    simpa only [d2FlowTreeRootDeficit_full] using hr
  have htotal : d2FlowTotal
      (fun u => d2FlowTreeRootDeficit (d2FlowTreeChild tree7 u)) =
        8192 * 8 ^ (height + 1) := by
    unfold d2FlowTotal
    calc
      (Finset.univ.sum fun u : Fin 8 =>
          d2FlowTreeRootDeficit (d2FlowTreeChild tree7 u)) =
        Finset.univ.sum (fun _ : Fin 8 => 8192 * 8 ^ height) := by
          apply Finset.sum_congr rfl
          intro u hu
          exact hchildFull u
      _ = 8 * (8192 * 8 ^ height) := by simp
      _ = 8192 * 8 ^ (height + 1) := by
        rw [Nat.pow_succ]
        ring
  have hcover : d2FlowTreeRootDeficit tree7 <= d2FlowTotal
      (fun u => d2FlowTreeRootDeficit (d2FlowTreeChild tree7 u)) := by
    cases htree7 : tree7 with
    | node G low high children =>
        have hnode : d2FlowTreeInv 8192 (.node G low high children) := by
          simpa [htree7] using hinv7
        have hc := d2FlowTreeInv_node_children_cover children hnode
        simpa [htree7, d2FlowTreeRootDeficit, d2FlowTotal] using hc
  have hactive : d2FlowCandidateActive d 15 7 = true :=
    (d2FlowCandidateActive_stage15_at hd).2.2.2
  have hrole : d2FlowCandidateRole d 15 7 = .botRise :=
    d2FlowCandidateRole_stage15_bottom hd
  have hinactive : d2FlowCandidateActive d 15 6 = false := by
    cases h : d2FlowCandidateActive d 15 6 with
    | false => rfl
    | true =>
        have hlevel := d2FlowCandidateActive_stage15_level_bound h
        omega
  have hlocal : d2FlowTreeRootDeficit
      (d2FlowStage (d2FlowCandidateActive d 15)
        (d2FlowCandidateRole d 15) (d2FlowCandidateQuota d 15)
        (height + 1) 7 tree7) = 8192 * 8 ^ (height + 1) := by
    cases htree7 : tree7 with
    | node G low high children =>
        have hnode : d2FlowTreeInv 8192 (.node G low high children) := by
          simpa [htree7] using hinv7
        have hc := d2FlowTreeInv_node_children_cover children hnode
        have hs := d2FlowStage_botRise_root_saturates
          (quota := d2FlowCandidateQuota d 15)
          (h := height) (i := 7) (G := G) (low := low) (high := high)
          children hactive hrole hc
        rw [hs]
        simpa [htree7] using htotal
  have hproject := d2FlowStage_path7_tree_of_inactive_parent
    (active := d2FlowCandidateActive d 15)
    (role := d2FlowCandidateRole d 15)
    (quota := d2FlowCandidateQuota d 15)
    (h := height + 1) (i := 0) before j k m l q r s hinactive
  have hrun : d2FlowCandidateRun d initial 16 =
      d2FlowCandidateStage d 15 before := by
    rw [d2FlowCandidateRun]
  change d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowCandidateRun d initial 16) j) k) m) l) q) r) s) = _
  rw [hrun]
  simp only [d2FlowCandidateStage]
  rw [hproject]
  simpa [tree7, tree6, tree4, tree2, before, d] using hlocal

end Chvatal.D2Reserve
