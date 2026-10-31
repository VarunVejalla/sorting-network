import D2Stage19Frontier
import D2Stage15LevelSevenBalance
import D2Stage18LevelEightChildrenFull
import D2NativeBotRise

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-- Along any depth-eight path, an inactive level-seven parent lets the
global recursive stage reach the selected level-eight subtree unchanged by
that parent's root write. Thus the selected subtree is exactly its own local
stage result. -/
theorem d2FlowStage_path8_tree_projection_of_inactive_parent
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i : Nat}
    (tree : D2FlowTree (h + 1 + 7))
    (j k m l q r s u : Fin 8)
    (hinactive : active (i + 7) = false) :
    d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowStage active role quota (h + 1 + 7) i tree) j) k) m) l) q) r) s) u =
      d2FlowStage active role quota h (i + 8)
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild tree j) k) m) l) q) r) s) u) := by
  have hproj := d2FlowStage_path7_child_projection
    (active := active) (role := role) (quota := quota)
    (h := h + 1) (i := i) tree j k m l q r s
  have hchild := congrArg (fun t => d2FlowTreeChild t u) hproj
  dsimp only at hchild
  let parent := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild tree j) k) m) l) q) r
  cases hparent : parent with
  | node G low high children =>
      dsimp only [parent] at hparent
      rw [hparent] at hchild
      conv at hchild =>
        rhs
        rw [d2FlowStage_child_child_projection]
        change d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) (i + 7)
            (children s)) u
      cases hlevel7 : children s with
      | node G7 low7 high7 grandchildren =>
          rw [hlevel7] at hchild
          conv at hchild =>
            rhs
            rw [d2FlowStage_inactive_child
              (active := active) (role := role) (quota := quota)
              (i := i + 7) (G := G7) (low := low7) (high := high7)
              grandchildren hinactive u]
          have hlevel : i + 7 + 1 = i + 8 := by omega
          rw [hlevel] at hchild
          rw [hparent]
          conv =>
            rhs
            change d2FlowStage active role quota h (i + 8)
              (d2FlowTreeChild (children s) u)
          rw [hlevel7]
          conv =>
            rhs
            change d2FlowStage active role quota h (i + 8)
              (grandchildren u)
          exact hchild

/-- Stage 18's bottom-rise fills each actual level-eight subtree in Run 19
to its native size: its level-nine children were full in Run 18, and the
inactive level-seven parent lets the local result reach the tree. -/
theorem d2FlowCandidateRun_stage19_levelEight_root_full
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r s u : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowCandidateRun (childDepth + 9)
                        (d2FlowTreeInitial 8192 (childDepth + 9)) 19) j) k) m) l) q) r) s) u) =
      8192 * 8 ^ (childDepth + 1) := by
  let d := childDepth + 9
  let initial := d2FlowTreeInitial 8192 d
  let run18 := d2FlowCandidateRun d initial 18
  let tree18 := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run18 j) k) m) l) q) r) s) u
  have hrunInv : d2FlowTreeInv 8192 run18 := by
    simpa [d, initial, run18] using
      d2FlowCandidateStage17_preserves_inv (childDepth + 2) (by omega)
  have hInv2 : d2FlowTreeInv 8192
      (d2FlowTreeChild (d2FlowTreeChild run18 j) k) :=
    d2FlowTreeInv_grandchild (h := childDepth + 7) run18 hrunInv j k
  have hInv4 : d2FlowTreeInv 8192
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run18 j) k) m) l) :=
    d2FlowTreeInv_grandchild (h := childDepth + 5)
      (d2FlowTreeChild (d2FlowTreeChild run18 j) k) hInv2 m l
  have hInv6 : d2FlowTreeInv 8192
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run18 j) k) m) l) q) r) :=
    d2FlowTreeInv_grandchild (h := childDepth + 3)
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild run18 j) k) m) l) hInv4 q r
  have hInv8 : d2FlowTreeInv 8192 tree18 := by
    simpa [tree18] using
      d2FlowTreeInv_grandchild (h := childDepth + 1)
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild run18 j) k) m) l) q) r) hInv6 s u
  let path : D2FlowPath 8 := .cons j
    (.cons k (.cons m (.cons l (.cons q (.cons r (.cons s
      (.cons u .nil)))))))
  have hchildren : ∀ v : Fin 8,
      d2FlowTreeRootDeficit (d2FlowTreeChild tree18 v) =
        8192 * 8 ^ childDepth := by
    intro v
    have hfull := d2FlowCandidateRun_stage18_levelEight_children_full
      childDepth hd path v
    change d2FlowTreeChild tree18 v = d2FlowTreeFull 8192 childDepth at hfull
    have hroot := congrArg d2FlowTreeRootDeficit hfull
    simpa only [d2FlowTreeRootDeficit_full] using hroot
  have hactive8 : d2FlowCandidateActive d 18 8 = true := by
    apply (d2FlowCandidateActive_stage18_iff (by dsimp [d]; omega)).2
    by_cases hsmall : d <= 15 <;> simp [hsmall]
  have hrole8 : d2FlowCandidateRole d 18 8 = .botRise :=
    d2FlowCandidateRole_stage18_bottom (by dsimp [d]; omega)
  have hfalse7 : d2FlowCandidateActive d 18 7 = false := by
    cases h : d2FlowCandidateActive d 18 7 with
    | false => rfl
    | true =>
        have hs := (d2FlowCandidateActive_stage18_iff
          (by dsimp [d]; omega)).mp h
        by_cases hsmall : d <= 15 <;> simp [hsmall] at hs <;> omega
  have hrun19 : d2FlowCandidateRun d initial 19 =
      d2FlowCandidateStage d 18 run18 := by
    rw [d2FlowCandidateRun.eq_def]
  have hproject :
      d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowCandidateStage d 18 run18) j) k) m) l) q) r) s) u =
      d2FlowStage (d2FlowCandidateActive d 18)
        (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
        (childDepth + 1) 8 tree18 := by
    exact d2FlowStage_path8_tree_projection_of_inactive_parent
      (active := d2FlowCandidateActive d 18)
      (role := d2FlowCandidateRole d 18)
      (quota := d2FlowCandidateQuota d 18)
      (h := childDepth + 1) (i := 0) (tree := run18)
      j k m l q r s u hfalse7
  cases htree : tree18 with
  | node G low high children =>
      have hinvNode : d2FlowTreeInv 8192 (.node G low high children) := by
        simpa [htree] using hInv8
      have hcover := d2FlowTreeInv_node_children_cover children hinvNode
      have hlocal : d2FlowTreeRootDeficit
          (d2FlowStage (d2FlowCandidateActive d 18)
            (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
            (childDepth + 1) 8 (.node G low high children)) =
          8192 * 8 ^ (childDepth + 1) := by
        apply d2FlowStage_botRise_root_full_of_full_children
          (scale := 8192) (h := childDepth) (i := 8)
          (G := G) (low := low) (high := high) children hactive8 hrole8
        · simpa [d2FlowTreeRootDeficit, d2FlowTotal] using hcover
        · intro v
          simpa [htree] using hchildren v
      change d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowTreeChild
                        (d2FlowCandidateRun d initial 19) j) k) m) l) q) r) s) u) = _
      rw [hrun19, hproject, htree]
      exact hlocal

/-- Each actual level-seven root in Run 19 is balanced: Stage 18 writes it as
the child of an active regular level-six sender. This is the root-balance
field needed for the Stage-19 level-seven bot-descending input contract. -/
theorem d2FlowCandidateRun_stage19_levelSeven_balanced
    (childDepth : Nat) (hd : 7 <= childDepth)
    (j k m l q r s : Fin 8) :
    let d := childDepth + 7
    let run19 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 19
    let tree := d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild run19 j) k) m) l) q) r) s
    (d2FlowTreeRootData tree).2.1 + (d2FlowTreeRootData tree).2.2 =
      d2FlowTreeRootDeficit tree := by
  obtain ⟨height, rfl⟩ : ∃ height, childDepth = height + 1 :=
    ⟨childDepth - 1, by omega⟩
  let d := height + 8
  let initial := d2FlowTreeInitial 8192 d
  let before := d2FlowCandidateRun d initial 18
  let run19 := d2FlowCandidateRun d initial 19
  let pathParent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild before j) k) m) l) q) r
  have hd14 : 14 <= d := by dsimp [d]; omega
  have hactive : d2FlowCandidateActive d 18 6 = true := by
    apply (d2FlowCandidateActive_stage18_iff hd14).2
    by_cases hsmall : d <= 15
    · simp [hsmall]
    · simp [hsmall]
  have hrole : d2FlowCandidateRole d 18 6 = .mid :=
    d2FlowCandidateRole_stage18_mid46 hd14 6 (Or.inr rfl)
  have hlocal :
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 18)
            (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
            (height + 2) 6 pathParent) s)).2.1 +
      (d2FlowTreeRootData
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 18)
            (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
            (height + 2) 6 pathParent) s)).2.2 =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (d2FlowCandidateActive d 18)
            (d2FlowCandidateRole d 18) (d2FlowCandidateQuota d 18)
            (height + 2) 6 pathParent) s) := by
    cases pathParent with
    | node G low high children =>
        exact d2FlowStage_regular_child_balanced children hactive
          (Or.inr (Or.inl hrole)) s
  have hrun : d2FlowCandidateRun d initial 19 =
      d2FlowCandidateStage d 18 before := by
    rw [d2FlowCandidateRun.eq_def]
  dsimp only [d, initial]
  rw [hrun]
  simp only [d2FlowCandidateStage]
  rw [d2FlowStage_path7_child_projection]
  simpa [pathParent] using hlocal

end Chvatal.D2Reserve
