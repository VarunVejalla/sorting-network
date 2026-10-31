import D2Stage17Frontier
import D2Stage16Frontier
import D2Stage15Frontier
import D2Stage14Arithmetic

namespace Chvatal.D2Reserve

attribute [local irreducible] d2FlowCandidateRun

set_option maxHeartbeats 12000000
set_option maxRecDepth 4096

/-- Every actual level-one sender enters Stage 17 with zero root deficit.
The Stage-16 root reset gives this directly except at depth 14, where the
Stage-14 reset is carried through the inactive root bands. -/
theorem d2FlowCandidateRun_stage17_levelOne_root_zero
    (childDepth : Nat) (hd : 7 <= childDepth) (j : Fin 8) :
    let d := childDepth + 7
    let run17 := d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) 17
    d2FlowTreeRootDeficit (d2FlowTreeChild run17 j) = 0 := by
  obtain ⟨height, rfl⟩ : exists height, childDepth = height + 7 :=
    ⟨childDepth - 7, by omega⟩
  cases height with
  | zero =>
      let initial : D2FlowTree 14 := d2FlowTreeInitial 8192 14
      let run14 : D2FlowTree 14 := d2FlowCandidateRun 14 initial 14
      let run15 : D2FlowTree 14 := d2FlowCandidateRun 14 initial 15
      let run16 : D2FlowTree 14 := d2FlowCandidateRun 14 initial 16
      let run17 : D2FlowTree 14 := d2FlowCandidateRun 14 initial 17
      have hrun15 : run15 = d2FlowCandidateStage 14 14 run14 := by
        change d2FlowCandidateRun 14 initial 15 =
          d2FlowCandidateStage 14 14 (d2FlowCandidateRun 14 initial 14)
        rw [d2FlowCandidateRun.eq_def]
      have hrun16 : run16 = d2FlowCandidateStage 14 15 run15 := by
        change d2FlowCandidateRun 14 initial 16 =
          d2FlowCandidateStage 14 15 (d2FlowCandidateRun 14 initial 15)
        rw [d2FlowCandidateRun.eq_def]
      have hrun17 : run17 = d2FlowCandidateStage 14 16 run16 := by
        change d2FlowCandidateRun 14 initial 17 =
          d2FlowCandidateStage 14 16 (d2FlowCandidateRun 14 initial 16)
        rw [d2FlowCandidateRun.eq_def]
      have hfront14 := d2FlowCandidateStage14_frontiers 14 (by omega)
      have hactive14 : d2FlowCandidateActive 14 14 0 = true := hfront14.1
      have hrole14 : d2FlowCandidateRole 14 14 0 = .topDesc := hfront14.2.1
      have hsource : d2FlowTreeRootDeficit (d2FlowTreeChild run15 j) = 0 := by
        rw [hrun15]
        cases hnode : run14 with
        | node G low high children =>
            simp only [d2FlowCandidateStage]
            exact d2FlowStage_topDesc_child_deficit
              children hactive14 hrole14 j
      have hfalse15_0 : d2FlowCandidateActive 14 15 0 = false := by
        apply Bool.eq_false_of_not_eq_true
        intro ht
        have hlevels := d2FlowCandidateActive_stage15_level_bound ht
        rcases hlevels with h | h | h | h <;> omega
      have hfront15 := d2FlowCandidateActive_stage15_at (d := 14) (by omega)
      have hactive15_1 : d2FlowCandidateActive 14 15 1 = true := hfront15.1
      have hrole15_1 : d2FlowCandidateRole 14 15 1 = .topDesc := by
        simpa using d2FlowCandidateRole_stage15_top (d := 14) (by omega)
      have hfalse16_0 : d2FlowCandidateActive 14 16 0 = false := by
        apply Bool.eq_false_of_not_eq_true
        intro ht
        have hlevels := (d2FlowCandidateActive_stage16_iff
          (d := 14) (i := 0) (by omega)).mp ht
        simp at hlevels
      have hfalse16_1 : d2FlowCandidateActive 14 16 1 = false := by
        apply Bool.eq_false_of_not_eq_true
        intro ht
        have hlevels := (d2FlowCandidateActive_stage16_iff
          (d := 14) (i := 1) (by omega)).mp ht
        simp at hlevels
      have hmid : d2FlowTreeRootDeficit (d2FlowTreeChild run16 j) =
          d2FlowTreeRootDeficit (d2FlowTreeChild run15 j) := by
        cases hnode : run15 with
        | node G low high children =>
            rw [hrun16]
            simp only [d2FlowCandidateStage]
            rw [hnode]
            rw [d2FlowStage_inactive_child children hfalse15_0 j]
            cases hchild : children j with
            | node G1 low1 high1 grandchildren =>
                have hdef := d2FlowStage_active_node_deficit
                  (active := d2FlowCandidateActive 14 15)
                  (role := d2FlowCandidateRole 14 15)
                  (quota := d2FlowCandidateQuota 14 15)
                  (h := 12) (i := 1)
                  (G := G1) (low := low1) (high := high1)
                  grandchildren hactive15_1
                have hleft : d2FlowTreeRootDeficit
                    (d2FlowStage (d2FlowCandidateActive 14 15)
                      (d2FlowCandidateRole 14 15) (d2FlowCandidateQuota 14 15)
                      13 1 (D2FlowTree.node G1 low1 high1 grandchildren)) = G1 := by
                  simpa [hrole15_1] using hdef
                have hright : d2FlowTreeRootDeficit
                    (d2FlowTreeChild (D2FlowTree.node G low high children) j) = G1 := by
                  simp [d2FlowTreeChild, hchild, d2FlowTreeRootDeficit]
                exact hleft.trans hright.symm
      have hlast : d2FlowTreeRootDeficit (d2FlowTreeChild run17 j) =
          d2FlowTreeRootDeficit (d2FlowTreeChild run16 j) := by
        cases hnode : run16 with
        | node G low high children =>
            rw [hrun17]
            simp only [d2FlowCandidateStage]
            rw [hnode]
            rw [d2FlowStage_inactive_child children hfalse16_0 j]
            exact d2FlowStage_root_deficit_of_inactive
              (active := d2FlowCandidateActive 14 16)
              (role := d2FlowCandidateRole 14 16)
              (quota := d2FlowCandidateQuota 14 16)
              (i := 1) (children j) hfalse16_1
      have hzero : d2FlowTreeRootDeficit (d2FlowTreeChild run17 j) = 0 :=
        hlast.trans (hmid.trans hsource)
      simpa [initial, run17] using hzero
  | succ height =>
      let d := height + 15
      let initial : D2FlowTree (height + 15) := d2FlowTreeInitial 8192 (height + 15)
      let run16 : D2FlowTree (height + 15) :=
        d2FlowCandidateRun (height + 15) initial 16
      let run17 : D2FlowTree (height + 15) :=
        d2FlowCandidateRun (height + 15) initial 17
      have hd14 : 14 <= height + 15 := by omega
      have hactive16_0 : d2FlowCandidateActive (height + 15) 16 0 = true := by
        apply (d2FlowCandidateActive_stage16_iff hd14).2
        simp
      have hrole16_0 : d2FlowCandidateRole (height + 15) 16 0 = .topDesc := by
        simpa using d2FlowCandidateRole_stage16_top (d := height + 15) hd14
      have hrun17 : run17 = d2FlowCandidateStage (height + 15) 16 run16 := by
        change d2FlowCandidateRun (height + 15) initial 17 =
          d2FlowCandidateStage (height + 15) 16
            (d2FlowCandidateRun (height + 15) initial 16)
        rw [d2FlowCandidateRun.eq_def]
      have hzero : d2FlowTreeRootDeficit (d2FlowTreeChild run17 j) = 0 := by
        rw [hrun17]
        simp only [d2FlowCandidateStage]
        cases hnode : run16 with
        | node G low high children =>
            exact d2FlowStage_topDesc_child_deficit
              children hactive16_0 hrole16_0 j
      simpa [initial, run17] using hzero

end Chvatal.D2Reserve
