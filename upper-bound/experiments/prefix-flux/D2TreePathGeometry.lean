import D2FlowPathLast

namespace Chvatal.D2Reserve

theorem d2FlowCandidateRun_inv_transport {d₁ d₂ t : Nat} (hd : d₁ = d₂)
    (hinv : d2FlowTreeInv 8192
      (d2FlowCandidateRun d₁ (d2FlowTreeInitial 8192 d₁) t)) :
    d2FlowTreeInv 8192
      (d2FlowCandidateRun d₂ (d2FlowTreeInitial 8192 d₂) t) := by
  cases hd
  exact hinv

theorem d2FlowTree_cast_cancel {a b : Nat} (e : a = b)
    (tree : D2FlowTree a) :
    cast (congrArg D2FlowTree e.symm)
      (cast (congrArg D2FlowTree e) tree) = tree := by
  cases e
  rfl

/-- A path whose length equals the tree height always lands at a leaf. -/
theorem d2FlowTreeAtPath_fullDepth_leaf {n : Nat}
    (tree : D2FlowTree (0 + n)) (path : D2FlowPath n) :
    ∃ G low high, d2FlowTreeAtPath (h := 0) n tree path = D2FlowTree.leaf G low high := by
  induction path with
  | nil =>
      cases tree with
      | leaf G low high => exact ⟨G, low, high, rfl⟩
  | @cons n port tail ih =>
      cases tree with
      | node G low high children =>
          exact ih (children port)

/-- The affine-core predicate has no terminal-node obligations, so its
full-depth path case is automatic. -/
theorem d2FlowStageAffineCoreInputs_atFullDepth
    {active : Nat → Bool} {role : Nat → D2Role} {cap : Nat → Nat}
    {n : Nat} (tree : D2FlowTree (0 + n)) (path : D2FlowPath n) :
    d2FlowStageAffineCoreInputs active role cap n
      (d2FlowTreeAtPath (h := 0) n tree path) := by
  obtain ⟨G, low, high, hleaf⟩ := d2FlowTreeAtPath_fullDepth_leaf tree path
  simp [hleaf, d2FlowStageAffineCoreInputs]

/-- One scheduled update transports the affine-core provider to every node of
the next run, assuming the two preceding providers and the current invariant. -/
theorem d2FlowCandidateRun_affine_core_atPath
    {d h i t : Nat} (hdPath : d = h + i) (hd : 7 <= d) (ht : 3 <= t)
    (path : D2FlowPath i)
    (hcorePrev : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive d (t - 1) k)
      (fun k => d2FlowCandidateRole d (t - 1) k)
      (fun k => d2FlowCandidateCapacity d k (t - 1)) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 1)))
    (hcoreNow : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive d t k)
      (fun k => d2FlowCandidateRole d t k)
      (fun k => d2FlowCandidateCapacity d k t) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t))
    (hinvNow : d2FlowTreeInv 8192
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) :
    d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive d (t + 1) k)
      (fun k => d2FlowCandidateRole d (t + 1) k)
      (fun k => d2FlowCandidateCapacity d k (t + 1)) i
      (d2FlowTreeAtPath i
        (cast (congrArg D2FlowTree hdPath)
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1))) path) := by
  induction h generalizing d i path with
  | zero =>
      let treeNext := cast (congrArg D2FlowTree hdPath)
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1))
      simpa [treeNext] using
        (d2FlowStageAffineCoreInputs_atFullDepth
          (active := fun k => d2FlowCandidateActive d (t + 1) k)
          (role := fun k => d2FlowCandidateRole d (t + 1) k)
          (cap := fun k => d2FlowCandidateCapacity d k (t + 1))
          (tree := treeNext) path)
  | succ h ih =>
      let treeNext := cast (congrArg D2FlowTree hdPath)
        (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1))
      have hinvNext := d2FlowCandidateRun_preserves_inv_next_of_affine_core
        (d := d) (t := t) hd (by omega) hinvNow hcoreNow
      cases hnode : d2FlowTreeAtPath i treeNext path with
      | node G low high children =>
          simp only [d2FlowStageAffineCoreInputs]
          constructor
          · intro port
            have hdChild : d = h + (i + 1) := by rw [hdPath]; omega
            let treeChild := cast (congrArg D2FlowTree hdChild)
              (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1))
            have hchildCore := ih (d := d) (i := i + 1)
              (hdPath := hdChild) hd (d2FlowPathSnoc path port)
              hcorePrev hcoreNow hinvNow
            have hassoc : h + (i + 1) = (h + 1) + i := by omega
            have hcast : cast (congrArg D2FlowTree hassoc) treeChild = treeNext := by
              cases hdPath
              simp [treeChild, treeNext]
            have hproject := d2FlowTreeAtPath_snoc
              (h := h) (n := i) treeChild path port
            have hchildTree :
                d2FlowTreeAtPath (i + 1) treeChild (d2FlowPathSnoc path port) =
                  d2FlowTreeChild (d2FlowTreeAtPath i treeNext path) port := by
              rw [hproject, hcast]
            rw [hchildTree, hnode] at hchildCore
            exact hchildCore
          · classical
            by_cases haBool : d2FlowCandidateActive d (t + 1) i = true
            · have ha : active d (tfD2 d) i (t + 1) := by
                have hmatch := d2FlowCandidateActive_matches_schedule
                  (d := d) (t := t + 1) (i := i) (by omega)
                rw [hmatch] at haBool
                exact of_decide_eq_true haBool
              have hlocal : low + high = G /\
                match d2FlowCandidateRole d (t + 1) i with
                | .topDesc => G = 0
                | .botRise => True
                | .topRise =>
                    G = 0 /\
                      d2FlowCandidateCapacity d i (t + 1) <=
                        128 * d2FlowTreeRootDeficit (children 0) /\
                      d2FlowCandidateCapacity d i (t + 1) <=
                        128 * d2FlowTreeRootDeficit (children 7)
                | .mid | .botDesc =>
                    8192 * G + 7 <= 15 * d2FlowCandidateCapacity d i (t + 1) /\
                      d2FlowCandidateCapacity d i (t + 1) <=
                        128 * d2FlowTreeRootDeficit (children 0) /\
                      d2FlowCandidateCapacity d i (t + 1) <=
                        128 * d2FlowTreeRootDeficit (children 7) := by
                by_cases hi0 : i = 0
                · subst i
                  cases path with
                  | nil =>
                      have hdRoot : d = h + 1 := by simpa using hdPath
                      have hcorePrevRoot := d2FlowCandidateRun_affine_core_transport
                        (d₁ := d) (d₂ := h + 1) (t := t - 1) hdRoot hcorePrev
                      have hinvNextRoot := d2FlowCandidateRun_inv_transport
                        (d₁ := d) (d₂ := h + 1) (t := t + 1) hdRoot hinvNext
                      have haRoot : active (h + 1) (tfD2 (h + 1)) 0 (t + 1) := by
                        simpa [hdRoot] using ha
                      have hroot := d2FlowCandidateRun_active_root_affine_local_contract
                        (d := h + 1) (by omega) (by omega) haRoot hcorePrevRoot hinvNextRoot
                      have hrootEq := d2FlowCandidateRun_initial_cast hdRoot (t + 1)
                      have htreeEq : d2FlowCandidateRun (h + 1)
                          (d2FlowTreeInitial 8192 (h + 1)) (t + 1) =
                          D2FlowTree.node G low high children := by
                        calc
                          _ = cast (congrArg D2FlowTree hdRoot)
                              (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1)) :=
                                hrootEq.symm
                          _ = treeNext := rfl
                          _ = d2FlowTreeAtPath 0 treeNext D2FlowPath.nil := rfl
                          _ = _ := hnode
                      rw [htreeEq] at hroot
                      rw [hdRoot]
                      rw [d2FlowCandidateRole_matches_schedule
                        (d := h + 1) (t := t + 1) (i := 0) (by omega)]
                      rcases hroot with ⟨hbal, hzero, hrole⟩
                      constructor
                      · simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hbal
                      · simp only [hrole]
                        exact hzero
                · cases i with
                  | zero => omega
                  | succ parentLevel =>
                      obtain ⟨parentPath, lastPort, hpath⟩ :=
                        d2FlowPath_exists_snoc path
                      let dLocal := h + 2 + parentLevel
                      have hdLocal : dLocal = d := by dsimp [dLocal]; rw [hdPath]; omega
                      have hcorePrevLocal := d2FlowCandidateRun_affine_core_transport
                        (d₁ := d) (d₂ := dLocal) (t := t - 1) hdLocal.symm hcorePrev
                      have hcoreNowLocal := d2FlowCandidateRun_affine_core_transport
                        (d₁ := d) (d₂ := dLocal) (t := t) hdLocal.symm hcoreNow
                      have hchildActive : active dLocal (tfD2 dLocal)
                          (parentLevel + 1) (t + 1) := by
                        simpa [dLocal, hdLocal] using ha
                      have hlocalChild := d2FlowCandidateRun_active_child_affine_local_contract
                        (h := h) (i := parentLevel) (t := t)
                        (by omega) ht parentPath lastPort hchildActive
                        hcorePrevLocal hcoreNowLocal
                        (d2FlowCandidateRun_inv_transport
                          (d₁ := d) (d₂ := dLocal) (t := t) hdLocal.symm hinvNow)
                      have htreeHeight : (h + 1) + (parentLevel + 1) =
                          (h + 2) + parentLevel := by omega
                      have hrootCast := d2FlowCandidateRun_initial_cast
                        htreeHeight.symm (t + 1)
                      have hfullEq :
                          cast (congrArg D2FlowTree htreeHeight.symm)
                            (d2FlowCandidateRun dLocal
                              (d2FlowTreeInitial 8192 dLocal) (t + 1)) = treeNext := by
                        calc
                          _ = d2FlowCandidateRun
                              (h + 1 + (parentLevel + 1))
                              (d2FlowTreeInitial 8192 (h + 1 + (parentLevel + 1)))
                              (t + 1) := hrootCast
                          _ = treeNext := (d2FlowCandidateRun_initial_cast hdPath
                            (t + 1)).symm
                      have hproject := d2FlowTreeAtPath_snoc
                        (h := h + 1) (n := parentLevel)
                        (cast (congrArg D2FlowTree htreeHeight.symm)
                          (d2FlowCandidateRun dLocal
                            (d2FlowTreeInitial 8192 dLocal) (t + 1)))
                        parentPath lastPort
                      have hnodeLocal :
                          d2FlowTreeChild
                            (d2FlowTreeAtPath parentLevel
                              (d2FlowCandidateRun dLocal
                                (d2FlowTreeInitial 8192 dLocal) (t + 1)) parentPath)
                            lastPort = D2FlowTree.node G low high children := by
                        have hnodeFull :
                            d2FlowTreeAtPath (parentLevel + 1)
                              (cast (congrArg D2FlowTree htreeHeight.symm)
                                (d2FlowCandidateRun dLocal
                                  (d2FlowTreeInitial 8192 dLocal) (t + 1)))
                              (d2FlowPathSnoc parentPath lastPort) =
                              D2FlowTree.node G low high children := by
                          calc
                            _ = d2FlowTreeAtPath (parentLevel + 1) treeNext
                                (d2FlowPathSnoc parentPath lastPort) := by rw [hfullEq]
                            _ = d2FlowTreeAtPath (parentLevel + 1) treeNext path := by
                              rw [hpath]
                            _ = _ := hnode
                        have hinner :
                            cast (congrArg D2FlowTree
                              htreeHeight)
                              (cast (congrArg D2FlowTree htreeHeight.symm)
                                (d2FlowCandidateRun dLocal
                                  (d2FlowTreeInitial 8192 dLocal) (t + 1))) =
                              d2FlowCandidateRun dLocal
                                (d2FlowTreeInitial 8192 dLocal) (t + 1) := by
                          exact d2FlowTree_cast_cancel htreeHeight.symm _
                        rw [hinner] at hproject
                        exact hproject.symm.trans hnodeFull
                      rw [d2FlowCandidateRole_matches_schedule
                        (d := d) (t := t + 1) (i := parentLevel + 1) (by omega)]
                      dsimp at hlocalChild
                      rw [hnodeLocal] at hlocalChild
                      have hdArith : h + 2 + parentLevel = d := by omega
                      rw [hdArith] at hlocalChild
                      simp [d2FlowTreeRootData, d2FlowTreeRootDeficit,
                        d2FlowTreeChild] at hlocalChild
                      rcases hlocalChild with ⟨hbalance, hprofile, hreserves⟩
                      refine ⟨hbalance, ?_⟩
                      cases hrole : d2ScheduleRole d (parentLevel + 1) (t + 1) with
                      | topDesc =>
                          simpa [hrole] using hprofile
                      | botRise =>
                          simp [hrole] at hprofile ⊢
                      | topRise =>
                          have hendpoints := hreserves (Or.inl hrole)
                          simp [hrole] at hprofile
                          rcases hprofile with ⟨hzero, _⟩
                          simpa [hrole] using ⟨hzero, hendpoints.1, hendpoints.2⟩
                      | mid =>
                          simp [hrole] at hprofile
                          have hendpoints := hreserves (Or.inr (Or.inl hrole))
                          exact ⟨hprofile, hendpoints⟩
                      | botDesc =>
                          simp [hrole] at hprofile
                          have hendpoints := hreserves (Or.inr (Or.inr hrole))
                          exact ⟨hprofile, hendpoints⟩
              simpa [haBool] using hlocal
            · simp [haBool]

/-- Root specialization: the full affine-core provider advances one stage
from the two previous providers and the current invariant. -/
theorem d2FlowCandidateRun_affine_core_next
    {d t : Nat} (hd : 7 <= d) (ht : 3 <= t)
    (hcorePrev : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive d (t - 1) k)
      (fun k => d2FlowCandidateRole d (t - 1) k)
      (fun k => d2FlowCandidateCapacity d k (t - 1)) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t - 1)))
    (hcoreNow : d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive d t k)
      (fun k => d2FlowCandidateRole d t k)
      (fun k => d2FlowCandidateCapacity d k t) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t))
    (hinvNow : d2FlowTreeInv 8192
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t)) :
    d2FlowStageAffineCoreInputs
      (fun k => d2FlowCandidateActive d (t + 1) k)
      (fun k => d2FlowCandidateRole d (t + 1) k)
      (fun k => d2FlowCandidateCapacity d k (t + 1)) 0
      (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) (t + 1)) := by
  have hroot := d2FlowCandidateRun_affine_core_atPath
    (d := d) (h := d) (i := 0) (t := t) (by omega) hd ht .nil
    hcorePrev hcoreNow hinvNow
  simpa [d2FlowTreeAtPath, d2FlowCandidateRun_initial_cast] using hroot

end Chvatal.D2Reserve
