import D2BotRiseRunBridge

namespace Chvatal.D2Reserve

theorem d2FlowTreeAtPath_full
    {h n : Nat} (path : D2FlowPath n) :
    d2FlowTreeAtPath n (d2FlowTreeFull 8192 (h + n)) path =
      d2FlowTreeFull 8192 h := by
  induction path generalizing h with
  | nil => rfl
  | @cons n j tail ih =>
      simp only [d2FlowTreeAtPath, d2FlowTreeChild, d2FlowTreeFull]
      exact ih (h := h)

theorem d2FlowTreeInitial_atPath_full
    {h n : Nat} (path : D2FlowPath (n + 1)) :
    d2FlowTreeAtPath (n + 1)
      (d2FlowTreeInitial 8192 (h + 1 + (n + 1))) path =
      d2FlowTreeFull 8192 (h + 1) := by
  cases path with
  | cons j tail =>
      simp only [d2FlowTreeAtPath, d2FlowTreeInitial, d2FlowTreeChild]
      exact d2FlowTreeAtPath_full tail

theorem d2FlowTreePathContext_initial_eq_atPath
    {h n : Nat} (initial : D2FlowTree (h + n))
    (path : D2FlowPath n) (i : Nat)
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat) :
    (d2FlowTreePathContext n initial path i active role quota overwrite).initial =
      d2FlowTreeAtPath n initial path := by
  induction path generalizing h i overwrite with
  | nil => rfl
  | @cons n j tail ih =>
      simp only [d2FlowTreePathContext, d2FlowTreeAtPath]
      exact ih (initial := d2FlowTreeChild initial j) (i := i + 1)
        (overwrite := d2FlowTreeChildOverwrite
          (fun k => d2FlowTreeRunWithParentOverwrites initial i active role
            quota overwrite k) (i := i) active role quota j)

/-! If a selected parent and child follow a preserving callback history, the
child root in the actual candidate run remains its initial native value. -/
theorem d2FlowCandidateRun_path_child_root_preserved
    {h n t : Nat} (path : D2FlowPath (n + 1)) (child : Fin 8)
    (hpreserves : ∀ k, k < t →
      d2FlowCandidateRunActive (h + 1 + (n + 1)) k (n + 2) = false ∧
        (d2FlowCandidateRunActive (h + 1 + (n + 1)) k (n + 1) = false ∨
          d2FlowCandidateRunRole (h + 1 + (n + 1)) k (n + 1) = .botRise)) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath (n + 1)
          (d2FlowCandidateRun (h + 1 + (n + 1))
            (d2FlowTreeInitial 8192 (h + 1 + (n + 1))) t) path) child) =
      8192 * 8 ^ h := by
  let d := h + 1 + (n + 1)
  let active := d2FlowCandidateRunActive d
  let role := d2FlowCandidateRunRole d
  let quota := d2FlowCandidateRunQuota d
  let overwrite := d2FlowCandidateRunOverwrite d
    (d2FlowTreeInitial 8192 d)
  let ctx := d2FlowTreePathContext (n + 1)
    (d2FlowTreeInitial 8192 d) path 0 active role quota overwrite
  have hlevel : ctx.level = n + 1 := by
    dsimp [ctx, d, active, role, quota, overwrite]
    simpa using d2FlowTreePathContext_level
      (d2FlowTreeInitial 8192 (h + 1 + (n + 1))) path 0
      (d2FlowCandidateRunActive (h + 1 + (n + 1)))
      (d2FlowCandidateRunRole (h + 1 + (n + 1)))
      (d2FlowCandidateRunQuota (h + 1 + (n + 1)))
      (d2FlowCandidateRunOverwrite (h + 1 + (n + 1))
        (d2FlowTreeInitial 8192 (h + 1 + (n + 1))))
  have hctxInitial : ctx.initial = d2FlowTreeFull 8192 (h + 1) := by
    rw [d2FlowTreePathContext_initial_eq_atPath]
    exact d2FlowTreeInitial_atPath_full path
  have htrace := d2FlowTreePathHistory_child_trace
    (initial := d2FlowTreeInitial 8192 d) (path := path) (i := 0)
    active role quota overwrite child t
  rw [hlevel, hctxInitial] at htrace
  have hstable := d2ChildDeficitTrace_eq_of_preserves
    (initial := (d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowTreeFull 8192 (h + 1)) child) : Rat) / 8192)
    (childActive := fun k => active k (n + 2))
    (childPort := fun k =>
      (d2FlowStagePort (active k) (role k) (quota k) h
        (n + 2)
        (d2FlowTreeChild
          (d2FlowTreeRunWithParentOverwrites
            (d2FlowTreeFull 8192 (h + 1)) (n + 1)
            active role quota ctx.overwrite k) child) : Rat) / 8192)
    (parentActive := fun k => active k (n + 1))
    (parentRole := fun k => role k (n + 1))
    (cutDeficit := fun k =>
      (d2FlowTreeParentCutAt
        (i := n + 1)
        (d2FlowTreeRunWithParentOverwrites
          (d2FlowTreeFull 8192 (h + 1)) (n + 1)
          active role quota ctx.overwrite k)
        (role k) (quota k) child : Rat) / 8192)
    (s := 0) (n := t) (by
      intro k hk
      simpa using hpreserves k hk)
  simp only [Nat.zero_add] at hstable
  have hpath := d2FlowCandidateRun_path_as_history
    (initial := d2FlowTreeInitial 8192 d) (path := path) (step := t)
  rw [← hpath] at htrace
  have htrace' := htrace
  simp only [Nat.add_assoc, Nat.reduceAdd] at htrace'
  dsimp [ctx] at hstable
  rw [hstable] at htrace'
  have hinitialRoot : d2FlowTreeRootDeficit
      (d2FlowTreeChild (d2FlowTreeFull 8192 (h + 1)) child) =
        8192 * 8 ^ h := by
    cases h <;> rfl
  have hactual :
      (d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath (n + 1)
            (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) path)
          child) : Rat) / 8192 =
      (8192 * 8 ^ h : Nat) / 8192 := by
    simpa [d, d2ChildDeficitTrace, hinitialRoot] using htrace'
  have hcast : (d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath (n + 1)
          (d2FlowCandidateRun d (d2FlowTreeInitial 8192 d) t) path) child) : Rat) =
        (8192 * 8 ^ h : Nat) := by
    have h := hactual
    field_simp at h
    exact_mod_cast h
  exact_mod_cast hcast

theorem d2FlowCandidateRun_strong_parent_children_native
    {h j : Nat} (hd : 7 ≤ h + 1 + (j + 2)) (hj : 1 ≤ j)
    (hwindow : 3 * j + 2 ≤ tfD2 (h + 1 + (j + 2)))
    (path : D2FlowPath (j + 2)) (child : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath (j + 2)
          (d2FlowCandidateRun (h + 1 + (j + 2))
            (d2FlowTreeInitial 8192 (h + 1 + (j + 2))) (3 * j + 2)) path)
        child) = 8192 * 8 ^ h := by
  have hpreserves := d2FlowCandidate_botRise_callback_window hd hj hwindow
  exact d2FlowCandidateRun_path_child_root_preserved path child hpreserves

private theorem d2FlowCandidateRunActive_false_of_schedule_inactive
    {d t i : Nat} (ht : 0 < t)
    (hinactive : ¬ active d (tfD2 d) i t) :
    d2FlowCandidateRunActive d t i = false := by
  classical
  rw [d2FlowCandidateRunActive,
    d2FlowCandidateActive_matches_schedule (d := d) (t := t) (i := i) ht]
  simp [hinactive]

theorem d2FlowCandidateRun_strong_parent_grandchildren_native
    {h j : Nat} (hh : 1 ≤ h)
    (hd : 7 ≤ (h - 1) + 1 + ((j + 2) + 1))
    (hj : 1 ≤ j)
    (hwindow : 3 * j + 2 ≤ tfD2 ((h - 1) + 1 + ((j + 2) + 1)))
    (path : D2FlowPath (j + 2)) (child grandchild : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath ((j + 2) + 1)
          (d2FlowCandidateRun ((h - 1) + 1 + ((j + 2) + 1))
            (d2FlowTreeInitial 8192 ((h - 1) + 1 + ((j + 2) + 1)))
            (3 * j + 2)) (D2FlowPath.cons child path)) grandchild) =
      8192 * 8 ^ (h - 1) := by
  let d := (h - 1) + 1 + ((j + 2) + 1)
  have hpreserves : ∀ k, k < 3 * j + 2 →
      d2FlowCandidateRunActive d k (j + 4) = false ∧
        (d2FlowCandidateRunActive d k (j + 3) = false ∨
          d2FlowCandidateRunRole d k (j + 3) = .botRise) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp [d, d2FlowCandidateRunActive, d2FlowCandidateActive,
        d2FlowCandidateRunRole, d2FlowCandidateRole]
    · have hinactive := botRise_history_inactive_before
        (d := d) (tf := tfD2 d) (j := j + 1) (s := k)
        (by omega) (by omega)
      rcases hinactive with ⟨hparent, hchild⟩
      exact ⟨d2FlowCandidateRunActive_false_of_schedule_inactive
          (by omega) hchild,
        Or.inl (d2FlowCandidateRunActive_false_of_schedule_inactive
          (by omega) hparent)⟩
  exact d2FlowCandidateRun_path_child_root_preserved
    (h := h - 1) (n := j + 2) (path := D2FlowPath.cons child path)
    grandchild hpreserves

end Chvatal.D2Reserve
