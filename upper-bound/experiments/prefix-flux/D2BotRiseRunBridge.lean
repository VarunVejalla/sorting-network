import D2BotRiseReserveArithmetic

namespace Chvatal.D2Reserve

set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false

/-- The path context advances its local schedule level by exactly the path
length. -/
theorem d2FlowTreePathContext_level
    {h n : Nat} (initial : D2FlowTree (h + n))
    (path : D2FlowPath n) (i : Nat)
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat) :
    (d2FlowTreePathContext n initial path i active role quota overwrite).level = i + n := by
  induction path generalizing h i overwrite with
  | nil => rfl
  | @cons n j tail ih =>
      simp only [d2FlowTreePathContext]
      rw [ih]
      omega

/-- Schedule callbacks along the exceptional bottom-rise history: the child
is inactive throughout; the parent is inactive except at the rise itself. -/
theorem d2FlowCandidate_botRise_callback_window
    {d j : Nat} (hd : 7 ≤ d) (hj : 1 ≤ j)
    (hwindow : 3 * j + 2 ≤ tfD2 d) :
    ∀ k, k < 3 * j + 2 →
      d2FlowCandidateRunActive d k (j + 3) = false ∧
        (d2FlowCandidateRunActive d k (j + 2) = false ∨
          d2FlowCandidateRunRole d k (j + 2) = .botRise) := by
  classical
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [d2FlowCandidateRunActive, d2FlowCandidateRunRole,
      d2FlowCandidateActive, d2FlowCandidateRole]
  · by_cases hbefore : k < 3 * j
    · have hs : k + 1 ≤ 3 * j := by omega
      have hinactive := botRise_history_inactive_before
        (d := d) (tf := tfD2 d) hj hs
      rcases hinactive with ⟨hparent, hchild⟩
      have hchild' : d2FlowCandidateRunActive d k (j + 3) = false := by
        rw [d2FlowCandidateRunActive]
        rw [d2FlowCandidateActive_matches_schedule (d := d)
          (t := k) (i := j + 3) (by omega)]
        simp [hchild]
      have hparent' : d2FlowCandidateRunActive d k (j + 2) = false := by
        rw [d2FlowCandidateRunActive]
        rw [d2FlowCandidateActive_matches_schedule (d := d)
          (t := k) (i := j + 2) (by omega)]
        simp [hparent]
      exact ⟨hchild', Or.inl hparent'⟩
    · by_cases hrise : k = 3 * j
      · subst k
        have hchild : ¬ active d (tfD2 d) (j + 3) (3 * j) :=
          (botRise_children_inactive (d := d) (tf := tfD2 d) hj).1
        have hchild' : d2FlowCandidateRunActive d (3 * j) (j + 3) = false := by
          rw [d2FlowCandidateRunActive]
          rw [d2FlowCandidateActive_matches_schedule (d := d)
            (t := 3 * j) (i := j + 3) (by omega)]
          simp [hchild]
        have hboundary : 3 * (j + 2) = 3 * j + 6 := by omega
        have hfront := botRise_boundary_frontier (by omega) hboundary
        have htf : 3 * j < tfD2 d := by omega
        have hgap := frontiers_separated_before_tf hd (by omega) htf
        have hnotTop : j + 2 ≠ alpha d (3 * j) := by
          intro heq
          rw [hfront.1, heq] at hgap
          omega
        have hnotMove : ¬ omega (3 * j) < omega (3 * j + 1) := by
          have hnext : omega (3 * j + 1) = j + 1 := by omega
          rw [hfront.1, hnext]
          omega
        have hrole : d2ScheduleRole d (j + 2) (3 * j) = .botRise := by
          rw [d2ScheduleRole, if_neg hnotTop, if_pos hfront.1.symm,
            if_neg hnotMove]
        have hrole' : d2FlowCandidateRunRole d (3 * j) (j + 2) = .botRise := by
          rw [d2FlowCandidateRunRole,
            d2FlowCandidateRole_matches_schedule (d := d)
              (t := 3 * j) (by omega)]
          exact hrole
        exact ⟨hchild', Or.inr hrole'⟩
      · have hnext : k = 3 * j + 1 := by omega
        subst k
        have hchild : ¬ active d (tfD2 d) (j + 3) (3 * j + 1) :=
          (botRise_children_inactive (d := d) (tf := tfD2 d) hj).2
        have hparent : ¬ active d (tfD2 d) (j + 2) (3 * j + 1) := by
          unfold active
          simp only [if_neg (by omega : 3 * j + 1 ≠ 0),
            if_neg (by omega : 3 * j + 1 ≠ 1)]
          omega
        have hchild' : d2FlowCandidateRunActive d (3 * j + 1) (j + 3) = false := by
          rw [d2FlowCandidateRunActive]
          rw [d2FlowCandidateActive_matches_schedule (d := d)
            (t := 3 * j + 1) (i := j + 3) (by omega)]
          simp [hchild]
        have hparent' : d2FlowCandidateRunActive d (3 * j + 1) (j + 2) = false := by
          rw [d2FlowCandidateRunActive]
          rw [d2FlowCandidateActive_matches_schedule (d := d)
            (t := 3 * j + 1) (i := j + 2) (by omega)]
          simp [hparent]
        exact ⟨hchild', Or.inl hparent'⟩

/-- Along any path, the actual candidate run preserves a child root through
the two-stage bot-rise window. If the initial root is native, so is the
endpoint at the next ordinary visit. -/
theorem d2FlowCandidateRun_botRise_path_child_preserved
    {h j : Nat} (hd : 7 ≤ h + 1 + (j + 2)) (hj : 1 ≤ j)
    (hwindow : 3 * j + 2 ≤ tfD2 (h + 1 + (j + 2)))
    (initial : D2FlowTree (h + 1 + (j + 2)))
    (path : D2FlowPath (j + 2)) (port : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath (j + 2)
          (d2FlowCandidateRun (h + 1 + (j + 2)) initial (3 * j + 2)) path) port) =
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreePathContext (j + 2) initial path 0
          (d2FlowCandidateRunActive (h + 1 + (j + 2)))
          (d2FlowCandidateRunRole (h + 1 + (j + 2)))
          (d2FlowCandidateRunQuota (h + 1 + (j + 2)))
          (d2FlowCandidateRunOverwrite (h + 1 + (j + 2)) initial)).initial port) := by
  let d := h + 1 + (j + 2)
  let active := d2FlowCandidateRunActive d
  let role := d2FlowCandidateRunRole d
  let quota := d2FlowCandidateRunQuota d
  let overwrite := d2FlowCandidateRunOverwrite d initial
  let ctx := d2FlowTreePathContext (j + 2) initial path 0
    (d2FlowCandidateRunActive d) (d2FlowCandidateRunRole d)
    (d2FlowCandidateRunQuota d) (d2FlowCandidateRunOverwrite d initial)
  have hlevel : ctx.level = j + 2 := by
    simpa [ctx, active, role, quota, overwrite] using
      d2FlowTreePathContext_level initial path 0 active role quota overwrite
  have hpres : ∀ k, k < 3 * j + 2 →
      active k (ctx.level + 1) = false ∧
        (active k ctx.level = false ∨ role k ctx.level = .botRise) := by
    intro k hk
    have h := d2FlowCandidate_botRise_callback_window hd hj hwindow k hk
    simpa [active, role, ctx, hlevel] using h
  have hstable := d2FlowTreePathHistory_child_root_preserved
    initial path 0 active role quota overwrite port (3 * j + 2) hpres
  have hpath := d2FlowCandidateRun_path_as_history
    (initial := initial) (path := path) (step := 3 * j + 2)
  rw [hpath]
  exact hstable

/-- Any lower bound on a path endpoint child root before the exceptional
window survives the actual two-stage candidate run. -/
theorem d2FlowCandidateRun_botRise_path_child_bound
    {h j native : Nat} (hd : 7 ≤ h + 1 + (j + 2)) (hj : 1 ≤ j)
    (hwindow : 3 * j + 2 ≤ tfD2 (h + 1 + (j + 2)))
    (initial : D2FlowTree (h + 1 + (j + 2)))
    (path : D2FlowPath (j + 2)) (port : Fin 8)
    (hreserve : native ≤ d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreePathContext (j + 2) initial path 0
          (d2FlowCandidateRunActive (h + 1 + (j + 2)))
          (d2FlowCandidateRunRole (h + 1 + (j + 2)))
          (d2FlowCandidateRunQuota (h + 1 + (j + 2)))
          (d2FlowCandidateRunOverwrite (h + 1 + (j + 2)) initial)).initial port)) :
    native ≤ d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowTreeAtPath (j + 2)
          (d2FlowCandidateRun (h + 1 + (j + 2)) initial (3 * j + 2)) path) port) := by
  rw [d2FlowCandidateRun_botRise_path_child_preserved hd hj hwindow
    initial path port]
  exact hreserve

end Chvatal.D2Reserve
