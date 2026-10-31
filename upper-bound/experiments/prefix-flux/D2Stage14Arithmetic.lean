import D2ScheduleReserve

namespace Chvatal.D2Reserve

private theorem decide_false_of_not {p : Prop} [Decidable p]
    (hn : ¬ p) : decide p = false := by
  cases h : decide p with
  | false => rfl
  | true => exact (hn (of_decide_eq_true h)).elim

/-- If every level below the current root is inactive, a recursive stage is
the identity on the whole subtree. -/
theorem d2FlowStage_eq_self_of_inactive_tail
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} :
    ∀ {h i : Nat} (tree : D2FlowTree h),
      (∀ q, i ≤ q → active q = false) →
      d2FlowStage active role quota h i tree = tree := by
  intro h
  induction h with
  | zero => intro i tree _; cases tree <;> rfl
  | succ h ih =>
      intro i tree hinactive
      cases tree with
      | node G low high children =>
          have hroot := hinactive i (by omega)
          have hchildren :
              (fun j => d2FlowStage active role quota h (i + 1) (children j)) =
                children := by
            funext j
            apply ih
            intro q hq
            exact hinactive q (by omega)
          simp [d2FlowStage, hroot, hchildren]

/-- A subtree's immediate children survive a run when its own scheduled
actions are either inactive or bottom-rise, and all deeper levels are
inactive. Root overwrites from its parent do not affect these children. -/
theorem d2FlowTreeRun_child_eq_of_inactive_or_botRise
    {h i : Nat} (initial : D2FlowTree (h + 1))
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat) (steps : Nat)
    (hroot : ∀ k, k < steps →
      active k i = false ∨
        (active k i = true ∧ role k i = .botRise))
    (hdeep : ∀ k, k < steps → ∀ q, i < q → active k q = false)
    (j : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeRunWithParentOverwrites initial i active role quota overwrite steps) j =
    d2FlowTreeChild initial j := by
  induction steps with
  | zero => rfl
  | succ n ih =>
      have hprev := ih
        (fun k hk => hroot k (by omega))
        (fun k hk q hq => hdeep k (by omega) q hq)
      have hstep := hroot n (by omega)
      have hdesc := hdeep n (by omega)
      cases initial with
      | node G low high children =>
        rw [d2FlowTreeRunWithParentOverwrites]
        change d2FlowTreeChild
          (d2FlowTreeSetRoot
            (d2FlowStage (active n) (role n) (quota n) (h + 1) i
              (d2FlowTreeRunWithParentOverwrites
                (.node G low high children) i active role quota overwrite n))
            _ _ _) j = children j
        rw [d2FlowTreeChild_setRoot]
        cases htree : d2FlowTreeRunWithParentOverwrites
            (.node G low high children) i active role quota overwrite n with
        | node G' low' high' children' =>
          rw [htree] at hprev
          have hprev' : children' j = children j := by
            simpa [d2FlowTreeChild] using hprev
          cases hstep with
          | inl hinactive =>
              rw [d2FlowStage_inactive_child children' hinactive j]
              rw [hprev']
              exact d2FlowStage_eq_self_of_inactive_tail (children j) (by
                intro q hq
                exact hdesc q (by omega))
          | inr hbot =>
              rcases hbot with ⟨hactive, hrole⟩
              simp only [d2FlowStage, hactive, if_pos, hrole, d2FlowTreeChild]
              rw [hprev']
              exact d2FlowStage_eq_self_of_inactive_tail (children j) (by
                intro q hq
                exact hdesc q (by omega))

theorem d2FlowTreeFull_atPath {h n : Nat} (scale : Nat)
    (path : D2FlowPath n) :
    d2FlowTreeAtPath n (d2FlowTreeFull scale (h + n)) path =
      d2FlowTreeFull scale h := by
  induction path generalizing h with
  | nil => rfl
  | @cons n j tail ih =>
      simp only [d2FlowTreeAtPath, d2FlowTreeChild, d2FlowTreeFull]
      exact ih (h := h)

theorem d2FlowTreePathContext_initial_eq_atPath {h n : Nat}
    (initial : D2FlowTree (h + n)) (path : D2FlowPath n) (i : Nat)
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat) :
    (d2FlowTreePathContext n initial path i active role quota overwrite).initial =
      d2FlowTreeAtPath n initial path := by
  induction path generalizing h i overwrite with
  | nil => rfl
  | @cons n j tail ih =>
      simp only [d2FlowTreePathContext, d2FlowTreeAtPath]
      exact ih (initial := d2FlowTreeChild initial j)
        (h := h) (i := i + 1)
        (overwrite := d2FlowTreeChildOverwrite
          (fun k => d2FlowTreeRunWithParentOverwrites initial i active role
            quota overwrite k) (i := i) active role quota j)

theorem d2FlowTreePathContext_level_eq {h n : Nat}
    (initial : D2FlowTree (h + n)) (path : D2FlowPath n) (i : Nat)
    (active : Nat → Nat → Bool) (role : Nat → Nat → D2Role)
    (quota : Nat → Nat → D2Role → Nat)
    (overwrite : Nat → Nat × Nat × Nat) :
    (d2FlowTreePathContext n initial path i active role quota overwrite).level =
      i + n := by
  induction path generalizing h i overwrite with
  | nil => simp [d2FlowTreePathContext]
  | @cons n j tail ih =>
      simp only [d2FlowTreePathContext]
      rw [ih (h := h) (i := i + 1)]
      omega

/-- Through stages 0–13, every level-six subtree retains full level-seven
children. This supplies the tight level-six reserve at the Stage-14 input. -/
theorem d2FlowCandidateLevelSix_children_preserved
    (childDepth : Nat) (hd : 7 ≤ childDepth)
    (path : D2FlowPath 6) (j : Fin 8) :
    d2FlowTreeChild
      (d2FlowTreeAtPath 6
        (d2FlowCandidateRun (childDepth + 7)
          (d2FlowTreeInitial 8192 (childDepth + 7)) 14) path) j =
      d2FlowTreeFull 8192 childDepth := by
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let active := d2FlowCandidateRunActive d
  let role := d2FlowCandidateRunRole d
  let quota := d2FlowCandidateRunQuota d
  let overwrite := d2FlowCandidateRunOverwrite d initial
  let context := d2FlowTreePathContext 6 initial path 0 active role quota overwrite
  have hpath := d2FlowCandidateRun_path_as_history
    (h := childDepth + 1) (n := 6) (initial := initial)
    (path := path) (step := 14)
  have hinitial : d2FlowTreeAtPath 6 initial path =
      d2FlowTreeFull 8192 (childDepth + 1) := by
    cases path with
    | cons first tail =>
        simp only [initial, d, d2FlowTreeAtPath, d2FlowTreeChild,
          d2FlowTreeInitial]
        simpa [Nat.add_assoc] using
          (d2FlowTreeFull_atPath (h := childDepth + 1) (n := 5) 8192 tail)
  have hcontextInitial : context.initial =
      d2FlowTreeFull 8192 (childDepth + 1) := by
    rw [d2FlowTreePathContext_initial_eq_atPath]
    exact hinitial
  have hcontextLevel : context.level = 6 := by
    rw [d2FlowTreePathContext_level_eq]
  rw [show d2FlowCandidateRun d initial 14 =
      d2FlowCandidateRun (childDepth + 7) initial 14 by rfl] at hpath
  rw [hpath, d2FlowTreePathHistory_eq_context_run]
  change d2FlowTreeChild
      (d2FlowTreeRunWithParentOverwrites context.initial context.level
        active role quota context.overwrite 14) j =
    d2FlowTreeFull 8192 childDepth
  rw [hcontextLevel, hcontextInitial]
  apply d2FlowTreeRun_child_eq_of_inactive_or_botRise
    (active := active) (role := role) (quota := quota)
    (overwrite := context.overwrite) (steps := 14) (i := 6)
  · intro k hk
    by_cases hk12 : k = 12
    · subst k
      have hdD : 13 ≤ childDepth + 7 := by omega
      have hf := d2FlowCandidateStage12_frontiers (childDepth + 7) hdD
      exact Or.inr ⟨hf.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.1⟩
    · left
      by_cases hk0 : k = 0
      · subst k
        change d2FlowCandidateActive d 0 6 = false
        simp [d2FlowCandidateActive]
      by_cases hk1 : k = 1
      · subst k
        change d2FlowCandidateActive d 1 6 = false
        simp [d2FlowCandidateActive]
      have hfalse : ¬ (2 ≤ k ∧ k ≤ tfD2 d ∧ 6 % 2 = k % 2 ∧
          3 * 6 + 3 * d ≥ 2 * k + 11 ∧ 3 * 6 < k + 8) := by
        dsimp [d]
        omega
      change d2FlowCandidateActive d k 6 = false
      unfold d2FlowCandidateActive
      simp only [if_neg hk0, if_neg hk1]
      exact decide_false_of_not hfalse
  · intro k hk q hq
    have hfalse : ¬ (2 ≤ k ∧ k ≤ tfD2 d ∧ q % 2 = k % 2 ∧
        3 * q + 3 * d ≥ 2 * k + 11 ∧ 3 * q < k + 8) := by
      dsimp [d]
      omega
    change d2FlowCandidateActive d k q = false
    unfold d2FlowCandidateActive
    by_cases hk0 : k = 0
    · have hq0 : q ≠ 0 := by omega
      simp [hk0, hq0]
    by_cases hk1 : k = 1
    · have hq1 : q ≠ 1 := by omega
      simp [hk1, hq1]
    simp only [if_neg hk0, if_neg hk1]
    exact decide_false_of_not hfalse

/-- The first post-bootstrap snapshot has the same frontier shape for every
dimension `d ≥ 14`: a top reset, two middle senders, and one bottom-descending
sender. -/
theorem d2FlowCandidateStage14_frontiers (d : Nat) (hd : 14 ≤ d) :
    d2FlowCandidateActive d 14 0 = true ∧
      d2FlowCandidateRole d 14 0 = .topDesc ∧
      d2FlowCandidateActive d 14 2 = true ∧
      d2FlowCandidateRole d 14 2 = .mid ∧
      d2FlowCandidateActive d 14 4 = true ∧
      d2FlowCandidateRole d 14 4 = .mid ∧
      d2FlowCandidateActive d 14 6 = true ∧
      d2FlowCandidateRole d 14 6 = .botDesc ∧
      d2FlowCandidateActive d 14 8 = false := by
  have htf : 14 ≤ tfD2 d := by unfold tfD2; omega
  have hstar14 : alphaStar d 14 = 0 := by
    unfold alphaStar
    have h : 39 ≤ 3 * d := by omega
    simp [h]
  have hstar15 : alphaStar d 15 = 0 := by
    unfold alphaStar
    have h : 41 ≤ 3 * d := by omega
    simp [h]
  have ha14 : alpha d 14 = 0 := by
    simp [alpha, hstar14, ceilParity]
  have ha15 : alpha d 15 = 1 := by
    simp [alpha, hstar15, ceilParity]
  have ho14 : omega 14 = 6 := by norm_num [omega, ceilParity]
  have ho15 : omega 15 = 7 := by norm_num [omega, ceilParity]
  have hactive0 : d2FlowCandidateActive d 14 0 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive2 : d2FlowCandidateActive d 14 2 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive4 : d2FlowCandidateActive d 14 4 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hactive6 : d2FlowCandidateActive d 14 6 = true := by
    simp [d2FlowCandidateActive, tfD2]
    omega
  have hinactive8 : d2FlowCandidateActive d 14 8 = false := by
    simp [d2FlowCandidateActive]
  have hrole0 : d2FlowCandidateRole d 14 0 = .topDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha14, ha15]
  have hrole2 : d2FlowCandidateRole d 14 2 = .mid := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha14, ho14]
  have hrole4 : d2FlowCandidateRole d 14 4 = .mid := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha14, ho14]
  have hrole6 : d2FlowCandidateRole d 14 6 = .botDesc := by
    rw [d2FlowCandidateRole_matches_schedule (by omega)]
    simp [d2ScheduleRole, ha14, ho14, ho15]
  exact ⟨hactive0, hrole0, hactive2, hrole2, hactive4, hrole4,
    hactive6, hrole6, hinactive8⟩

/-- The tight Stage-14 level-six reserve is exactly its full level-seven
native child size. -/
theorem d2FlowCandidateStage14_levelSix_capacity_eq_nativeChild
    (d : Nat) (hd : 14 ≤ d) :
    d2FlowCandidateCapacity d 6 14 = 128 * (8192 * 8 ^ (d - 7)) := by
  have hexp : d2FlowCandidateCapacityExponent d 6 14 = 3 * d - 1 := by
    simp [d2FlowCandidateCapacityExponent]
    omega
  rw [show d2FlowCandidateCapacity d 6 14 =
    2 ^ d2FlowCandidateCapacityExponent d 6 14 by rfl, hexp]
  have hpow : 2 ^ (3 * d - 1) = 2 ^ 20 * 2 ^ (3 * (d - 7)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  norm_num [pow_mul]
  ring

/-- At the Stage-14 level-four mid sender, half of a child level-five
Stage-13 bottom-descending quota is already more than enough for the required
endpoint reserve. This is the exact numerical factor needed to pass a
Stage-13 level-five cut into Stage 14's level-four gate. -/
theorem d2FlowCandidateStage14_levelFour_halfQuota_covers_capacity
    (d : Nat) (hd : 14 <= d) :
    d2FlowCandidateCapacity d 4 14 <=
      128 * (d2FlowCandidateQuota d 13 5 .botDesc / 2) := by
  have hcap : d2FlowCandidateCapacity d 4 14 = 2 ^ (3 * d - 7) := by
    simp [d2FlowCandidateCapacity, d2FlowCandidateCapacityExponent]
    omega
  have hquota : d2FlowCandidateQuota d 13 5 .botDesc =
      15 * 2 ^ (3 * d - 14) := by
    simp [d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
    omega
  have hhalf : d2FlowCandidateQuota d 13 5 .botDesc / 2 =
      15 * 2 ^ (3 * d - 15) := by
    rw [hquota, show 3 * d - 14 = 1 + (3 * d - 15) by omega, pow_add]
    omega
  have hscale : 3 * d - 7 = 8 + (3 * d - 15) := by omega
  rw [hcap, hhalf, hscale, pow_add]
  nlinarith [show 0 < 2 ^ (3 * d - 15) by positivity]

/-- Therefore full level-seven children discharge both Stage-14 level-six
endpoint-reserve inequalities with equality. -/
theorem d2FlowCandidateStage14_levelSix_endpoint_reserves_of_full_children
    (d : Nat) (hd : 14 ≤ d)
    (children : Fin 8 → D2FlowTree (d - 7))
    (hfull : ∀ j, d2FlowTreeRootDeficit (children j) = 8192 * 8 ^ (d - 7)) :
    d2FlowCandidateCapacity d 6 14 ≤
        128 * d2FlowTreeRootDeficit (children ⟨0, by omega⟩) ∧
      d2FlowCandidateCapacity d 6 14 ≤
        128 * d2FlowTreeRootDeficit (children ⟨7, by omega⟩) := by
  rw [d2FlowCandidateStage14_levelSix_capacity_eq_nativeChild d hd,
    hfull ⟨0, by omega⟩, hfull ⟨7, by omega⟩]
  exact ⟨le_rfl, le_rfl⟩

/-- The actual Stage-14 level-six endpoint reserve holds uniformly: the
capacity is exactly the native size of each preserved full child. -/
theorem d2FlowCandidateStage14_actual_levelSix_endpoint_reserves
    (childDepth : Nat) (hd : 7 ≤ childDepth) (path : D2FlowPath 6) :
    d2FlowCandidateCapacity (childDepth + 7) 6 14 ≤
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeAtPath 6
              (d2FlowCandidateRun (childDepth + 7)
                (d2FlowTreeInitial 8192 (childDepth + 7)) 14) path)
            ⟨0, by omega⟩) ∧
      d2FlowCandidateCapacity (childDepth + 7) 6 14 ≤
        128 * d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowTreeAtPath 6
              (d2FlowCandidateRun (childDepth + 7)
                (d2FlowTreeInitial 8192 (childDepth + 7)) 14) path)
            ⟨7, by omega⟩) := by
  have hfull : ∀ j : Fin 8,
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeAtPath 6
            (d2FlowCandidateRun (childDepth + 7)
              (d2FlowTreeInitial 8192 (childDepth + 7)) 14) path) j) =
        8192 * 8 ^ childDepth := by
    intro j
    rw [d2FlowCandidateLevelSix_children_preserved childDepth hd path j,
      d2FlowTreeFull_root_deficit]
  exact d2FlowCandidateStage14_levelSix_endpoint_reserves_of_full_children
    (d := childDepth + 7) (by omega)
    (fun j => d2FlowTreeChild
      (d2FlowTreeAtPath 6
        (d2FlowCandidateRun (childDepth + 7)
          (d2FlowTreeInitial 8192 (childDepth + 7)) 14) path) j)
    hfull

/-- Every actual level-six node at the Stage-14 input is balanced: its
Stage-13 level-five parent writes balanced root data into each child. -/
theorem d2FlowCandidateStage14_actual_levelSix_balanced
    (childDepth : Nat) (hd : 7 ≤ childDepth) :
    ∀ j k m l q s,
      let output := d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowCandidateRun (childDepth + 7)
                    (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j) k) m) l) q) s
      (d2FlowTreeRootData output).2.1 + (d2FlowTreeRootData output).2.2 =
        d2FlowTreeRootDeficit output := by
  intro j k m l q s
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let before := d2FlowCandidateRun d initial 13
  let parent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild before j) k) m) l) q
  have hfront := d2FlowCandidateStage13_frontiers d (by omega)
  rcases hfront with ⟨_, _, _, _, hactive5, hrole5, _⟩
  have hregular : d2FlowCandidateRole d 13 5 = .topRise ∨
      d2FlowCandidateRole d 13 5 = .mid ∨
      d2FlowCandidateRole d 13 5 = .botDesc := Or.inr (Or.inr hrole5)
  cases hparent : parent with
  | node G low high children =>
      have hproject := d2FlowStage_path6_tree_projection
        (active := d2FlowCandidateActive d 13)
        (role := d2FlowCandidateRole d 13)
        (quota := d2FlowCandidateQuota d 13)
        (h := childDepth + 1) (i := 0)
        (d2FlowCandidateRun d initial 13) j k m l q s
      have hproject' :
          d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowCandidateRun d initial 14) j) k) m) l) q) s =
            d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive d 13)
                (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
                (childDepth + 2) 5 parent) s := by
        simpa [before, d, initial, d2FlowCandidateRun,
          d2FlowCandidateStage, parent] using hproject
      rw [hparent] at hproject'
      rw [hproject']
      exact d2FlowStage_regular_child_balanced children hactive5 hregular s

set_option maxHeartbeats 10000000
set_option linter.constructorNameAsVariable false
/-- Every actual level-six deficit entering Stage 14 is within its required
1/512 cap. Stage 13 clears interior children and bounds each endpoint by
`G + quota/2`; the stage/level capacity ratio makes that fit. -/
theorem d2FlowCandidateStage14_actual_levelSix_deficit_bound
    (childDepth : Nat) (hd : 7 ≤ childDepth) :
    ∀ j k m l q s,
      512 * d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowCandidateRun (childDepth + 7)
                      (d2FlowTreeInitial 8192 (childDepth + 7)) 14) j) k) m) l) q) s) ≤
        d2FlowCandidateCapacity (childDepth + 7) 6 14 := by
  intro j k m l q s
  let d := childDepth + 7
  let initial := d2FlowTreeInitial 8192 d
  let before := d2FlowCandidateRun d initial 13
  let parent := d2FlowTreeChild
    (d2FlowTreeChild
      (d2FlowTreeChild
        (d2FlowTreeChild
          (d2FlowTreeChild before j) k) m) l) q
  have hfront := d2FlowCandidateStage13_frontiers d (by omega)
  rcases hfront with ⟨_, _, _, _, hactive5, hrole5, _⟩
  have hregular : d2FlowCandidateRole d 13 5 = .topRise ∨
      d2FlowCandidateRole d 13 5 = .mid ∨
      d2FlowCandidateRole d 13 5 = .botDesc := Or.inr (Or.inr hrole5)
  have hinput := d2FlowCandidateStage13_actual_levelFive_inputs
    (childDepth + 1) (by omega) j k m l q
  change d2FlowStageInvInputs 8192
    (d2FlowCandidateActive d 13) (d2FlowCandidateRole d 13)
    (d2FlowCandidateQuota d 13)
    (fun r => d2FlowCandidateCapacity d r 13) 5 parent at hinput
  cases hparent : parent with
  | node G low high children =>
      rw [hparent] at hinput
      simp only [d2FlowStageInvInputs, hactive5, if_pos, hrole5] at hinput
      rcases hinput with ⟨_, ⟨hbalance, hG, hquotaCap, hquotaAlloc,
        hquotaEven, hleft, hright⟩⟩
      let c := d2FlowCandidateCapacity d 5 13
      let pi := d2FlowCandidateQuota d 13 5 .botDesc
      let sizes : Fin 8 → Nat := fun r => d2FlowTreeRootDeficit (children r)
      have htotal : pi ≤ d2FlowTotal sizes - G := by
        simpa [pi, sizes] using hquotaAlloc
      have hpiPos : 0 < pi := by
        simp [pi, d2FlowCandidateQuota, d2FlowCandidateCapacityExponent]
      have hGtotal : G ≤ d2FlowTotal sizes := by
        have hsubPos : 0 < d2FlowTotal sizes - G := lt_of_lt_of_le hpiPos htotal
        exact Nat.le_of_lt (Nat.lt_of_sub_pos hsubPos)
      have hconserve : (d2FlowTotal sizes - G) + G = d2FlowTotal sizes :=
        Nat.sub_add_cancel hGtotal
      have hquotaEven' : pi = 2 * (pi / 2) := by
        dsimp [pi]
        omega
      have hquotaAlloc' :
          d2FlowCandidateQuota d 13 5 (d2FlowCandidateRole d 13 5) ≤
            d2FlowTotal sizes - G := by
        simpa [pi, hrole5, sizes] using htotal
      have hquotaEven'' :
          d2FlowCandidateQuota d 13 5 (d2FlowCandidateRole d 13 5) =
            2 * (d2FlowCandidateQuota d 13 5
              (d2FlowCandidateRole d 13 5) / 2) := by
        simpa [pi, hrole5] using hquotaEven'
      have hquotaCap' :
          256 * d2FlowCandidateQuota d 13 5
              (d2FlowCandidateRole d 13 5) ≤ c := by
        simpa [hrole5, c] using hquotaCap
      have hGweak : 4096 * G ≤ 23 * c := by
        dsimp [c]
        nlinarith [hG]
      have hprofile := d2FlowStage_regular_child_profile_tolerant
        (active := d2FlowCandidateActive d 13)
        (role := d2FlowCandidateRole d 13)
        (quota := d2FlowCandidateQuota d 13)
        (children := children) (h := childDepth + 1) (i := 5)
        (G := G) (low := low) (high := high)
        (a := d2FlowTotal sizes - G) (c := c)
        hactive5 hregular hbalance hconserve hquotaAlloc' hquotaEven'' hGweak
        (by omega) (by omega) hquotaCap' hleft hright
      rw [hrole5] at hprofile
      have hchildBound :
          512 * d2FlowTreeRootDeficit
            (d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive d 13)
                (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
                (childDepth + 2) 5 (.node G low high children)) s) ≤ 2 * c := by
        have hprofile0 :
            d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 13)
                  (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
                  (childDepth + 2) 5 (.node G low high children)) 0) =
              low + pi / 2 := by
          simpa [Nat.add_assoc, pi] using hprofile.1
        have hprofile7 :
            d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 13)
                  (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
                  (childDepth + 2) 5 (.node G low high children)) 7) =
              high + pi / 2 := by
          simpa [Nat.add_assoc, pi] using hprofile.2.1
        by_cases hs0 : s.val = 0
        · have hs : s = ⟨0, by omega⟩ := Fin.ext hs0
          have hzero : d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowStage (d2FlowCandidateActive d 13)
                  (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
                  (childDepth + 2) 5 (.node G low high children)) s) =
              low + pi / 2 := by
            simpa [hs] using hprofile0
          rw [hzero]
          have hlow : low ≤ G := by omega
          have hhalf : 512 * (pi / 2) ≤ c := by
            nlinarith [hquotaCap', hquotaEven']
          nlinarith [hG, hhalf, hlow]
        · by_cases hs7 : s.val = 7
          · have hs : s = ⟨7, by omega⟩ := Fin.ext hs7
            have hlast : d2FlowTreeRootDeficit
                (d2FlowTreeChild
                  (d2FlowStage (d2FlowCandidateActive d 13)
                    (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
                    (childDepth + 2) 5 (.node G low high children)) s) =
                high + pi / 2 := by
              simpa [hs] using hprofile7
            rw [hlast]
            have hhigh : high ≤ G := by omega
            have hhalf : 512 * (pi / 2) ≤ c := by
              nlinarith [hquotaCap', hquotaEven']
            nlinarith [hG, hhalf, hhigh]
          · have hinterior := hprofile.2.2 s (by omega) (by omega)
            have hinterior' : d2FlowTreeRootDeficit
                (d2FlowTreeChild
                  (d2FlowStage (d2FlowCandidateActive d 13)
                    (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
                    (childDepth + 2) 5 (.node G low high children)) s) = 0 := by
              simpa [Nat.add_assoc] using hinterior
            rw [hinterior']
            omega
      have hcapacity := d2FlowCandidateCapacity_succ_level_next_stage
        d 5 13 (by omega)
      have hproject := d2FlowStage_path6_tree_projection
        (active := d2FlowCandidateActive d 13)
        (role := d2FlowCandidateRole d 13)
        (quota := d2FlowCandidateQuota d 13)
        (h := childDepth + 1) (i := 0)
        (d2FlowCandidateRun d initial 13) j k m l q s
      have hproject' :
          d2FlowTreeChild
            (d2FlowTreeChild
              (d2FlowTreeChild
                (d2FlowTreeChild
                  (d2FlowTreeChild
                    (d2FlowTreeChild
                      (d2FlowCandidateRun d initial 14) j) k) m) l) q) s =
            d2FlowTreeChild
              (d2FlowStage (d2FlowCandidateActive d 13)
                (d2FlowCandidateRole d 13) (d2FlowCandidateQuota d 13)
                (childDepth + 2) 5 parent) s := by
        simpa [before, d, initial, d2FlowCandidateRun,
          d2FlowCandidateStage, parent] using hproject
      rw [hparent] at hproject'
      rw [hproject']
      have hcapShift :
          d2FlowCandidateCapacity d 6 14 = 2 * c := by
        simpa [c] using hcapacity
      rw [hcapShift]
      exact hchildBound

end Chvatal.D2Reserve
