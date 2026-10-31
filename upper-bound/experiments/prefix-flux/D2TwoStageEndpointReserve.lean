import D2ScheduleReserve

namespace Chvatal.D2Reserve

set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

/-- A regular sender exports the two fields needed by its active child at the
next level and stage: the child deficit is at most twice the parent's cap,
and the child endpoint data are balanced. -/
theorem d2FlowStage_regular_child_cap_and_balance
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {cap : Nat → Nat}
    {stageDepth i : Nat}
    (tree : D2FlowTree (stageDepth + 1))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hinv : d2FlowTreeInv 8192 tree)
    (hinputs : d2FlowStageInvInputs 8192 active role quota cap i tree)
    (j : Fin 8) :
    512 * d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota
          (stageDepth + 1) i tree) j) ≤ 2 * cap i ∧
      (d2FlowTreeRootData
        (d2FlowTreeChild (d2FlowStage active role quota
          (stageDepth + 1) i tree) j)).2.1 +
      (d2FlowTreeRootData
        (d2FlowTreeChild (d2FlowStage active role quota
          (stageDepth + 1) i tree) j)).2.2 =
      d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota
          (stageDepth + 1) i tree) j) := by
  have hcap := d2FlowStage_regular_child_g_bound_of_tree_inputs
    tree ha hr hinv hinputs j
  cases tree with
  | node G low high children =>
      refine ⟨hcap, ?_⟩
      exact d2FlowStage_regular_child_balanced children ha hr j

/-- An ordinary sender writes at least half its quota into each endpoint
child. This is the concrete recursive-tree form of endpoint-reserve creation,
including the balance, allocation, parity, deficit, and endpoint-cap gates. -/
theorem d2FlowStage_regular_endpoint_halves
    {h i G low high : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat} {cap : Nat → Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hbalance : low + high = G)
    (hcover : G ≤ d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdeficit : 512 * G ≤ cap i)
    (hquota : 256 * quota i (role i) ≤ cap i)
    (halloc : quota i (role i) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (heven : quota i (role i) % 2 = 0)
    (hleft : cap i ≤ 128 * d2FlowTreeRootDeficit (children 0))
    (hright : cap i ≤ 128 * d2FlowTreeRootDeficit (children 7)) :
    quota i (role i) / 2 ≤ d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) 0) ∧
    quota i (role i) / 2 ≤ d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) 7) := by
  have hconserve :
      (d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) + G =
        Finset.univ.sum (fun j : Fin 8 =>
          d2FlowTreeRootDeficit (children j)) := by
    simpa [d2FlowTotal] using Nat.sub_add_cancel hcover
  have hlow : low ≤ G := by omega
  have hhigh : high ≤ G := by omega
  have hprofile := d2FlowStage_regular_child_profile_tolerant
    (active := active) (role := role) (quota := quota)
    (h := h) (i := i) (G := G) (low := low) (high := high)
    (a := d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (c := cap i) children ha hr hbalance hconserve halloc
    (by omega : quota i (role i) = 2 * (quota i (role i) / 2))
    (by nlinarith [hdeficit]) hlow hhigh hquota hleft hright
  constructor
  · rw [hprofile.1]
    omega
  · rw [hprofile.2.1]
    omega

/-- A following stage preserves the endpoint reserves when the sender level
is inactive. Its recursive child step can only increase a child's root
deficit, so the half-quota reserve survives without a trace-oracle premise. -/
theorem d2FlowStage_inactive_preserves_endpoint_halves
    {h i : Nat} {active : Nat → Bool}
    {role : Nat → D2Role} {quota : Nat → D2Role → Nat}
    (hinactive : active i = false)
    (tree : D2FlowTree (h + 1))
    (half : Nat)
    (hleft : half ≤ d2FlowTreeRootDeficit (d2FlowTreeChild tree 0))
    (hright : half ≤ d2FlowTreeRootDeficit (d2FlowTreeChild tree 7)) :
    half ≤ d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i tree) 0) ∧
    half ≤ d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota (h + 1) i tree) 7) := by
  cases htree : tree with
  | node G' low' high' grandchildren =>
      rw [htree] at hleft hright
      constructor
      · rw [d2FlowStage_inactive_child grandchildren hinactive 0]
        exact le_trans hleft
          (d2FlowStage_root_deficit_mono active role quota (i + 1)
            (d2FlowTreeChild (.node G' low' high' grandchildren) 0))
      · rw [d2FlowStage_inactive_child grandchildren hinactive 7]
        exact le_trans hright
          (d2FlowStage_root_deficit_mono active role quota (i + 1)
            (d2FlowTreeChild (.node G' low' high' grandchildren) 7))

/-- The endpoint-reserve induction step for an ordinary sender visit: the
ordinary cut writes half its quota into each endpoint child; one intervening
inactive visit of the same level cannot erase that reserve. Under the
schedule's 16-to-1 capacity decrease and ordinary-quota lower bound, the
reserve is sufficient for the next visit at this level. -/
theorem d2FlowStage_regular_two_step_endpoint_reserve
    {h i G low high oldCap newCap : Nat}
    {active nextActive : Nat → Bool}
    {role nextRole : Nat → D2Role}
    {quota nextQuota : Nat → D2Role → Nat}
    (children : Fin 8 → D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hbalance : low + high = G)
    (hcover : G ≤ d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdeficit : 512 * G ≤ oldCap)
    (hquota : 256 * quota i (role i) ≤ oldCap)
    (halloc : quota i (role i) ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (heven : quota i (role i) % 2 = 0)
    (hleft : oldCap ≤ 128 * d2FlowTreeRootDeficit (children 0))
    (hright : oldCap ≤ 128 * d2FlowTreeRootDeficit (children 7))
    (hinactive : nextActive i = false)
    (hcap : oldCap = 16 * newCap)
    (hquotaLower : 15 * oldCap ≤ 4096 * quota i (role i)) :
    newCap ≤ 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage nextActive nextRole nextQuota (h + 1) i
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children))) 0) ∧
    newCap ≤ 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage nextActive nextRole nextQuota (h + 1) i
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children))) 7) := by
  have hcreated := d2FlowStage_regular_endpoint_halves
    (cap := fun _ => oldCap) children ha hr
    hbalance hcover hdeficit hquota halloc heven hleft hright
  have hretained := d2FlowStage_inactive_preserves_endpoint_halves
    (active := nextActive) (role := nextRole) (quota := nextQuota) hinactive
    (d2FlowStage active role quota (h + 1) i
      (.node G low high children))
    (quota i (role i) / 2) hcreated.1 hcreated.2
  have hhalf : newCap ≤ 128 * (quota i (role i) / 2) := by
    omega
  constructor
  · exact le_trans hhalf (Nat.mul_le_mul_left 128 hretained.1)
  · exact le_trans hhalf (Nat.mul_le_mul_left 128 hretained.2)

/-- If an ancestor overwrites this sender's root after its ordinary update,
the endpoint reserves generated in its children still survive the next
inactive visit. An inactive root update recurses into the same child trees
regardless of the overwritten root data. -/
theorem d2FlowStage_inactive_root_overwrite_irrelevant
    {h i G' low' high' : Nat}
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat}
    (hinactive : active i = false)
    (tree : D2FlowTree (h + 1)) :
    d2FlowStage active role quota (h + 1) i
        (d2FlowTreeSetRoot tree G' low' high') =
      d2FlowTreeSetRoot
        (d2FlowStage active role quota (h + 1) i tree) G' low' high' := by
  cases tree with
  | node oldG oldLow oldHigh children =>
      simp [d2FlowStage, d2FlowTreeSetRoot, hinactive]

/-- The ordinary two-step reserve theorem remains valid when an ancestor
replaces the sender's root data between its active update and the following
inactive stage. The endpoint child roots are unaffected by that replacement. -/
theorem d2FlowStage_regular_two_step_endpoint_reserve_of_root_overwrite
    {h i G low high oldCap newCap G' low' high' : Nat}
    {active nextActive : Nat -> Bool}
    {role nextRole : Nat -> D2Role}
    {quota nextQuota : Nat -> D2Role -> Nat}
    (children : Fin 8 -> D2FlowTree h)
    (ha : active i = true)
    (hr : role i = .topRise \/ role i = .mid \/ role i = .botDesc)
    (hbalance : low + high = G)
    (hcover : G <= d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdeficit : 512 * G <= oldCap)
    (hquota : 256 * quota i (role i) <= oldCap)
    (halloc : quota i (role i) <=
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G)
    (heven : quota i (role i) % 2 = 0)
    (hleft : oldCap <= 128 * d2FlowTreeRootDeficit (children 0))
    (hright : oldCap <= 128 * d2FlowTreeRootDeficit (children 7))
    (hinactive : nextActive i = false)
    (hcap : oldCap = 16 * newCap)
    (hquotaLower : 15 * oldCap <= 4096 * quota i (role i)) :
    newCap <= 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage nextActive nextRole nextQuota (h + 1) i
          (d2FlowTreeSetRoot
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) G' low' high')) 0) /\
    newCap <= 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage nextActive nextRole nextQuota (h + 1) i
          (d2FlowTreeSetRoot
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) G' low' high')) 7) := by
  have hbase := d2FlowStage_regular_two_step_endpoint_reserve
    (active := active) (nextActive := nextActive)
    (role := role) (nextRole := nextRole)
    (quota := quota) (nextQuota := nextQuota)
    (oldCap := oldCap) (newCap := newCap)
    children ha hr hbalance hcover hdeficit hquota halloc heven
    hleft hright hinactive hcap hquotaLower
  have hcomm := d2FlowStage_inactive_root_overwrite_irrelevant
    (active := nextActive) (role := nextRole) (quota := nextQuota)
    (G' := G') (low' := low') (high' := high') hinactive
    (d2FlowStage active role quota (h + 1) i
      (.node G low high children))
  have hchild (j : Fin 8) :
      d2FlowTreeChild
          (d2FlowStage nextActive nextRole nextQuota (h + 1) i
            (d2FlowTreeSetRoot
              (d2FlowStage active role quota (h + 1) i
                (.node G low high children)) G' low' high')) j =
        d2FlowTreeChild
          (d2FlowStage nextActive nextRole nextQuota (h + 1) i
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children))) j := by
    rw [hcomm, d2FlowTreeChild_setRoot]
  constructor
  · rw [hchild 0]
    exact hbase.1
  · rw [hchild 7]
    exact hbase.2

/-- In an actual path history, the selected sender's child roots after two
stages agree with the two local stage transitions whenever the sender is
inactive at the intervening stage. The ancestor overwrite after the first
transition changes only the sender root, and the overwrite after the second
transition changes none of its children. -/
theorem d2FlowTreeRunWithParentOverwrites_child_two_step_eq
    {h i n : Nat} (initial : D2FlowTree (h + 1))
    (active : Nat -> Nat -> Bool) (role : Nat -> Nat -> D2Role)
    (quota : Nat -> Nat -> D2Role -> Nat)
    (overwrite : Nat -> Nat × Nat × Nat) (j : Fin 8)
    (hinactive : active (n + 1) i = false) :
    d2FlowTreeChild
        (d2FlowTreeRunWithParentOverwrites initial i active role quota
          overwrite (n + 2)) j =
      d2FlowTreeChild
        (d2FlowStage (active (n + 1)) (role (n + 1)) (quota (n + 1))
          (h + 1) i
          (d2FlowStage (active n) (role n) (quota n) (h + 1) i
            (d2FlowTreeRunWithParentOverwrites initial i active role quota
              overwrite n))) j := by
  simp only [d2FlowTreeRunWithParentOverwrites, d2FlowTreeChild_setRoot]
  rw [d2FlowStage_inactive_root_overwrite_irrelevant
    (active := active (n + 1)) (role := role (n + 1))
    (quota := quota (n + 1)) hinactive]
  rw [d2FlowTreeChild_setRoot]

end Chvatal.D2Reserve
