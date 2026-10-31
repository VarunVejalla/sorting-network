import D2Stage14Inputs

namespace Chvatal.D2Reserve

theorem d2FlowStageInvInputs_botDesc_of_contract
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    (scale i : Nat) {h : Nat} (tree : D2FlowTree (h + 1))
    (hactive : active i = true) (hrole : role i = .botDesc)
    (hchildren : forall s : Fin 8,
      d2FlowStageInvInputs scale active role quota cap (i + 1)
        (d2FlowTreeChild tree s))
    (hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree)
    (hdeficit : 512 * d2FlowTreeRootDeficit tree ≤ cap i)
    (hquotaCap : 256 * quota i .botDesc ≤ cap i)
    (halloc : quota i .botDesc ≤
      d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) -
        d2FlowTreeRootDeficit tree)
    (heven : quota i .botDesc % 2 = 0)
    (hleft : cap i ≤ 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild tree (Fin.mk 0 (by omega))))
    (hright : cap i ≤ 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild tree (Fin.mk 7 (by omega)))) :
    d2FlowStageInvInputs scale active role quota cap i tree := by
  cases tree with
  | node G low high children =>
    have hb : low + high = G := by
      simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hbalance
    have hd : 512 * G ≤ cap i := by
      simpa [d2FlowTreeRootDeficit] using hdeficit
    have ha : quota i .botDesc ≤
        d2FlowTotal (fun s => d2FlowTreeRootDeficit (children s)) - G := by
      simpa [d2FlowTreeChild, d2FlowTreeRootDeficit] using halloc
    have hl : cap i ≤ 128 * d2FlowTreeRootDeficit (children (Fin.mk 0 (by omega))) := by
      simpa [d2FlowTreeChild] using hleft
    have hr : cap i ≤ 128 * d2FlowTreeRootDeficit (children (Fin.mk 7 (by omega))) := by
      simpa [d2FlowTreeChild] using hright
    simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
    exact ⟨hchildren, hb, hd, hquotaCap, ha, heven, hl, hr⟩

/-- Mid-role counterpart of `d2FlowStageInvInputs_botDesc_of_contract`.
The hypotheses are stated at an arbitrary tree, so callers can establish
contracts for expensive concrete runs without case-splitting on and reducing
the run itself. -/
theorem d2FlowStageInvInputs_mid_of_contract
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    (scale i : Nat) {h : Nat} (tree : D2FlowTree (h + 1))
    (hactive : active i = true) (hrole : role i = .mid)
    (hchildren : forall s : Fin 8,
      d2FlowStageInvInputs scale active role quota cap (i + 1)
        (d2FlowTreeChild tree s))
    (hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree)
    (hdeficit : 512 * d2FlowTreeRootDeficit tree <= cap i)
    (hquotaCap : 256 * quota i .mid <= cap i)
    (halloc : quota i .mid <=
      d2FlowTotal (fun s => d2FlowTreeRootDeficit (d2FlowTreeChild tree s)) -
        d2FlowTreeRootDeficit tree)
    (heven : quota i .mid % 2 = 0)
    (hleft : cap i <= 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild tree (Fin.mk 0 (by omega))))
    (hright : cap i <= 128 * d2FlowTreeRootDeficit
      (d2FlowTreeChild tree (Fin.mk 7 (by omega)))) :
    d2FlowStageInvInputs scale active role quota cap i tree := by
  cases tree with
  | node G low high children =>
    have hb : low + high = G := by
      simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hbalance
    have hd : 512 * G <= cap i := by
      simpa [d2FlowTreeRootDeficit] using hdeficit
    have ha : quota i .mid <=
        d2FlowTotal (fun s => d2FlowTreeRootDeficit (children s)) - G := by
      simpa [d2FlowTreeChild, d2FlowTreeRootDeficit] using halloc
    have hl : cap i <= 128 * d2FlowTreeRootDeficit
        (children (Fin.mk 0 (by omega))) := by
      simpa [d2FlowTreeChild] using hleft
    have hr : cap i <= 128 * d2FlowTreeRootDeficit
        (children (Fin.mk 7 (by omega))) := by
      simpa [d2FlowTreeChild] using hright
    simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
    exact ⟨by simpa [d2FlowTreeChild] using hchildren,
      hb, hd, hquotaCap, ha, heven, hl, hr⟩


 /-- An inactive level contributes only its recursively checked children to
the stage-input predicate. -/
theorem d2FlowStageInvInputs_inactive_of_children
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    (scale i : Nat) {h : Nat} (tree : D2FlowTree (h + 1))
    (hinactive : active i = false)
    (hchildren : forall s : Fin 8,
      d2FlowStageInvInputs scale active role quota cap (i + 1)
        (d2FlowTreeChild tree s)) :
    d2FlowStageInvInputs scale active role quota cap i tree := by
  cases tree with
  | node G low high children =>
    simp only [d2FlowStageInvInputs, hinactive]
    constructor
    · intro s
      exact hchildren s
    · trivial

/-- Convert a three-edge path contract to the child view used when assembling
the preceding level. This is generic in the root tree, so path reduction does
not unfold any concrete run. -/
theorem d2FlowStageInvInputs_path3_child
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    (scale : Nat) {h : Nat} (tree : D2FlowTree (h + 3))
    (j k m : Fin 8)
    (hpath : d2FlowStageInvInputs scale active role quota cap 3
      (d2FlowTreeAtPath 3 tree (.cons j (.cons k (.cons m .nil))))) :
    d2FlowStageInvInputs scale active role quota cap 3
      (d2FlowTreeChild
        (d2FlowTreeAtPath 2 tree (.cons j (.cons k .nil))) m) := by
  simpa only [d2FlowTreeAtPath] using hpath

/-- Two-edge path counterpart used to assemble the inactive level-one gate. -/
theorem d2FlowStageInvInputs_path2_child
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    (scale : Nat) {h : Nat} (tree : D2FlowTree (h + 2))
    (j k : Fin 8)
    (hpath : d2FlowStageInvInputs scale active role quota cap 2
      (d2FlowTreeAtPath 2 tree (.cons j (.cons k .nil)))) :
    d2FlowStageInvInputs scale active role quota cap 2
      (d2FlowTreeChild (d2FlowTreeChild tree j) k) := by
  simpa only [d2FlowTreeAtPath] using hpath

/-- Assemble a `topDesc` root contract from its reset, balance, and the
recursive contracts for all children. -/
theorem d2FlowStageInvInputs_topDesc_of_contract
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {cap : Nat -> Nat}
    (scale i : Nat) {h : Nat} (tree : D2FlowTree (h + 1))
    (hactive : active i = true) (hrole : role i = .topDesc)
    (hchildren : forall s : Fin 8,
      d2FlowStageInvInputs scale active role quota cap (i + 1)
        (d2FlowTreeChild tree s))
    (hbalance : (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree)
    (hzero : d2FlowTreeRootDeficit tree = 0) :
    d2FlowStageInvInputs scale active role quota cap i tree := by
  cases tree with
  | node G low high children =>
    have hb : low + high = G := by
      simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hbalance
    have hz : G = 0 := by
      simpa [d2FlowTreeRootDeficit] using hzero
    simp only [d2FlowStageInvInputs, hactive, if_true, hrole]
    exact ⟨hchildren, hb, hz⟩

/-- A top-descending root sends no additional mass into its own deficit. -/
theorem d2FlowStage_root_deficit_of_topDesc
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i : Nat}
    (tree : D2FlowTree h) (ha : active i = true)
    (hr : role i = .topDesc) :
    d2FlowTreeRootDeficit (d2FlowStage active role quota h i tree) =
      d2FlowTreeRootDeficit tree := by
  cases tree with
  | leaf G low high => rfl
  | node G low high children =>
      simp [d2FlowStage, ha, hr, d2FlowTreeRootDeficit]

/-- At positive tree height, the invariant's conditional balance clause
applies automatically when the root deficit is zero. -/
theorem d2FlowTreeInv_root_balance_of_zero
    {h scale : Nat} (tree : D2FlowTree (h + 1))
    (hinv : d2FlowTreeInv scale tree)
    (hscale : 0 < scale)
    (hz : d2FlowTreeRootDeficit tree = 0) :
    (d2FlowTreeRootData tree).2.1 +
      (d2FlowTreeRootData tree).2.2 = d2FlowTreeRootDeficit tree := by
  cases tree with
  | node G low high children =>
      have hG : G = 0 := by simpa [d2FlowTreeRootDeficit] using hz
      have hinv' : d2FlowTreeInv scale (.node G low high children) := by
        simpa using hinv
      have hlt : G < scale * 8 ^ (h + 1) := by rw [hG]; positivity
      have hb := hinv'.2.2.1 hlt
      simpa [d2FlowTreeRootData, d2FlowTreeRootDeficit] using hb

end Chvatal.D2Reserve
