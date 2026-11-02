import D2DynamicSenderNode

/-! The active-parent case of the dynamic sender-set size transition. -/

namespace Chvatal.D2OrdinaryRankRouting

open Chvatal.D2Reserve

private theorem d2FlowTreeAllocation_eq_capacity_sub_root
    {h scale : Nat} (tree : D2FlowTree h)
    (hcover : d2FlowTreeRootDeficit tree <=
      d2FlowTreeCapacityMass scale tree) :
    d2FlowTreeAllocation scale tree =
      d2FlowTreeCapacityMass scale tree - d2FlowTreeRootDeficit tree := by
  cases tree with
  | leaf G low high =>
      have hG : G <= scale := by
        simpa [d2FlowTreeRootDeficit, d2FlowTreeCapacityMass] using hcover
      simp [d2FlowTreeAllocation, d2FlowTreeRootDeficit,
        d2FlowTreeCapacityMass]
  | node G low high children =>
      simp only [d2FlowTreeAllocation, d2FlowTreeRootDeficit,
        d2FlowTreeCapacityMass]

/-- Every node's current sender set has the allocation prescribed by its flow
tree node. -/
def d2SenderLayoutFlowSizes {Wire : Type*} [DecidableEq Wire]
    (scale : Nat) : {h : Nat} -> D2SenderLayout Wire h ->
      D2FlowTree h -> Prop
  | 0, .leaf bag, .leaf G low high =>
      bag.card = d2FlowTreeAllocation scale (.leaf G low high)
  | h + 1, .node bag layoutChildren, .node G low high flowChildren =>
      bag.card = d2FlowTreeAllocation scale
        (.node G low high flowChildren) /\
      forall j, d2SenderLayoutFlowSizes scale
        (layoutChildren j) (flowChildren j)

/-- Local facts needed to lift one recursive set-routing stage through the
flow allocation recurrence. Active nodes provide their exact up/down-port
sizes and disjointness; inactive nodes provide disjoint retained/child sets. -/
def d2SenderLayoutStageSizeContract {Wire : Type*} [DecidableEq Wire]
    (scale : Nat) (active : Nat -> Bool) (role : Nat -> D2Role)
    (quota : Nat -> D2Role -> Nat)
    (split : Nat -> Finset Wire -> D2SenderPorts Wire) :
    {h : Nat} -> (i : Nat) -> (layout : D2SenderLayout Wire h) ->
      (flow : D2FlowTree h) -> Prop
  | 0, i, .leaf _, .leaf G low high =>
      d2FlowTreeInv scale (.leaf G low high) /\ active i = false
  | h + 1, i, .node bag layoutChildren,
      .node G low high flowChildren =>
      d2FlowTreeInv scale (.node G low high flowChildren) /\
      (forall j, d2SenderLayoutStageSizeContract scale active role quota split
        (i + 1) (layoutChildren j) (flowChildren j)) /\
      (if active i = true then
        active (i + 1) = false /\
        d2FlowTreeAllocation scale
          (d2FlowStage active role quota (h + 1) i
            (.node G low high flowChildren)) = 0 /\
        (split i bag).up.card = d2FlowStagePort active role quota
          (h + 1) i (.node G low high flowChildren) /\
        (forall j,
          ((split i bag).down j).card =
            d2FlowTreeRootDeficit (flowChildren j) -
              d2FlowTreeRootDeficit
                (d2FlowTreeChild
                  (d2FlowStage active role quota (h + 1) i
                    (.node G low high flowChildren)) j) /\
          Disjoint
            (d2SenderLayoutRootBag
              (d2SenderLayoutStage active split h (i + 1)
                (layoutChildren j)).1)
            ((split i bag).down j) /\
          d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowStage active role quota (h + 1) i
                  (.node G low high flowChildren)) j) <=
            d2FlowTreeCapacityMass scale
              (d2FlowStage active role quota h (i + 1)
                (flowChildren j)) /\
          d2FlowTreeRootDeficit
              (d2FlowTreeChild
                (d2FlowStage active role quota (h + 1) i
                  (.node G low high flowChildren)) j) <=
            d2FlowTreeRootDeficit (flowChildren j))
      else
        Disjoint bag (Finset.univ.biUnion fun j =>
          (d2SenderLayoutStage active split h (i + 1)
            (layoutChildren j)).2) /\
        (forall j k, j != k ->
          Disjoint
            ((d2SenderLayoutStage active split h (i + 1)
              (layoutChildren j)).2)
            ((d2SenderLayoutStage active split h (i + 1)
              (layoutChildren k)).2)))

/-- If an active parent sends its down-port into an inactive child, the
updated child sender set has exactly the allocation prescribed by the flow
tree after the parent's root overwrite.

The recursive child's set-size equality is the induction hypothesis. The
other physical premise is the exact down-port width and its disjointness from
that recursively updated set. -/
theorem d2SenderLayout_active_parent_child_cardinality
    {Wire : Type*} [DecidableEq Wire]
    {active : Nat -> Bool} {role : Nat -> D2Role}
    {quota : Nat -> D2Role -> Nat} {h scale i G low high : Nat}
    (layoutChild : D2SenderLayout Wire h)
    (flowChildren : Fin 8 -> D2FlowTree h) (j : Fin 8)
    (split : Nat -> Finset Wire -> D2SenderPorts Wire)
    (parentDown : Finset Wire)
    (hchildInactive : active (i + 1) = false)
    (hinv : d2FlowTreeInv scale (flowChildren j))
    (hrecCard : (d2SenderLayoutRootBag
      (d2SenderLayoutStage active split h (i + 1) layoutChild).1).card =
        d2FlowTreeAllocation scale
          (d2FlowStage active role quota h (i + 1) (flowChildren j)))
    (hdownCard : parentDown.card =
      d2FlowTreeRootDeficit (flowChildren j) -
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high flowChildren)) j))
    (hdownDisjoint : Disjoint
      (d2SenderLayoutRootBag
        (d2SenderLayoutStage active split h (i + 1) layoutChild).1)
      parentDown)
    (hpostCover : d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high flowChildren)) j) <=
      d2FlowTreeCapacityMass scale
        (d2FlowStage active role quota h (i + 1) (flowChildren j)))
    (hrootDrop : d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high flowChildren)) j) <=
      d2FlowTreeRootDeficit (flowChildren j)) :
    (d2SenderLayoutRootBag
      (d2SenderLayoutSetRoot
        (d2SenderLayoutStage active split h (i + 1) layoutChild).1
        (d2SenderLayoutRootBag
          (d2SenderLayoutStage active split h (i + 1) layoutChild).1 ∪
        parentDown))).card = d2FlowTreeAllocation scale
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high flowChildren)) j) := by
  let flowChild := flowChildren j
  let flowPost := d2FlowTreeChild
    (d2FlowStage active role quota (h + 1) i
      (.node G low high flowChildren)) j
  let recFlow := d2FlowStage active role quota h (i + 1) flowChild
  have hpost : flowPost = d2FlowTreeSetRoot recFlow
      (d2FlowTreeRootData flowPost).1
      (d2FlowTreeRootData flowPost).2.1
      (d2FlowTreeRootData flowPost).2.2 := by
    exact d2FlowStage_child_decomposes (children := flowChildren) j
  have hcapMono : d2FlowTreeCapacityMass scale flowChild <=
      d2FlowTreeCapacityMass scale recFlow :=
    d2FlowTreeCapacityMass_inactive_stage_mono active role quota
      (i + 1) flowChild hchildInactive
  have hchildCover : d2FlowTreeRootDeficit flowChild <=
      d2FlowTreeCapacityMass scale flowChild :=
    d2FlowTreeInv_root_le_capacityMass flowChild hinv
  have hrecCover : d2FlowTreeRootDeficit flowChild <=
      d2FlowTreeCapacityMass scale recFlow := le_trans hchildCover hcapMono
  have hrootSame := d2FlowStage_root_deficit_of_inactive
    (active := active) (role := role) (quota := quota)
    (h := h) (i := i + 1) flowChild hchildInactive
  have hrecCover' : d2FlowTreeRootDeficit recFlow <=
      d2FlowTreeCapacityMass scale recFlow := by
    rw [hrootSame]
    exact hrecCover
  have hrecAllocation : d2FlowTreeAllocation scale recFlow =
      d2FlowTreeCapacityMass scale recFlow -
        d2FlowTreeRootDeficit recFlow :=
    d2FlowTreeAllocation_eq_capacity_sub_root recFlow hrecCover'
  have hrecCapacity : d2FlowTreeAllocation scale recFlow +
      d2FlowTreeRootDeficit flowChild =
        d2FlowTreeCapacityMass scale recFlow := by
    rw [hrecAllocation, hrootSame]
    exact Nat.sub_add_cancel hrecCover
  have hpostCapacityMass : d2FlowTreeCapacityMass scale flowPost =
      d2FlowTreeCapacityMass scale recFlow := by
    rw [hpost, d2FlowTreeCapacityMass_setRoot]
  have hpostCover' : d2FlowTreeRootDeficit flowPost <=
      d2FlowTreeCapacityMass scale flowPost := by
    rw [hpostCapacityMass]
    simpa [flowPost, recFlow] using hpostCover
  have hpostCoverRec : d2FlowTreeRootDeficit flowPost <=
      d2FlowTreeCapacityMass scale recFlow := by
    rw [← hpostCapacityMass]
    exact hpostCover'
  have hpostCapacity : d2FlowTreeAllocation scale flowPost +
      d2FlowTreeRootDeficit flowPost =
        d2FlowTreeCapacityMass scale recFlow := by
    rw [d2FlowTreeAllocation_eq_capacity_sub_root flowPost hpostCover',
      hpostCapacityMass]
    exact Nat.sub_add_cancel hpostCoverRec
  have hlayoutRoot := d2SenderLayoutRootBag_setRoot
    (d2SenderLayoutStage active split h (i + 1) layoutChild).1
    (d2SenderLayoutRootBag
      (d2SenderLayoutStage active split h (i + 1) layoutChild).1 ∪
      parentDown)
  rw [hlayoutRoot, Finset.card_union_of_disjoint hdownDisjoint,
    hrecCard, hdownCard]
  have hrecCapacity' :
      d2FlowTreeAllocation scale
          (d2FlowStage active role quota h (i + 1) (flowChildren j)) +
        d2FlowTreeRootDeficit (flowChildren j) =
          d2FlowTreeCapacityMass scale recFlow := by
    simpa [recFlow, flowChild] using hrecCapacity
  have hpostCapacity' :
      d2FlowTreeAllocation scale
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high flowChildren)) j) +
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high flowChildren)) j) =
          d2FlowTreeCapacityMass scale recFlow := by
    simpa [flowPost] using hpostCapacity
  omega

theorem d2SenderLayoutFlowSizes_root_card {Wire : Type*} [DecidableEq Wire]
    {scale h : Nat} {layout : D2SenderLayout Wire h} {flow : D2FlowTree h}
    (hsize : d2SenderLayoutFlowSizes scale layout flow) :
    (d2SenderLayoutRootBag layout).card =
      d2FlowTreeAllocation scale flow := by
  cases layout with
  | leaf bag =>
      cases flow with
      | leaf G low high => exact hsize
  | node bag children =>
      cases flow with
      | node G low high flowChildren => exact hsize.1

theorem d2SenderLayoutFlowSizes_setRoot {Wire : Type*} [DecidableEq Wire]
    {scale h : Nat} {layout : D2SenderLayout Wire h} {flow : D2FlowTree h}
    (bag : Finset Wire) (G low high : Nat)
    (hsize : d2SenderLayoutFlowSizes scale layout flow)
    (hcard : bag.card = d2FlowTreeAllocation scale
      (d2FlowTreeSetRoot flow G low high)) :
    d2SenderLayoutFlowSizes scale (d2SenderLayoutSetRoot layout bag)
      (d2FlowTreeSetRoot flow G low high) := by
  cases layout with
  | leaf oldBag =>
      cases flow with
      | leaf oldG oldLow oldHigh => exact hcard
  | node oldBag children =>
      cases flow with
      | node oldG oldLow oldHigh flowChildren => exact ⟨hcard, hsize.2⟩

theorem d2SenderLayoutFlowSizes_node {Wire : Type*} [DecidableEq Wire]
    {scale h : Nat} {bag : Finset Wire}
    {children : Fin 8 -> D2SenderLayout Wire h} {flow : D2FlowTree (h + 1)}
    (hroot : bag.card = d2FlowTreeAllocation scale flow)
    (hchildren : forall j, d2SenderLayoutFlowSizes scale (children j)
      (d2FlowTreeChild flow j)) :
    d2SenderLayoutFlowSizes scale (.node bag children) flow := by
  cases flow with
  | node G low high flowChildren => exact ⟨hroot, hchildren⟩

/-- The recursive sender-set layout and abstract flow preserve exact sender
cardinalities in one stage, provided each active local router supplies its
port sizes and disjoint pieces. This is the all-tree size induction interface;
the candidate physical ports still have to discharge its contract. -/
theorem d2SenderLayoutStage_preserves_flow_sizes
    {Wire : Type*} [DecidableEq Wire]
    (scale : Nat) (active : Nat -> Bool) (role : Nat -> D2Role)
    (quota : Nat -> D2Role -> Nat)
    (split : Nat -> Finset Wire -> D2SenderPorts Wire) :
    forall {h : Nat} (i : Nat) (layout : D2SenderLayout Wire h)
      (flow : D2FlowTree h),
      d2SenderLayoutFlowSizes scale layout flow ->
      d2SenderLayoutStageSizeContract scale active role quota split i
        layout flow ->
      d2SenderLayoutFlowSizes scale
        (d2SenderLayoutStage active split h i layout).1
        (d2FlowStage active role quota h i flow) /\
      (d2SenderLayoutStage active split h i layout).2.card =
        d2FlowStagePort active role quota h i flow := by
  intro h
  induction h with
  | zero =>
      intro i layout flow hsize hcontract
      cases layout with
      | leaf bag =>
        cases flow with
        | leaf G low high =>
          exact ⟨hsize, by
            show (∅ : Finset Wire).card = _
            simp [d2FlowStagePort, d2FlowStage]⟩
  | succ h ih =>
      intro i layout flow hsize hcontract
      cases layout with
      | node bag layoutChildren =>
        cases flow with
        | node G low high flowChildren =>
          rcases hsize with ⟨hrootSize, hchildrenSize⟩
          rcases hcontract with ⟨hinv, hchildrenContract, hlocal⟩
          have hchildResult (j : Fin 8) :=
            ih (i + 1) (layoutChildren j) (flowChildren j)
              (hchildrenSize j) (hchildrenContract j)
          by_cases ha : active i = true
          · rw [if_pos ha] at hlocal
            rcases hlocal with ⟨hnextInactive, hparentZero, hparentUp,
              hdown⟩
            constructor
            · rw [d2SenderLayoutStage_node_active_eq active split i bag
                layoutChildren ha]
              refine d2SenderLayoutFlowSizes_node ?_ ?_
              · rw [hparentZero]
                rfl
              · intro j
                have hchildSize :=
                  d2SenderLayout_active_parent_child_cardinality
                    (role := role) (quota := quota) (G := G) (low := low)
                    (high := high) (scale := scale)
                    (layoutChildren j) flowChildren j split
                    ((split i bag).down j) hnextInactive
                    (hinv.2.2.2 j)
                    (d2SenderLayoutFlowSizes_root_card (hchildResult j).1)
                    (hdown j).1 (hdown j).2.1
                    (hdown j).2.2.1 (hdown j).2.2.2
                rw [d2SenderLayoutRootBag_setRoot] at hchildSize
                have hpost := d2FlowStage_child_decomposes
                  (active := active) (role := role) (quota := quota)
                  (i := i) (G := G) (low := low) (high := high)
                  flowChildren j
                rw [hpost]
                refine d2SenderLayoutFlowSizes_setRoot _ _ _ _
                  (hchildResult j).1 ?_
                rw [← hpost]
                exact hchildSize
            · rw [(d2SenderLayoutStage_node_active active split i bag
                layoutChildren ha).2]
              exact hparentUp
          · have hinactive : active i = false := by
              cases hactive : active i <;> simp_all
            rw [if_neg ha] at hlocal
            rcases hlocal with ⟨hdisjoint, hchildDisjoint⟩
            have hroot :=
              d2SenderLayoutStage_inactive_root_card_eq_allocation
                (role := role) (quota := quota)
                bag layoutChildren flowChildren split hinactive hinv
                (by simpa using hrootSize)
                (fun j => (hchildResult j).2)
                (fun j k hne => hchildDisjoint j k (bne_iff_ne.mpr hne))
                hdisjoint
            have hparentInactive :=
              d2SenderLayoutStage_node_inactive active split i bag
                layoutChildren hinactive
            rw [hparentInactive.1] at hroot
            constructor
            · rw [d2SenderLayoutStage_node_inactive_eq active split i bag
                layoutChildren hinactive]
              refine d2SenderLayoutFlowSizes_node hroot ?_
              intro j
              rw [d2FlowStage_inactive_child]
              · exact (hchildResult j).1
              · exact hinactive
            · rw [hparentInactive.2]
              have hrootSame := d2FlowStage_root_deficit_of_inactive
                (active := active) (role := role) (quota := quota)
                (h := h + 1) (i := i) (.node G low high flowChildren)
                hinactive
              show (∅ : Finset Wire).card = _
              simp [d2FlowStagePort, hrootSame]

end Chvatal.D2OrdinaryRankRouting
