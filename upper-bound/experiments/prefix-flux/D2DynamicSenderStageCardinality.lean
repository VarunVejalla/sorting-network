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

end Chvatal.D2OrdinaryRankRouting
