import D2RoutedMass
import D2ScheduleReserve

/-! Size formulas for the physical rank pieces and the abstract flow
allocation recurrence used by the proposed dynamic sender-set representation.
The concrete tree-wide sender layout and spatial profile invariant remain
open. -/

namespace Chvatal.D2OrdinaryRankRouting

open Chvatal
open Chvatal.D2RoutedMass
open Chvatal.D2Reserve

/-- Total capacity currently represented below a flow-tree node. A leaf has
its fixed native capacity; an internal node's capacity mass is the sum of its
child root deficits. -/
def d2FlowTreeCapacityMass (scale : Nat) : {h : Nat} → D2FlowTree h → Nat
  | 0, .leaf _ _ _ => scale
  | _ + 1, .node _ _ _ children =>
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j))

theorem d2FlowTreeCapacityMass_setRoot {h scale : Nat}
    (tree : D2FlowTree h) (G low high : Nat) :
    d2FlowTreeCapacityMass scale
        (d2FlowTreeSetRoot tree G low high) =
      d2FlowTreeCapacityMass scale tree := by
  cases tree <;> rfl

theorem d2FlowTreeInv_root_le_capacityMass {h scale : Nat}
    (tree : D2FlowTree h) (hinv : d2FlowTreeInv scale tree) :
    d2FlowTreeRootDeficit tree ≤ d2FlowTreeCapacityMass scale tree := by
  cases tree with
  | leaf G low high =>
      simpa [d2FlowTreeRootDeficit, d2FlowTreeCapacityMass,
        d2FlowTreeInv] using hinv.1
  | node G low high children =>
      simpa [d2FlowTreeRootDeficit, d2FlowTreeCapacityMass,
        d2FlowTreeInv] using hinv.2.1

/-- A receiver's allocation after its parent overwrites the root is its old
allocation plus the incoming parent down-port plus all incoming child
up-ports. The latter total is the growth of the receiver's child-root mass.
This is the exact size recurrence needed for dynamic sender sets. -/
theorem d2FlowTreeAllocation_after_root_overwrite
    {h scale : Nat} (before afterRecursive : D2FlowTree h)
    (newRoot : Nat) (newLow newHigh : Nat)
    (hbeforeCover : d2FlowTreeRootDeficit before ≤
      d2FlowTreeCapacityMass scale before)
    (hnewCover : newRoot ≤ d2FlowTreeCapacityMass scale afterRecursive)
    (hrootDrop : newRoot ≤ d2FlowTreeRootDeficit before)
    (hmassMono : d2FlowTreeCapacityMass scale before ≤
      d2FlowTreeCapacityMass scale afterRecursive) :
    d2FlowTreeAllocation scale
        (d2FlowTreeSetRoot afterRecursive newRoot newLow newHigh) =
      d2FlowTreeAllocation scale before +
        (d2FlowTreeRootDeficit before - newRoot) +
        (d2FlowTreeCapacityMass scale afterRecursive -
          d2FlowTreeCapacityMass scale before) := by
  have hbefore : d2FlowTreeAllocation scale before +
      d2FlowTreeRootDeficit before = d2FlowTreeCapacityMass scale before := by
    cases before with
    | leaf G low high =>
        have hcover : G ≤ scale := by
          simpa [d2FlowTreeRootDeficit, d2FlowTreeCapacityMass] using hbeforeCover
        simpa [d2FlowTreeAllocation, d2FlowTreeRootDeficit,
          d2FlowTreeCapacityMass] using Nat.sub_add_cancel hcover
    | node G low high children =>
        simp only [d2FlowTreeAllocation, d2FlowTreeCapacityMass]
        exact Nat.sub_add_cancel hbeforeCover
  have hafter : d2FlowTreeAllocation scale
      (d2FlowTreeSetRoot afterRecursive newRoot newLow newHigh) + newRoot =
        d2FlowTreeCapacityMass scale afterRecursive := by
    cases afterRecursive with
    | leaf G low high =>
        have hcover : newRoot ≤ scale := by
          simpa [d2FlowTreeCapacityMass] using hnewCover
        simpa [d2FlowTreeSetRoot, d2FlowTreeAllocation,
          d2FlowTreeCapacityMass, d2FlowTreeRootDeficit] using
            Nat.sub_add_cancel hcover
    | node G low high children =>
        simp only [d2FlowTreeSetRoot, d2FlowTreeAllocation,
          d2FlowTreeCapacityMass, d2FlowTreeRootDeficit]
        exact Nat.sub_add_cancel hnewCover
  have hafterVal : d2FlowTreeAllocation scale
      (d2FlowTreeSetRoot afterRecursive newRoot newLow newHigh) =
        d2FlowTreeCapacityMass scale afterRecursive - newRoot := by omega
  rw [hafterVal]
  omega

/-- Recursive updates never decrease a node's capacity mass: each child root
deficit is monotone under `d2FlowStage`. -/
theorem d2FlowTreeCapacityMass_inactive_stage_mono
    (active : Nat → Bool) (role : Nat → D2Role)
    (quota : Nat → D2Role → Nat) {h scale : Nat} (i : Nat)
    (tree : D2FlowTree h) (ha : active i = false) :
    d2FlowTreeCapacityMass scale tree ≤
      d2FlowTreeCapacityMass scale
        (d2FlowStage active role quota h i tree) := by
  cases tree with
  | leaf G low high => rfl
  | node G low high children =>
      simp only [d2FlowTreeCapacityMass, d2FlowStage, ha]
      apply Finset.sum_le_sum
      intro j hj
      exact d2FlowStage_root_deficit_mono active role quota (i + 1)
        (children j)

/-- For an inactive node, the increase in capacity mass is the sum of the
root-deficit increases of its children, i.e. the total size of their outgoing
up-ports. -/
theorem d2FlowTreeCapacityMass_inactive_stage_increment
    (active : Nat → Bool) (role : Nat → D2Role)
    (quota : Nat → D2Role → Nat) {h scale : Nat} (i : Nat)
    (children : Fin 8 → D2FlowTree h) (G low high : Nat)
    (ha : active i = false) :
    d2FlowTotal (fun j =>
        d2FlowStagePort active role quota h (i + 1) (children j)) =
      d2FlowTreeCapacityMass scale
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) -
        d2FlowTreeCapacityMass scale (.node G low high children) := by
  have hpoint (j : Fin 8) :
      d2FlowTreeRootDeficit (children j) +
        d2FlowStagePort active role quota h (i + 1) (children j) =
      d2FlowTreeRootDeficit
        (d2FlowStage active role quota h (i + 1) (children j)) := by
    exact (d2FlowStage_root_eq_old_add_port active role quota
      (i + 1) (children j)).symm
  have hsum : d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) +
      d2FlowTotal (fun j =>
        d2FlowStagePort active role quota h (i + 1) (children j)) =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit
        (d2FlowStage active role quota h (i + 1) (children j))) := by
    unfold d2FlowTotal
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact hpoint j
  have hafter : d2FlowTreeCapacityMass scale
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit
        (d2FlowStage active role quota h (i + 1) (children j))) := by
    simp [d2FlowTreeCapacityMass, d2FlowStage, ha]
  have hbefore : d2FlowTreeCapacityMass scale
      (.node G low high children) =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    rfl
  rw [hafter, hbefore]
  omega

/-- Specialization to a receiver whose own level is inactive. Its recursive
children send up-ports while it retains its sender set, and a parent overwrite
reduces its root by exactly the incoming down-port. The allocation change is
therefore exactly the sum of those incoming port widths. -/
theorem d2FlowTreeAllocation_after_inactive_recursive_stage
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h scale i : Nat}
    (tree : D2FlowTree h) (ha : active i = false)
    (hinv : d2FlowTreeInv scale tree) (newRoot newLow newHigh : Nat)
    (hnewCover : newRoot ≤ d2FlowTreeCapacityMass scale
      (d2FlowStage active role quota h i tree))
    (hrootDrop : newRoot ≤ d2FlowTreeRootDeficit tree) :
    d2FlowTreeAllocation scale
        (d2FlowTreeSetRoot
          (d2FlowStage active role quota h i tree) newRoot newLow newHigh) =
      d2FlowTreeAllocation scale tree +
        (d2FlowTreeRootDeficit tree - newRoot) +
        (d2FlowTreeCapacityMass scale
          (d2FlowStage active role quota h i tree) -
          d2FlowTreeCapacityMass scale tree) := by
  have hbeforeCover : d2FlowTreeRootDeficit tree ≤
      d2FlowTreeCapacityMass scale tree := by
    cases tree with
    | leaf G low high =>
        simpa [d2FlowTreeRootDeficit, d2FlowTreeCapacityMass,
          d2FlowTreeInv] using hinv.1
    | node G low high children =>
        simpa [d2FlowTreeRootDeficit, d2FlowTreeCapacityMass,
          d2FlowTreeInv] using hinv.2.1
  exact d2FlowTreeAllocation_after_root_overwrite tree
    (d2FlowStage active role quota h i tree) newRoot newLow newHigh
    hbeforeCover hnewCover hrootDrop
    (d2FlowTreeCapacityMass_inactive_stage_mono
      active role quota i tree ha)

/-- An active ordinary parent only lowers a child's root deficit. This is
the exact down-port width charged in the inactive-receiver recurrence. -/
theorem d2FlowStage_regular_child_root_drop
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h) (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hcuts : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
        high - quota i (role i) / 2) (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) ≤
      d2FlowTreeRootDeficit (children j) := by
  rw [d2FlowStage_regular_child_deficit children ha hr j]
  exact d2FlowCutChild_le_native (Nat.le_refl _) hcuts

/-- The ordinary parent cut also leaves every overwritten child with a valid
flow invariant. Its child-cover clause supplies the post-overwrite cover
hypothesis needed by the dynamic receiver-size recurrence. -/
theorem d2FlowStage_regular_child_postoverwrite_cover
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high scale : Nat}
    (children : Fin 8 → D2FlowTree h) (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (j : Fin 8)
    (hinv : d2FlowTreeInv scale
      (d2FlowStage active role quota h (i + 1) (children j)))
    (hcuts : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
        high - quota i (role i) / 2)
    (hcap : (d2FlowCutChild
        (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
        (d2FlowTreeRootDeficit (children j))
        (low + quota i (role i) / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
          high - quota i (role i) / 2)).1 ≤ scale * 8 ^ h) :
    (d2FlowCutChild
        (d2FlowPosition (fun k => d2FlowTreeRootDeficit (children k)) j)
        (d2FlowTreeRootDeficit (children j))
        (low + quota i (role i) / 2)
        (d2FlowTotal (fun k => d2FlowTreeRootDeficit (children k)) -
          high - quota i (role i) / 2)).1 ≤
      d2FlowTreeCapacityMass scale
        (d2FlowStage active role quota h (i + 1) (children j)) := by
  have hchildInv := d2FlowStage_regular_child_inv
    (G := G) (low := low) (high := high) children ha hr j hinv hcuts hcap
  have hcover := d2FlowTreeInv_root_le_capacityMass
    (d2FlowTreeChild
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) j) hchildInv
  rw [d2FlowStage_regular_child_setroot children ha hr j] at hcover
  rw [d2FlowTreeCapacityMass_setRoot] at hcover
  simpa only [d2FlowTreeSetRoot_deficit] using hcover

/-- A top-descending parent overwrites each child root with zero. This gives
both a nonnegative down-port and the post-overwrite cover automatically. -/
theorem d2FlowStage_topDesc_child_root_drop_and_cover
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high scale : Nat}
    (children : Fin 8 → D2FlowTree h) (ha : active i = true)
    (hr : role i = .topDesc) (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) ≤
      d2FlowTreeRootDeficit (children j) ∧
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) ≤
      d2FlowTreeCapacityMass scale
        (d2FlowStage active role quota h (i + 1) (children j)) := by
  rw [d2FlowStage_topDesc_child_deficit children ha hr j]
  exact ⟨Nat.zero_le _, Nat.zero_le _⟩

/-- At a bottom-rise parent the children are not overwritten. If the next
level is inactive, their root is exactly preserved, so the down-port is zero. -/
theorem d2FlowStage_botRise_child_root_preserved
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high : Nat}
    (children : Fin 8 → D2FlowTree h) (ha : active i = true)
    (hr : role i = .botRise) (hnext : active (i + 1) = false)
    (j : Fin 8) :
    d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j) =
      d2FlowTreeRootDeficit (children j) := by
  rw [d2FlowStage_botRise_child_deficit children ha hr j]
  exact d2FlowStage_root_deficit_of_inactive
    (active := active) (role := role) (quota := quota)
    (i := i + 1) (children j) hnext

/-- An active ordinary sender routes its entire allocation away: the total
post-cut child mass equals its updated root deficit. -/
theorem d2FlowStage_regular_sender_allocation_zero
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high scale : Nat}
    (children : Fin 8 → D2FlowTree h) (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hbal : G = low + high)
    (heven : quota i (role i) % 2 = 0)
    (hleft : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hdisjoint : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2) :
    d2FlowTreeAllocation scale
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) = 0 := by
  have hmass := d2FlowStage_regular_child_mass children ha hr hbal
    heven hleft hright hdisjoint
  have hroot : d2FlowTreeRootDeficit
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) = G + quota i (role i) := by
    rw [d2FlowStage_active_node_deficit children ha]
    rcases hr with htop | hmid | hbot
    · simp [htop]
    · simp [hmid]
    · simp [hbot]
  cases hstage : d2FlowStage active role quota (h + 1) i
      (.node G low high children) with
  | node G' low' high' children' =>
      have hmass' : d2FlowTotal (fun j =>
          d2FlowTreeRootDeficit (children' j)) = G + quota i (role i) := by
        simpa [hstage] using hmass
      have hroot' : G' = G + quota i (role i) := by
        simpa [hstage] using hroot
      simp only [d2FlowTreeAllocation]
      rw [hmass', hroot']
      omega

/-- The startup top-descending sender has zero post-stage allocation when
its required zero-deficit input contract holds. -/
theorem d2FlowStage_topDesc_sender_allocation_zero
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high scale : Nat}
    (children : Fin 8 → D2FlowTree h) (ha : active i = true)
    (hr : role i = .topDesc) (hG : G = 0) :
    d2FlowTreeAllocation scale
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) = 0 := by
  have hmass := d2FlowStage_topDesc_child_mass
    (quota := quota) (low := low) (high := high) children ha hr hG
  have hroot : d2FlowTreeRootDeficit
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) = 0 := by
    rw [d2FlowStage_active_node_deficit children ha]
    simp [hr, hG]
  cases hstage : d2FlowStage active role quota (h + 1) i
      (.node G low high children) with
  | node G' low' high' children' =>
      have hmass' : d2FlowTotal (fun j =>
          d2FlowTreeRootDeficit (children' j)) = G' := by
        simpa [hstage] using hmass
      have hroot' : G' = 0 := by simpa [hstage] using hroot
      simp only [d2FlowTreeAllocation]
      rw [hmass', hroot']

/-- A bottom-rising sender has zero post-stage allocation when its children
are inactive at the following stage, so their root deficits do not change. -/
theorem d2FlowStage_botRise_sender_allocation_zero
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high scale : Nat}
    (children : Fin 8 → D2FlowTree h) (ha : active i = true)
    (hr : role i = .botRise) (hnext : active (i + 1) = false)
    (hinv : d2FlowTreeInv scale (.node G low high children)) :
    d2FlowTreeAllocation scale
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) = 0 := by
  have hsum : d2FlowTotal (fun j => d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage active role quota (h + 1) i
          (.node G low high children)) j)) =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    unfold d2FlowTotal
    apply Finset.sum_congr rfl
    intro j hj
    exact d2FlowStage_botRise_child_root_deficit children ha hr hnext j
  have hcover := d2FlowTreeInv_node_children_cover children hinv
  have hroot : d2FlowTreeRootDeficit
      (d2FlowStage active role quota (h + 1) i
        (.node G low high children)) =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    rw [d2FlowStage_active_node_deficit children ha, hr]
    exact Nat.add_sub_of_le hcover
  cases hstage : d2FlowStage active role quota (h + 1) i
      (.node G low high children) with
  | node G' low' high' children' =>
      have hsum' : d2FlowTotal (fun j =>
          d2FlowTreeRootDeficit (children' j)) =
          d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
        simpa [hstage] using hsum
      have hroot' : G' = d2FlowTotal
          (fun j => d2FlowTreeRootDeficit (children j)) := by
        simpa [hstage] using hroot
      simp only [d2FlowTreeAllocation]
      rw [hsum', hroot']
      omega

/-- The size of one receiver's union is the sum of the sizes of the routed
pieces, provided pieces emitted by one sender are disjoint. -/
theorem routedTargetPiece_card_eq_sum
    {α I D J : Type*} [DecidableEq α] [Fintype D] [DecidableEq D]
    [DecidableEq J]
    (localPiece : I → D → Finset α) (target : I → D → J)
    (hdisjoint : ∀ i d d', d ≠ d' → Disjoint (localPiece i d) (localPiece i d'))
    (i : I) (j : J) :
    (routedTargetPiece localPiece target i j).card =
      ∑ d ∈ Finset.univ.filter (fun d : D => target i d = j),
        (localPiece i d).card := by
  classical
  simpa [trueMass] using
    routedTargetPiece_trueMass_eq_sum localPiece target hdisjoint
      (fun _ : α => true) i j

/-- If all current sender sets are disjoint, the next set collected for a
receiver has size equal to the total size of its incoming routed pieces. -/
theorem routedReceiver_card_eq_sum
    {α I D J : Type*} [Fintype I] [DecidableEq I]
    [Fintype D] [DecidableEq D] [DecidableEq J] [DecidableEq α]
    (source : I → Finset α) (localPiece : I → D → Finset α)
    (target : I → D → J)
    (hsourceDisjoint : ∀ i i', i ≠ i' → Disjoint (source i) (source i'))
    (hlocalSubset : ∀ i d, localPiece i d ⊆ source i)
    (j : J) :
    (Finset.univ.biUnion fun i => routedTargetPiece localPiece target i j).card =
      ∑ i ∈ Finset.univ,
        (routedTargetPiece localPiece target i j).card := by
  classical
  rw [Finset.card_biUnion]
  · simp only [Set.PairwiseDisjoint, Set.Pairwise]
    intro i _ i' _ hne
    change Disjoint (routedTargetPiece localPiece target i j)
      (routedTargetPiece localPiece target i' j)
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hleft : x ∈ source i :=
      routedTargetPiece_subset source localPiece target hlocalSubset i j hx
    have hright : x ∈ source i' :=
      routedTargetPiece_subset source localPiece target hlocalSubset i' j hx'
    exact (Finset.disjoint_left.mp (hsourceDisjoint i i' hne) hleft hright)

/-- The receiver size is therefore the sum of the widths of all incoming
ports, with no geometric assumption on how the sender sets are interleaved
inside the physical wire order. -/
theorem routedReceiver_card_eq_sum_of_piece_cards
    {α I D J : Type*} [Fintype I] [DecidableEq I]
    [Fintype D] [DecidableEq D] [DecidableEq J] [DecidableEq α]
    (source : I → Finset α) (localPiece : I → D → Finset α)
    (target : I → D → J)
    (hsourceDisjoint : ∀ i i', i ≠ i' → Disjoint (source i) (source i'))
    (hlocalSubset : ∀ i d, localPiece i d ⊆ source i)
    (hlocalDisjoint : ∀ i d d', d ≠ d' →
      Disjoint (localPiece i d) (localPiece i d'))
    (j : J) :
    (Finset.univ.biUnion fun i => routedTargetPiece localPiece target i j).card =
      ∑ i ∈ Finset.univ,
        ∑ d ∈ Finset.univ.filter (fun d : D => target i d = j),
          (localPiece i d).card := by
  rw [routedReceiver_card_eq_sum source localPiece target
    hsourceDisjoint hlocalSubset j]
  apply Finset.sum_congr rfl
  intro i hi
  exact routedTargetPiece_card_eq_sum localPiece target hlocalDisjoint i j

/-- An ordinary sender's parent piece has the sum of its two fringe widths.
The gap condition makes the first and last rank intervals disjoint. -/
theorem destinationPiece_parent_card {n ports : Nat}
    (s : Finset (Fin n)) (boundary : Nat → Nat) (left rightStart : Nat)
    (hleft : left ≤ s.card) (hgap : left ≤ rightStart) :
    (destinationPiece (ports := ports) s boundary left rightStart none).card =
      left + (s.card - rightStart) := by
  unfold destinationPiece
  rw [Finset.card_union_of_disjoint (disjoint_blockOf hgap)]
  rw [blockOf_card hleft, blockOf_card (by omega)]
  simp

/-- Each ordinary child piece has exactly the width of its rank interval. -/
theorem destinationPiece_child_card {n ports : Nat}
    (s : Finset (Fin n)) (boundary : Nat → Nat) (left rightStart : Nat)
    (j : Fin ports)
    (hhi : left + boundary (j.val + 1) ≤ s.card)
    (hmono : boundary j.val ≤ boundary (j.val + 1)) :
    (destinationPiece (ports := ports) s boundary left rightStart (some j)).card =
      boundary (j.val + 1) - boundary j.val := by
  unfold destinationPiece
  rw [blockOf_card hhi]
  omega

/-- For the concrete D2 cumulative boundaries, each ordinary child piece has
the exact width used by the flow update. -/
theorem destinationPiece_d2_child_card {n : Nat}
    (s : Finset (Fin n)) (sizes : Fin 8 → Nat) (left rightStart : Nat)
    (j : Fin 8)
    (hhi : left + d2FlowRankBoundary sizes (j.val + 1) ≤ s.card) :
    (destinationPiece (ports := 8) s (d2FlowRankBoundary sizes)
      left rightStart (some j)).card = sizes j := by
  have hmono : d2FlowRankBoundary sizes j.val ≤
      d2FlowRankBoundary sizes (j.val + 1) := by
    rw [d2FlowRankBoundary_succ sizes j.val j.isLt]
    exact Nat.le_add_right _ _
  rw [destinationPiece_child_card s (d2FlowRankBoundary sizes)
    left rightStart j hhi hmono]
  rw [d2FlowRankBoundary_succ sizes j.val j.isLt]
  simp

/-- For an even ordinary quota, the two parent fringe pieces have total size
exactly the quota sent up to the parent. -/
theorem destinationPiece_d2_parent_card {n : Nat}
    (s : Finset (Fin n)) (boundary : Nat → Nat) (quota : Nat)
    (hquota : quota ≤ s.card) (heven : quota % 2 = 0) :
    (destinationPiece (ports := 8) s boundary (quota / 2)
      (s.card - quota / 2) none).card = quota := by
  have hleft : quota / 2 ≤ s.card := by omega
  have hgap : quota / 2 ≤ s.card - quota / 2 := by omega
  rw [destinationPiece_parent_card s boundary (quota / 2)
    (s.card - quota / 2) hleft hgap]
  omega

end Chvatal.D2OrdinaryRankRouting
