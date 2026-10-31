import D2WirePartition
import D2FlowRankBridge

namespace Chvatal.D2OrdinaryRankRouting

open Chvatal
open Chvatal.D2Reserve

/-- Destinations of the pieces emitted by one ordinary D2 sender. `none` is
the parent; `some j` is child `j`. -/
def destinationPiece {n ports : Nat} (s : Finset (Fin n))
    (boundary : Nat → Nat) (left rightStart : Nat)
    (target : Option (Fin ports)) :
    Finset (Fin n) :=
  match target with
  | none =>
      Chvatal.blockOf s 0 left ∪
        Chvatal.blockOf s rightStart s.card
  | some j =>
      Chvatal.blockOf s (left + boundary j.val)
        (left + boundary (j.val + 1))

/-- The parent-plus-child destination pieces cover exactly the sender set. -/
theorem destinationPieces_cover {n ports : Nat} (s : Finset (Fin n))
    (boundary : Nat → Nat) (left rightStart : Nat)
    (hcover :
      (Chvatal.blockOf s 0 left ∪
        ((Finset.univ.biUnion fun i : Fin ports =>
          Chvatal.blockOf s (left + boundary i.val)
            (left + boundary (i.val + 1))) ∪
          Chvatal.blockOf s rightStart s.card)) = s) :
    Finset.univ.biUnion
      (destinationPiece (ports := ports) s boundary left rightStart) = s := by
  ext w
  constructor
  · simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    rintro ⟨target, htarget⟩
    cases target with
    | none =>
        rcases Finset.mem_union.mp htarget with hleft | hright
        · exact Chvatal.blockOf_subset hleft
        · exact Chvatal.blockOf_subset hright
    | some j => exact Chvatal.blockOf_subset htarget
  · intro hw
    have hwcover : w ∈ Chvatal.blockOf s 0 left ∪
        ((Finset.univ.biUnion fun i : Fin ports =>
          Chvatal.blockOf s (left + boundary i.val)
            (left + boundary (i.val + 1))) ∪
          Chvatal.blockOf s rightStart s.card) := by
      rw [hcover]
      exact hw
    rcases Finset.mem_union.mp hwcover with hleft | hrest
    · refine Finset.mem_biUnion.mpr ⟨none, Finset.mem_univ _, ?_⟩
      simp [destinationPiece, hleft]
    · rcases Finset.mem_union.mp hrest with hmid | hright
      · rcases Finset.mem_biUnion.mp hmid with ⟨i, hi, hpiece⟩
        refine Finset.mem_biUnion.mpr ⟨some i, Finset.mem_univ _, ?_⟩
        simpa [destinationPiece] using hpiece
      · refine Finset.mem_biUnion.mpr ⟨none, Finset.mem_univ _, ?_⟩
        simp [destinationPiece, hright]

/-- Each destination piece is a subset of the sender's current wire set. -/
theorem destinationPiece_subset {n ports : Nat} (s : Finset (Fin n))
    (boundary : Nat → Nat) (left rightStart : Nat)
    (target : Option (Fin ports)) :
    destinationPiece s boundary left rightStart target ⊆ s := by
  cases target with
  | none => exact Finset.union_subset Chvatal.blockOf_subset Chvatal.blockOf_subset
  | some j => exact Chvatal.blockOf_subset

/-- Pieces assigned to distinct parent/child destinations are disjoint. -/
theorem destinationPieces_disjoint {n ports : Nat} (s : Finset (Fin n))
    (boundary : Nat → Nat) (left rightStart : Nat)
    (hdisjoint :
      (Disjoint
        (Chvatal.blockOf s 0 left ∪
          Chvatal.blockOf s rightStart s.card)
        (Finset.univ.biUnion fun i : Fin ports =>
          Chvatal.blockOf s (left + boundary i.val)
            (left + boundary (i.val + 1)))) ∧
      (∀ i j : Fin ports, i ≠ j →
        Disjoint
          (Chvatal.blockOf s (left + boundary i.val)
            (left + boundary (i.val + 1)))
          (Chvatal.blockOf s (left + boundary j.val)
            (left + boundary (j.val + 1))))) :
    ∀ a b : Option (Fin ports), a ≠ b →
      Disjoint (destinationPiece (ports := ports) s boundary left rightStart a)
        (destinationPiece (ports := ports) s boundary left rightStart b) := by
  intro a b hab
  rw [Finset.disjoint_left]
  cases a with
  | none =>
      cases b with
      | none => exact (hab rfl).elim
      | some j =>
        intro x hparent hchild
        have hparent' : x ∈
            Chvatal.blockOf s 0 left ∪
              Chvatal.blockOf s rightStart s.card := by
          simpa [destinationPiece] using hparent
        have hchild' : x ∈ Finset.univ.biUnion (fun i : Fin ports =>
            Chvatal.blockOf s (left + boundary i.val)
              (left + boundary (i.val + 1))) :=
          Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by
            simpa [destinationPiece] using hchild⟩
        exact Finset.disjoint_left.mp hdisjoint.1 hparent' hchild'
  | some i =>
      cases b with
      | none =>
        intro x hchild hparent
        have hparent' : x ∈
            Chvatal.blockOf s 0 left ∪
              Chvatal.blockOf s rightStart s.card := by
          simpa [destinationPiece] using hparent
        have hchild' : x ∈ Finset.univ.biUnion (fun j : Fin ports =>
            Chvatal.blockOf s (left + boundary j.val)
              (left + boundary (j.val + 1))) :=
          Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by
            simpa [destinationPiece] using hchild⟩
        exact Finset.disjoint_left.mp hdisjoint.1.symm hchild' hparent'
      | some j =>
        intro x hleft hright
        have hij : i ≠ j := by
          intro heq
          apply hab
          simp [heq]
        exact Finset.disjoint_left.mp (hdisjoint.2 i j hij) hleft hright

/-- This is the exact local interface consumed by the global routing
conservation theorem. -/
theorem ordinary_sender_piece_partition {n ports : Nat}
    (s : Finset (Fin n)) (boundary : Nat → Nat) (left rightStart : Nat)
    (hcover :
      (Chvatal.blockOf s 0 left ∪
        ((Finset.univ.biUnion fun i : Fin ports =>
          Chvatal.blockOf s (left + boundary i.val)
            (left + boundary (i.val + 1))) ∪
          Chvatal.blockOf s rightStart s.card)) = s)
    (hdisjoint :
      (Disjoint
        (Chvatal.blockOf s 0 left ∪
          Chvatal.blockOf s rightStart s.card)
        (Finset.univ.biUnion fun i : Fin ports =>
          Chvatal.blockOf s (left + boundary i.val)
            (left + boundary (i.val + 1)))) ∧
      (∀ i j : Fin ports, i ≠ j →
        Disjoint
          (Chvatal.blockOf s (left + boundary i.val)
            (left + boundary (i.val + 1)))
          (Chvatal.blockOf s (left + boundary j.val)
            (left + boundary (j.val + 1))))) :
    (∀ target, destinationPiece (ports := ports) s boundary left rightStart target ⊆ s) ∧
      Finset.univ.biUnion
        (destinationPiece (ports := ports) s boundary left rightStart) = s ∧
      (∀ a b, a ≠ b →
        Disjoint (destinationPiece (ports := ports) s boundary left rightStart a)
          (destinationPiece (ports := ports) s boundary left rightStart b)) := by
  exact ⟨destinationPiece_subset s boundary left rightStart,
    destinationPieces_cover s boundary left rightStart hcover,
    destinationPieces_disjoint s boundary left rightStart hdisjoint⟩

/-- The ordinary D2 flow update supplies a partition of an actual sender's
sorted wire set into its parent and child destinations. This is local to one
ordinary sender; it does not establish that all senders together implement
the global scheduled stage. -/
theorem regular_stage_sender_piece_partition
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high n : Nat}
    (children : Fin 8 → D2FlowTree h) (s : Finset (Fin n))
    (ha : active i = true)
    (hr : role i = .topRise ∨ role i = .mid ∨ role i = .botDesc)
    (hbal : G = low + high)
    (heven : quota i (role i) % 2 = 0)
    (hleft : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hright : high + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)))
    (hgap : low + quota i (role i) / 2 ≤
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) -
        high - quota i (role i) / 2)
    (hsender : s.card =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    let widths : Fin 8 → Nat := fun j =>
      d2FlowTreeRootDeficit (children j) -
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)
    let boundary : Nat → Nat := d2FlowRankBoundary widths
    (∀ target, destinationPiece (ports := 8) s boundary
        (quota i (role i) / 2) (s.card - quota i (role i) / 2) target ⊆ s) ∧
      Finset.univ.biUnion (destinationPiece (ports := 8) s boundary
        (quota i (role i) / 2) (s.card - quota i (role i) / 2)) = s ∧
      (∀ a b, a ≠ b →
        Disjoint
          (destinationPiece (ports := 8) s boundary
            (quota i (role i) / 2) (s.card - quota i (role i) / 2) a)
          (destinationPiece (ports := 8) s boundary
            (quota i (role i) / 2) (s.card - quota i (role i) / 2) b)) := by
  let widths : Fin 8 → Nat := fun j =>
    d2FlowTreeRootDeficit (children j) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)
  let boundary : Nat → Nat := d2FlowRankBoundary widths
  have hcover := d2FlowStage_regular_sender_rank_ports_cover children s
    ha hr hbal heven hleft hright hgap hsender
  have hdisjoint := d2FlowStage_regular_sender_rank_ports_disjoint children s
    ha hr hbal heven hleft hright hgap hsender
  have hparts := ordinary_sender_piece_partition s boundary
    (quota i (role i) / 2) (s.card - quota i (role i) / 2)
    (by simpa only [boundary, widths] using hcover)
    (by simpa only [boundary, widths] using hdisjoint)
  simpa only [boundary, widths] using hparts

/-- At a top-descending sender the flow sends the entire sender set to its
eight children; the parent destination is empty. -/
theorem top_desc_sender_piece_partition
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high n : Nat}
    (children : Fin 8 → D2FlowTree h) (s : Finset (Fin n))
    (ha : active i = true) (hr : role i = .topDesc) (hG : G = 0)
    (hsender : s.card =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    let widths : Fin 8 → Nat := fun j =>
      d2FlowTreeRootDeficit (children j) -
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)
    let boundary : Nat → Nat := d2FlowRankBoundary widths
    (∀ target, destinationPiece (ports := 8) s boundary 0 s.card target ⊆ s) ∧
      Finset.univ.biUnion
        (destinationPiece (ports := 8) s boundary 0 s.card) = s ∧
      (∀ a b, a ≠ b →
        Disjoint (destinationPiece (ports := 8) s boundary 0 s.card a)
          (destinationPiece (ports := 8) s boundary 0 s.card b)) := by
  let widths : Fin 8 → Nat := fun j =>
    d2FlowTreeRootDeficit (children j) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)
  let boundary : Nat → Nat := d2FlowRankBoundary widths
  have hreset (tree : D2FlowTree h) :
      d2FlowTreeRootDeficit (d2FlowTreeSetRoot tree 0 0 0) = 0 := by
    cases tree <;> rfl
  have hpost (j : Fin 8) :
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j) = 0 := by
    simp only [d2FlowStage, ha, if_pos, hr, d2FlowTreeChild]
    exact hreset _
  have hsum : d2FlowTotal widths =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) := by
    unfold d2FlowTotal
    apply Finset.sum_congr rfl
    intro j hj
    simp [widths, hpost]
  have hconserve : 0 + d2FlowTotal widths =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    rw [hsum, hG]
    omega
  have heven : 0 % 2 = 0 := by decide
  have hcover := d2FlowSenderRankPorts_cover s widths 0
    (d2FlowTotal fun j => d2FlowTreeRootDeficit (children j)) G
    hsender heven hconserve
  have hdisjoint := d2FlowSenderRankPorts_disjoint s widths 0
    (d2FlowTotal fun j => d2FlowTreeRootDeficit (children j)) G
    hsender heven hconserve
  have hparts := ordinary_sender_piece_partition s boundary 0 s.card
    (by simpa only [boundary, widths] using hcover)
    (by simpa only [boundary, widths] using hdisjoint)
  simpa only [boundary, widths] using hparts

/-- At a bottom-rising sender whose children are inactive this stage, the
whole sender is routed to its parent and every child piece is empty. -/
theorem bot_rise_sender_piece_partition
    {active : Nat → Bool} {role : Nat → D2Role}
    {quota : Nat → D2Role → Nat} {h i G low high n : Nat}
    (children : Fin 8 → D2FlowTree h) (s : Finset (Fin n))
    (ha : active i = true) (hr : role i = .botRise)
    (hnext : active (i + 1) = false)
    (heven : (d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) - G) % 2 = 0)
    (hsender : s.card =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G) :
    let widths : Fin 8 → Nat := fun j =>
      d2FlowTreeRootDeficit (children j) -
        d2FlowTreeRootDeficit
          (d2FlowTreeChild
            (d2FlowStage active role quota (h + 1) i
              (.node G low high children)) j)
    let pi := d2FlowTotal
      (fun j => d2FlowTreeRootDeficit (children j)) - G
    let boundary : Nat → Nat := d2FlowRankBoundary widths
    (∀ target, destinationPiece (ports := 8) s boundary (pi / 2)
        (s.card - pi / 2) target ⊆ s) ∧
      Finset.univ.biUnion (destinationPiece (ports := 8) s boundary
        (pi / 2) (s.card - pi / 2)) = s ∧
      (∀ a b, a ≠ b →
        Disjoint
          (destinationPiece (ports := 8) s boundary (pi / 2)
            (s.card - pi / 2) a)
          (destinationPiece (ports := 8) s boundary (pi / 2)
            (s.card - pi / 2) b)) := by
  let widths : Fin 8 → Nat := fun j =>
    d2FlowTreeRootDeficit (children j) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j)
  let pi := d2FlowTotal
    (fun j => d2FlowTreeRootDeficit (children j)) - G
  let boundary : Nat → Nat := d2FlowRankBoundary widths
  have hpost (j : Fin 8) :
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota (h + 1) i
            (.node G low high children)) j) =
      d2FlowTreeRootDeficit (children j) :=
    d2FlowStage_botRise_child_root_deficit children ha hr hnext j
  have hwidth (j : Fin 8) : widths j = 0 := by
    simp [widths, hpost]
  have hsum : d2FlowTotal widths = 0 := by
    unfold d2FlowTotal
    apply Finset.sum_eq_zero
    intro j hj
    exact hwidth j
  have hconserve : pi + d2FlowTotal widths =
      d2FlowTotal (fun j => d2FlowTreeRootDeficit (children j)) - G := by
    simp [pi, hsum]
  have hcover := d2FlowSenderRankPorts_cover s widths pi
    (d2FlowTotal fun j => d2FlowTreeRootDeficit (children j)) G
    hsender heven hconserve
  have hdisjoint := d2FlowSenderRankPorts_disjoint s widths pi
    (d2FlowTotal fun j => d2FlowTreeRootDeficit (children j)) G
    hsender heven hconserve
  have hparts := ordinary_sender_piece_partition s boundary (pi / 2)
    (s.card - pi / 2)
    (by simpa only [boundary, widths, pi] using hcover)
    (by simpa only [boundary, widths, pi] using hdisjoint)
  simpa only [boundary, widths, pi] using hparts

/-- Collect all pieces of one source sender that are assigned to one
next-stage destination. -/
def routedTargetPiece
    {α I D J : Type*} [DecidableEq α] [Fintype D] [DecidableEq D]
    [DecidableEq J]
    (localPiece : I → D → Finset α) (target : I → D → J)
    (i : I) (j : J) : Finset α :=
  (Finset.univ.filter fun d : D => target i d = j).biUnion (localPiece i)

theorem routedTargetPiece_subset
    {α I D J : Type*} [DecidableEq α] [Fintype D] [DecidableEq D]
    [DecidableEq J]
    (source : I → Finset α) (localPiece : I → D → Finset α)
    (target : I → D → J)
    (hsubset : ∀ i d, localPiece i d ⊆ source i) :
    ∀ i j, routedTargetPiece localPiece target i j ⊆ source i := by
  intro i j x hx
  change x ∈ (Finset.univ.filter fun d : D => target i d = j).biUnion
    (localPiece i) at hx
  rcases Finset.mem_biUnion.mp hx with ⟨d, hd, hxd⟩
  exact hsubset i d hxd

theorem routedTargetPieces_cover
    {α I D J : Type*} [DecidableEq α] [Fintype D] [DecidableEq D]
    [Fintype J] [DecidableEq J]
    (source : I → Finset α) (localPiece : I → D → Finset α)
    (target : I → D → J)
    (hcover : ∀ i, Finset.univ.biUnion (localPiece i) = source i) :
    ∀ i, Finset.univ.biUnion (routedTargetPiece localPiece target i) = source i := by
  intro i
  ext x
  change (x ∈ Finset.univ.biUnion (routedTargetPiece localPiece target i)) ↔
    x ∈ source i
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨j, hj, hxj⟩
    change x ∈ (Finset.univ.filter fun d : D => target i d = j).biUnion
      (localPiece i) at hxj
    rcases Finset.mem_biUnion.mp hxj with ⟨d, hd, hxd⟩
    have hxlocal : x ∈ Finset.univ.biUnion (localPiece i) :=
      Finset.mem_biUnion.mpr ⟨d, Finset.mem_univ _, hxd⟩
    rw [← hcover i]
    exact hxlocal
  · intro hx
    have hxlocal : x ∈ Finset.univ.biUnion (localPiece i) := by
      rw [hcover i]
      exact hx
    rcases Finset.mem_biUnion.mp hxlocal with ⟨d, hd, hxd⟩
    refine Finset.mem_biUnion.mpr ⟨target i d, Finset.mem_univ _, ?_⟩
    change x ∈ (Finset.univ.filter fun e : D => target i e = target i d).biUnion
      (localPiece i)
    exact Finset.mem_biUnion.mpr
      ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, hxd⟩

theorem routedTargetPieces_disjoint
    {α I D J : Type*} [DecidableEq α] [Fintype D] [DecidableEq D]
    [DecidableEq J]
    (localPiece : I → D → Finset α) (target : I → D → J)
    (hdisjoint : ∀ i d d', d ≠ d' → Disjoint (localPiece i d) (localPiece i d')) :
    ∀ i j j', j ≠ j' →
      Disjoint (routedTargetPiece localPiece target i j)
        (routedTargetPiece localPiece target i j') := by
  intro i j j' hj
  rw [Finset.disjoint_left]
  intro x hx hx'
  change x ∈ (Finset.univ.filter fun d : D => target i d = j).biUnion
    (localPiece i) at hx
  change x ∈ (Finset.univ.filter fun d : D => target i d = j').biUnion
    (localPiece i) at hx'
  rcases Finset.mem_biUnion.mp hx with ⟨d, hd, hxd⟩
  rcases Finset.mem_biUnion.mp hx' with ⟨d', hd', hxd'⟩
  have hdj : target i d = j := (Finset.mem_filter.mp hd).2
  have hdj' : target i d' = j' := (Finset.mem_filter.mp hd').2
  by_cases hdd : d = d'
  · subst d'
    exact hj (hdj.symm.trans hdj')
  · exact Finset.disjoint_left.mp (hdisjoint i d d' hdd) hxd hxd'

/-- Global conservation from local destination partitions. This is the
composition step for the D2 stage: after the schedule supplies `target`,
collect each sender's parent/child pieces by their next-stage bag index. -/
theorem routed_local_destinations_preserve_partition
    {α I D J : Type*} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I]
    [Fintype D] [DecidableEq D] [Fintype J] [DecidableEq J]
    (source : I → Finset α) (localPiece : I → D → Finset α)
    (target : I → D → J)
    (hsourceCover : Finset.univ.biUnion source = Finset.univ)
    (hsourceDisjoint : ∀ i i', i ≠ i' → Disjoint (source i) (source i'))
    (hlocalSubset : ∀ i d, localPiece i d ⊆ source i)
    (hlocalCover : ∀ i, Finset.univ.biUnion (localPiece i) = source i)
    (hlocalDisjoint : ∀ i d d', d ≠ d' →
      Disjoint (localPiece i d) (localPiece i d')) :
    (∀ j j', j ≠ j' →
      Disjoint
        (Finset.univ.biUnion fun i => routedTargetPiece localPiece target i j)
        (Finset.univ.biUnion fun i => routedTargetPiece localPiece target i j')) ∧
      Finset.univ.biUnion (fun j =>
        Finset.univ.biUnion fun i => routedTargetPiece localPiece target i j) =
          Finset.univ := by
  apply Chvatal.D2WirePartition.routed_bags_partition source
    (routedTargetPiece localPiece target)
    hsourceCover hsourceDisjoint
    (routedTargetPiece_subset source localPiece target hlocalSubset)
    (routedTargetPieces_cover source localPiece target hlocalCover)
    (routedTargetPieces_disjoint localPiece target hlocalDisjoint)

end Chvatal.D2OrdinaryRankRouting
