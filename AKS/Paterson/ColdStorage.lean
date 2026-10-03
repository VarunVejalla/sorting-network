module

public import AKS.Paterson.Stage
public import AKS.Paterson.Schedule
public import AKS.Bags.Sizes

/-! # Register ownership with explicit cold storage

Paterson (1990), Section 5: storage is a simulated ancestor of the root.
Ownership includes storage as `none`, so routing accounts for every wire
without identifying stored wires with the root bag. No comparisons or value
dependent choices occur in this allocation.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

structure StoredPlacement (k : ℕ) where
  owner : Fin (2 ^ k) → Option (Bag k)

namespace StoredPlacement

def regs {k : ℕ} (pl : StoredPlacement k) (b : Bag k) : Finset (Fin (2 ^ k)) :=
  univ.filter (fun i ↦ pl.owner i = some b)

def cold {k : ℕ} (pl : StoredPlacement k) : Finset (Fin (2 ^ k)) :=
  univ.filter (fun i ↦ pl.owner i = none)

@[simp] theorem mem_regs {k : ℕ} (pl : StoredPlacement k) (b : Bag k) (i) :
    i ∈ pl.regs b ↔ pl.owner i = some b := by simp [regs]

@[simp] theorem mem_cold {k : ℕ} (pl : StoredPlacement k) (i) :
    i ∈ pl.cold ↔ pl.owner i = none := by simp [cold]

theorem disjoint {k : ℕ} (pl : StoredPlacement k) (a b : Bag k) (h : a ≠ b) :
    Disjoint (pl.regs a) (pl.regs b) := by
  rw [disjoint_left]
  intro i hi hj
  exact h (Option.some.inj ((pl.mem_regs a i).mp hi |>.symm.trans
    ((pl.mem_regs b i).mp hj)))

theorem cold_disjoint {k : ℕ} (pl : StoredPlacement k) (b : Bag k) :
    Disjoint pl.cold (pl.regs b) := by
  rw [disjoint_left]
  intro i hi hj
  have := (pl.mem_cold i).mp hi
  have := (pl.mem_regs b i).mp hj
  simp_all

theorem complete {k : ℕ} (pl : StoredPlacement k) (i : Fin (2 ^ k)) :
    i ∈ pl.cold ∨ ∃ b, i ∈ pl.regs b := by
  cases h : pl.owner i with
  | none => exact Or.inl ((pl.mem_cold i).mpr h)
  | some b => exact Or.inr ⟨b, (pl.mem_regs b i).mpr h⟩

/-- `feed` is the prescribed set returning from storage to the root. -/
def route {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ)
    (feed : Finset (Fin (2 ^ k))) : StoredPlacement k where
  owner i := match pl.owner i with
    | none => if i ∈ feed then some (Bag.root k) else none
    | some b =>
      if i ∈ (split (pl.regs b) (f b)).toParent then
        if b.l = 0 then none else some b.parent
      else if h : b.l < k then
        if i ∈ (split (pl.regs b) (f b)).toLeft then some (b.left h)
        else some (b.right h)
      else none

theorem route_from_cold {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ)
    (feed : Finset (Fin (2 ^ k))) {i} (hi : i ∈ pl.cold) :
    (pl.route f feed).owner i = if i ∈ feed then some (Bag.root k) else none := by
  simp only [route, (pl.mem_cold i).mp hi]

theorem route_to_parent {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ)
    (feed : Finset (Fin (2 ^ k))) (b : Bag k) {i}
    (hi : i ∈ (split (pl.regs b) (f b)).toParent) :
    (pl.route f feed).owner i = if b.l = 0 then none else some b.parent := by
  have hb := (pl.mem_regs b i).mp (split_toParent_subset _ _ hi)
  simp only [route, hb, hi, ite_true]

theorem route_to_left {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ)
    (feed : Finset (Fin (2 ^ k))) (b : Bag k) (h : b.l < k) {i}
    (hi : i ∈ (split (pl.regs b) (f b)).toLeft) :
    (pl.route f feed).owner i = some (b.left h) := by
  have hb := (pl.mem_regs b i).mp (split_toLeft_subset _ _ hi)
  have hp : i ∉ (split (pl.regs b) (f b)).toParent :=
    fun hp ↦ disjoint_left.mp (split_toParent_toLeft_disjoint _ _) hp hi
  simp only [route, hb, hp, ite_false, dif_pos h, hi, ite_true]

theorem route_to_right {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ)
    (feed : Finset (Fin (2 ^ k))) (b : Bag k) (h : b.l < k) {i}
    (hi : i ∈ (split (pl.regs b) (f b)).toRight) :
    (pl.route f feed).owner i = some (b.right h) := by
  have hb := (pl.mem_regs b i).mp (split_toRight_subset _ _ hi)
  have hp : i ∉ (split (pl.regs b) (f b)).toParent :=
    fun hp ↦ disjoint_left.mp (split_toParent_toRight_disjoint _ _) hp hi
  have hl : i ∉ (split (pl.regs b) (f b)).toLeft :=
    fun hl ↦ disjoint_left.mp (split_toLeft_toRight_disjoint _ _) hl hi
  simp only [route, hb, hp, hl, ite_false, dif_pos h]

/-- Exact storage flow, including the root's outgoing fringe. The leaf
condition rules out a spurious transfer of leaf middles into storage. -/
theorem route_cold {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ)
    (feed : Finset (Fin (2 ^ k)))
    (hleaf : ∀ b : Bag k, ¬ b.l < k → (pl.regs b).card / 2 ≤ f b) :
    (pl.route f feed).cold = (pl.cold \ feed) ∪
      (split (pl.regs (Bag.root k)) (f (Bag.root k))).toParent := by
  ext i
  cases ho : pl.owner i with
  | none =>
    have hn : i ∉ (split (pl.regs (Bag.root k)) (f (Bag.root k))).toParent := by
      intro hi
      have := (pl.mem_regs _ i).mp (split_toParent_subset _ _ hi)
      simp_all
    simp [mem_cold, route, ho, hn]
  | some b =>
    have hi : i ∈ pl.regs b := (pl.mem_regs b i).mpr ho
    rcases split_covers (pl.regs b) (f b) hi with hp | hl | hr
    · rw [mem_cold, route_to_parent pl f feed b hp]
      by_cases hb : b.l = 0
      · have heq : b = Bag.root k := by
          apply Bag.ext
          · exact hb
          · have hx := b.hx
            simp only [hb, pow_zero] at hx
            change b.x = 0
            omega
        subst b
        simp only [hb, ite_true, mem_union, mem_sdiff, mem_cold, ho,
          Option.some_ne_none, false_and, false_or, hp]
      · have hn : i ∉ (split (pl.regs (Bag.root k)) (f (Bag.root k))).toParent := by
          intro hroot
          have heq := Option.some.inj (ho.symm.trans
            ((pl.mem_regs _ i).mp (split_toParent_subset _ _ hroot)))
          exact hb (heq ▸ rfl)
        simp [hb, hn, mem_cold, ho]
    · by_cases h : b.l < k
      · rw [mem_cold, route_to_left pl f feed b h hl]
        have hn : i ∉ (split (pl.regs (Bag.root k)) (f (Bag.root k))).toParent := by
          intro hp
          have heq := Option.some.inj (ho.symm.trans
            ((pl.mem_regs _ i).mp (split_toParent_subset _ _ hp)))
          subst b
          exact disjoint_left.mp (split_toParent_toLeft_disjoint _ _) hp hl
        simp [mem_cold, ho, hn]
      · exact False.elim (by simpa [(split_leaf _ _ (hleaf b h)).1] using hl)
    · by_cases h : b.l < k
      · rw [mem_cold, route_to_right pl f feed b h hr]
        have hn : i ∉ (split (pl.regs (Bag.root k)) (f (Bag.root k))).toParent := by
          intro hp
          have heq := Option.some.inj (ho.symm.trans
            ((pl.mem_regs _ i).mp (split_toParent_subset _ _ hp)))
          subst b
          exact disjoint_left.mp (split_toParent_toRight_disjoint _ _) hp hr
        simp [mem_cold, ho, hn]
      · exact False.elim (by simpa [(split_leaf _ _ (hleaf b h)).2] using hr)

theorem route_cold_card {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ)
    (feed : Finset (Fin (2 ^ k))) (hfeed : feed ⊆ pl.cold)
    (hleaf : ∀ b : Bag k, ¬ b.l < k → (pl.regs b).card / 2 ≤ f b) :
    (pl.route f feed).cold.card = pl.cold.card - feed.card +
      splitParentCard (pl.regs (Bag.root k)).card (f (Bag.root k)) := by
  rw [route_cold pl f feed hleaf, card_union_of_disjoint]
  · rw [card_sdiff_of_subset hfeed, split_toParent_card]
  · exact (pl.cold_disjoint (Bag.root k)).mono sdiff_subset (split_toParent_subset _ _)

end StoredPlacement

end Paterson.Bags
