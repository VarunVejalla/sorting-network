module

public import AKS.Paterson.BoundarySchedule

/-! # Actual initial allocation and canonical storage feed

Register choices are positional. The rank permutation is not inspected by
the allocation, as required for an oblivious comparator network.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

def registerPrefix {n : ℕ} (regs : Finset (Fin n)) (count : ℕ) : Finset (Fin n) :=
  (univ.filter (fun i : Fin regs.card ↦ i.val < count)).image (regs.orderEmbOfFin rfl)

theorem registerPrefix_subset {n : ℕ} (regs : Finset (Fin n)) (count : ℕ) :
    registerPrefix regs count ⊆ regs := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := mem_image.mp hi
  exact orderEmbOfFin_mem regs rfl j

theorem registerPrefix_card {n : ℕ} (regs : Finset (Fin n)) (count : ℕ)
    (h : count ≤ regs.card) : (registerPrefix regs count).card = count := by
  rw [registerPrefix, card_image_of_injective _ (regs.orderEmbOfFin rfl).injective,
    card_filter_val_lt _ _ h]

/-- The central wires return from storage, leaving its two outer fringes.
This is the storage feed intended for the ordered global construction. -/
def centralFeed {k : ℕ} (regs : Finset (Fin (2 ^ k))) (count : ℕ) : Finset (Fin (2 ^ k)) :=
  let parts := split regs ((regs.card - count) / 2)
  parts.toLeft ∪ parts.toRight

theorem centralFeed_subset {k : ℕ} (regs : Finset (Fin (2 ^ k))) (count : ℕ) :
    centralFeed regs count ⊆ regs :=
  union_subset (split_toLeft_subset _ _) (split_toRight_subset _ _)

theorem centralFeed_card {k : ℕ} (regs : Finset (Fin (2 ^ k))) (count : ℕ)
    (hn : 2 ∣ regs.card) (hc : 2 ∣ count) (hle : count ≤ regs.card) :
    (centralFeed regs count).card = count := by
  rw [centralFeed, card_union_of_disjoint (split_toLeft_toRight_disjoint _ _),
    split_toLeft_card, split_toRight_card]
  unfold splitChildCard
  have hmodn := Nat.mod_eq_zero_of_dvd hn
  have hmodc := Nat.mod_eq_zero_of_dvd hc
  omega

namespace StoredPlacement

/-- Package storage with the root only for inherited subtree counting.
Actual comparison and routing still use the separate register sets. -/
def collapse {k : ℕ} (pl : StoredPlacement k) : Placement k where
  regs b := if b = Bag.root k then pl.regs b ∪ pl.cold else pl.regs b
  disjoint a b hab := by
    by_cases ha : a = Bag.root k
    · subst a
      have hb : b ≠ Bag.root k := Ne.symm hab
      simp only [ite_true, if_neg hb]
      exact disjoint_union_left.mpr ⟨pl.disjoint _ _ hab, pl.cold_disjoint _⟩
    · by_cases hb : b = Bag.root k
      · subst b
        simp only [if_neg ha, ite_true]
        exact disjoint_union_right.mpr ⟨pl.disjoint _ _ hab, (pl.cold_disjoint _).symm⟩
      · simp only [if_neg ha, if_neg hb]
        exact pl.disjoint _ _ hab
  complete i := by
    rcases pl.complete i with hc | ⟨b, hb⟩
    · exact ⟨Bag.root k, by simp only [ite_true]; exact mem_union_right _ hc⟩
    · refine ⟨b, ?_⟩
      by_cases h : b = Bag.root k
      · simp only [h, ite_true] at *
        exact mem_union_left _ hb
      · simpa only [if_neg h] using hb

theorem collapse_regs_of_pos {k : ℕ} (pl : StoredPlacement k) (b : Bag k) (hb : 1 ≤ b.l) :
    pl.collapse.regs b = pl.regs b := by
  have h : b ≠ Bag.root k := by intro h; have := congrArg Bag.l h; change b.l = 0 at this; omega
  simp only [collapse, if_neg h]

theorem root_strangers_zero {k : ℕ} (w : Fin (2 ^ k) → Fin (2 ^ k))
    (regs : Finset (Fin (2 ^ k))) {j : ℕ} (hj : 1 ≤ j) :
    (Bag.root k).strangers j w regs = 0 := by
  have hempty : regs.filter (fun i ↦ (Bag.root k).Strange j i w) = ∅ := by
    rw [filter_eq_empty_iff]
    intro i _
    simp only [Bag.Strange, show j ≠ 0 by omega, false_or]
    simp [Bag.ancestor, Bag.root, Bag.Native, nativeBagIdx_root (w i).isLt]
  simp only [Bag.strangers, hempty, card_empty]

theorem collapse_invariant {k : ℕ} (pl : StoredPlacement k) (cap : Bag k → ℚ)
    (hc : ∀ b, 0 ≤ cap b) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (hinv : Invariant fastParams cap pl.regs w) :
    Invariant fastParams cap pl.collapse.regs w := by
  intro b j hj
  by_cases hb : b = Bag.root k
  · subst b
    rw [root_strangers_zero w _ hj, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg fastParams.mu_pos.le
      (pow_nonneg fastParams.delta_pos.le _)) (hc _)
  · simpa only [collapse, if_neg hb] using hinv b j hj

def initial (k count : ℕ) : StoredPlacement k where
  owner i := if i.val < count then some (Bag.root k) else none

def centeredInitial (k count : ℕ) : StoredPlacement k where
  owner i := if i ∈ centralFeed univ count then some (Bag.root k) else none

theorem centeredInitial_root_regs (k count : ℕ) :
    (centeredInitial k count).regs (Bag.root k) = centralFeed univ count := by
  ext i
  simp [mem_regs, centeredInitial]

theorem centeredInitial_root_card (k count : ℕ) (hk : 1 ≤ k)
    (hc : 2 ∣ count) (hle : count ≤ 2 ^ k) :
    ((centeredInitial k count).regs (Bag.root k)).card = count := by
  rw [centeredInitial_root_regs]
  apply centralFeed_card
  · simp only [card_univ, Fintype.card_fin]
    exact dvd_pow_self 2 (by omega)
  · exact hc
  · simpa only [card_univ, Fintype.card_fin] using hle

theorem initial_root_regs (k count : ℕ) :
    (initial k count).regs (Bag.root k) = univ.filter (fun i ↦ i.val < count) := by
  ext i
  simp [mem_regs, initial]

theorem initial_other_regs (k count : ℕ) (b : Bag k) (hb : b ≠ Bag.root k) :
    (initial k count).regs b = ∅ := by
  ext i
  simp [mem_regs, initial, Ne.symm hb]

theorem initial_root_card (k count : ℕ) (h : count ≤ 2 ^ k) :
    ((initial k count).regs (Bag.root k)).card = count := by
  rw [initial_root_regs, card_filter_val_lt _ _ h]

theorem initial_cold_card (k count : ℕ) (h : count ≤ 2 ^ k) :
    (initial k count).cold.card = 2 ^ k - count := by
  have heq : (initial k count).cold = univ.filter (fun i ↦ count ≤ i.val) := by
    ext i
    simp [mem_cold, initial]
  rw [heq, card_filter_val_ge _ _ h]

/-- The root and every other bag satisfy the invariant at initialization
for every input rank permutation; storage has no stranger constraint. -/
theorem initial_invariant (k count : ℕ) (cap : Bag k → ℚ)
    (hc : ∀ b, 0 ≤ cap b) (w : Fin (2 ^ k) → Fin (2 ^ k)) :
    Invariant fastParams cap (initial k count).regs w := by
  intro b j hj
  have hnonneg : 0 ≤ fastParams.mu * fastParams.delta ^ (j - 1) * cap b :=
    mul_nonneg (mul_nonneg fastParams.mu_pos.le (pow_nonneg fastParams.delta_pos.le _)) (hc b)
  by_cases hb : b = Bag.root k
  · subst b
    have hempty : ((initial k count).regs (Bag.root k)).filter
        (fun i ↦ (Bag.root k).Strange j i w) = ∅ := by
      rw [filter_eq_empty_iff]
      intro i _
      simp only [Bag.Strange, show j ≠ 0 by omega, false_or]
      simp [Bag.ancestor, Bag.root, Bag.Native, nativeBagIdx_root (w i).isLt]
    simpa only [Bag.strangers, hempty, card_empty, Nat.cast_zero] using hnonneg
  · simpa only [initial_other_regs k count b hb, Bag.strangers_empty, Nat.cast_zero] using hnonneg

/-- Feed exactly the requested number of actual storage wires. -/
def feedRoute {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ) (count : ℕ) :
    StoredPlacement k := pl.route f (registerPrefix pl.cold count)

theorem feedRoute_cold_card {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ) (count : ℕ)
    (hc : count ≤ pl.cold.card)
    (hleaf : ∀ b : Bag k, ¬ b.l < k → (pl.regs b).card / 2 ≤ f b) :
    (pl.feedRoute f count).cold.card = pl.cold.card - count +
      splitParentCard (pl.regs (Bag.root k)).card (f (Bag.root k)) := by
  rw [feedRoute, route_cold_card _ _ _ (registerPrefix_subset _ _) hleaf,
    registerPrefix_card _ _ hc]

def centralFeedRoute {k : ℕ} (pl : StoredPlacement k) (f : Bag k → ℕ) (count : ℕ) :
    StoredPlacement k := pl.route f (centralFeed pl.cold count)

theorem centralFeedRoute_cold_card {k : ℕ} (pl : StoredPlacement k)
    (f : Bag k → ℕ) (count : ℕ) (hn : 2 ∣ pl.cold.card) (hc : 2 ∣ count)
    (hle : count ≤ pl.cold.card)
    (hleaf : ∀ b : Bag k, ¬ b.l < k → (pl.regs b).card / 2 ≤ f b) :
    (pl.centralFeedRoute f count).cold.card = pl.cold.card - count +
      splitParentCard (pl.regs (Bag.root k)).card (f (Bag.root k)) := by
  rw [centralFeedRoute, route_cold_card _ _ _ (centralFeed_subset _ _) hleaf,
    centralFeed_card _ _ hn hc hle]

end StoredPlacement

end Paterson.Bags
