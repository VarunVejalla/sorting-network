module

public import AKS.Paterson.RootAllocationBudget

/-! # Exact cardinalities of the region rebuilt at a root split -/

@[expose] public section

namespace Paterson.Bags

open Finset BigOperators

theorem levelRegisters_card {root : ℚ} {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (l : ℕ) (hl : l ≤ k) :
    (levelRegisters pl l hl).card = 2 ^ l * bagTarget root k t l := by
  unfold levelRegisters
  rw [card_biUnion]
  · simp only [ha.1, sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  · intro x _ y _ hxy
    apply pl.disjoint
    intro heq
    exact hxy (Fin.ext (congrArg Bag.x heq))

theorem levelRegisters_disjoint {k : ℕ} (pl : StoredPlacement k) (l m : ℕ)
    (hl : l ≤ k) (hm : m ≤ k) (hne : l ≠ m) :
    Disjoint (levelRegisters pl l hl) (levelRegisters pl m hm) := by
  rw [disjoint_left]
  intro i hi hj
  obtain ⟨x, _, hx⟩ := mem_biUnion.mp hi
  obtain ⟨y, _, hy⟩ := mem_biUnion.mp hj
  exact disjoint_left.mp (pl.disjoint _ _ (fun heq ↦ hne (congrArg Bag.l heq))) hx hy

theorem cold_levelRegisters_disjoint {k : ℕ} (pl : StoredPlacement k) (l : ℕ) (hl : l ≤ k) :
    Disjoint pl.cold (levelRegisters pl l hl) := by
  rw [disjoint_left]
  intro i hi hj
  obtain ⟨x, _, hx⟩ := mem_biUnion.mp hj
  exact disjoint_left.mp (pl.cold_disjoint _) hi hx

theorem root_levelRegisters_disjoint {k : ℕ} (pl : StoredPlacement k) (l : ℕ)
    (hl : l ≤ k) (hpos : 0 < l) : Disjoint (pl.regs (Bag.root k)) (levelRegisters pl l hl) := by
  rw [disjoint_left]
  intro i hi hj
  obtain ⟨x, _, hx⟩ := mem_biUnion.mp hj
  apply disjoint_left.mp (pl.disjoint _ _ _) hi hx
  intro heq
  have h := congrArg Bag.l heq
  change 0 = l at h
  omega

theorem upperRegisters_card {root : ℚ} {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) :
    (upperRegisters pl hk).card = pl.cold.card + (pl.regs (Bag.root k)).card +
      4 * bagTarget root k t 2 + 16 * bagTarget root k t 4 := by
  have hc4 := cold_levelRegisters_disjoint pl 4 (by omega)
  have hr4 := root_levelRegisters_disjoint pl 4 (by omega) (by omega)
  have h24 := levelRegisters_disjoint pl 2 4 (by omega) (by omega) (by omega)
  have hc2 := cold_levelRegisters_disjoint pl 2 (by omega)
  have hr2 := root_levelRegisters_disjoint pl 2 (by omega) (by omega)
  rw [upperRegisters,
    card_union_of_disjoint (disjoint_union_left.mpr
      ⟨disjoint_union_left.mpr ⟨hc4, hr4⟩, h24⟩),
    card_union_of_disjoint (disjoint_union_left.mpr ⟨hc2, hr2⟩),
    card_union_of_disjoint (pl.cold_disjoint (Bag.root k)),
    levelRegisters_card pl ha, levelRegisters_card pl ha]
  norm_num

theorem subtreeTotal_grand_le {root : ℚ} {k t l : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t l) :
    4 * subtreeTotal root k t (l + 2) ≤ subtreeTotal root k t l := by
  obtain ⟨hsmall, hlarge⟩ := subtreeTotal_nesting (k := k) hc
  omega

theorem upperRegisters_complement_count {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 5 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0) :
    (upperRegisters pl hk).card = 2 ^ k - 64 * subtreeTotal root k t 6 := by
  have h0 := subtreeTotal_grand_le (k := k) hc
  have h2 := subtreeTotal_grand_le (k := k) (hc.trans (root_capacity_le_level hr t 2))
  have h4 := subtreeTotal_grand_le (k := k) (hc.trans (root_capacity_le_level hr t 4))
  have hroot := root_total_le hr k t hk
  have hp0 : (t + 0) % 2 = 0 := by omega
  have hp2 : (t + 2) % 2 = 0 := by omega
  have hp4 : (t + 4) % 2 = 0 := by omega
  rw [upperRegisters_card hk pl ha, ha.2, ha.1 (Bag.root k)]
  simp only [coldTarget, if_pos hp, Bag.root, bagTarget, if_pos hp0, if_pos hp2, if_pos hp4]
  norm_num only at h0 h2 h4 ⊢
  omega

theorem upperRegisters_dvd64 {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0) :
    64 ∣ (upperRegisters pl (by omega)).card := by
  rw [upperRegisters_complement_count hr (by omega) hc pl ha hp]
  exact Nat.dvd_sub (Nat.pow_dvd_pow 2 hk) (dvd_mul_right 64 _)

end Paterson.Bags
