module

public import AKS.Paterson.GridCounting

/-! # Actual allocation counts after rebuilding the upper region -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem allocated_rebuild_fit {root : ℚ} {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) :
    bagTarget root k t 4 + bagTarget root k t 2 / 4 ≤ (upperRegisters pl hk).card / 16 := by
  have hn2 : 4 ∣ bagTarget root k t 2 :=
    dvd_trans (by norm_num) (bagTarget_dvd _ _ _ _)
  have hn2' := Nat.mul_div_cancel' hn2
  have hU := upperRegisters_card hk pl ha
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).mpr
  nlinarith

def allocatedRebuild {k : ℕ} (root : ℚ) (t : ℕ) (pl : StoredPlacement k)
    (hk : 5 ≤ k) : StoredPlacement k :=
  rebuildUpper pl hk (bagTarget root k t 2) (bagTarget root k t 4)

theorem allocatedRebuild_low_cards {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (b : Bag k) (hb : b.l < 6) :
    ((allocatedRebuild root t pl (by omega)).regs b).card =
      if b.l = 2 ∨ b.l = 4 then bagTarget root k t b.l else 0 := by
  have hfit := allocated_rebuild_fit (by omega : 5 ≤ k) pl ha
  have hd : 16 ∣ (upperRegisters pl (by omega)).card :=
    dvd_trans (by norm_num) (upperRegisters_dvd64 hr hk hc pl ha hp)
  by_cases hw : 0 < (upperRegisters pl (by omega)).card / 16
  · by_cases hb2 : b.l = 2
    · rw [if_pos (Or.inl hb2), hb2]
      exact rebuildUpper_two_card (by omega) pl ha hp _ _ hw hd hfit
        (dvd_trans (by norm_num) (bagTarget_dvd _ _ _ _)) b hb2
    · by_cases hb4 : b.l = 4
      · rw [if_pos (Or.inr hb4), hb4]
        exact rebuildUpper_four_card (by omega) pl ha hp _ _ hw hd
          (by omega) b hb4
      · rw [if_neg (by omega)]
        exact congrArg card (rebuildUpper_other_low_empty (by omega) pl ha hp _ _ b hb hb2 hb4)
  · have hz : (upperRegisters pl (by omega)).card = 0 := by
      have hm := Nat.mul_div_cancel' hd
      omega
    have hsub := rebuildUpper_low_regs_subset (by omega : 5 ≤ k) pl ha hp
      (bagTarget root k t 2) (bagTarget root k t 4) b hb
    have hcard : ((allocatedRebuild root t pl (by omega)).regs b).card = 0 := by
      exact Nat.eq_zero_of_le_zero (hz ▸ card_le_card hsub)
    rw [hcard]
    split_ifs with h
    · rcases h with h2 | h4
      · rw [h2]
        have hU := upperRegisters_card (by omega : 5 ≤ k) pl ha
        omega
      · rw [h4]
        omega
    · rfl

theorem allocatedRebuild_cold_subset {k : ℕ} (root : ℚ) (t : ℕ)
    (pl : StoredPlacement k) (hk : 5 ≤ k) :
    (allocatedRebuild root t pl hk).cold ⊆ upperRegisters pl hk := by
  intro i hi
  by_contra hu
  have ho := (StoredPlacement.mem_cold _ i).mp hi
  rw [allocatedRebuild, rebuildUpper_owner_outside pl hk _ _ hu] at ho
  have hc := (pl.mem_cold i).mpr ho
  exact hu (mem_union_left _ (mem_union_left _ (mem_union_left _ hc)))

theorem allocatedRebuild_upper_partition {root : ℚ} {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0) :
    (allocatedRebuild root t pl hk).cold ∪
      levelRegisters (allocatedRebuild root t pl hk) 2 (by omega) ∪
      levelRegisters (allocatedRebuild root t pl hk) 4 (by omega) = upperRegisters pl hk := by
  ext i
  constructor
  · intro hi
    rcases mem_union.mp hi with h02 | h4
    · rcases mem_union.mp h02 with hc | h2
      · exact allocatedRebuild_cold_subset root t pl hk hc
      · obtain ⟨x, _, hx⟩ := mem_biUnion.mp h2
        exact rebuildUpper_low_regs_subset hk pl ha hp _ _ _ (by change 2 < 6; omega) hx
    · obtain ⟨x, _, hx⟩ := mem_biUnion.mp h4
      exact rebuildUpper_low_regs_subset hk pl ha hp _ _ _ (by change 4 < 6; omega) hx
  · intro hi
    rcases rebuildUpper_owner_inside pl hk (bagTarget root k t 2) (bagTarget root k t 4) hi
      with he | ⟨b, he, hb⟩
    · exact mem_union_left _ (mem_union_left _ ((StoredPlacement.mem_cold _ i).mpr he))
    · have hm := (StoredPlacement.mem_regs _ b i).mpr he
      rcases hb with hb2 | hb4
      · apply mem_union_left
        apply mem_union_right
        simpa only [hb2] using mem_levelRegisters (allocatedRebuild root t pl hk) b hm
      · apply mem_union_right
        simpa only [hb4] using mem_levelRegisters (allocatedRebuild root t pl hk) b hm

theorem allocatedRebuild_level_card {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (l : ℕ) (hl : l = 2 ∨ l = 4) :
    (levelRegisters (allocatedRebuild root t pl (by omega)) l (by omega)).card =
      2 ^ l * bagTarget root k t l := by
  unfold levelRegisters
  rw [card_biUnion]
  · have hs (x : Fin (2 ^ l)) :
        ((allocatedRebuild root t pl (by omega)).regs ⟨l, x.val, by omega, x.isLt⟩).card =
          bagTarget root k t l := by
      simpa only [if_pos hl] using allocatedRebuild_low_cards hr hk hc pl ha hp
        (⟨l, x.val, by omega, x.isLt⟩ : Bag k) (by change l < 6; omega)
    simp only [hs, sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  · intro x _ y _ hxy
    apply StoredPlacement.disjoint
    intro he
    exact hxy (Fin.ext (congrArg Bag.x he))

theorem allocatedRebuild_cold_card {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0) :
    (allocatedRebuild root t pl (by omega)).cold.card =
      pl.cold.card + (pl.regs (Bag.root k)).card := by
  let new := allocatedRebuild root t pl (by omega)
  have hpart := congrArg card (allocatedRebuild_upper_partition (by omega : 5 ≤ k) pl ha hp)
  rw [card_union_of_disjoint (disjoint_union_left.mpr
    ⟨cold_levelRegisters_disjoint new 4 (by omega),
      levelRegisters_disjoint new 2 4 (by omega) (by omega) (by omega)⟩),
    card_union_of_disjoint (cold_levelRegisters_disjoint new 2 (by omega)),
    allocatedRebuild_level_card hr hk hc pl ha hp 2 (by omega),
    allocatedRebuild_level_card hr hk hc pl ha hp 4 (by omega),
    upperRegisters_card (by omega) pl ha] at hpart
  norm_num at hpart
  change new.cold.card = _
  omega

end Paterson.Bags
