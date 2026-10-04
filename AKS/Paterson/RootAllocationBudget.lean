module

public import AKS.Paterson.ScheduledInvariant
public import AKS.Paterson.Root

/-! # Exact-sort budget for the actual allocated upper region -/

@[expose] public section

namespace Paterson.Bags

open Finset BigOperators

theorem allocated_bag_upper {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (b : Bag k) :
    ((pl.regs b).card : ℚ) ≤ capacity fastParams root t b.l + 32 := by
  have hcap := hc.trans (root_capacity_le_level hr t b.l)
  by_cases hp : (t + b.l) % 2 = 0
  · by_cases hf : 0 ≤ nativeWidth k b.l / 4 -
        ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.l)
    · have hmin : (128 : ℚ) ≤ fastParams.minCapacity := by norm_num [fastParams]
      have hn := (scheduledBag_full_bounds fastParams hf (hmin.trans hcap)).2.le
      rw [← bagTarget_eq_scheduledBag root k t b.l hp, ← ha.1 b] at hn
      exact hn
    · have hn := allocated_partial_half_upper hr pl ha b hp (le_of_lt (lt_of_not_ge hf))
      have heven := Nat.mul_div_cancel' (allocated_even pl ha b)
      have hevenQ : (2 : ℚ) * ((pl.regs b).card / 2 : ℕ) = (pl.regs b).card := by
        exact_mod_cast heven
      linarith
  · rw [allocated_inactive_empty pl ha b hp, card_empty, Nat.cast_zero]
    linarith [capacity_nonneg fastParams hr t b.l]

def levelRegisters {k : ℕ} (pl : StoredPlacement k) (l : ℕ) (hl : l ≤ k) : Finset (Fin (2 ^ k)) :=
  univ.biUnion fun x : Fin (2 ^ l) ↦ pl.regs ⟨l, x.val, hl, x.isLt⟩

theorem levelRegisters_upper {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (l : ℕ) (hl : l ≤ k) :
    ((levelRegisters pl l hl).card : ℚ) ≤ (2 : ℚ) ^ l * (capacity fastParams root t l + 32) := by
  have hcard : (univ.biUnion (fun x : Fin (2 ^ l) ↦ pl.regs ⟨l, x.val, hl, x.isLt⟩)).card ≤
      ∑ x : Fin (2 ^ l), (pl.regs ⟨l, x.val, hl, x.isLt⟩).card := card_biUnion_le
  have hQ : ((levelRegisters pl l hl).card : ℚ) ≤
      ∑ x : Fin (2 ^ l), ((pl.regs ⟨l, x.val, hl, x.isLt⟩).card : ℚ) := by
    exact_mod_cast hcard
  apply hQ.trans
  calc (∑ x : Fin (2 ^ l), ((pl.regs ⟨l, x.val, hl, x.isLt⟩).card : ℚ))
      ≤ ∑ _ : Fin (2 ^ l), (capacity fastParams root t l + 32) := by
        apply sum_le_sum
        intro x _
        exact allocated_bag_upper hr hc pl ha _
    _ = _ := by simp; ring

theorem allocated_cold_upper {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0) :
    (pl.cold.card : ℚ) ≤ ancestorReserve fastParams (capacity fastParams root t 0) := by
  have htotal := root_total_le hr k t hk
  have hround := le_ceil32 (idealSubtree fastParams (nativeWidth k 0) (capacity fastParams root t 0))
  have hideal := le_max_right (0 : ℚ)
    (nativeWidth k 0 - ancestorReserve fastParams (capacity fastParams root t 0))
  rw [ha.2, coldTarget, if_pos hp, Nat.cast_sub htotal]
  simp only [nativeWidth, pow_zero, div_one] at hideal hround
  have htotalQ : ((subtreeTotal root k t 0 : ℕ) : ℚ) =
      ceil32 (idealSubtree fastParams ((2 : ℚ) ^ k) (capacity fastParams root t 0)) := by
    simp only [subtreeTotal, scheduledSubtree, nativeWidth, pow_zero, div_one]
  rw [htotalQ]
  push_cast
  unfold idealSubtree at hround ⊢
  linarith

def upperRegisters {k : ℕ} (pl : StoredPlacement k) (hk : 5 ≤ k) : Finset (Fin (2 ^ k)) :=
  pl.cold ∪ pl.regs (Bag.root k) ∪ levelRegisters pl 2 (by omega) ∪ levelRegisters pl 4 (by omega)

theorem allocated_upper_region_budget {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 5 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (hceil : capacity fastParams root t 0 ≤ rootCeiling)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0) :
    (upperRegisters pl hk).card < 2 ^ 33 := by
  have hcap (l : ℕ) : capacity fastParams root t l =
      capacity fastParams root t 0 * fastParams.A ^ l := by simp [capacity]
  have h2 := levelRegisters_upper hr hc pl ha 2 (by omega)
  have h4 := levelRegisters_upper hr hc pl ha 4 (by omega)
  rw [hcap 2] at h2
  rw [hcap 4] at h4
  have hbudget := root_region_budget hceil (allocated_cold_upper hr hk pl ha hp)
    (allocated_bag_upper hr hc pl ha (Bag.root k))
    (level2 := (levelRegisters pl 2 (by omega)).card)
    (level4 := (levelRegisters pl 4 (by omega)).card)
    (by simpa only [show (2 : ℚ) ^ 2 = 4 by norm_num] using h2)
    (by simpa only [show (2 : ℚ) ^ 4 = 16 by norm_num] using h4)
  have hcard : (upperRegisters pl hk).card ≤ pl.cold.card + (pl.regs (Bag.root k)).card +
      (levelRegisters pl 2 (by omega)).card + (levelRegisters pl 4 (by omega)).card :=
    (card_union_le _ _).trans
      (Nat.add_le_add_right ((card_union_le _ _).trans
        (Nat.add_le_add_right (card_union_le _ _) _)) _)
  have hcardQ : ((upperRegisters pl hk).card : ℚ) ≤ pl.cold.card + (pl.regs (Bag.root k)).card +
      (levelRegisters pl 2 (by omega)).card + (levelRegisters pl 4 (by omega)).card := by exact_mod_cast hcard
  exact_mod_cast hcardQ.trans_lt hbudget

end Paterson.Bags
