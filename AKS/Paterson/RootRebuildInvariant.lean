module

public import AKS.Paterson.RootRebuildContainment
public import AKS.Paterson.RootRebuildErrors

/-! # The actual upper-region sort and rebuild preserve the rank invariant -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem strangers_above_root_zero {k : ℕ} (b : Bag k) {j : ℕ} (hj : b.l < j)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (S : Finset (Fin (2 ^ k))) :
    b.strangers j w S = 0 := by
  have hlevel : (b.ancestor (j - 1)).l = 0 := by change b.l - (j - 1) = 0; omega
  have hanc : b.ancestor (j - 1) = Bag.root k := by
    apply Bag.ext hlevel
    have hx := (b.ancestor (j - 1)).hx
    rw [hlevel, pow_zero] at hx
    change (b.ancestor (j - 1)).x = 0
    omega
  unfold Bag.strangers
  rw [card_eq_zero, filter_eq_empty_iff]
  intro i _
  simp only [Bag.Strange, show j ≠ 0 by omega, false_or, hanc]
  exact not_not.mpr (Bag.native_root i w)

theorem allocatedRebuild_upper_strangers {root : ℚ} (hr : 0 ≤ root)
    {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w)
    (b : Bag k) (hb : b.l = 2 ∨ b.l = 4) (j : ℕ) (hj : 1 ≤ j) :
    let U := upperRegisters pl (by omega)
    let w' := ((bitonicNetwork U.card).scatterEmbed (2 ^ k) (U.orderEmbOfFin rfl)).exec w
    (b.strangers j w' ((allocatedRebuild root t pl (by omega)).regs b) : ℚ) ≤
      fastParams.mu * fastParams.delta ^ (j - 1) * capacity fastParams root t b.l := by
  dsimp only
  have hn : 0 ≤ fastParams.mu * fastParams.delta ^ (j - 1) * capacity fastParams root t b.l :=
    mul_nonneg (mul_nonneg fastParams.mu_pos.le (pow_nonneg fastParams.delta_pos.le _))
      (capacity_nonneg fastParams hr _ _)
  by_cases hjb : b.l < j
  · rw [strangers_above_root_zero b hjb, Nat.cast_zero]
    exact hn
  · let c := b.ancestor (j - 1)
    have hcL : c.l = b.l - (j - 1) := rfl
    have hL : c.l ≤ b.l := Nat.sub_le _ _
    have hL6 : c.l ≤ 6 := by omega
    have hd : 2 ^ b.l ∣ (upperRegisters pl (by omega)).card :=
      dvd_trans (Nat.pow_dvd_pow 2 (by omega : b.l ≤ 6))
        (upperRegisters_dvd64 hr hk hc pl ha hp)
    have hs := (allocatedRebuild_upper_bin hr hk hc pl ha hp b hb).trans
      (positionalBin_ancestor (upperRegisters pl (by omega)) hL hd b.x)
    have hsub : (allocatedRebuild root t pl (by omega)).regs b ⊆
        positionalBin (upperRegisters pl (by omega)) c.l c.x := by
      have he : b.l - c.l = j - 1 := by omega
      simpa only [he] using hs
    let U := upperRegisters pl (by omega)
    let v := ((bitonicNetwork U.card).scatterEmbed (2 ^ k) (U.orderEmbOfFin rfl)).exec w
    have h := upper_sorted_subset_errors hr hk hL6 hc pl ha hp w hw c.x c.hx
      ((allocatedRebuild root t pl (by omega)).regs b) hsub
    have heq : ((allocatedRebuild root t pl (by omega)).regs b).filter
        (fun i ↦ b.Strange j i v) =
      ((allocatedRebuild root t pl (by omega)).regs b).filter (fun i ↦
        (v i).val < c.x * bagSize k c.l ∨ (c.x + 1) * bagSize k c.l ≤ (v i).val) := by
      ext i
      simp only [mem_filter, Bag.Strange, show j ≠ 0 by omega, false_or]
      apply and_congr_right
      intro _
      change ¬ c.Native i v ↔ _
      rw [c.native_iff]
      simp only [not_and_or, not_le, not_lt, Bag.lo, Bag.hi, Bag.size]
    change (((((allocatedRebuild root t pl (by omega)).regs b).filter
      (fun i ↦ b.Strange j i v)).card : ℚ)) ≤ _
    rw [heq]
    apply h.trans
    apply (mul_le_mul_of_nonneg_left (deepErrors_bound hr hL6 pl w hi)
      (by norm_num : (0 : ℚ) ≤ 2)).trans
    rcases hb with hb2 | hb4
    · rw [hb2]
      exact root_rebuild_level2_budget hr (by omega) hj (by omega)
    · rw [hb4]
      exact root_rebuild_level4_budget hr (by omega) hj (by omega)

theorem allocatedRebuild_preserves {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w) :
    let U := upperRegisters pl (by omega)
    Invariant fastParams (fun c ↦ capacity fastParams root t c.l)
      (allocatedRebuild root t pl (by omega)).regs
      (((bitonicNetwork U.card).scatterEmbed (2 ^ k) (U.orderEmbOfFin rfl)).exec w) := by
  dsimp only
  intro b j hj
  by_cases hb : 6 ≤ b.l
  · rw [allocatedRebuild, rebuildUpper_deep_regs hk pl ha hp _ _ b hb]
    have heq : b.strangers j
        (((bitonicNetwork (upperRegisters pl (by omega)).card).scatterEmbed (2 ^ k)
          ((upperRegisters pl (by omega)).orderEmbOfFin rfl)).exec w) (pl.regs b) =
        b.strangers j w (pl.regs b) := by
      unfold Bag.strangers
      congr 1
      apply filter_congr
      intro i hiB
      have hout : i ∉ upperRegisters pl (by omega) := fun hU ↦
        disjoint_left.mp (deepRegisters_disjoint_upper hk pl ha hp)
          (mem_deepRegisters_of_owner pl hk b hb hiB) hU
      have hrange : i ∉ Set.range ((upperRegisters pl (by omega)).orderEmbOfFin rfl) := by
        rw [range_orderEmbOfFin]; exact hout
      have hv := ComparatorNetwork.scatterEmbed_exec_outside
        (bitonicNetwork (upperRegisters pl (by omega)).card) (2 ^ k)
        ((upperRegisters pl (by omega)).orderEmbOfFin rfl) w i hrange
      simp only [Bag.Strange, Bag.Native, hv]
    rw [heq]
    exact hi b j hj
  · by_cases hb24 : b.l = 2 ∨ b.l = 4
    · exact allocatedRebuild_upper_strangers hr hk hc pl ha hp w hw hi b hb24 j hj
    · rw [allocatedRebuild, rebuildUpper_other_low_empty (by omega) pl ha hp _ _ b
        (by omega) (by omega) (by omega), Bag.strangers_empty, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg fastParams.mu_pos.le (pow_nonneg fastParams.delta_pos.le _))
        (capacity_nonneg fastParams hr _ _)

end Paterson.Bags
