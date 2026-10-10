module

public import AKS.Paterson.DeepPrefixAgreement

/-! # Exact global rank prefix counts -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem coarse_prefix_count {k L : ℕ} (hL : L ≤ k)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (q : ℕ) (hq : q ≤ 2 ^ L) :
    (univ.filter (fun i ↦ nativeBagIdx k L (w i).val < q)).card =
      q * bagSize k L := by
  have hsize : 2 ^ L * bagSize k L = 2 ^ k := by
    unfold bagSize
    rw [Nat.pow_div hL (by positivity), ← pow_add, Nat.add_sub_of_le hL]
  have hbound : q * bagSize k L ≤ 2 ^ k := by
    rw [← hsize]
    exact Nat.mul_le_mul_right _ hq
  have hpred : (fun i ↦ nativeBagIdx k L (w i).val < q) =
      (fun i ↦ (w i).val < q * bagSize k L) := by
    funext i
    apply propext
    exact Nat.div_lt_iff_lt_mul (bagSize_pos hL)
  have hfilter : univ.filter (fun i ↦ nativeBagIdx k L (w i).val < q) =
      univ.filter (fun i ↦ (w i).val < q * bagSize k L) := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    exact (congrFun hpred i).to_iff
  rw [hfilter, bijection_count_val_lt w hw, card_filter_val_lt _ _ hbound]

theorem allocated_coarse_prefix_capacity {root : ℚ} (hr : 0 ≤ root)
    {k t L : ℕ} (hk : 6 ≤ k) (hL : L ≤ 6)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (hp : t % 2 = 0) (q : ℕ) :
    (q * 2 ^ (6 - L)) * subtreeTotal root k t 6 ≤ q * bagSize k L := by
  have hd : 64 * subtreeTotal root k t 6 ≤ 2 ^ k := by
    rw [← deepRegisters_card hr hk hc pl ha hp]
    exact (card_le_card (subset_univ _)).trans_eq (by simp)
  have h64 : 2 ^ L * 2 ^ (6 - L) = 64 := by
    rw [← pow_add, Nat.add_sub_of_le hL]; norm_num
  have hsize : 2 ^ L * bagSize k L = 2 ^ k := by
    unfold bagSize
    rw [Nat.pow_div (by omega : L ≤ k) (by positivity), ← pow_add,
      Nat.add_sub_of_le (by omega : L ≤ k)]
  have hmul : 2 ^ L * (2 ^ (6 - L) * subtreeTotal root k t 6) ≤
      2 ^ L * bagSize k L := by
    simpa only [← mul_assoc, h64, hsize] using hd
  have hsmall : 2 ^ (6 - L) * subtreeTotal root k t 6 ≤ bagSize k L :=
    le_of_mul_le_mul_left hmul (by positivity)
  simpa only [mul_assoc] using Nat.mul_le_mul_left q hsmall

theorem allocated_actual_prefix_discrepancy {root : ℚ} (hr : 0 ≤ root)
    {k t L : ℕ} (hk : 6 ≤ k) (hL : L ≤ 6)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (hp : t % 2 = 0) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (hw : Function.Injective w) (q : ℕ) (hq : q ≤ 2 ^ L) :
    (((upperRegisters pl (by omega)).filter
      (fun i ↦ nativeBagIdx k L (w i).val < q)).card : ℚ) -
        (q * bagSize k L - (q * 2 ^ (6 - L)) * subtreeTotal root k t 6 : ℕ) ≤
          (deepErrors pl w L).card ∧
    ((q * bagSize k L - (q * 2 ^ (6 - L)) * subtreeTotal root k t 6 : ℕ) : ℚ) -
      ((upperRegisters pl (by omega)).filter
        (fun i ↦ nativeBagIdx k L (w i).val < q)).card ≤
          (deepErrors pl w L).card :=
  allocated_remaining_prefix_discrepancy hr hk hL hc pl ha hp w q hq _
    (coarse_prefix_count (by omega) w hw q hq)
    (allocated_coarse_prefix_capacity hr hk hL hc pl ha hp q)

end Paterson.Bags
