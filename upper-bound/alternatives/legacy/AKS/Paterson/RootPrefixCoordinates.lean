module

public import AKS.Paterson.CoarsePrefixCount

/-! # Expected prefix boundaries in the exactly sorted upper region

All prefix boundaries are integer positions in the actual upper register set.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem upper_prefix_coordinate {root : ℚ} (hr : 0 ≤ root)
    {k t L : ℕ} (hk : 6 ≤ k) (hL : L ≤ 6)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (hp : t % 2 = 0) (q : ℕ) :
    q * bagSize k L - (q * 2 ^ (6 - L)) * subtreeTotal root k t 6 =
      q * ((upperRegisters pl (by omega)).card / 2 ^ L) := by
  have hdiv : 2 ^ L ∣ (upperRegisters pl (by omega)).card :=
    dvd_trans (Nat.pow_dvd_pow 2 hL) (upperRegisters_dvd64 hr hk hc pl ha hp)
  have hU := Nat.mul_div_cancel' hdiv
  have hD := deepRegisters_card hr hk hc pl ha hp
  have htotal : (upperRegisters pl (by omega)).card + 64 * subtreeTotal root k t 6 =
      2 ^ k := by
    rw [← hD, ← card_union_of_disjoint (deepRegisters_disjoint_upper hk pl ha hp).symm,
      upper_deep_complete hk pl ha hp]
    simp
  have h64 : 2 ^ L * 2 ^ (6 - L) = 64 := by
    rw [← pow_add, Nat.add_sub_of_le hL]; norm_num
  have hsize : 2 ^ L * bagSize k L = 2 ^ k := by
    unfold bagSize
    rw [Nat.pow_div (by omega : L ≤ k) (by positivity), ← pow_add,
      Nat.add_sub_of_le (by omega : L ≤ k)]
  have hratio : bagSize k L = (upperRegisters pl (by omega)).card / 2 ^ L +
      2 ^ (6 - L) * subtreeTotal root k t 6 := by
    have hpos : 0 < (2 : ℕ) ^ L := by positivity
    nlinarith [hU, h64, hsize, htotal]
  rw [hratio, mul_add, ← mul_assoc, Nat.add_sub_cancel_right]

theorem upper_prefix_discrepancy {root : ℚ} (hr : 0 ≤ root)
    {k t L : ℕ} (hk : 6 ≤ k) (hL : L ≤ 6)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (hp : t % 2 = 0) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (hw : Function.Injective w) (q : ℕ) (hq : q ≤ 2 ^ L) :
    (((upperRegisters pl (by omega)).filter
      (fun i ↦ (w i).val < q * bagSize k L)).card : ℚ) -
        ((q * ((upperRegisters pl (by omega)).card / 2 ^ L) : ℕ) : ℚ) ≤
          (deepErrors pl w L).card ∧
    ((q * ((upperRegisters pl (by omega)).card / 2 ^ L) : ℕ) : ℚ) -
      ((upperRegisters pl (by omega)).filter
        (fun i ↦ (w i).val < q * bagSize k L)).card ≤ (deepErrors pl w L).card := by
  have h := allocated_actual_prefix_discrepancy hr hk hL hc pl ha hp w hw q hq
  rw [upper_prefix_coordinate hr hk hL hc pl ha hp] at h
  have hfilter : (upperRegisters pl (by omega)).filter
      (fun i ↦ nativeBagIdx k L (w i).val < q) =
      (upperRegisters pl (by omega)).filter (fun i ↦ (w i).val < q * bagSize k L) := by
    ext i
    simp only [mem_filter]
    exact and_congr_right (fun _ ↦ Nat.div_lt_iff_lt_mul (bagSize_pos (by omega)))
  rw [hfilter] at h
  simpa only [Nat.cast_mul] using h

end Paterson.Bags
