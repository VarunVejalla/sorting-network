module

public import AKS.Paterson.RootPrefixCoordinates

/-! # Errors after the actual scattered upper-region sort -/

@[expose] public section

namespace Paterson.Bags

open Finset

def positionalBin {k : ℕ} (U : Finset (Fin (2 ^ k))) (L q : ℕ) :
    Finset (Fin (2 ^ k)) :=
  (univ.filter (fun i : Fin U.card ↦
    q * (U.card / 2 ^ L) ≤ i.val ∧ i.val < (q + 1) * (U.card / 2 ^ L))).image
    (U.orderEmbOfFin rfl)

theorem positionalBin_subset {k : ℕ} (U : Finset (Fin (2 ^ k))) (L q : ℕ) :
    positionalBin U L q ⊆ U := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := mem_image.mp hi
  exact orderEmbOfFin_mem U rfl j

theorem upper_sorted_bin_errors {root : ℚ} (hr : 0 ≤ root)
    {k t L : ℕ} (hk : 6 ≤ k) (hL : L ≤ 6)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (hp : t % 2 = 0) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (hw : Function.Injective w) (q : ℕ) (hq : q < 2 ^ L) :
    let U := upperRegisters pl (by omega)
    let w' := ((bitonicNetwork U.card).scatterEmbed (2 ^ k) (U.orderEmbOfFin rfl)).exec w
    (((positionalBin U L q).filter (fun i ↦
      (w' i).val < q * bagSize k L ∨ (q + 1) * bagSize k L ≤ (w' i).val)).card : ℚ) ≤
        2 * (deepErrors pl w L).card := by
  dsimp only
  let U := upperRegisters pl (by omega)
  have hlo := (upper_prefix_discrepancy hr hk hL hc pl ha hp w hw q (by omega)).1
  have hhi := (upper_prefix_discrepancy hr hk hL hc pl ha hp w hw (q + 1) hq).2
  rw [filter_regs_card] at hlo hhi
  have hb : (q + 1) * (U.card / 2 ^ L) ≤ U.card := by
    exact (Nat.mul_le_mul_right _ hq).trans (Nat.mul_div_le _ _)
  have h := sorted_network_bin_wrong_bound (bitonicNetwork U.card)
    (bitonicNetwork_sorts U.card) (w ∘ U.orderEmbOfFin rfl)
    (q * (U.card / 2 ^ L)) ((q + 1) * (U.card / 2 ^ L))
    (q * bagSize k L) ((q + 1) * bagSize k L) hb
    (by positivity : (0 : ℚ) ≤ (deepErrors pl w L).card) hlo hhi
  rw [positionalBin, filter_image_card]
  simpa only [mem_filter, mem_univ, true_and, Function.comp_apply,
    ComparatorNetwork.scatterEmbed_exec_inside, filter_filter, and_assoc] using h

theorem upper_sorted_subset_errors {root : ℚ} (hr : 0 ≤ root)
    {k t L : ℕ} (hk : 6 ≤ k) (hL : L ≤ 6)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (hp : t % 2 = 0) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (hw : Function.Injective w) (q : ℕ) (hq : q < 2 ^ L)
    (S : Finset (Fin (2 ^ k)))
    (hS : S ⊆ positionalBin (upperRegisters pl (by omega)) L q) :
    let U := upperRegisters pl (by omega)
    let w' := ((bitonicNetwork U.card).scatterEmbed (2 ^ k) (U.orderEmbOfFin rfl)).exec w
    ((S.filter (fun i ↦
      (w' i).val < q * bagSize k L ∨ (q + 1) * bagSize k L ≤ (w' i).val)).card : ℚ) ≤
        2 * (deepErrors pl w L).card := by
  exact (Nat.cast_le.mpr (card_le_card (filter_subset_filter _ hS))).trans
    (upper_sorted_bin_errors hr hk hL hc pl ha hp w hw q hq)

theorem upper_sorted_half_pure {root : ℚ} (hr : 0 ≤ root)
    {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (hceil : capacity fastParams root t 0 ≤ rootCeiling)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (hp : t % 2 = 0) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (hw : Function.Injective w)
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w)
    (q : Fin 2) :
    let U := upperRegisters pl (by omega)
    let w' := ((bitonicNetwork U.card).scatterEmbed (2 ^ k) (U.orderEmbOfFin rfl)).exec w
    ∀ i ∈ positionalBin U 1 q.val, nativeBagIdx k 1 (w' i).val = q.val := by
  dsimp only
  let U := upperRegisters pl (by omega)
  let v := ((bitonicNetwork U.card).scatterEmbed (2 ^ k) (U.orderEmbOfFin rfl)).exec w
  intro i hiB
  have h := upper_sorted_bin_errors hr hk (by omega : 1 ≤ 6) hc pl ha hp w hw
    q.val (by simpa using q.isLt)
  rw [deepErrors_one_empty hr hceil pl w hi, card_empty, Nat.cast_zero, mul_zero] at h
  have hz : ((positionalBin U 1 q.val).filter
      (fun j ↦ (v j).val < q.val * bagSize k 1 ∨
        (q.val + 1) * bagSize k 1 ≤ (v j).val)).card = 0 := by
    exact Nat.eq_zero_of_le_zero (by exact_mod_cast h)
  have hnot : ¬ ((v i).val < q.val * bagSize k 1 ∨
      (q.val + 1) * bagSize k 1 ≤ (v i).val) := by
    intro hbad
    have hm : i ∈ (positionalBin U 1 q.val).filter
        (fun j ↦ (v j).val < q.val * bagSize k 1 ∨
          (q.val + 1) * bagSize k 1 ≤ (v j).val) := mem_filter.mpr ⟨hiB, hbad⟩
    rw [card_eq_zero.mp hz] at hm
    exact notMem_empty i hm
  have hlo := (Nat.le_div_iff_mul_le (bagSize_pos (by omega : 1 ≤ k))).mpr
    (show q.val * bagSize k 1 ≤ (v i).val by omega)
  have hhi := (Nat.div_lt_iff_lt_mul (bagSize_pos (by omega : 1 ≤ k))).mpr
    (show (v i).val < (q.val + 1) * bagSize k 1 by omega)
  change (v i).val / bagSize k 1 = q.val
  omega

end Paterson.Bags
