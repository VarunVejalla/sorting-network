module

public import AKS.Paterson.DeepOwnership

/-! # Exact coarse-half purity of all retained deep registers -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem deepErrors_one_empty {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hceil : capacity fastParams root t 0 ≤ rootCeiling)
    (pl : StoredPlacement k) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w) :
    deepErrors pl w 1 = ∅ := by
  have hcap (l : ℕ) : capacity fastParams root t l =
      capacity fastParams root t 0 * fastParams.A ^ l := by simp [capacity]
  have hi' : Invariant fastParams
      (fun b ↦ capacity fastParams root t 0 * fastParams.A ^ b.l) pl.regs w := by
    intro b j hj
    have h := hi b j hj
    dsimp only at h ⊢
    rw [hcap b.l] at h
    exact h
  have hz (q : ℕ) (hq : 6 + 2 * q ≤ k) : levelStrangers pl w 1 (6 + 2 * q) hq = ∅ := by
    unfold levelStrangers
    apply subset_empty.mp
    intro i hi
    obtain ⟨x, _, hx⟩ := mem_biUnion.mp hi
    have h := deep_half_strangers_zero hceil (capacity_nonneg fastParams hr _ _)
      pl.regs w hi' (⟨6 + 2 * q, x.val, hq, x.isLt⟩ : Bag k)
      (by change 6 ≤ 6 + 2 * q; omega)
    have hc : ((pl.regs ⟨6 + 2 * q, x.val, hq, x.isLt⟩).filter
        (fun i ↦ (⟨6 + 2 * q, x.val, hq, x.isLt⟩ : Bag k).Strange
          (6 + 2 * q - 1 + 1) i w)).card = 0 := by
      simpa only [Bag.strangers, show 6 + 2 * q - 1 + 1 = 6 + 2 * q by omega] using h
    rw [card_eq_zero.mp hc] at hx
    exact hx
  unfold deepErrors
  apply subset_empty.mp
  intro i hi
  obtain ⟨q, _, hqi⟩ := mem_biUnion.mp hi
  split_ifs at hqi with hq
  · rw [hz q hq] at hqi
    exact hqi
  · exact hqi

end Paterson.Bags
