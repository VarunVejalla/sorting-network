module

public import AKS.Paterson.ScheduledPartialTransition

/-! # Stranger-invariant preservation for the concrete mixed stage -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem next_nonroot_capacity_ge_root {root : ℚ} (hr : 0 ≤ root) (t : ℕ)
    {k : ℕ} (b : Bag k) (hb : 1 ≤ b.l) :
    capacity fastParams root t 0 ≤ capacity fastParams root (t + 1) b.l := by
  have hl : b.l = b.parent.l + 1 := by change b.l = b.l - 1 + 1; omega
  have hfac : (1 : ℚ) ≤ fastParams.nu * fastParams.A := by norm_num [fastParams]
  calc capacity fastParams root t 0 ≤ capacity fastParams root t b.parent.l :=
      root_capacity_le_level hr t b.parent.l
    _ ≤ (fastParams.nu * fastParams.A) * capacity fastParams root t b.parent.l :=
      le_mul_of_one_le_left (capacity_nonneg fastParams hr t b.parent.l) hfac
    _ = capacity fastParams root (t + 1) b.l := by
      rw [hl, capacity_stage_succ, capacity_level_succ]
      ring

theorem allocated_partial_zero_middle {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (b : Bag k) (hb : 1 ≤ b.l) (hk : b.l < k)
    (hf : nativeWidth k b.parent.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.parent.l) ≤ 0)
    (hm : splitChildCard (pl.regs b.parent).card (fringeTarget root k t b.parent.l) = 0) :
    (allocationStep root t pl).regs b = ∅ := by
  have hlevel : b.l = b.parent.l + 1 := by change b.l = b.l - 1 + 1; omega
  have hL := allocated_partial_grand_empty pl ha b.parent (b.left hk)
    (by change b.l + 1 = b.parent.l + 2; omega) hf
  have hR := allocated_partial_grand_empty pl ha b.parent (b.right hk)
    (by change b.l + 1 = b.parent.l + 2; omega) hf
  have hleaf : ∀ c : Bag k, ¬ c.l < k →
      (pl.regs c).card / 2 ≤ fringeTarget root k t c.l := by
    intro c hck
    rw [allocation_leaf_empty hr hc pl ha c hck]
    exact Nat.zero_le _
  apply card_eq_zero.mp
  rw [allocationStep, StoredPlacement.centralFeedRoute, pl.route_bag_card _ _ hleaf b hb,
    dif_pos hk, hL, hR, card_empty, splitParentCard_zero_left, splitParentCard_zero_left, hm]

theorem scheduledCompare_preserves {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 5 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w) :
    Invariant fastParams (fun c ↦ capacity fastParams root (t + 1) c.l)
      (allocationStep root t pl).regs ((scheduledCompare hr pl ha).exec w) := by
  have hnew := allocationStep_preserves hr hk hc pl ha
  intro b j hj
  have hnn : 0 ≤ fastParams.mu * fastParams.delta ^ (j - 1) *
      capacity fastParams root (t + 1) b.l :=
    mul_nonneg (mul_nonneg fastParams.mu_pos.le (pow_nonneg fastParams.delta_pos.le _))
      (capacity_nonneg fastParams hr _ _)
  by_cases hb0 : b.l = 0
  · have heq : b = Bag.root k := by
      apply Bag.ext hb0
      have hx := b.hx
      simp only [hb0, pow_zero] at hx
      change b.x = 0
      omega
    subst b
    rw [StoredPlacement.root_strangers_zero _ _ hj]
    exact hnn
  have hb : 1 ≤ b.l := by omega
  by_cases hactive : (t + 1 + b.l) % 2 = 0
  · by_cases hbK : b.l < k
    · have hp : (t + b.parent.l) % 2 = 0 := by
        change (t + (b.l - 1)) % 2 = 0
        omega
      by_cases hf : 0 ≤ nativeWidth k b.parent.l / 4 -
          ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.parent.l)
      · apply allocated_full_transition hr hc pl ha (scheduledLocalNetwork hr pl ha) w hw hi
          b hb hbK hp hf _ j hj
        simp only [scheduledLocalNetwork, dif_pos hf]
      · have hf' := lt_of_not_ge hf
        by_cases hm : 0 < splitChildCard (pl.regs b.parent).card (fringeTarget root k t b.parent.l)
        · exact scheduled_partial_transition hr hc pl ha w hw hi b hb hbK hp hf' hm j hj
        · have hz := allocated_partial_zero_middle hr hc pl ha b hb hbK hf'.le (by omega)
          rw [hz, Bag.strangers_empty]
          exact hnn
    · have hcap := hc.trans (next_nonroot_capacity_ge_root hr t b hb)
      have hz := subtreeTotal_zero_of_deep (show k ≤ b.l by omega) hcap
      have hcard : ((allocationStep root t pl).regs b).card = 0 := by
        rw [hnew.1 b, bagTarget, if_pos hactive, hz, Nat.zero_sub]
      rw [card_eq_zero.mp hcard, Bag.strangers_empty]
      exact hnn
  · rw [allocated_inactive_empty _ hnew b hactive, Bag.strangers_empty]
    exact hnn

theorem scheduledInitial_strangerInvariant (k : ℕ) (w : Fin (2 ^ k) → Fin (2 ^ k)) :
    Invariant fastParams (fun b ↦ capacity fastParams (initialCapacity k) 0 b.l)
      (scheduledInitial k).regs w := by
  intro b j hj
  have hnn : 0 ≤ fastParams.mu * fastParams.delta ^ (j - 1) *
      capacity fastParams (initialCapacity k) 0 b.l :=
    mul_nonneg (mul_nonneg fastParams.mu_pos.le (pow_nonneg fastParams.delta_pos.le _))
      (capacity_nonneg fastParams (initialCapacity_nonneg k) _ _)
  by_cases hb : b = Bag.root k
  · subst b
    rw [StoredPlacement.root_strangers_zero _ _ hj]
    exact hnn
  · rw [scheduledInitial, centeredInitial_other_regs _ _ b hb, Bag.strangers_empty]
    exact hnn

end Paterson.Bags
