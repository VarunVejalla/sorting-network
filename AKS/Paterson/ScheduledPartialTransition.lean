module

public import AKS.Paterson.ScheduledPartialSource

/-! # Preservation at the clipped bottom boundary -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem subtreeTotal_grand_zero {root : ℚ} {k t l : ℕ}
    (hf : nativeWidth k l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t l) ≤ 0) :
    subtreeTotal root k t (l + 2) = 0 := by
  have hw : nativeWidth k (l + 2) = nativeWidth k l / 4 := by
    rw [show l + 2 = (l + 1) + 1 by omega, nativeWidth_succ, nativeWidth_succ]
    ring
  have hc : capacity fastParams root t (l + 2) =
      fastParams.A ^ 2 * capacity fastParams root t l := by
    rw [show l + 2 = (l + 1) + 1 by omega, capacity_level_succ, capacity_level_succ]
    ring
  unfold subtreeTotal scheduledSubtree idealSubtree
  rw [hw, hc, max_eq_left hf]
  exact ceil32_of_nonpos (by rfl)

theorem allocated_partial_grand_empty {root : ℚ} {k t : ℕ}
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (parent c : Bag k)
    (hl : c.l = parent.l + 2)
    (hf : nativeWidth k parent.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t parent.l) ≤ 0) :
    pl.regs c = ∅ := by
  apply card_eq_zero.mp
  rw [ha.1 c, hl]
  unfold bagTarget
  have hz := subtreeTotal_grand_zero hf
  split_ifs <;> simp only [hz, Nat.zero_sub]

theorem scheduled_partial_transition {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w)
    (b : Bag k) (hb : 1 ≤ b.l) (hk : b.l < k) (hp : (t + b.parent.l) % 2 = 0)
    (hf : nativeWidth k b.parent.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.parent.l) < 0)
    (hm : 0 < splitChildCard (pl.regs b.parent).card (fringeTarget root k t b.parent.l)) :
    ∀ j, 1 ≤ j →
      (b.strangers j ((scheduledCompare hr pl ha).exec w)
        ((allocationStep root t pl).regs b) : ℚ) ≤
        fastParams.mu * fastParams.delta ^ (j - 1) * capacity fastParams root (t + 1) b.l := by
  let f := fun c : Bag k ↦ fringeTarget root k t c.l
  let fromParent := if b.x % 2 = 0 then (split (pl.regs b.parent) (f b.parent)).toLeft
    else (split (pl.regs b.parent) (f b.parent)).toRight
  have hlevel : b.l = b.parent.l + 1 := by change b.l = b.l - 1 + 1; omega
  have hL := allocated_partial_grand_empty pl ha b.parent (b.left hk)
    (by change b.l + 1 = b.parent.l + 2; omega) hf.le
  have hR := allocated_partial_grand_empty pl ha b.parent (b.right hk)
    (by change b.l + 1 = b.parent.l + 2; omega) hf.le
  have hLP : (split (pl.regs (b.left hk)) (f (b.left hk))).toParent = ∅ := by
    apply subset_empty.mp
    simpa only [hL] using split_toParent_subset (pl.regs (b.left hk)) (f (b.left hk))
  have hRP : (split (pl.regs (b.right hk)) (f (b.right hk))).toParent = ∅ := by
    apply subset_empty.mp
    simpa only [hR] using split_toParent_subset (pl.regs (b.right hk)) (f (b.right hk))
  have hleaf : ∀ c : Bag k, ¬ c.l < k → (pl.regs c).card / 2 ≤ f c := by
    intro c hck
    rw [allocation_leaf_empty hr hc pl ha c hck]
    exact Nat.zero_le _
  have hregs : (allocationStep root t pl).regs b = fromParent := by
    rw [allocationStep, StoredPlacement.centralFeedRoute, pl.route_regs_of_pos _ _ hleaf b hb]
    simp only [stageRegs, dif_pos hk, hLP, hRP, empty_union,
      show b.l ≠ 0 by omega, ite_false]
    rfl
  have hcP := hc.trans (root_capacity_le_level hr t b.parent.l)
  have hsmall := scheduled_partial_supported hr pl ha b.parent hp hcP hf hm
  have hhalf := (fast_clipped_routing (width := nativeWidth k b.parent.l) hcP).1
  rw [← bagTarget_eq_scheduledBag root k t b.parent.l hp,
    ← fringeTarget_eq_scheduledFringe root k t b.parent.l hp, ← ha.1 b.parent] at hhalf
  have hn : 0 < (pl.regs b.parent).card := by unfold splitChildCard at hm; omega
  have hfilter : ∀ j, 1 ≤ j →
      (b.parent.strangers j ((scheduledCompare hr pl ha).exec w) fromParent : ℚ) ≤
        (patersonDelta0 + refinementTailError) * b.parent.strangers j w (pl.regs b.parent) := by
    intro j hj
    have hpow : fastParams.delta ^ (j - 1) ≤ 1 :=
      pow_le_one₀ fastParams.delta_pos.le fastParams.delta_lt_one.le
    have hold : (b.parent.strangers j w (pl.regs b.parent) : ℚ) ≤
        fastParams.mu * capacity fastParams root t b.parent.l := by
      apply (hi b.parent j hj).trans
      calc fastParams.mu * fastParams.delta ^ (j - 1) * capacity fastParams root t b.parent.l
          ≤ fastParams.mu * 1 * capacity fastParams root t b.parent.l :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow fastParams.mu_pos.le)
              (capacity_nonneg fastParams hr t b.parent.l)
        _ = _ := by ring
    have hs : (b.parent.strangers j w (pl.regs b.parent) : ℝ) ≤
        (partialSupport (root := root) (t := t) pl b.parent : ℝ) * (pl.regs b.parent).card := by
      rw [partialSupport_mul pl b.parent hn]
      exact_mod_cast hold
    have h := bagNetwork_filters (pl.regs b.parent) (allocated_even pl ha b.parent)
      (scheduledLocalNetwork hr pl ha b.parent) hsmall (f b.parent) (le_refl _) hhalf
      w ((scheduledCompare hr pl ha).exec w) hw
      (fun i ↦ pl.compare_exec_view _ b.parent w i) b.parent j hj hs
    have hsub : fromParent ⊆ (split (pl.regs b.parent) (f b.parent)).toLeft ∪
        (split (pl.regs b.parent) (f b.parent)).toRight := by
      dsimp [fromParent]
      split_ifs
      · exact subset_union_left
      · exact subset_union_right
    have hmR : (b.parent.strangers j ((scheduledCompare hr pl ha).exec w) fromParent : ℝ) ≤
        b.parent.strangers j ((scheduledCompare hr pl ha).exec w)
          ((split (pl.regs b.parent) (f b.parent)).toLeft ∪
            (split (pl.regs b.parent) (f b.parent)).toRight) := by
      exact_mod_cast Bag.strangers_mono _ _ _ hsub
    exact_mod_cast hmR.trans h
  have herr : (0 : ℚ) ≤ patersonDelta0 + refinementTailError := by
    norm_num [patersonDelta0, refinementTailError, patersonDelta2, patersonDelta3,
      patersonDelta4, patersonDelta5]
  have hratio : capacity fastParams root t b.parent.l = capacity fastParams root t b.l / fastParams.A := by
    rw [hlevel, capacity_level_succ]
    field_simp [show fastParams.A ≠ 0 by norm_num [fastParams]]
  intro j hj
  rw [hregs]
  by_cases hj2 : 2 ≤ j
  · have hshift := Bag.strangers_parent_eq b (j - 1) (by omega) hb
      ((scheduledCompare hr pl ha).exec w) fromParent
    rw [show j - 1 + 1 = j by omega] at hshift
    rw [← hshift]
    apply (hfilter (j - 1) (by omega)).trans
    apply (mul_le_mul_of_nonneg_left (hi b.parent (j - 1) (by omega)) herr).trans
    dsimp only
    rw [hratio, show j - 1 - 1 = j - 2 by omega, capacity_stage_succ]
    exact partial_tail_arithmetic (capacity_nonneg fastParams hr t b.l) hj2
  · have hj1 : j = 1 := by omega
    subst j
    simpa only [Nat.sub_self, pow_zero, mul_one] using
      scheduled_partial_first_source hr hc pl ha w hw hi b hb hp hf hm

end Paterson.Bags
