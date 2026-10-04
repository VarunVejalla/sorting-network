module

public import AKS.Paterson.StoredTransition

/-! # Full-parent preservation with actual rounded allocation

All size, fringe, and rank-balance premises are discharged from the allocation
and old stranger invariants. Other local networks in the stage may be partial.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem fringeTarget_eq_scheduledFringe (root : ℚ) (k t l : ℕ)
    (hp : (t + l) % 2 = 0) :
    fringeTarget root k t l = scheduledFringe fastParams (nativeWidth k l)
      (capacity fastParams root t l) := by
  have hc : capacity fastParams root (t + 1) (l + 1) =
      fastParams.nu * fastParams.A * capacity fastParams root t l := by
    rw [capacity_stage_succ, capacity_level_succ]
    ring
  simp only [fringeTarget, if_pos hp, subtreeTotal, scheduledFringe, nativeWidth_succ, hc]

theorem allocated_full_transition {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (nets : (c : Bag k) → ComparatorNetwork (pl.regs c).card)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w)
    (b : Bag k) (hb : 1 ≤ b.l) (hk : b.l < k)
    (hp : (t + b.parent.l) % 2 = 0)
    (hf : 0 ≤ nativeWidth k b.parent.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.parent.l))
    (hnet : nets b.parent = separatorNetwork (pl.regs b.parent).card) :
    ∀ j, 1 ≤ j →
      (b.strangers j ((pl.compare nets).exec w) ((allocationStep root t pl).regs b) : ℚ) ≤
        fastParams.mu * fastParams.delta ^ (j - 1) * capacity fastParams root (t + 1) b.l := by
  have hcP := hc.trans (root_capacity_le_level hr t b.parent.l)
  have hmin : (128 : ℚ) ≤ fastParams.minCapacity := by norm_num [fastParams]
  have hn := scheduledBag_full_bounds fastParams hf (hmin.trans hcP)
  rw [← bagTarget_eq_scheduledBag root k t b.parent.l hp, ← ha.1 b.parent] at hn
  have hdvd : 32 ∣ (pl.regs b.parent).card := by rw [ha.1 b.parent]; exact bagTarget_dvd _ _ _ _
  have hfr := fast_scheduled_fringe_bounds hf hcP
  rw [← bagTarget_eq_scheduledBag root k t b.parent.l hp,
    ← fringeTarget_eq_scheduledFringe root k t b.parent.l hp, ← ha.1 b.parent] at hfr
  have hfrN : (pl.regs b.parent).card / 32 ≤ fringeTarget root k t b.parent.l := by
    exact_mod_cast (Nat.cast_div_le (m := (pl.regs b.parent).card) (n := 32) (α := ℚ)).trans hfr
  have hhalf := (fast_scheduled_routing hf hcP).1
  rw [← bagTarget_eq_scheduledBag root k t b.parent.l hp,
    ← fringeTarget_eq_scheduledFringe root k t b.parent.l hp, ← ha.1 b.parent] at hhalf
  have hbalance := allocated_full_cohort_balance hr hc pl ha w hw hi b hb hp hf
  have hbalance' : goodCohort ((pl.regs b.parent).card / 2) ≤
      if b.x % 2 = 0 then ((pl.regs b.parent).filter (fun i ↦ (w i).val < b.hi)).card
      else ((pl.regs b.parent).filter (fun i ↦ b.lo ≤ (w i).val)).card := by
    unfold WrongSide at hbalance
    split_ifs at hbalance ⊢ <;> simpa only [not_le, not_lt] using hbalance
  have hlevel : b.l = b.parent.l + 1 := by change b.l = b.l - 1 + 1; omega
  have hratio : capacity fastParams root t b.parent.l =
      capacity fastParams root t b.l / fastParams.A := by
    rw [hlevel, capacity_level_succ]
    field_simp [show fastParams.A ≠ 0 by norm_num [fastParams]]
  have h := stored_full_interior_step pl nets w hw
    (fun c ↦ capacity fastParams root t c.l) hi
    (fun c ↦ fringeTarget root k t c.l) b hb hk hnet
    (hc.trans (root_capacity_le_level hr t b.l)) hcP
    (by change capacity fastParams root t (b.l + 1) = _; rw [capacity_level_succ])
    (by change capacity fastParams root t (b.l + 1) = _; rw [capacity_level_succ])
    hratio hdvd hn.1.le hn.2.le hfrN hhalf hbalance'
  have hleaf : ∀ c : Bag k, ¬ c.l < k →
      (pl.regs c).card / 2 ≤ fringeTarget root k t c.l := by
    intro c hck
    rw [allocation_leaf_empty hr hc pl ha c hck]
    exact Nat.zero_le _
  intro j hj
  rw [allocationStep, StoredPlacement.centralFeedRoute,
    pl.route_regs_of_pos _ _ hleaf b hb]
  simpa only [capacity_stage_succ] using h j hj

end Paterson.Bags
