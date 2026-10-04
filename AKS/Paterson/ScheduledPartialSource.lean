module

public import AKS.Paterson.ScheduledContract

/-! # Fresh source budget for the actual scheduled partial parent -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem scheduled_partial_first_source {root : ℚ} (hr : 0 ≤ root) {k t : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w)
    (b : Bag k) (hb : 1 ≤ b.l) (hp : (t + b.parent.l) % 2 = 0)
    (hf : nativeWidth k b.parent.l / 4 -
      ancestorReserve fastParams (fastParams.A ^ 2 * capacity fastParams root t b.parent.l) < 0)
    (hm : 0 < splitChildCard (pl.regs b.parent).card (fringeTarget root k t b.parent.l)) :
    (b.strangers 1 ((scheduledCompare hr pl ha).exec w)
      (if b.x % 2 = 0 then (split (pl.regs b.parent) (fringeTarget root k t b.parent.l)).toLeft
        else (split (pl.regs b.parent) (fringeTarget root k t b.parent.l)).toRight) : ℚ) ≤
      fastParams.mu * capacity fastParams root (t + 1) b.l := by
  let half := (pl.regs b.parent).card / 2
  let available := ((pl.regs b.parent).filter (fun i ↦ ¬ WrongSide b w i)).card
  let r := availableCohort half available
  have hrank := availableCohort_bounds half available
  have hrsize : r ≤ (pl.regs b.parent).card := hrank.2.2.trans (Nat.div_le_self _ _)
  have hsmall := scheduled_partial_supported hr pl ha b.parent hp
    (hc.trans (root_capacity_le_level hr t b.parent.l)) hf hm
  have hold : (b.parent.strangers 1 w (pl.regs b.parent) : ℝ) ≤
      (partialSupport (root := root) (t := t) pl b.parent : ℝ) * (pl.regs b.parent).card := by
    have hn : 0 < (pl.regs b.parent).card := by unfold splitChildCard at hm; omega
    rw [partialSupport_mul pl b.parent hn]
    exact_mod_cast (show (b.parent.strangers 1 w (pl.regs b.parent) : ℚ) ≤
      fastParams.mu * capacity fastParams root t b.parent.l by
      simpa only [Nat.sub_self, pow_zero, mul_one] using hi b.parent 1 (by omega))
  have hhalf := (fast_clipped_routing
    (width := nativeWidth k b.parent.l)
    (hc.trans (root_capacity_le_level hr t b.parent.l))).1
  rw [← bagTarget_eq_scheduledBag root k t b.parent.l hp,
    ← fringeTarget_eq_scheduledFringe root k t b.parent.l hp, ← ha.1 b.parent] at hhalf
  have hbalance : r ≤ if b.x % 2 = 0 then
      ((pl.regs b.parent).filter (fun i ↦ (w i).val < b.hi)).card else
      ((pl.regs b.parent).filter (fun i ↦ b.lo ≤ (w i).val)).card := by
    have h := hrank.1
    dsimp [r, available] at h ⊢
    unfold WrongSide at h ⊢
    split_ifs at h ⊢ <;> simpa only [not_le, not_lt] using h
  have herr : (0 : ℚ) ≤ patersonDelta0 + refinementTailError := by
    norm_num [patersonDelta0, refinementTailError, patersonDelta2, patersonDelta3,
      patersonDelta4, patersonDelta5]
  have hraw := stored_supported_first_source pl (scheduledLocalNetwork hr pl ha)
    w hw b hb (allocated_even pl ha b.parent) (fringeTarget root k t b.parent.l) hhalf
    herr (by simpa only [Rat.cast_add] using hsmall)
    (scheduledLocalNetwork_firstContract hr pl ha b.parent) hold r hrsize
    (by exact_mod_cast hrank.2.1) hbalance
  exact hraw.trans (allocated_partial_fresh_budget hr hc pl ha w hw hi b hb hp hf.le)

end Paterson.Bags
