module

public import AKS.Paterson.StoredFresh
public import AKS.Paterson.AllocatedBalance

/-! # Full-parent invariant preservation in mixed storage-aware stages -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem stored_full_interior_step {k : ℕ} (pl : StoredPlacement k)
    (nets : (c : Bag k) → ComparatorNetwork (pl.regs c).card)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (cap : Bag k → ℚ) (hinv : Invariant fastParams cap pl.regs w)
    (f : Bag k → ℕ) (b : Bag k) (hl : 1 ≤ b.l) (hk : b.l < k)
    (hnet : nets b.parent = separatorNetwork (pl.regs b.parent).card)
    (hc : fastParams.minCapacity ≤ cap b)
    (hcParent : fastParams.minCapacity ≤ cap b.parent)
    (hcLeft : cap (b.left hk) = fastParams.A * cap b)
    (hcRight : cap (b.right hk) = fastParams.A * cap b)
    (hcRatio : cap b.parent = cap b / fastParams.A)
    (hdvd : 32 ∣ (pl.regs b.parent).card)
    (hlower : cap b.parent - 128 ≤ ((pl.regs b.parent).card : ℚ))
    (hupper : ((pl.regs b.parent).card : ℚ) ≤ cap b.parent + 32)
    (hf : (pl.regs b.parent).card / 32 ≤ f b.parent)
    (hhalf : f b.parent ≤ (pl.regs b.parent).card / 2)
    (hbalance : goodCohort ((pl.regs b.parent).card / 2) ≤
      if b.x % 2 = 0 then ((pl.regs b.parent).filter (fun i ↦ (w i).val < b.hi)).card
      else ((pl.regs b.parent).filter (fun i ↦ b.lo ≤ (w i).val)).card) :
    ∀ j, 1 ≤ j →
      (b.strangers j ((pl.compare nets).exec w)
        (stageRegs (fun c ↦ split (pl.regs c) (f c)) b) : ℚ) ≤
        fastParams.mu * fastParams.delta ^ (j - 1) * (fastParams.nu * cap b) := by
  let fromParent := if b.x % 2 = 0 then (split (pl.regs b.parent) (f b.parent)).toLeft
    else (split (pl.regs b.parent) (f b.parent)).toRight
  have hlocal := pl.compare_local nets
  have hsupport := fast_support_slack hcParent hlower
  have hfilter : ∀ j, 1 ≤ j →
      (b.parent.strangers j ((pl.compare nets).exec w) fromParent : ℚ) ≤
        fastParams.tailError * b.parent.strangers j ((pl.compare nets).exec w)
          (pl.regs b.parent) := by
    intro j hj
    have hpow : fastParams.delta ^ (j - 1) ≤ 1 :=
      pow_le_one₀ fastParams.delta_pos.le fastParams.delta_lt_one.le
    have hcohort : (b.parent.strangers j w (pl.regs b.parent) : ℚ) ≤
        fastParams.mu * cap b.parent := by
      apply (hinv b.parent j hj).trans
      calc fastParams.mu * fastParams.delta ^ (j - 1) * cap b.parent
          ≤ fastParams.mu * 1 * cap b.parent :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow fastParams.mu_pos.le)
              (fastParams.minCapacity_pos.le.trans hcParent)
        _ = fastParams.mu * cap b.parent := by ring
    have h := bagSeparator_filters (pl.regs b.parent) hdvd (f b.parent) hf hhalf w
      ((pl.compare nets).exec w) hw
      (fun i ↦ by rw [pl.compare_exec_view nets b.parent, hnet]) b.parent j hj
      (by exact_mod_cast hcohort.trans hsupport)
    have hsub : fromParent ⊆ (split (pl.regs b.parent) (f b.parent)).toLeft ∪
        (split (pl.regs b.parent) (f b.parent)).toRight := by
      dsimp [fromParent]
      split
      · exact subset_union_left
      · exact subset_union_right
    have hmono : (b.parent.strangers j ((pl.compare nets).exec w) fromParent : ℝ) ≤
        (b.parent.strangers j ((pl.compare nets).exec w)
          ((split (pl.regs b.parent) (f b.parent)).toLeft ∪
            (split (pl.regs b.parent) (f b.parent)).toRight) : ℝ) := by
      exact_mod_cast Bag.strangers_mono _ _ _ hsub
    have hQ : (b.parent.strangers j ((pl.compare nets).exec w) fromParent : ℚ) ≤
        patersonTailError * b.parent.strangers j w (pl.regs b.parent) := by
      exact_mod_cast hmono.trans h
    simpa only [local_strangers_preserved pl.regs (pl.compare nets) hlocal, fastParams] using hQ
  have hfirst : (b.strangers 1 ((pl.compare nets).exec w) fromParent : ℚ) ≤
      fastParams.freshCost * cap b + fastParams.roundingAllowance := by
    apply stored_full_first_source pl nets w hw b hl (cap b) hnet (hcRatio ▸ hcParent) hdvd
      (hcRatio ▸ hlower) (hcRatio ▸ hupper)
      _ hbalance (f b.parent) hf hhalf
    simpa only [hcRatio, mul_div_assoc, Nat.sub_self, pow_zero, mul_one] using
      hinv b.parent 1 (by omega)
  have h := interior_step fastParams cap pl.regs w (pl.compare nets) b hl hk
    (split (pl.regs (b.left hk)) (f (b.left hk))).toParent
    (split (pl.regs (b.right hk)) (f (b.right hk))).toParent fromParent
    (split_toParent_subset _ _) (split_toParent_subset _ _) hlocal hinv
    hc hcLeft hcRight hcRatio hfilter hfirst
  simpa only [stageRegs, dif_pos hk, show b.l ≠ 0 by omega, ite_false, fromParent] using h

end Paterson.Bags
