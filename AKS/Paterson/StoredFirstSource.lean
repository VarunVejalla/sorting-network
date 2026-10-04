module

public import AKS.Paterson.StoredSupportedFresh

/-! # Fresh strangers from a supported local network and an available cohort -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem stored_supported_first_source {k : ℕ} (pl : StoredPlacement k)
    (nets : (c : Bag k) → ComparatorNetwork (pl.regs c).card)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (b : Bag k) (hl : 1 ≤ b.l)
    (heven : 2 ∣ (pl.regs b.parent).card) (f : ℕ)
    (hhalf : f ≤ (pl.regs b.parent).card / 2)
    {support : ℝ} {err : ℚ} (herr : 0 ≤ err)
    (hsmall : IsSupportedSeparator (nets b.parent) f support err)
    (hgood : FirstContract (nets b.parent))
    (hold : (b.parent.strangers 1 w (pl.regs b.parent) : ℝ) ≤
      support * (pl.regs b.parent).card)
    (r : ℕ) (hr : r ≤ (pl.regs b.parent).card)
    (hs : (r : ℝ) ≤ (patersonAlpha0 : ℝ) * ((pl.regs b.parent).card / 2 : ℕ))
    (hbalance : r ≤ if b.x % 2 = 0 then
      ((pl.regs b.parent).filter (fun i ↦ (w i).val < b.hi)).card
      else ((pl.regs b.parent).filter (fun i ↦ b.lo ≤ (w i).val)).card) :
    (b.strangers 1 ((pl.compare nets).exec w)
      (if b.x % 2 = 0 then (split (pl.regs b.parent) f).toLeft
        else (split (pl.regs b.parent) f).toRight) : ℚ) ≤
      err * b.parent.strangers 1 w (pl.regs b.parent) +
        (((pl.regs b.parent).card / 2 : ℕ) - (r : ℚ) + patersonDelta0 * r) := by
  let regs := pl.regs b.parent
  let half := regs.card / 2
  have hpk : b.parent.l < k := by have := b.hl; change b.l - 1 < k; omega
  rw [strangers_one_eq]
  by_cases hevenB : b.x % 2 = 0
  · simp only [hevenB, ite_true] at hbalance ⊢
    have hb := Bag.parent_left_eq b hl hevenB hpk
    have hloEq : b.lo = b.parent.lo :=
      (congrArg Bag.lo hb).symm.trans (Bag.lo_left_eq b.parent hpk)
    have hlow : ((regs.filter (fun i ↦ (w i).val < b.lo)).card : ℚ) ≤
        (b.parent.strangers 1 w (pl.regs b.parent) : ℚ) := by
      rw [strangers_one_eq]
      apply Nat.cast_le.mpr
      apply card_le_card
      intro i hi
      simp only [mem_filter] at hi ⊢
      exact ⟨hi.1, Or.inl (hloEq ▸ hi.2)⟩
    have hraw := supported_left_interval pl nets b.parent heven f hsmall hgood hhalf w hw b.lo b.hi r
      (by have hlowR : ((regs.filter (fun i ↦ (w i).val < b.lo)).card : ℝ) ≤ b.parent.strangers 1 w regs := by exact_mod_cast hlow
          exact hlowR.trans hold) hr hbalance hs
    have hrawQ :
        ((((split regs f).toLeft).filter (fun i ↦ ((pl.compare nets).exec w i).val < b.lo ∨
          b.hi ≤ ((pl.compare nets).exec w i).val)).card : ℚ) ≤
        err * (regs.filter (fun i ↦ (w i).val < b.lo)).card +
          ((half : ℚ) - r + patersonDelta0 * r) := by exact_mod_cast hraw
    apply hrawQ.trans
    exact add_le_add (mul_le_mul_of_nonneg_left hlow herr) (le_refl _)
  · simp only [hevenB, ite_false] at hbalance ⊢
    have hb := Bag.parent_right_eq b hl hevenB hpk
    have hhiEq : b.hi = b.parent.hi :=
      (congrArg Bag.hi hb).symm.trans (Bag.hi_right_eq b.parent hpk)
    have hhigh : ((regs.filter (fun i ↦ b.hi ≤ (w i).val)).card : ℚ) ≤
        (b.parent.strangers 1 w (pl.regs b.parent) : ℚ) := by
      rw [strangers_one_eq]
      apply Nat.cast_le.mpr
      apply card_le_card
      intro i hi
      simp only [mem_filter] at hi ⊢
      exact ⟨hi.1, Or.inr (hhiEq ▸ hi.2)⟩
    have hraw := supported_right_interval pl nets b.parent heven f hsmall hgood hhalf w hw b.lo b.hi r
      (by have hhighR : ((regs.filter (fun i ↦ b.hi ≤ (w i).val)).card : ℝ) ≤ b.parent.strangers 1 w regs := by exact_mod_cast hhigh
          exact hhighR.trans hold) (b.lo_lt_hi.le.trans (bag_hi_le b))
      hr hbalance hs
    have hrawQ :
        ((((split regs f).toRight).filter (fun i ↦ ((pl.compare nets).exec w i).val < b.lo ∨
          b.hi ≤ ((pl.compare nets).exec w i).val)).card : ℚ) ≤
        err * (regs.filter (fun i ↦ b.hi ≤ (w i).val)).card +
          ((half : ℚ) - r + patersonDelta0 * r) := by exact_mod_cast hraw
    apply hrawQ.trans
    exact add_le_add (mul_le_mul_of_nonneg_left hhigh herr) (le_refl _)

end Paterson.Bags
