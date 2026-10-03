module

public import AKS.Paterson.Balance

/-! # Concrete interior invariant preservation

The comparison stage and outgoing pieces here are actual networks and register
sets. Old-stranger filtering and fresh-stranger bounds are derived, rather than
assumed. The remaining balance and size premises belong to the global rounded
scheduler and its cold-storage conservation proof.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem strangers_one_eq {k : ℕ} (b : Bag k) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (S : Finset (Fin (2 ^ k))) :
    b.strangers 1 w S = (S.filter (fun i ↦ (w i).val < b.lo ∨ b.hi ≤ (w i).val)).card := by
  have ha : b.ancestor 0 = b := by
    apply Bag.ext <;> simp [Bag.ancestor]
  unfold Bag.strangers
  congr 1
  ext i
  simp only [mem_filter]
  apply and_congr_right
  intro _
  simp only [Bag.Strange, Nat.reduceEqDiff, false_or, Nat.sub_self, ha]
  rw [Bag.native_iff]
  simp only [not_and_or, Nat.not_le, Nat.not_lt]

theorem bag_hi_le {k : ℕ} (b : Bag k) : b.hi ≤ 2 ^ k := by
  calc b.hi = (b.x + 1) * b.size := rfl
    _ ≤ 2 ^ b.l * b.size := Nat.mul_le_mul_right _ (by have := b.hx; omega)
    _ = 2 ^ k := Nat.mul_div_cancel' (Nat.pow_dvd_pow 2 b.hl)

def goodCohort (half : ℕ) : ℕ := ⌊patersonAlpha0 * (half : ℚ)⌋₊

theorem goodCohort_bounds (half : ℕ) :
    patersonAlpha0 * half - 1 ≤ (goodCohort half : ℚ) ∧
      (goodCohort half : ℚ) ≤ patersonAlpha0 * half ∧ goodCohort half ≤ half := by
  have hα : 0 ≤ patersonAlpha0 ∧ patersonAlpha0 ≤ 1 := by norm_num [patersonAlpha0_eq]
  have hfloor := Nat.floor_le (mul_nonneg hα.1 (Nat.cast_nonneg half))
  have hl := Nat.lt_floor_add_one (patersonAlpha0 * (half : ℚ))
  have hm : patersonAlpha0 * (half : ℚ) ≤ half :=
    mul_le_of_le_one_left (Nat.cast_nonneg half) hα.2
  exact ⟨by dsimp [goodCohort]; linarith, hfloor, by exact_mod_cast hfloor.trans hm⟩

/-- Input rank balance required by the first halver for this child. -/
def ChildBalance {k : ℕ} (pl : Placement k) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (b : Bag k) : Prop :=
  goodCohort ((pl.regs b.parent).card / 2) ≤
    if b.x % 2 = 0 then ((pl.regs b.parent).filter (fun i ↦ (w i).val < b.hi)).card
    else ((pl.regs b.parent).filter (fun i ↦ b.lo ≤ (w i).val)).card

theorem fast_support_slack {cap : ℚ} {n : ℕ}
    (hc : fastParams.minCapacity ≤ cap) (hn : cap - 128 ≤ (n : ℚ)) :
    fastParams.mu * cap ≤ patersonMu * n := by
  norm_num [fastParams, patersonMu] at *
  linarith

/-- Fresh strangers in a real parent output, using the selected large cohort
and both contracts of the same local separator. -/
theorem parallel_first_source {k : ℕ} (pl : Placement k)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (b : Bag k) (hl : 1 ≤ b.l) (cap : ℚ)
    (hc : fastParams.minCapacity ≤ cap / fastParams.A)
    (hdvd : 32 ∣ (pl.regs b.parent).card)
    (hlower : cap / fastParams.A - 128 ≤ ((pl.regs b.parent).card : ℚ))
    (hupper : ((pl.regs b.parent).card : ℚ) ≤ cap / fastParams.A + 32)
    (hold : (b.parent.strangers 1 w (pl.regs b.parent) : ℚ) ≤
      fastParams.mu * cap / fastParams.A)
    (hbalance : ChildBalance pl w b) (f : ℕ)
    (hf : (pl.regs b.parent).card / 32 ≤ f)
    (hhalf : f ≤ (pl.regs b.parent).card / 2) :
    (b.strangers 1 ((parallel pl).exec w)
      (if b.x % 2 = 0 then (split (pl.regs b.parent) f).toLeft
        else (split (pl.regs b.parent) f).toRight) : ℚ) ≤
      fastParams.freshCost * cap + fastParams.roundingAllowance := by
  let regs := pl.regs b.parent
  let half := regs.card / 2
  let r := goodCohort half
  obtain ⟨hrlower, hrupper, hrhalf⟩ := goodCohort_bounds half
  have hr : r ≤ regs.card := hrhalf.trans (Nat.div_le_self _ _)
  have hs : (r : ℝ) ≤ (patersonAlpha0 : ℝ) * half := by exact_mod_cast hrupper
  have heven : 2 ∣ regs.card := dvd_trans (by norm_num) hdvd
  have hhalfEq : 2 * half = regs.card := Nat.mul_div_cancel' heven
  have hhalfQ : 2 * (half : ℚ) = regs.card := by exact_mod_cast hhalfEq
  have hhalfCap : (half : ℚ) ≤ cap / (2 * fastParams.A) + 16 := by
    have hupper' : (regs.card : ℚ) ≤ cap / fastParams.A + 32 := hupper
    rw [show cap / (2 * fastParams.A) = cap / fastParams.A / 2 by ring]
    linarith
  have hsupport : fastParams.mu * cap / fastParams.A ≤ patersonMu * regs.card := by
    simpa only [mul_div_assoc] using fast_support_slack hc hlower
  have hpk : b.parent.l < k := by have := b.hl; change b.l - 1 < k; omega
  rw [strangers_one_eq]
  unfold ChildBalance at hbalance
  by_cases hevenB : b.x % 2 = 0
  · simp only [hevenB, ite_true] at hbalance ⊢
    have hb := Bag.parent_left_eq b hl hevenB hpk
    have hloEq : b.lo = b.parent.lo :=
      (congrArg Bag.lo hb).symm.trans (Bag.lo_left_eq b.parent hpk)
    have hlow : ((regs.filter (fun i ↦ (w i).val < b.lo)).card : ℚ) ≤
        fastParams.mu * cap / fastParams.A := by
      apply le_trans _ hold
      rw [strangers_one_eq]
      apply Nat.cast_le.mpr
      apply card_le_card
      intro i hi
      simp only [mem_filter] at hi ⊢
      exact ⟨hi.1, Or.inl (hloEq ▸ hi.2)⟩
    have hraw := parallel_left_interval pl b.parent hdvd f hf hhalf w hw b.lo b.hi r
      (by exact_mod_cast hlow.trans hsupport) hr hbalance hs
    have hrawQ :
        ((((split regs f).toLeft).filter (fun i ↦ ((parallel pl).exec w i).val < b.lo ∨
          b.hi ≤ ((parallel pl).exec w i).val)).card : ℚ) ≤
        patersonTailError * (regs.filter (fun i ↦ (w i).val < b.lo)).card +
          ((half : ℚ) - r + patersonDelta0 * r) := by exact_mod_cast hraw
    apply hrawQ.trans
    have ha := fast_fresh_arithmetic hhalfCap hrlower (by exact_mod_cast hrhalf) hlow
    dsimp [r]
    linarith
  · simp only [hevenB, ite_false] at hbalance ⊢
    have hb := Bag.parent_right_eq b hl hevenB hpk
    have hhiEq : b.hi = b.parent.hi :=
      (congrArg Bag.hi hb).symm.trans (Bag.hi_right_eq b.parent hpk)
    have hhigh : ((regs.filter (fun i ↦ b.hi ≤ (w i).val)).card : ℚ) ≤
        fastParams.mu * cap / fastParams.A := by
      apply le_trans _ hold
      rw [strangers_one_eq]
      apply Nat.cast_le.mpr
      apply card_le_card
      intro i hi
      simp only [mem_filter] at hi ⊢
      exact ⟨hi.1, Or.inr (hhiEq ▸ hi.2)⟩
    have hraw := parallel_right_interval pl b.parent hdvd f hf hhalf w hw b.lo b.hi r
      (by exact_mod_cast hhigh.trans hsupport) (b.lo_lt_hi.le.trans (bag_hi_le b))
      hr hbalance hs
    have hrawQ :
        ((((split regs f).toRight).filter (fun i ↦ ((parallel pl).exec w i).val < b.lo ∨
          b.hi ≤ ((parallel pl).exec w i).val)).card : ℚ) ≤
        patersonTailError * (regs.filter (fun i ↦ b.hi ≤ (w i).val)).card +
          ((half : ℚ) - r + patersonDelta0 * r) := by exact_mod_cast hraw
    apply hrawQ.trans
    have ha := fast_fresh_arithmetic hhalfCap hrlower (by exact_mod_cast hrhalf) hhigh
    dsimp [r]
    linarith

/-- Complete interior preservation for the actual parallel network and
register routing. The two source inequalities of `interior_step` are now
proved from the separator. Size, capacity, and input balance remain explicit
scheduler obligations, as do root and partial-level transitions. -/
theorem interior_parallel_step {k : ℕ} (pl : Placement k)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (cap : Bag k → ℚ) (hinv : Invariant fastParams cap pl.regs w)
    (f : Bag k → ℕ) (b : Bag k) (hl : 1 ≤ b.l) (hk : b.l < k)
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
    (hbalance : ChildBalance pl w b) :
    ∀ j, 1 ≤ j →
      (b.strangers j ((parallel pl).exec w)
        (stageRegs (fun c ↦ split (pl.regs c) (f c)) b) : ℚ) ≤
        fastParams.mu * fastParams.delta ^ (j - 1) * (fastParams.nu * cap b) := by
  let fromParent := if b.x % 2 = 0 then (split (pl.regs b.parent) (f b.parent)).toLeft
    else (split (pl.regs b.parent) (f b.parent)).toRight
  have hlocal := parallel_local pl
  have hsupport := fast_support_slack hcParent hlower
  have hfilter : ∀ j, 1 ≤ j →
      (b.parent.strangers j ((parallel pl).exec w) fromParent : ℚ) ≤
        fastParams.tailError * b.parent.strangers j ((parallel pl).exec w)
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
    have h := parallel_filters pl b.parent hdvd (f b.parent) hf hhalf w hw j hj
      (by exact_mod_cast hcohort.trans hsupport)
    have hsub : fromParent ⊆ (split (pl.regs b.parent) (f b.parent)).toLeft ∪
        (split (pl.regs b.parent) (f b.parent)).toRight := by
      dsimp [fromParent]
      split
      · exact subset_union_left
      · exact subset_union_right
    have hmono : (b.parent.strangers j ((parallel pl).exec w) fromParent : ℝ) ≤
        (b.parent.strangers j ((parallel pl).exec w)
          ((split (pl.regs b.parent) (f b.parent)).toLeft ∪
            (split (pl.regs b.parent) (f b.parent)).toRight) : ℝ) := by
      exact_mod_cast Bag.strangers_mono _ _ _ hsub
    have hQ : (b.parent.strangers j ((parallel pl).exec w) fromParent : ℚ) ≤
        patersonTailError * b.parent.strangers j w (pl.regs b.parent) := by
      exact_mod_cast hmono.trans h
    simpa only [local_strangers_preserved pl.regs (parallel pl) hlocal, fastParams] using hQ
  have hfirst : (b.strangers 1 ((parallel pl).exec w) fromParent : ℚ) ≤
      fastParams.freshCost * cap b + fastParams.roundingAllowance := by
    apply parallel_first_source pl w hw b hl (cap b) (hcRatio ▸ hcParent) hdvd
      (hcRatio ▸ hlower) (hcRatio ▸ hupper)
      _ hbalance (f b.parent) hf hhalf
    simpa only [hcRatio, mul_div_assoc, Nat.sub_self, pow_zero, mul_one] using
      hinv b.parent 1 (by omega)
  have h := interior_step fastParams cap pl.regs w (parallel pl) b hl hk
    (split (pl.regs (b.left hk)) (f (b.left hk))).toParent
    (split (pl.regs (b.right hk)) (f (b.right hk))).toParent fromParent
    (split_toParent_subset _ _) (split_toParent_subset _ _) hlocal hinv
    hc hcLeft hcRight hcRatio hfilter hfirst
  simpa only [stageRegs, dif_pos hk, show b.l ≠ 0 by omega, ite_false, fromParent] using h

end Paterson.Bags
