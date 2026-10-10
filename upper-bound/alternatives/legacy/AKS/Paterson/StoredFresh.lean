module

public import AKS.Paterson.StoredStage
public import AKS.Paterson.Transition

/-! # Full-bag fresh sources with separate cold storage

The local separator may be one member of a mixed full/partial parallel stage.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem stored_left_interval {k : ℕ} (pl : StoredPlacement k)
    (nets : (b : Bag k) → ComparatorNetwork (pl.regs b).card)
    (parent : Bag k) (hnet : nets parent = separatorNetwork (pl.regs parent).card)
    (hdvd : 32 ∣ (pl.regs parent).card) (f : ℕ)
    (hf : (pl.regs parent).card / 32 ≤ f)
    (hhalf : f ≤ (pl.regs parent).card / 2)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w) (lo hi r : ℕ)
    (hlo : (((pl.regs parent).filter (fun i ↦ (w i).val < lo)).card : ℝ) ≤
      (patersonMu : ℝ) * (pl.regs parent).card)
    (hr : r ≤ (pl.regs parent).card)
    (hbalance : r ≤ ((pl.regs parent).filter (fun i ↦ (w i).val < hi)).card)
    (hs : (r : ℝ) ≤ (patersonAlpha0 : ℝ) * ((pl.regs parent).card / 2 : ℕ)) :
    ((((split (pl.regs parent) f).toLeft).filter (fun i ↦
      ((pl.compare nets).exec w i).val < lo ∨ hi ≤ ((pl.compare nets).exec w i).val)).card : ℝ) ≤
      (patersonTailError : ℝ) *
        ((pl.regs parent).filter (fun i ↦ (w i).val < lo)).card +
      (((pl.regs parent).card / 2 : ℕ) - (r : ℝ) + (patersonDelta0 : ℝ) * r) := by
  let regs := pl.regs parent
  let emb := regs.orderEmbOfFin rfl
  have hhalf' : f ≤ regs.card / 2 := hhalf
  have hout :
      (((split regs f).toLeft).filter (fun i ↦
        ((pl.compare nets).exec w i).val < lo ∨ hi ≤ ((pl.compare nets).exec w i).val)).card =
      (univ.filter (fun i : Fin regs.card ↦ f ≤ i.val ∧ i.val < regs.card / 2 ∧
        (((separatorNetwork regs.card).exec (w ∘ emb) i).val < lo ∨
          hi ≤ ((separatorNetwork regs.card).exec (w ∘ emb) i).val))).card := by
    change (((univ.filter (fun i : Fin regs.card ↦
      f ≤ i.val ∧ i.val < f + (regs.card / 2 - f))).image emb).filter _).card = _
    rw [filter_image_card, filter_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    rw [pl.compare_exec_view nets parent, hnet]
    have heq : f + (regs.card / 2 - f) = regs.card / 2 := by omega
    rw [heq]
    tauto
  rw [hout, filter_regs_card] at ⊢
  rw [filter_regs_card] at hlo hbalance
  exact separator_middle_left hdvd hf (w ∘ emb) (hw.comp emb.injective)
    lo hi r hlo hr hbalance hs

theorem stored_right_interval {k : ℕ} (pl : StoredPlacement k)
    (nets : (b : Bag k) → ComparatorNetwork (pl.regs b).card)
    (parent : Bag k) (hnet : nets parent = separatorNetwork (pl.regs parent).card)
    (hdvd : 32 ∣ (pl.regs parent).card) (f : ℕ)
    (hf : (pl.regs parent).card / 32 ≤ f)
    (hhalf : f ≤ (pl.regs parent).card / 2)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w) (lo hi r : ℕ)
    (hhi : (((pl.regs parent).filter (fun i ↦ hi ≤ (w i).val)).card : ℝ) ≤
      (patersonMu : ℝ) * (pl.regs parent).card)
    (ht : lo ≤ 2 ^ k) (hr : r ≤ (pl.regs parent).card)
    (hbalance : r ≤ ((pl.regs parent).filter (fun i ↦ lo ≤ (w i).val)).card)
    (hs : (r : ℝ) ≤ (patersonAlpha0 : ℝ) * ((pl.regs parent).card / 2 : ℕ)) :
    ((((split (pl.regs parent) f).toRight).filter (fun i ↦
      ((pl.compare nets).exec w i).val < lo ∨ hi ≤ ((pl.compare nets).exec w i).val)).card : ℝ) ≤
      (patersonTailError : ℝ) *
        ((pl.regs parent).filter (fun i ↦ hi ≤ (w i).val)).card +
      (((pl.regs parent).card / 2 : ℕ) - (r : ℝ) + (patersonDelta0 : ℝ) * r) := by
  let regs := pl.regs parent
  let emb := regs.orderEmbOfFin rfl
  have hhalf' : f ≤ regs.card / 2 := hhalf
  have heven : 2 ∣ regs.card := dvd_trans (by norm_num) hdvd
  have hcard : 2 * (regs.card / 2) = regs.card := Nat.mul_div_cancel' heven
  have hout :
      (((split regs f).toRight).filter (fun i ↦
        ((pl.compare nets).exec w i).val < lo ∨ hi ≤ ((pl.compare nets).exec w i).val)).card =
      (univ.filter (fun i : Fin regs.card ↦ regs.card / 2 ≤ i.val ∧ i.val < regs.card - f ∧
        (((separatorNetwork regs.card).exec (w ∘ emb) i).val < lo ∨
          hi ≤ ((separatorNetwork regs.card).exec (w ∘ emb) i).val))).card := by
    change (((univ.filter (fun i : Fin regs.card ↦
      f + (regs.card / 2 - f) ≤ i.val ∧ i.val < f + 2 * (regs.card / 2 - f))).image
      emb).filter _).card = _
    rw [filter_image_card, filter_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    rw [pl.compare_exec_view nets parent, hnet]
    have heq : f + (regs.card / 2 - f) = regs.card / 2 := by omega
    have heq' : f + 2 * (regs.card / 2 - f) = regs.card - f := by omega
    rw [heq, heq']
    tauto
  rw [hout, filter_regs_card] at ⊢
  rw [filter_regs_card] at hhi hbalance
  exact separator_middle_right hdvd hf (w ∘ emb) (hw.comp emb.injective)
    lo hi r hhi ht hr hbalance hs

theorem stored_full_first_source {k : ℕ} (pl : StoredPlacement k)
    (nets : (c : Bag k) → ComparatorNetwork (pl.regs c).card)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (hw : Function.Injective w)
    (b : Bag k) (hl : 1 ≤ b.l) (cap : ℚ)
    (hnet : nets b.parent = separatorNetwork (pl.regs b.parent).card)
    (hc : fastParams.minCapacity ≤ cap / fastParams.A)
    (hdvd : 32 ∣ (pl.regs b.parent).card)
    (hlower : cap / fastParams.A - 128 ≤ ((pl.regs b.parent).card : ℚ))
    (hupper : ((pl.regs b.parent).card : ℚ) ≤ cap / fastParams.A + 32)
    (hold : (b.parent.strangers 1 w (pl.regs b.parent) : ℚ) ≤
      fastParams.mu * cap / fastParams.A)
    (hbalance : goodCohort ((pl.regs b.parent).card / 2) ≤
      if b.x % 2 = 0 then ((pl.regs b.parent).filter (fun i ↦ (w i).val < b.hi)).card
      else ((pl.regs b.parent).filter (fun i ↦ b.lo ≤ (w i).val)).card) (f : ℕ)
    (hf : (pl.regs b.parent).card / 32 ≤ f)
    (hhalf : f ≤ (pl.regs b.parent).card / 2) :
    (b.strangers 1 ((pl.compare nets).exec w)
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
    have hraw := stored_left_interval pl nets b.parent hnet hdvd f hf hhalf w hw b.lo b.hi r
      (by exact_mod_cast hlow.trans hsupport) hr hbalance hs
    have hrawQ :
        ((((split regs f).toLeft).filter (fun i ↦ ((pl.compare nets).exec w i).val < b.lo ∨
          b.hi ≤ ((pl.compare nets).exec w i).val)).card : ℚ) ≤
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
    have hraw := stored_right_interval pl nets b.parent hnet hdvd f hf hhalf w hw b.lo b.hi r
      (by exact_mod_cast hhigh.trans hsupport) (b.lo_lt_hi.le.trans (bag_hi_le b))
      hr hbalance hs
    have hrawQ :
        ((((split regs f).toRight).filter (fun i ↦ ((pl.compare nets).exec w i).val < b.lo ∨
          b.hi ≤ ((pl.compare nets).exec w i).val)).card : ℚ) ≤
        patersonTailError * (regs.filter (fun i ↦ b.hi ≤ (w i).val)).card +
          ((half : ℚ) - r + patersonDelta0 * r) := by exact_mod_cast hraw
    apply hrawQ.trans
    have ha := fast_fresh_arithmetic hhalfCap hrlower (by exact_mod_cast hrhalf) hhigh
    dsimp [r]
    linarith

end Paterson.Bags
