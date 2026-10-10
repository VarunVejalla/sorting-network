module

public import AKS.Paterson.Stage
public import AKS.Paterson.FastParams

/-! # Fresh-stranger bounds for actual rounded bag outputs

The large-cohort balance is explicit: it must be obtained from the global
placement and storage invariant. Given that balance, these lemmas supply the
first-stranger source estimate from the concrete separator, retaining the
residual old-stranger term. They do not assume a bound on the destination bag.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem fast_fresh_arithmetic {b half cohort old : ℚ}
    (hhalf : half ≤ b / (2 * fastParams.A) + 16)
    (hcohort : patersonAlpha0 * half - 1 ≤ cohort)
    (hcohortMax : cohort ≤ half)
    (hold : old ≤ fastParams.mu * b / fastParams.A) :
    patersonTailError * old + half - cohort + patersonDelta0 * cohort ≤
      fastParams.freshCost * b + fastParams.roundingAllowance := by
  norm_num [fastParams, patersonAlpha0_eq, patersonDelta0,
    patersonTailError, patersonDelta1, patersonDelta2, patersonDelta3,
    patersonDelta4, patersonDelta5] at *
  linarith

/-- Both local contracts are certified on this same network. -/
theorem separator_middle_left {n ambient f : ℕ} (hdvd : 32 ∣ n)
    (hf : n / 32 ≤ f) (u : Fin n → Fin ambient) (hu : Function.Injective u)
    (lo hi r : ℕ)
    (hlo : ((univ.filter (fun i ↦ (u i).val < lo)).card : ℝ) ≤ (patersonMu : ℝ) * n)
    (hr : r ≤ n)
    (hbalance : r ≤ (univ.filter (fun i ↦ (u i).val < hi)).card)
    (hs : (r : ℝ) ≤ (patersonAlpha0 : ℝ) * (n / 2 : ℕ)) :
    ((univ.filter (fun i ↦ f ≤ i.val ∧ i.val < n / 2 ∧
      (((separatorNetwork n).exec u i).val < lo ∨
        hi ≤ ((separatorNetwork n).exec u i).val))).card : ℝ) ≤
      (patersonTailError : ℝ) * (univ.filter (fun i ↦ (u i).val < lo)).card +
        ((n / 2 : ℕ) - (r : ℝ) + (patersonDelta0 : ℝ) * r) := by
  have heven : 2 ∣ n := dvd_trans (by norm_num) hdvd
  obtain ⟨m, rfl⟩ := heven
  simpa using middle_left_strangers
    (supported_separator_mono_fringe (separatorNetwork_certificate_of_dvd32 _ hdvd).1 hf)
    (separatorNetwork_good m) u hu lo hi r (by simpa using hlo) hr hbalance
    (by simpa using hs)

theorem separator_middle_right {n ambient f : ℕ} (hdvd : 32 ∣ n)
    (hf : n / 32 ≤ f) (u : Fin n → Fin ambient) (hu : Function.Injective u)
    (lo hi r : ℕ)
    (hhi : ((univ.filter (fun i ↦ hi ≤ (u i).val)).card : ℝ) ≤ (patersonMu : ℝ) * n)
    (ht : lo ≤ ambient) (hr : r ≤ n)
    (hbalance : r ≤ (univ.filter (fun i ↦ lo ≤ (u i).val)).card)
    (hs : (r : ℝ) ≤ (patersonAlpha0 : ℝ) * (n / 2 : ℕ)) :
    ((univ.filter (fun i ↦ n / 2 ≤ i.val ∧ i.val < n - f ∧
      (((separatorNetwork n).exec u i).val < lo ∨
        hi ≤ ((separatorNetwork n).exec u i).val))).card : ℝ) ≤
      (patersonTailError : ℝ) * (univ.filter (fun i ↦ hi ≤ (u i).val)).card +
        ((n / 2 : ℕ) - (r : ℝ) + (patersonDelta0 : ℝ) * r) := by
  have heven : 2 ∣ n := dvd_trans (by norm_num) hdvd
  obtain ⟨m, rfl⟩ := heven
  simpa using middle_right_strangers
    (supported_separator_mono_fringe (separatorNetwork_certificate_of_dvd32 _ hdvd).1 hf)
    (separatorNetwork_good m) u hu lo hi r (by simpa using hhi) ht hr hbalance
    (by simpa using hs)

/-- Left routing viewed in local coordinates, including the actual scattered
execution of the whole parallel comparison stage. -/
theorem parallel_left_interval {k : ℕ} (pl : Placement k) (parent : Bag k)
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
      ((parallel pl).exec w i).val < lo ∨ hi ≤ ((parallel pl).exec w i).val)).card : ℝ) ≤
      (patersonTailError : ℝ) *
        ((pl.regs parent).filter (fun i ↦ (w i).val < lo)).card +
      (((pl.regs parent).card / 2 : ℕ) - (r : ℝ) + (patersonDelta0 : ℝ) * r) := by
  let regs := pl.regs parent
  let emb := regs.orderEmbOfFin rfl
  have hhalf' : f ≤ regs.card / 2 := hhalf
  have hout :
      (((split regs f).toLeft).filter (fun i ↦
        ((parallel pl).exec w i).val < lo ∨ hi ≤ ((parallel pl).exec w i).val)).card =
      (univ.filter (fun i : Fin regs.card ↦ f ≤ i.val ∧ i.val < regs.card / 2 ∧
        (((separatorNetwork regs.card).exec (w ∘ emb) i).val < lo ∨
          hi ≤ ((separatorNetwork regs.card).exec (w ∘ emb) i).val))).card := by
    change (((univ.filter (fun i : Fin regs.card ↦
      f ≤ i.val ∧ i.val < f + (regs.card / 2 - f))).image emb).filter _).card = _
    rw [filter_image_card, filter_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    rw [parallel_exec_view]
    have heq : f + (regs.card / 2 - f) = regs.card / 2 := by omega
    rw [heq]
    tauto
  rw [hout, filter_regs_card] at ⊢
  rw [filter_regs_card] at hlo hbalance
  exact separator_middle_left hdvd hf (w ∘ emb) (hw.comp emb.injective)
    lo hi r hlo hr hbalance hs

theorem parallel_right_interval {k : ℕ} (pl : Placement k) (parent : Bag k)
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
      ((parallel pl).exec w i).val < lo ∨ hi ≤ ((parallel pl).exec w i).val)).card : ℝ) ≤
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
        ((parallel pl).exec w i).val < lo ∨ hi ≤ ((parallel pl).exec w i).val)).card =
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
    rw [parallel_exec_view]
    have heq : f + (regs.card / 2 - f) = regs.card / 2 := by omega
    have heq' : f + 2 * (regs.card / 2 - f) = regs.card - f := by omega
    rw [heq, heq']
    tauto
  rw [hout, filter_regs_card] at ⊢
  rw [filter_regs_card] at hhi hbalance
  exact separator_middle_right hdvd hf (w ∘ emb) (hw.comp emb.injective)
    lo hi r hhi ht hr hbalance hs

end Paterson.Bags
