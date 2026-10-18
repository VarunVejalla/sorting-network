import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.unnecessarySeqFocus false

/-!
An abstract rank-ramp obstruction under mass conservation and centered
variance contraction. This file isolates the per-cut inequality used by the
finite packet screens from their schedule-specific matrix arguments.
-/

open Finset BigOperators

namespace Chvatal.PacketAlignment

theorem selected_sum_centered_le {n h : Nat} (hn : 0 < n) (hh : h ≤ n)
    (H : Finset (Fin n)) (hH : H.card = h) (x : Fin n → Real)
    (gamma : Real) (hgamma0 : 0 ≤ gamma)
    (hsum : (∑ i, x i) = h)
    (hvariance : (∑ i, (x i - (h : Real) / n) ^ 2) ≤
      gamma ^ 2 * ((h : Real) * ((n - h : Nat) : Real) / n)) :
    (∑ i ∈ H, x i) ≤ (h : Real) ^ 2 / n +
      gamma * ((h : Real) * ((n - h : Nat) : Real) / n) := by
  classical
  let mu : Real := (h : Real) / n
  let sigma : Real := (h : Real) * ((n - h : Nat) : Real) / n
  let f : Fin n → Real := fun i => if i ∈ H then 1 - mu else -mu
  let g : Fin n → Real := fun i => x i - mu
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hsumG : (∑ i, g i) = 0 := by
    simp [g, mu, Finset.sum_sub_distrib, hsum, Fintype.card_fin]
    field_simp [hnR.ne']
    ring
  have hpoint (i : Fin n) :
      f i ^ 2 = (if i ∈ H then 1 else 0) * (1 - 2 * mu) + mu ^ 2 := by
    by_cases hi : i ∈ H <;> simp [f, hi] <;> ring
  have hnorm : (∑ i, f i ^ 2) = sigma := by
    calc
      (∑ i, f i ^ 2) =
          ∑ i, ((if i ∈ H then 1 else 0) * (1 - 2 * mu) + mu ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hpoint i
      _ = (H.card : Real) * (1 - 2 * mu) + (n : Real) * mu ^ 2 := by
        simp [Finset.sum_add_distrib, Fintype.card_fin]
        ring
      _ = sigma := by
        simp [sigma, mu, hH]
        rw [Nat.cast_sub hh]
        field_simp
        ring
  have hdot : (∑ i, f i * g i) = ∑ i ∈ H, g i := by
    calc
      (∑ i, f i * g i) =
          ∑ i, ((if i ∈ H then 1 else 0) * g i - mu * g i) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ H <;> simp [f, g, hi] <;> ring
      _ = (∑ i, if i ∈ H then g i else 0) - mu * (∑ i, g i) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ H <;> simp [hi]
      _ = ∑ i ∈ H, g i := by
        simp [Finset.sum_ite_mem, hsumG]
  have hvariance' : (∑ i, g i ^ 2) ≤ gamma ^ 2 * sigma := by
    simpa [g, mu, sigma] using hvariance
  have hsigma0 : 0 ≤ sigma := by
    dsimp [sigma]
    positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n)) f g
  have hresSq : (∑ i ∈ H, g i) ^ 2 ≤ (gamma * sigma) ^ 2 := by
    rw [← hdot]
    calc
      (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * (∑ i, g i ^ 2) := hcs
      _ ≤ sigma * (gamma ^ 2 * sigma) := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left hvariance' hsigma0
      _ = (gamma * sigma) ^ 2 := by ring
  have hres : (∑ i ∈ H, g i) ≤ gamma * sigma := by
    by_contra hnot
    have hlt : gamma * sigma < ∑ i ∈ H, g i := lt_of_not_ge hnot
    nlinarith [hresSq, mul_nonneg hgamma0 hsigma0]
  calc
    (∑ i ∈ H, x i) = (∑ i ∈ H, (g i + mu)) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [g]
      ring
    _ = (∑ i ∈ H, g i) + (H.card : Real) * mu := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ gamma * sigma + (H.card : Real) * mu := by nlinarith [hres]
    _ = (h : Real) ^ 2 / n + gamma *
        ((h : Real) * ((n - h : Nat) : Real) / n) := by
      rw [hH]
      simp only [mu, sigma]
      rw [Nat.cast_sub hh]
      field_simp [hnR.ne']
      ring

theorem rank_step_l1_error_lower_bound {n h : Nat} (hn : 0 < n) (hh : h ≤ n)
    (H : Finset (Fin n)) (hH : H.card = h) (x : Fin n → Real)
    (gamma : Real) (hgamma0 : 0 ≤ gamma)
    (hsum : (∑ i, x i) = h)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hvariance : (∑ i, (x i - (h : Real) / n) ^ 2) ≤
      gamma ^ 2 * ((h : Real) * ((n - h : Nat) : Real) / n)) :
    2 * (1 - gamma) * ((h : Real) * ((n - h : Nat) : Real) / n) ≤
      ∑ i, |x i - if i ∈ H then (1 : Real) else 0| := by
  classical
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hselected := selected_sum_centered_le hn hh H hH x gamma hgamma0 hsum hvariance
  have habs :
      (∑ i, |x i - if i ∈ H then (1 : Real) else 0|) =
        2 * (h : Real) - 2 * (∑ i ∈ H, x i) := by
    have hpoint (i : Fin n) :
        |x i - if i ∈ H then (1 : Real) else 0| =
          if i ∈ H then 1 - x i else x i := by
      by_cases hi : i ∈ H
      · simp only [if_pos hi]
        rw [abs_of_nonpos (by linarith [hx1 i])]
        ring
      · simp only [if_neg hi]
        simp only [sub_zero]
        exact abs_of_nonneg (hx0 i)
    have hfilter : Finset.univ.filter (fun i : Fin n => i ∈ H) = H := by
      ext i
      simp
    have hfilterNot : Finset.univ.filter (fun i : Fin n => i ∉ H) = Hᶜ := by
      ext i
      simp
    have hcomp : (∑ i ∈ Hᶜ, x i) = (h : Real) - (∑ i ∈ H, x i) := by
      have heq := Finset.sum_compl_add_sum H (fun i => x i)
      rw [hsum] at heq
      linarith
    have hsub : (∑ i ∈ H, (1 - x i)) = (h : Real) - (∑ i ∈ H, x i) := by
      rw [Finset.sum_sub_distrib]
      simp [hH]
    calc
      _ = ∑ i, (if i ∈ H then 1 - x i else x i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hpoint i
      _ = (∑ i ∈ H, (1 - x i)) + (∑ i ∈ Hᶜ, x i) := by
        rw [Finset.sum_ite]
        simp only [hfilter, hfilterNot]
      _ = 2 * (h : Real) - 2 * (∑ i ∈ H, x i) := by rw [hsub, hcomp]; ring
  have hsigma : (h : Real) - (h : Real) ^ 2 / n =
      (h : Real) * ((n - h : Nat) : Real) / n := by
    rw [Nat.cast_sub hh]
    field_simp [hnR.ne']
  rw [habs]
  nlinarith [hselected, hsigma]

end Chvatal.PacketAlignment

#print axioms Chvatal.PacketAlignment.selected_sum_centered_le
#print axioms Chvatal.PacketAlignment.rank_step_l1_error_lower_bound
