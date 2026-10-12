import AKS.Chvatal.Bulk2Count
import Mathlib.Tactic

namespace Tapered945
open Chvatal

/-- The reusable Variant-B per-cell estimate. The half-column hypothesis
must be obtained from a genuine complementary-tail witness; it is not free. -/
theorem bernstein_half_columns {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (i : Nat) (hc : totalColumnOnes c = n*i)
    (S : Finset (Fin n)) (hS : (S.card : Real) ≤ (n : Real)/2)
    (lam d E1 : Real) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hexc : (excessAbove c i : Real) ≤ (E1/2)*(m*n))
    (bad : Finset (Scramble m n))
    (hbad : ∀ σ ∈ bad,
      (i : Real)*S.card + (d/2)*(m*n) ≤ (onesInColumns c σ S : Real)) :
    (bad.card : Real) ≤
      Real.exp (-((n : Real)*m*(lam*d/2 - lam^2*(1/2+2*lam/9)*E1/2))) *
        (Fintype.card (Scramble m n) : Real) := by
  let cl : Real := lam^2*(1/2+2*lam/9)
  let V : Real := ∑ r : Fin m,
    (((monotoneRowOnes c r).card : Real)/n)*(1-((monotoneRowOnes c r).card : Real)/n)
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hcl : 0 ≤ cl := by dsimp [cl]; positivity
  have hV0 : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro r _
    apply mul_nonneg (div_nonneg (Nat.cast_nonneg _) hnR.le)
    have hd := row_density_le_one hn c r
    linarith
  have hVE : V ≤ E1*m := by
    have hv := variance_le_of_excess hn c i hc
    change V ≤ _ at hv
    refine hv.trans ?_
    rw [div_le_iff₀ hnR]
    nlinarith
  have hsV : (S.card : Real)*cl*V ≤ ((n : Real)/2)*cl*(E1*m) := by
    calc
      _ ≤ ((n : Real)/2)*cl*V :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS hcl) hV0
      _ ≤ _ := mul_le_mul_of_nonneg_left hVE (by positivity)
  have h := lemma63BernsteinBound hn c i hc S lam ((d/2)*(m*n)) hl0 hl1 bad hbad
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  change -lam*((d/2)*(m*n)) + S.card*cl*V ≤ _
  calc
    _ ≤ -lam*((d/2)*(m*n)) + ((n : Real)/2)*cl*(E1*m) := add_le_add (le_refl _) hsV
    _ = _ := by dsimp [cl]; ring

/-- Exact candidate rate certificate; a rate certificate alone proves no
uniform good-scramble existence statement. -/
theorem candidate_bernstein_rate_positive :
    (0 : Real) < (1/80 : Real)*(1/2^21)/2 -
      (1/80 : Real)^2*(1/2+2*(1/80 : Real)/9)*(38/10^6)/2 := by
  norm_num

/-- Tight logarithmic union-cost estimate, valid above the candidate floor. -/
theorem candidate_union_log_bound (m : Nat) (hm : 2^34 ≤ m) :
    Real.log (2*((m : Real)+1)) ≤
      35*Real.log 2 + ((m : Real)/2^34-1) + 1/2^34 := by
  have hM : (2 : Real)^34 ≤ m := by exact_mod_cast hm
  have hm0 : (0 : Real) < m := lt_of_lt_of_le (by positivity) hM
  have hlogm := Real.log_le_sub_one_of_pos (div_pos hm0 (by positivity : (0 : Real)<2^34))
  rw [Real.log_div hm0.ne' (by positivity), Real.log_pow] at hlogm
  have hlogp := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : Real)<m+1) hm0)
  rw [Real.log_div (by positivity) hm0.ne'] at hlogp
  have hdiv : ((m : Real)+1)/m-1 = 1/m := by field_simp; ring
  rw [hdiv] at hlogp
  have hinv : 1/(m : Real) ≤ 1/(2 : Real)^34 :=
    one_div_le_one_div_of_le (by positivity) hM
  rw [Real.log_mul (by norm_num) (by positivity)]
  push_cast at hlogm
  linarith

theorem candidate_round_one_gap (m : Nat) (hm : 2^34 ≤ m) :
    Real.log (2*((m : Real)+1)) + 1/2 ≤ (m : Real)*(38/10^6 : Real)^2 := by
  have hb := candidate_union_log_bound m hm
  have hl := Real.log_two_lt_d9
  have hM : (2 : Real)^34 ≤ m := by exact_mod_cast hm
  have hg := mul_le_mul_of_nonneg_right hM
    (show (0 : Real) ≤ (38/10^6 : Real)^2-1/2^34 by norm_num)
  norm_num at hb hl hg ⊢
  nlinarith

theorem candidate_round_two_gap (m : Nat) (hm : 2^34 ≤ m) :
    Real.log (2*((m : Real)+1)) + 1/2 ≤ (m : Real)*
      ((1/80 : Real)*(1/2^21)/2 -
        (1/80 : Real)^2*(1/2+2*(1/80 : Real)/9)*(38/10^6)/2) := by
  have hb := candidate_union_log_bound m hm
  have hl := Real.log_two_lt_d9
  have hM : (2 : Real)^34 ≤ m := by exact_mod_cast hm
  have hg := mul_le_mul_of_nonneg_right hM
    (show (0 : Real) ≤ ((1/80 : Real)*(1/2^21)/2 -
      (1/80 : Real)^2*(1/2+2*(1/80 : Real)/9)*(38/10^6)/2)-1/2^34 by norm_num)
  norm_num at hb hl hg ⊢
  nlinarith

/-- A half-unit exponent gap pays for an explicit two-orientation union. -/
theorem two_tail_union_factor_le {m n : Nat} (hm : 0 < m) (hn : 16 ≤ n)
    (K : Real) (hgap : Real.log (2*((m : Real)+1)) + 1/2 ≤ (m : Real)*K) :
    2 * ((2*((m : Real)+1))^n * Real.exp (-((n : Real)*m*K))) ≤ 1/1000 := by
  have hb : 2*((m : Real)+1) = Real.exp (Real.log (2*((m : Real)+1))) :=
    (Real.exp_log (by positivity)).symm
  have he : (2*((m : Real)+1))^n * Real.exp (-((n : Real)*m*K)) =
      Real.exp ((n : Real)*(Real.log (2*((m : Real)+1))-(m : Real)*K)) := by
    conv_lhs => lhs; rw [hb]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  have hnR : (16 : Real) ≤ n := by exact_mod_cast hn
  have hx : (n : Real)*(Real.log (2*((m : Real)+1))-(m : Real)*K) ≤ -8 := by
    have h := mul_le_mul_of_nonneg_left (show Real.log (2*((m : Real)+1))-(m : Real)*K ≤ -1/2 by linarith)
      (Nat.cast_nonneg n : (0 : Real) ≤ n)
    nlinarith
  have h2 : (2000 : Real) ≤ Real.exp 8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2.7)
      (show (2.7 : Real) ≤ Real.exp 1 by have he := Real.exp_one_gt_d9; linarith) 8
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    linarith
  have hi : Real.exp (-8) ≤ 1/2000 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have h := (Real.exp_le_exp.mpr hx).trans hi
  linarith

end Tapered945
