module
/-
  §7 paper-scale scramble numerics (DCS-TR-294 §7): ordinary `m ≈ 2^60`, root `m = 2^79`,
  Chernoff `hepsB` vs paper `ε_B`, and large-`f` Lemma 6.2 floors for `invariant7.epsF`.
-/

public import AKS.Chvatal.DepthSkeleton
public import AKS.Chvatal.Lemma62
public import AKS.Chvatal.Params
public import AKS.Chvatal.Theorem51Core
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

set_option maxHeartbeats 2400000

@[expose] public section

namespace Chvatal

private theorem paperOrdinaryM_cast : (paperOrdinaryM : ℝ) = (2 : ℝ) ^ 60 := by
  unfold paperOrdinaryM
  norm_num

private theorem paperRootM_cast : (paperRootM : ℝ) = (2 : ℝ) ^ 79 := by
  unfold paperRootM
  norm_num

theorem log_paperOrdinaryM : Real.log (paperOrdinaryM : ℝ) = 60 * Real.log 2 := by
  rw [paperOrdinaryM_cast]
  simpa using Real.log_pow (2 : ℝ) (by norm_num : (0 : ℝ) < 2) 60

theorem log_paperRootM : Real.log (paperRootM : ℝ) = 79 * Real.log 2 := by
  rw [paperRootM_cast]
  simpa using Real.log_pow (2 : ℝ) (by norm_num : (0 : ℝ) < 2) 79
















/-! **Lemma 6.2 `ε_F` floor at `f = 2^58` (large-`f` asymptotics)** -/


private theorem paperOrdinary_two_div_f58_le :
    (2 : ℝ) / ((2 ^ 58 - 2 : ℝ)) ≤ (2 : ℝ) / (2 ^ 57) := by norm_num


private theorem paperOrdinary_deltaF_eq : (invariant7.deltaF : ℝ) = (128 / 4095 : ℝ) := by
  unfold invariant7
  norm_num

private theorem paperOrdinary_logDenom_pos :
    (0 : ℝ) < Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) := by
  apply Real.log_pos
  have he : Real.exp 1 < (28 / 10 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hden : Real.exp 1 * (128 / 4095 : ℝ) < (28 / 10 : ℝ) * (128 / 4095 : ℝ) := by gcongr
  have hden' : (28 / 10 : ℝ) * (128 / 4095 : ℝ) < (12 / 100 : ℝ) := by norm_num
  have hlt : Real.exp 1 * (128 / 4095 : ℝ) < (12 / 100 : ℝ) := lt_trans hden hden'
  have hpos : (0 : ℝ) < Real.exp 1 * (128 / 4095 : ℝ) := by positivity
  have hfrac : (1 : ℝ) < (12 / 100 : ℝ) / (Real.exp 1 * (128 / 4095 : ℝ)) := by
    rw [one_lt_div hpos]
    exact hlt
  simpa [show (0.12 : ℝ) = (12 / 100 : ℝ) from by norm_num] using hfrac

private theorem two_pow_58_eq_paperOrdinary_div_four :
    (2 ^ 58 : ℝ) = (paperOrdinaryM : ℝ) / 4 := by
  rw [paperOrdinaryM_cast]
  norm_num

private theorem paperOrdinary_logNumer_lt :
    Real.log (3 * Real.exp 5 * (2 ^ 58 : ℝ)) < (48 : ℝ) := by
  have hf58 : Real.log ((2 ^ 58 : ℝ)) = 58 * Real.log 2 := by
    have hm : (paperOrdinaryM : ℝ) ≠ 0 := by
      exact_mod_cast (show paperOrdinaryM ≠ 0 from by decide)
    rw [two_pow_58_eq_paperOrdinary_div_four, Real.log_div hm (by norm_num : (4 : ℝ) ≠ 0), log_paperOrdinaryM]
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 from by norm_num]
      simpa using Real.log_pow (2 : ℝ) (by norm_num : (0 : ℝ) < 2) 2
    linarith
  have hln3 : Real.log (3 : ℝ) < (2 : ℝ) := by
    have h3 : (3 : ℝ) < Real.exp 2 := by
      have := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
      linarith [Real.exp_pos 2]
    have hlog : Real.log 3 < Real.log (Real.exp 2) :=
      (Real.log_lt_log_iff (by norm_num) (Real.exp_pos 2)).2 h3
    rw [Real.log_exp] at hlog
    exact hlog
  have hsplit :
      Real.log (3 * Real.exp 5 * (2 ^ 58 : ℝ)) = Real.log 3 + 5 + 58 * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp, hf58]
  have hbound : Real.log 3 + 5 + 58 * Real.log 2 < (48 : ℝ) := by
    nlinarith [Real.log_two_lt_d9, hln3]
  exact hsplit ▸ hbound

private theorem paperOrdinary_log_one_pt_two_gt_tenth : (1 / 10 : ℝ) < Real.log (12 / 10 : ℝ) := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < (2 / 10 : ℝ))
  rw [show (1 : ℝ) + 2 / 10 = (12 / 10 : ℝ) from by ring] at h
  exact lt_trans (by norm_num : (1 / 10 : ℝ) < 2 * (2 / 10) / (2 / 10 + 2)) h

private theorem paperOrdinary_logDenom_gt :
    (1 / 10 : ℝ) < Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) := by
  rw [show (0.12 : ℝ) = (12 / 100 : ℝ) from by norm_num]
  set frac : ℝ := (12 / 100 : ℝ) / (Real.exp 1 * (128 / 4095 : ℝ))
  have h12 : (12 / 10 : ℝ) < frac := by
    have hden : (12 / 10 : ℝ) * (Real.exp 1 * (128 / 4095 : ℝ)) < (12 / 100 : ℝ) := by
      have he : Real.exp 1 < (28 / 10 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have := mul_lt_mul_of_pos_right he (by norm_num : (0 : ℝ) < (128 / 4095 : ℝ))
      norm_num at this ⊢
      linarith
    rw [lt_div_iff₀ (by positivity)]
    exact hden
  have hlog12 : Real.log (12 / 10 : ℝ) < Real.log frac :=
    Real.log_lt_log (by norm_num) h12
  exact paperOrdinary_log_one_pt_two_gt_tenth.trans hlog12

private theorem paperOrdinary_epsF_lemma62_bracket_le :
    (1 : ℝ) + Real.log (3 * Real.exp 5 * (2 ^ 58 : ℝ)) /
        Real.log (0.12 / (Real.exp 1 * (invariant7.deltaF : ℝ))) ≤ (20000 : ℝ) := by
  rw [paperOrdinary_deltaF_eq]
  have hL := paperOrdinary_logDenom_gt
  have hLpos : (0 : ℝ) < Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) :=
    paperOrdinary_logDenom_pos
  have hdiv :
      1 + Real.log (3 * Real.exp 5 * (2 ^ 58 : ℝ)) /
          Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) <
        (20000 : ℝ) := by
    have hratio :
        Real.log (3 * Real.exp 5 * (2 ^ 58 : ℝ)) /
            Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) <
          (481 : ℝ) := by
      have hmul :
          Real.log (3 * Real.exp 5 * (2 ^ 58 : ℝ)) <
            (481 : ℝ) * Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) := by
        calc
          Real.log (3 * Real.exp 5 * (2 ^ 58 : ℝ)) < (48 : ℝ) := paperOrdinary_logNumer_lt
          _ < (481 : ℝ) * (1 / 10 : ℝ) := by norm_num
          _ < (481 : ℝ) * Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) :=
            mul_lt_mul_of_pos_left hL (by norm_num : (0 : ℝ) < 481)
      exact (div_lt_iff₀ hLpos).2 hmul
    linarith
  exact le_of_lt hdiv

structure PaperOrdinary_epsF_lemma62_Certificate where
  bound : epsF_lemma62_lb (2 ^ 58) (invariant7.deltaF : ℝ) ≤ (invariant7.epsF : ℝ)

theorem paperOrdinary_epsF_lemma62_lb_le_invariant7 :
    epsF_lemma62_lb (2 ^ 58) (invariant7.deltaF : ℝ) ≤ (invariant7.epsF : ℝ) := by
  rw [paperOrdinary_deltaF_eq, show (invariant7.epsF : ℝ) = (1 / 80000000 : ℝ) from by
    unfold invariant7; norm_num]
  unfold epsF_lemma62_lb
  have hbr := paperOrdinary_epsF_lemma62_bracket_le
  rw [paperOrdinary_deltaF_eq] at hbr
  have hprod : (2 : ℝ) / (2 ^ 57) * (20000 : ℝ) < (1 / 80000000 : ℝ) := by norm_num
  have hbracket_nonneg :
      (0 : ℝ) ≤
        1 + Real.log (3 * Real.exp 5 * (2 ^ 58 : ℝ)) /
          Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) := by
    have hnum : (0 : ℝ) ≤ Real.log (3 * Real.exp 5 * (2 ^ 58 : ℝ)) := by
      refine Real.log_nonneg ?_
      have hgt : (1 : ℝ) < 3 * Real.exp 5 * (2 ^ 58 : ℝ) := by
        have h58pos : (0 : ℝ) < (2 ^ 58 : ℝ) := by positivity
        have he5 : (1 : ℝ) < Real.exp 5 := by
          have := Real.add_one_lt_exp (by norm_num : (5 : ℝ) ≠ 0)
          linarith [Real.exp_pos 5]
        have hmul : (1 : ℝ) < (3 : ℝ) * Real.exp 5 := by nlinarith [he5]
        nlinarith [hmul, h58pos, Real.exp_pos 5]
      exact le_of_lt hgt
    exact add_nonneg zero_le_one (div_nonneg hnum (le_of_lt paperOrdinary_logDenom_pos))
  have hstep :
      (2 : ℝ) / ((2 ^ 58 - 2 : ℝ)) *
          (1 + Real.log (3 * Real.exp 5 * (2 ^ 58 : ℝ)) /
            Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ)))) ≤
        (1 / 80000000 : ℝ) := by
    have hcoef :
        (2 : ℝ) / ((2 ^ 58 - 2 : ℝ)) ≤ (2 : ℝ) / (2 ^ 57) := paperOrdinary_two_div_f58_le
    have hmul :
        (2 : ℝ) / ((2 ^ 58 - 2 : ℝ)) *
            (1 + Real.log (3 * Real.exp 5 * (2 ^ 58 : ℝ)) /
              Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ)))) ≤
          (2 : ℝ) / (2 ^ 57) * (20000 : ℝ) := by
      calc
        (2 : ℝ) / ((2 ^ 58 - 2 : ℝ)) *
            (1 + Real.log (3 * Real.exp 5 * (2 ^ 58 : ℝ)) /
              Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ)))) ≤
            (2 : ℝ) / (2 ^ 57) *
              (1 + Real.log (3 * Real.exp 5 * (2 ^ 58 : ℝ)) /
                Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ)))) :=
          mul_le_mul_of_nonneg_right paperOrdinary_two_div_f58_le hbracket_nonneg
        _ ≤ (2 : ℝ) / (2 ^ 57) * (20000 : ℝ) :=
          mul_le_mul_of_nonneg_left hbr (by positivity)
    exact le_trans hmul hprod.le
  exact_mod_cast hstep

def paperOrdinary_epsF_lemma62_certificate : PaperOrdinary_epsF_lemma62_Certificate :=
  ⟨paperOrdinary_epsF_lemma62_lb_le_invariant7⟩

structure PaperOrdinaryTheorem51Residual where
  epsF_lemma62 : PaperOrdinary_epsF_lemma62_Certificate

def PaperOrdinaryTheorem51Residual.discharged : PaperOrdinaryTheorem51Residual where
  epsF_lemma62 := paperOrdinary_epsF_lemma62_certificate




/-! **Fringe worst-case `ε_F` (Lemma 6.2 Chernoff) at paper ordinary geometry** -/









/-! **Lemma 6.2 cell union (`hclose`) at paper scale: `jMax ≈ 2^57`, not `≤ 48`. ** -/



/-! **Lemma 6.2 `ε_F` floor at root `f = 2^78`** -/


private theorem paperRoot_two_div_f78_le :
    (2 : ℝ) / ((2 ^ 78 - 2 : ℝ)) ≤ (2 : ℝ) / (2 ^ 77) := by norm_num

private theorem two_pow_78_eq_paperRoot_div_two :
    (2 ^ 78 : ℝ) = (paperRootM : ℝ) / 2 := by
  rw [paperRootM_cast]
  norm_num

private theorem paperRoot_logNumer_lt :
    Real.log (3 * Real.exp 5 * (2 ^ 78 : ℝ)) < (62 : ℝ) := by
  have hf78 : Real.log ((2 ^ 78 : ℝ)) = 78 * Real.log 2 := by
    have hm : (paperRootM : ℝ) ≠ 0 := by
      exact_mod_cast (show paperRootM ≠ 0 from by decide)
    rw [two_pow_78_eq_paperRoot_div_two, Real.log_div hm (by norm_num : (2 : ℝ) ≠ 0),
      log_paperRootM]
    have hlog2 : Real.log (2 : ℝ) = Real.log 2 := rfl
    linarith
  have hln3 : Real.log (3 : ℝ) < (2 : ℝ) := by
    have h3 : (3 : ℝ) < Real.exp 2 := by
      have := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
      linarith [Real.exp_pos 2]
    have hlog : Real.log 3 < Real.log (Real.exp 2) :=
      (Real.log_lt_log_iff (by norm_num) (Real.exp_pos 2)).2 h3
    rw [Real.log_exp] at hlog
    exact hlog
  have hsplit :
      Real.log (3 * Real.exp 5 * (2 ^ 78 : ℝ)) = Real.log 3 + 5 + 78 * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp, hf78]
  have hbound : Real.log 3 + 5 + 78 * Real.log 2 < (62 : ℝ) := by
    nlinarith [Real.log_two_lt_d9, hln3]
  exact hsplit ▸ hbound

private theorem paperRoot_epsF_lemma62_bracket_le :
    (1 : ℝ) + Real.log (3 * Real.exp 5 * (2 ^ 78 : ℝ)) /
        Real.log (0.12 / (Real.exp 1 * (invariant7.deltaF : ℝ))) ≤ (20000 : ℝ) := by
  rw [paperOrdinary_deltaF_eq]
  have hL := paperOrdinary_logDenom_gt
  have hLpos : (0 : ℝ) < Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) :=
    paperOrdinary_logDenom_pos
  have hdiv :
      1 + Real.log (3 * Real.exp 5 * (2 ^ 78 : ℝ)) /
          Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) <
        (20000 : ℝ) := by
    have hratio :
        Real.log (3 * Real.exp 5 * (2 ^ 78 : ℝ)) /
            Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) <
          (621 : ℝ) := by
      have hmul :
          Real.log (3 * Real.exp 5 * (2 ^ 78 : ℝ)) <
            (621 : ℝ) * Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) := by
        calc
          Real.log (3 * Real.exp 5 * (2 ^ 78 : ℝ)) < (62 : ℝ) := paperRoot_logNumer_lt
          _ < (621 : ℝ) * (1 / 10 : ℝ) := by norm_num
          _ < (621 : ℝ) * Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) :=
            mul_lt_mul_of_pos_left hL (by norm_num : (0 : ℝ) < 621)
      exact (div_lt_iff₀ hLpos).2 hmul
    linarith
  exact le_of_lt hdiv

structure PaperRoot_epsF_lemma62_Certificate where
  bound : epsF_lemma62_lb (2 ^ 78) (invariant7.deltaF : ℝ) ≤ (invariant7.epsF : ℝ)

theorem paperRoot_epsF_lemma62_lb_le_invariant7 :
    epsF_lemma62_lb (2 ^ 78) (invariant7.deltaF : ℝ) ≤ (invariant7.epsF : ℝ) := by
  rw [paperOrdinary_deltaF_eq, show (invariant7.epsF : ℝ) = (1 / 80000000 : ℝ) from by
    unfold invariant7; norm_num]
  unfold epsF_lemma62_lb
  have hbr := paperRoot_epsF_lemma62_bracket_le
  rw [paperOrdinary_deltaF_eq] at hbr
  have hprod : (2 : ℝ) / (2 ^ 77) * (20000 : ℝ) < (1 / 80000000 : ℝ) := by norm_num
  have hbracket_nonneg :
      (0 : ℝ) ≤
        1 + Real.log (3 * Real.exp 5 * (2 ^ 78 : ℝ)) /
          Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ))) := by
    have hnum : (0 : ℝ) ≤ Real.log (3 * Real.exp 5 * (2 ^ 78 : ℝ)) := by
      refine Real.log_nonneg ?_
      have hgt : (1 : ℝ) < 3 * Real.exp 5 * (2 ^ 78 : ℝ) := by
        have h78pos : (0 : ℝ) < (2 ^ 78 : ℝ) := by positivity
        have he5 : (1 : ℝ) < Real.exp 5 := by
          have := Real.add_one_lt_exp (by norm_num : (5 : ℝ) ≠ 0)
          linarith [Real.exp_pos 5]
        have hmul : (1 : ℝ) < (3 : ℝ) * Real.exp 5 := by nlinarith [he5]
        nlinarith [hmul, h78pos, Real.exp_pos 5]
      exact le_of_lt hgt
    exact add_nonneg zero_le_one (div_nonneg hnum (le_of_lt paperOrdinary_logDenom_pos))
  have hstep :
      (2 : ℝ) / ((2 ^ 78 - 2 : ℝ)) *
          (1 + Real.log (3 * Real.exp 5 * (2 ^ 78 : ℝ)) /
            Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ)))) ≤
        (1 / 80000000 : ℝ) := by
    have hmul :
        (2 : ℝ) / ((2 ^ 78 - 2 : ℝ)) *
            (1 + Real.log (3 * Real.exp 5 * (2 ^ 78 : ℝ)) /
              Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ)))) ≤
          (2 : ℝ) / (2 ^ 77) * (20000 : ℝ) := by
      calc
        (2 : ℝ) / ((2 ^ 78 - 2 : ℝ)) *
            (1 + Real.log (3 * Real.exp 5 * (2 ^ 78 : ℝ)) /
              Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ)))) ≤
            (2 : ℝ) / (2 ^ 77) *
              (1 + Real.log (3 * Real.exp 5 * (2 ^ 78 : ℝ)) /
                Real.log (0.12 / (Real.exp 1 * (128 / 4095 : ℝ)))) :=
          mul_le_mul_of_nonneg_right paperRoot_two_div_f78_le hbracket_nonneg
        _ ≤ (2 : ℝ) / (2 ^ 77) * (20000 : ℝ) :=
          mul_le_mul_of_nonneg_left hbr (by positivity)
    exact le_trans hmul hprod.le
  exact_mod_cast hstep

def paperRoot_epsF_lemma62_certificate : PaperRoot_epsF_lemma62_Certificate :=
  ⟨paperRoot_epsF_lemma62_lb_le_invariant7⟩

structure PaperRootTheorem51Residual where
  epsF_lemma62 : PaperRoot_epsF_lemma62_Certificate

def PaperRootTheorem51Residual.discharged : PaperRootTheorem51Residual where
  epsF_lemma62 := paperRoot_epsF_lemma62_certificate




end Chvatal
