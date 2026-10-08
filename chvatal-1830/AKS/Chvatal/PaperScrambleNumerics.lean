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

private theorem sqrt59_comm :
    Real.sqrt (1 + Real.log 2 * 59) = Real.sqrt (1 + 59 * Real.log 2) := by
  congr 1
  ring

private theorem sqrt79_comm :
    Real.sqrt (1 + Real.log 2 * 79) = Real.sqrt (1 + 79 * Real.log 2) := by
  congr 1
  ring

theorem chernoff_hepsB_paperOrdinaryM_le_paperOrdinaryEpsB :
    chernoff_hepsB paperOrdinaryM ≤ paperOrdinaryEpsB := by
  unfold chernoff_hepsB paperOrdinaryEpsB
  rw [log_paperOrdinaryM, paperOrdinaryM_cast]
  have h59 : 2 * (1 + 60 * Real.log 2) ≤ 4 * (1 + 59 * Real.log 2) := by
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hinside :
      2 * (1 + 60 * Real.log 2) / (2 : ℝ) ^ 60 ≤
        (Real.sqrt (1 + 59 * Real.log 2) / 2 ^ 29) ^ 2 := by
    have hrearr :
        4 * (1 + 59 * Real.log 2) / (2 : ℝ) ^ 60 =
          (Real.sqrt (1 + 59 * Real.log 2) / 2 ^ 29) ^ 2 := by
      have h29 : (0 : ℝ) < (2 ^ 29 : ℝ) := by positivity
      have hsq : (Real.sqrt (1 + 59 * Real.log 2)) ^ 2 = 1 + 59 * Real.log 2 :=
        Real.sq_sqrt (by positivity)
      field_simp [h29.ne']
      ring_nf
      rw [sqrt59_comm, hsq]
      ring
    linarith
  have hnn : (0 : ℝ) ≤ 2 * (1 + 60 * Real.log 2) / (2 : ℝ) ^ 60 := by positivity
  have hsqrt := Real.sqrt_le_sqrt hinside
  have hside : (0 : ℝ) ≤ Real.sqrt (1 + 59 * Real.log 2) / 2 ^ 29 := by positivity
  rwa [Real.sqrt_sq hside] at hsqrt

theorem chernoff_hepsB_paperRootM_le_paperRootEpsB :
    chernoff_hepsB paperRootM ≤ paperRootEpsB := by
  unfold chernoff_hepsB paperRootEpsB
  rw [log_paperRootM, paperRootM_cast]
  have hinside :
      2 * (1 + 79 * Real.log 2) / (2 : ℝ) ^ 79 =
        (Real.sqrt (1 + 79 * Real.log 2) / 2 ^ 39) ^ 2 := by
    have h39 : (0 : ℝ) < (2 ^ 39 : ℝ) := by positivity
    have hsq : (Real.sqrt (1 + 79 * Real.log 2)) ^ 2 = 1 + 79 * Real.log 2 :=
      Real.sq_sqrt (by positivity)
    field_simp [h39.ne']
    ring_nf
    rw [sqrt79_comm, hsq]
    ring
  have hnn : (0 : ℝ) ≤ 2 * (1 + 79 * Real.log 2) / (2 : ℝ) ^ 79 := by positivity
  have hsqrt := Real.sqrt_le_sqrt (le_of_eq hinside)
  have hside : (0 : ℝ) ≤ Real.sqrt (1 + 79 * Real.log 2) / 2 ^ 39 := by positivity
  rwa [Real.sqrt_sq hside] at hsqrt

theorem invariant7_epsB_lt_paperOrdinaryEpsB :
    (invariant7.epsB : ℝ) < paperOrdinaryEpsB := by
  unfold paperOrdinaryEpsB invariant7
  have hsqrt : (1 : ℝ) < Real.sqrt (1 + 59 * Real.log 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have h29 : (0 : ℝ) < (2 ^ 29 : ℝ) := by positivity
  have hmid : (1 / 1000000000000000 : ℝ) < Real.sqrt (1 + 59 * Real.log 2) / 2 ^ 29 :=
    lt_of_lt_of_le (by norm_num) (div_le_div_of_nonneg_right (le_of_lt hsqrt) h29.le)
  linarith

theorem chernoff_hepsB_paperOrdinaryM_gt_invariant7_epsB :
    (invariant7.epsB : ℝ) < chernoff_hepsB paperOrdinaryM := by
  have hlo : (1 / 1000000000000000 : ℝ) < chernoff_hepsB paperOrdinaryM := by
    unfold chernoff_hepsB
    rw [log_paperOrdinaryM, paperOrdinaryM_cast]
    have hgt : (1 / 1000000000000000 : ℝ) ^ 2 < (2 : ℝ) / (2 : ℝ) ^ 60 := by
      have hpow : (2 : ℝ) ^ 60 = (1152921504606846976 : ℝ) := by norm_num
      rw [hpow]
      norm_num
    have hlo : (2 : ℝ) < 2 * (1 + 60 * Real.log 2) := by
      have h1 : (1 : ℝ) < 1 + 60 * Real.log 2 := by
        linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      nlinarith
    have hstep : (2 : ℝ) / (2 : ℝ) ^ 60 < 2 * (1 + 60 * Real.log 2) / (2 : ℝ) ^ 60 :=
      div_lt_div_of_pos_right hlo (by positivity)
    have hinside : (1 / 1000000000000000 : ℝ) ^ 2 <
        2 * (1 + 60 * Real.log 2) / (2 : ℝ) ^ 60 :=
      lt_trans hgt hstep
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 1000000000000000)).mpr hinside
  exact lt_of_le_of_lt (le_of_eq (by norm_num [invariant7])) hlo

theorem not_chernoff_hepsB_le_invariant7_at_paperOrdinaryM :
    ¬ chernoff_hepsB paperOrdinaryM ≤ (invariant7.epsB : ℝ) :=
  not_le_of_gt chernoff_hepsB_paperOrdinaryM_gt_invariant7_epsB

theorem paperOrdinaryGeometry_f : paperOrdinaryGeometry.f = 2 ^ 58 := rfl

theorem paperOrdinaryGeometry_m : paperOrdinaryGeometry.m = paperOrdinaryM := rfl

theorem paperOrdinaryGeometry_n : paperOrdinaryGeometry.n = 16 := rfl

theorem paperOrdinary_hepsF_ge_4e :
    (4 * Real.exp 1) / (paperOrdinaryGeometry.f : ℝ) ≤ (invariant7.epsF : ℝ) := by
  rw [paperOrdinaryGeometry_f]
  unfold invariant7
  have h4e : (4 * Real.exp 1) < (11 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hpow58 : (80000000 : ℝ) * 11 ≤ (2 ^ 58 : ℝ) := by
    exact_mod_cast (show (80000000 : ℕ) * 11 ≤ 2 ^ 58 by decide)
  have hpos : (0 : ℝ) < (2 ^ 58 : ℝ) := by positivity
  have h11 : (11 : ℝ) / (2 ^ 58) ≤ (1 / 80000000 : ℝ) := by
    rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 80000000)]
    linarith
  have hlt : (4 * Real.exp 1) / (2 ^ 58 : ℝ) < (11 : ℝ) / (2 ^ 58) :=
    div_lt_div_of_pos_right h4e hpos
  linarith

theorem paperRootGeometry_f : paperRootGeometry.f = 2 ^ 78 := rfl

theorem paperRootGeometry_m : paperRootGeometry.m = paperRootM := rfl

theorem paperRootGeometry_n : paperRootGeometry.n = 16 := rfl

theorem paperRoot_hepsF_ge_4e :
    (4 * Real.exp 1) / (paperRootGeometry.f : ℝ) ≤ (invariant7.epsF : ℝ) := by
  rw [paperRootGeometry_f, show (invariant7.epsF : ℝ) = (1 / 80000000 : ℝ) from by
    unfold invariant7; norm_num]
  have h4e : (4 * Real.exp 1) < (12 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hpow : ((2 ^ 78 : Nat) : ℝ) = (2 : ℝ) ^ 78 := by norm_cast
  rw [hpow]
  have hdiv : (4 * Real.exp 1) / ((2 : ℝ) ^ 78) < (12 : ℝ) / ((2 : ℝ) ^ 78) :=
    div_lt_div_of_pos_right h4e (by positivity)
  have hsmall : (12 : ℝ) / ((2 : ℝ) ^ 78) < (1 / 80000000 : ℝ) := by
    rw [← hpow]; norm_num
  exact le_of_lt (hdiv.trans hsmall)

/-! **Lemma 6.2 `ε_F` floor at `f = 2^58` (large-`f` asymptotics)** -/

private theorem paperOrdinary_f58_sub_two_ge_2p57 : 2 ^ 57 ≤ 2 ^ 58 - 2 := by decide

private theorem paperOrdinary_two_div_f58_le :
    (2 : ℝ) / ((2 ^ 58 - 2 : ℝ)) ≤ (2 : ℝ) / (2 ^ 57) := by norm_num

private theorem paperOrdinary_two_div_2p57_lt :
    (2 : ℝ) / (2 ^ 57) < (1 / 10 ^ 14 : ℝ) := by norm_num

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

noncomputable def theorem51Params_paperOrdinaryGeometry (C : PaperOrdinaryTheorem51Residual) :
    Theorem51Params paperOrdinaryGeometry :=
  theorem51Params_paperOrdinary paperOrdinaryGeometry
    (by
      rw [paperOrdinaryGeometry_m]
      exact chernoff_hepsB_paperOrdinaryM_le_paperOrdinaryEpsB)
    paperOrdinary_hepsF_ge_4e
    C.epsF_lemma62.bound

theorem theorem51Params_paperOrdinaryGeometry_chernoff :
    Real.sqrt (2 * (1 + Real.log paperOrdinaryGeometry.m) / paperOrdinaryGeometry.m) ≤
      paperOrdinaryEpsB := by
  rw [paperOrdinaryGeometry_m]
  exact chernoff_hepsB_paperOrdinaryM_le_paperOrdinaryEpsB

noncomputable def theorem51Params_paperOrdinaryGeometry_discharged :
    Theorem51Params paperOrdinaryGeometry :=
  theorem51Params_paperOrdinaryGeometry PaperOrdinaryTheorem51Residual.discharged

/-! **Fringe worst-case `ε_F` (Lemma 6.2 Chernoff) at paper ordinary geometry** -/

noncomputable def paperOrdinary_hepsWorst : ℝ :=
  Real.sqrt
    ((1 + Real.log (paperOrdinaryM : ℝ)) * 16 * (7 * 2 ^ 57) * 16 / 2)

theorem fringeRowCount_paperOrdinary :
    fringeRowCount paperOrdinaryM (2 ^ 58) (by decide : Even (2 ^ 58)) = 7 * 2 ^ 57 := by
  rw [fringeRowCount_eq, show paperOrdinaryM - (2 ^ 58) / 2 = 7 * 2 ^ 57 from by decide]

private theorem paperOrdinary_hepsWorst_inside_gt :
    (896 : ℝ) * (2 ^ 57 : ℝ) <
      (1 + Real.log (paperOrdinaryM : ℝ)) * 16 * (7 * 2 ^ 57) * 16 / 2 := by
  rw [log_paperOrdinaryM]
  have h1 : (1 : ℝ) < 1 + 60 * Real.log 2 := by
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hEq :
      (1 + 60 * Real.log 2) * 16 * (7 * 2 ^ 57) * 16 / 2 =
        (1 + 60 * Real.log 2) * ((896 : ℝ) * (2 ^ 57 : ℝ)) := by ring
  rw [hEq]
  have hpos : (0 : ℝ) < (896 * 2 ^ 57 : ℝ) := by norm_num
  simpa [one_mul] using mul_lt_mul_of_pos_right h1 hpos

theorem paperOrdinary_hepsWorst_gt_125 : (125 : ℝ) < paperOrdinary_hepsWorst := by
  unfold paperOrdinary_hepsWorst
  have hinside := paperOrdinary_hepsWorst_inside_gt
  have h125 : (125 : ℝ) ^ 2 < (896 : ℝ) * (2 ^ 57 : ℝ) := by
    have h57 : (2 ^ 57 : ℝ) = (144115188075855872 : ℝ) := by norm_num
    rw [h57]
    norm_num
  have h125' : (125 : ℝ) < Real.sqrt ((896 : ℝ) * (2 ^ 57 : ℝ)) := by
    rw [Real.lt_sqrt (by norm_num)]
    exact h125
  exact h125'.trans (Real.sqrt_lt_sqrt (by positivity) hinside)

theorem paperOrdinary_hepsWorst_gt_ten : (10 : ℝ) < paperOrdinary_hepsWorst := by
  unfold paperOrdinary_hepsWorst
  have hinside := paperOrdinary_hepsWorst_inside_gt
  have h896 : (10 : ℝ) ^ 2 < (896 : ℝ) * (2 ^ 57 : ℝ) := by
    have h57 : (2 ^ 57 : ℝ) = (144115188075855872 : ℝ) := by norm_num
    rw [h57]
    norm_num
  have h10 : (10 : ℝ) < Real.sqrt ((896 : ℝ) * (2 ^ 57 : ℝ)) := by
    rw [Real.lt_sqrt (by norm_num)]
    exact h896
  exact h10.trans (Real.sqrt_lt_sqrt (by positivity) hinside)

theorem invariant7_epsF_lt_paperOrdinary_hepsWorst :
    (invariant7.epsF : ℝ) < paperOrdinary_hepsWorst := by
  have heps : (invariant7.epsF : ℝ) < (1 : ℝ) := by
    unfold invariant7
    norm_num
  linarith [paperOrdinary_hepsWorst_gt_ten]

theorem not_paperOrdinary_hepsWorst_le_invariant7_epsF :
    ¬ paperOrdinary_hepsWorst ≤ (invariant7.epsF : ℝ) :=
  not_le_of_gt invariant7_epsF_lt_paperOrdinary_hepsWorst

/-- Numeric scale: fringe worst-case `ε_F` at `(m,f) = (2^60,2^58)` is `≈ 7.4×10^10`, not `1.25×10⁻⁸`. -/
theorem paperOrdinary_hepsWorst_gt_invariant7_epsF_by_factor :
    (10 ^ 10 : ℝ) * (invariant7.epsF : ℝ) < paperOrdinary_hepsWorst := by
  have heps : (invariant7.epsF : ℝ) = (1 / 80000000 : ℝ) := by
    unfold invariant7
    norm_num
  rw [heps, show (10 ^ 10 : ℝ) * (1 / 80000000 : ℝ) = (125 : ℝ) from by norm_num]
  exact paperOrdinary_hepsWorst_gt_125

/-! **Lemma 6.2 cell union (`hclose`) at paper scale: `jMax ≈ 2^57`, not `≤ 48`. ** -/

theorem paperOrdinary_lemma62_jMax_gt_48 :
    (48 : ℝ) < (lemma62_jMax (invariant7.deltaF : ℝ) (2 ^ 58) 16 : ℝ) := by
  have hfloor :
      lemma62_jMax (invariant7.deltaF : ℝ) (2 ^ 58) 16 =
        Nat.floor ((128 : ℝ) / 4095 * (2 ^ 62 : ℝ)) := by
    dsimp [lemma62_jMax, invariant7]
    norm_num
  have hgt : (48 : ℝ) < (128 : ℝ) / 4095 * (2 ^ 62 : ℝ) := by norm_num
  rw [hfloor]
  have h49 : (49 : ℝ) ≤ (128 : ℝ) / 4095 * (2 ^ 62 : ℝ) := by norm_num
  have h49' : (49 : ℕ) ≤ Nat.floor ((128 : ℝ) / 4095 * (2 ^ 62 : ℝ)) :=
    (Nat.le_floor_iff (by positivity)).2 h49
  exact_mod_cast Nat.lt_of_lt_of_le (by decide : 48 < 49) h49'

/-- Residual: `lemma62_cellUnionFactor ≤ failFactor` is not proved at paper `(m,jMax)`; numerically false. -/
def PaperOrdinary_hclose_residual : Prop :=
  lemma62_cellUnionFactor paperOrdinaryM 16
      (lemma62_jMax (invariant7.deltaF : ℝ) (2 ^ 58) 16) ≤
    lemma62_failFactor Lemma62InnerBound.thirty.x

/-! **Lemma 6.2 `ε_F` floor at root `f = 2^78`** -/

private theorem paperRoot_f78_sub_two_ge_2p77 : 2 ^ 77 ≤ 2 ^ 78 - 2 := by decide

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

noncomputable def theorem51Params_paperRootGeometry (C : PaperRootTheorem51Residual) :
    Theorem51Params paperRootGeometry :=
  theorem51Params_paperRoot paperRootGeometry
    (by
      rw [paperRootGeometry_m]
      exact chernoff_hepsB_paperRootM_le_paperRootEpsB)
    paperRoot_hepsF_ge_4e
    C.epsF_lemma62.bound

theorem theorem51Params_paperRootGeometry_chernoff :
    Real.sqrt (2 * (1 + Real.log paperRootGeometry.m) / paperRootGeometry.m) ≤
      paperRootEpsB := by
  rw [paperRootGeometry_m]
  exact chernoff_hepsB_paperRootM_le_paperRootEpsB

noncomputable def theorem51Params_paperRootGeometry_discharged :
    Theorem51Params paperRootGeometry :=
  theorem51Params_paperRootGeometry PaperRootTheorem51Residual.discharged

end Chvatal
