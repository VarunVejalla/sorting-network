module

/-
  # Chvátal Lemma 6.2: the numeric claim `x < 0.32`

  Source: Chvátal, DCS-TR-294, p. 22, end of the proof of Lemma 6.2.  With
  `xval n f j = (e²(f+2)² n/(4j))^{2/(εf)} (e f n/(2εj))^{2/f} (2 e j/(f n))` we prove
  `xval ≤ 3/10` on the parameter range of `Lemma62Params` (plus `1/ε ≤ j`, which is
  not needed by the argument).  The parameter `n` cancels after substituting `u = j/(f n)`.
-/

public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import AKS.Chvatal.Lemma62Ratio

@[expose] public section

namespace Chvatal

/-- The quantity `x` of the paper, over the reals. -/
noncomputable def xval (n f j : ℝ) : ℝ :=
  ((Real.exp 1 ^ 2 * (f + 2) ^ 2 * n / (4 * j)) ^ (2 / (eps * f))) *
    ((Real.exp 1 * f * n / (2 * eps * j)) ^ (2 / f)) * (2 * Real.exp 1 * j / (f * n))

lemma xval_pos {n f j : ℝ} (hn : 0 < n) (hf : 0 < f) (hj : 0 < j) : 0 < xval n f j := by
  have := eps_pos
  unfold xval
  positivity

set_option maxHeartbeats 1600000 in
theorem xval_le_three_tenths {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j)
    (_hj1 : 8 * 10 ^ 7 ≤ j) : xval (n : ℝ) f j ≤ 3 / 10 := by
  have hf := P.f_pos
  have hN := P.N_pos
  have hj := P.hj
  have hep := eps_pos
  have hf0 : (1.7e10 : ℝ) ≤ f := by have := P.hf; norm_num at this ⊢; linarith
  set N : ℝ := (n : ℝ) with hNdef
  have hx := xval_pos hN hf hj
  -- logs of the three bases
  have h1 : Real.log (Real.exp 1 ^ 2 * (f + 2) ^ 2 * N / (4 * j)) =
      2 + 2 * Real.log (f + 2) + Real.log N - 2 * Real.log 2 - Real.log j := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_exp,
      Real.log_mul (by norm_num) (by positivity), h4]
    push_cast; ring
  have h2 : Real.log (Real.exp 1 * f * N / (2 * eps * j)) =
      1 + Real.log f + Real.log N - Real.log 2 - Real.log eps - Real.log j := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
    ring
  have h3 : Real.log (2 * Real.exp 1 * j / (f * N)) =
      Real.log 2 + 1 + Real.log j - Real.log f - Real.log N := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp,
      Real.log_mul (by positivity) (by positivity)]
    ring
  have hlog : Real.log (xval N f j) =
      2 / (eps * f) * (2 + 2 * Real.log (f + 2) + Real.log N - 2 * Real.log 2 - Real.log j) +
      2 / f * (1 + Real.log f + Real.log N - Real.log 2 - Real.log eps - Real.log j) +
      (Real.log 2 + 1 + Real.log j - Real.log f - Real.log N) := by
    unfold xval
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by positivity), Real.log_rpow (by positivity), h1, h2, h3]
  -- the variable u = j/(f n)
  set u : ℝ := j / (f * N) with hu
  have hu_pos : 0 < u := by positivity
  have hju : Real.log j = Real.log u + Real.log f + Real.log N := by
    have : j = u * f * N := by rw [hu]; field_simp
    conv_lhs => rw [this]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have hu_le : u ≤ 1 / 31 := by
    rw [hu, div_le_iff₀ (by positivity)]
    nlinarith [P.hjf, mul_pos hf hN]
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have hL : Real.log u ≤ -3.43 := by
    have h1' : Real.log u ≤ Real.log (1 / 31) := Real.log_le_log hu_pos hu_le
    have h2' : Real.log (1 / 31 : ℝ) = -(5 * Real.log 2) + Real.log (32 / 31) := by
      rw [show (1 / 31 : ℝ) = (1 / 32) * (32 / 31) by norm_num,
        Real.log_mul (by norm_num) (by norm_num), one_div, Real.log_inv,
        show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
      push_cast; ring
    have h3' := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 32 / 31 by norm_num)
    linarith
  -- size of the f-dependent coefficients
  set a : ℝ := 2 / (eps * f) with ha
  set b : ℝ := 2 / f with hb
  have ha_eq : a = 1.6e8 / f := by
    rw [ha]; unfold eps; field_simp; norm_num
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have ha1 : a ≤ 0.00942 := by
    rw [ha_eq, div_le_iff₀ hf]; nlinarith
  have hb1 : b ≤ 1.2e-10 := by
    rw [hb, div_le_iff₀ hf]; nlinarith
  -- log f / f is antitone
  have hlf_f : Real.log f / f ≤ Real.log 1.7e10 / 1.7e10 := by
    have he : Real.exp 1 ≤ 1.7e10 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    exact Real.log_div_self_antitoneOn (show (1.7e10 : ℝ) ∈ {x | Real.exp 1 ≤ x} from he)
      (show f ∈ {x | Real.exp 1 ≤ x} from le_trans he hf0) hf0
  have hlf0 : Real.log (1.7e10 : ℝ) ≤ 35 * Real.log 2 := by
    have h := Real.log_le_log (show (0:ℝ) < 1.7e10 by norm_num)
      (show (1.7e10 : ℝ) ≤ 2 ^ 35 by norm_num)
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have hlf0' : Real.log (1.7e10 : ℝ) ≤ 24.27 := by linarith
  have haf : a * Real.log f ≤ 0.2285 := by
    have : a * Real.log f = 1.6e8 * (Real.log f / f) := by rw [ha_eq]; ring
    rw [this]
    have h := mul_le_mul_of_nonneg_left hlf_f (by norm_num : (0 : ℝ) ≤ 1.6e8)
    have h' : Real.log 1.7e10 / 1.7e10 ≤ 24.27 / 1.7e10 :=
      div_le_div_of_nonneg_right hlf0' (by norm_num)
    have := mul_le_mul_of_nonneg_left h' (by norm_num : (0 : ℝ) ≤ 1.6e8)
    norm_num at this ⊢
    linarith
  have hlf2 : Real.log (f + 2) ≤ Real.log f + b := by
    have : Real.log (f + 2) = Real.log f + Real.log (1 + 2 / f) := by
      rw [← Real.log_mul hf.ne' (by positivity)]; congr 1; field_simp
    rw [this]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 2 / f by positivity)
    rw [hb]; linarith
  have heps : -Real.log eps ≤ 8 * 10 ^ 7 := by
    have : eps = (8 * 10 ^ 7 : ℝ)⁻¹ := by unfold eps; rw [one_div]
    rw [this, Real.log_inv, neg_neg]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 8 * 10 ^ 7 by norm_num)
    linarith
  -- assemble
  have hcoef : 0.99 ≤ 1 - a - b := by linarith
  have hcw : (1 - a - b) * Real.log u ≤ 0.99 * (-3.43) := by
    have e1 : (1 - a - b) * Real.log u ≤ (1 - a - b) * (-3.43) :=
      mul_le_mul_of_nonneg_left hL (by linarith)
    linarith only [e1, hcoef]
  have hab : a * Real.log (f + 2) ≤ a * Real.log f + a * b :=
    by have := mul_le_mul_of_nonneg_left hlf2 ha0.le; rw [mul_add] at this; exact this
  have hab2 : a * b ≤ 0.00942 * 1.2e-10 := mul_le_mul ha1 hb1 hb0.le (by norm_num)
  have hl4 : 0 ≤ a * Real.log 2 := by positivity
  have hbe : b * (1 - Real.log 2 - Real.log eps) ≤ 1.2e-10 * (1 + 8 * 10 ^ 7) := by
    have : 1 - Real.log 2 - Real.log eps ≤ 1 + 8 * 10 ^ 7 := by linarith
    calc b * (1 - Real.log 2 - Real.log eps) ≤ b * (1 + 8 * 10 ^ 7) :=
          mul_le_mul_of_nonneg_left this hb0.le
      _ ≤ 1.2e-10 * (1 + 8 * 10 ^ 7) := by nlinarith
  have hexp : Real.log (xval N f j) =
      a * (2 + 2 * Real.log (f + 2) - 2 * Real.log 2 - Real.log f) +
      b * (1 - Real.log 2 - Real.log eps) + (Real.log 2 + 1) +
      (1 - a - b) * Real.log u := by
    rw [hlog, hju]; ring
  have hlt : Real.log (xval N f j) ≤ Real.log (1 / 4) := by
    have : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
      rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [this, hexp]
    nlinarith
  have := (Real.log_le_log_iff hx (by norm_num)).mp hlt
  linarith

theorem xval_pow_le {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j)
    (hj1 : 8 * 10 ^ 7 ≤ j) (E : ℕ) :
    xval (n : ℝ) f j ^ E ≤ (3 / 10) ^ E :=
  pow_le_pow_left₀ (xval_pos P.N_pos P.f_pos P.hj).le (xval_le_three_tenths P hj1) E

end Chvatal
