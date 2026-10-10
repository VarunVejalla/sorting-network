import AKS.Chvatal.Lemma63
open Chvatal

theorem bernoulli_cubic_aux (x : ℝ) (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + (2 / 9) * |x| ^ 3 := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  have h2 := (abs_le.1 h).2
  simp [Finset.sum_range_succ, Nat.factorial] at h2
  norm_num at h2
  nlinarith

theorem bernoulli_mgf_bernstein {p lam : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    1 - p + p * Real.exp lam ≤
      Real.exp (p * lam + lam ^ 2 * (1 / 2 + 2 * lam / 9) * (p * (1 - p))) := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hx1 : |lam * (1 - p)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  have hx2 : |-(lam * p)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]; nlinarith
  have e1 := bernoulli_cubic_aux _ hx1
  have e2 := bernoulli_cubic_aux _ hx2
  rw [abs_of_nonneg (by positivity : 0 ≤ lam * (1 - p))] at e1
  rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ lam * p)] at e2
  have c1 : (1 - p) ^ 3 ≤ (1 - p) ^ 2 := by
    have := pow_le_pow_of_le_one hq0 (by linarith : 1 - p ≤ 1) (by norm_num : 2 ≤ 3)
    exact this
  have c2 : p ^ 3 ≤ p ^ 2 := pow_le_pow_of_le_one h0 h1 (by norm_num : 2 ≤ 3)
  have l3 : 0 ≤ lam ^ 3 := by positivity
  have key : p * Real.exp (lam * (1 - p)) + (1 - p) * Real.exp (-(lam * p)) ≤
      1 + lam ^ 2 * (1 / 2 + 2 * lam / 9) * (p * (1 - p)) := by
    have a1 := mul_le_mul_of_nonneg_left e1 h0
    have a2 := mul_le_mul_of_nonneg_left e2 hq0
    have b1 : p * ((lam * (1 - p)) ^ 3) ≤ p * (lam ^ 3 * (1 - p) ^ 2) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left c1 l3) h0
    have b2 : (1 - p) * ((lam * p) ^ 3) ≤ (1 - p) * (lam ^ 3 * p ^ 2) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left c2 l3) hq0
    nlinarith
  have hfac : 1 - p + p * Real.exp lam =
      Real.exp (p * lam) * (p * Real.exp (lam * (1 - p)) + (1 - p) * Real.exp (-(lam * p))) := by
    have r1 : Real.exp (p * lam) * Real.exp (lam * (1 - p)) = Real.exp lam := by
      rw [← Real.exp_add]; congr 1; ring
    have r2 : Real.exp (p * lam) * Real.exp (-(lam * p)) = 1 := by
      rw [← Real.exp_add]; rw [show p * lam + -(lam * p) = 0 by ring]; simp
    calc 1 - p + p * Real.exp lam = (1 - p) * (Real.exp (p * lam) * Real.exp (-(lam * p))) +
          p * (Real.exp (p * lam) * Real.exp (lam * (1 - p))) := by rw [r1, r2]; ring
      _ = _ := by ring
  rw [hfac, Real.exp_add]
  gcongr
  calc _ ≤ 1 + lam ^ 2 * (1 / 2 + 2 * lam / 9) * (p * (1 - p)) := key
    _ ≤ _ := by linarith [Real.add_one_le_exp (lam ^ 2 * (1 / 2 + 2 * lam / 9) * (p * (1 - p)))]
