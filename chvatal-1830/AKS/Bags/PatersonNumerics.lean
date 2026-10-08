module

public import AKS.Bags.PatersonParams
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Certified numerical bounds for Paterson's halvers

Logarithms are enclosed using eight terms of the atanh series and its proved
remainder bound. Scaling the input by a power of two keeps these certificates
small. Every certificate is rational arithmetic checked by the kernel.
-/

@[expose] public section

open Finset

namespace Paterson

noncomputable def logApprox (x : ℝ) : ℝ :=
  2 * ∑ i ∈ range 8, ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1)

noncomputable def logError (x : ℝ) : ℝ :=
  2 * (|(x - 1) / (x + 1)| ^ 17 / (1 - ((x - 1) / (x + 1)) ^ 2))

theorem log_bounds {x : ℝ} (hx : 0 < x) :
    logApprox x - logError x ≤ Real.log x ∧
      Real.log x ≤ logApprox x + logError x := by
  have hxp : 0 < x + 1 := by linarith
  have hz : |(x - 1) / (x + 1)| < 1 := by
    rw [abs_lt]
    constructor
    · apply (lt_div_iff₀ hxp).mpr
      linarith
    · apply (div_lt_iff₀ hxp).mpr
      linarith
  have heq : (1 + (x - 1) / (x + 1)) / (1 - (x - 1) / (x + 1)) = x := by
    field_simp
    ring
  have h := Real.sum_range_sub_log_div_le hz 8
  rw [heq] at h
  have hl := (abs_le.mp h).1
  have hu := (abs_le.mp h).2
  norm_num only at hl hu
  constructor <;> unfold logApprox logError <;> linarith

noncomputable def logLower (x : ℝ) (k : ℕ) : ℝ :=
  logApprox (x * 2 ^ k) - logError (x * 2 ^ k) -
    k * (logApprox 2 + logError 2)

noncomputable def logUpper (x : ℝ) (k : ℕ) : ℝ :=
  logApprox (x * 2 ^ k) + logError (x * 2 ^ k) -
    k * (logApprox 2 - logError 2)

theorem log_dyadic_bounds {x : ℝ} (hx : 0 < x) (k : ℕ) :
    logLower x k ≤ Real.log x ∧ Real.log x ≤ logUpper x k := by
  have hscaled := log_bounds (mul_pos hx (pow_pos (show (0 : ℝ) < 2 by norm_num) k))
  have htwo := log_bounds (show (0 : ℝ) < 2 by norm_num)
  have hlow := mul_le_mul_of_nonneg_left htwo.1 (Nat.cast_nonneg k)
  have hhigh := mul_le_mul_of_nonneg_left htwo.2 (Nat.cast_nonneg k)
  rw [Real.log_mul (ne_of_gt hx) (by positivity), Real.log_pow] at hscaled
  constructor <;> simp only [logLower, logUpper] <;> linarith [hscaled.1, hscaled.2]

/-- Reduce an entropy-depth upper bound to an exact rational certificate in
four logarithm enclosures. -/
theorem entropy_depth_le (p q c : ℝ) (kp kpc kq kqc : ℕ)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1)
    (hcoef : 0 ≤ (c - 1) * p - q)
    (hcert : ((c - 1) * p - q) * logUpper q kq -
      p * logLower p kp - (1 - p) * logLower (1 - p) kpc -
      (1 - q) * logLower (1 - q) kqc ≤ 0) :
    1 + (patersonEntropy p + patersonEntropy q) / (-p * Real.log q) ≤ c := by
  have hden : 0 < -p * Real.log q :=
    mul_pos_of_neg_of_neg (neg_neg_of_pos hp) (Real.log_neg hq hq1)
  have hbq := mul_le_mul_of_nonneg_left (log_dyadic_bounds hq kq).2 hcoef
  have hbp := mul_le_mul_of_nonneg_left (log_dyadic_bounds hp kp).1 hp.le
  have hbpc := mul_le_mul_of_nonneg_left
    (log_dyadic_bounds (sub_pos.mpr hp1) kpc).1 (sub_nonneg.mpr hp1.le)
  have hbqc := mul_le_mul_of_nonneg_left
    (log_dyadic_bounds (sub_pos.mpr hq1) kqc).1 (sub_nonneg.mpr hq1.le)
  have he : patersonEntropy p + patersonEntropy q ≤ (c - 1) * (-p * Real.log q) := by
    unfold patersonEntropy
    nlinarith only [hbq, hbp, hbpc, hbqc, hcert]
  have hd := (div_le_iff₀ hden).mpr he
  linarith

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem depth_bound_level0 :
    patersonHalverDepthBound patersonAlpha0 patersonDelta0 ≤ 262 := by
  unfold patersonHalverDepthBound
  apply entropy_depth_le _ _ 262 7 1 1 4
  all_goals norm_num [patersonAlpha0_eq, patersonDelta0,
    logLower, logUpper, logApprox, logError, Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem depth_bound_level1 :
    patersonHalverDepthBound (2 * patersonMu) patersonDelta1 ≤ 263 := by
  unfold patersonHalverDepthBound
  apply entropy_depth_le _ _ 263 13 1 5 1
  all_goals norm_num [patersonMu, patersonDelta1,
    logLower, logUpper, logApprox, logError, Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem depth_bound_level2 :
    patersonHalverDepthBound (4 * patersonMu) patersonDelta2 ≤ 155 := by
  unfold patersonHalverDepthBound
  apply entropy_depth_le _ _ 155 11 1 4 1
  all_goals norm_num [patersonMu, patersonDelta2,
    logLower, logUpper, logApprox, logError, Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem depth_bound_level3 :
    patersonHalverDepthBound (8 * patersonMu) patersonDelta3 ≤ 167 := by
  unfold patersonHalverDepthBound
  apply entropy_depth_le _ _ 167 10 1 3 1
  all_goals norm_num [patersonMu, patersonDelta3,
    logLower, logUpper, logApprox, logError, Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem depth_bound_level4 :
    patersonHalverDepthBound (16 * patersonMu) patersonDelta4 ≤ 187 := by
  unfold patersonHalverDepthBound
  apply entropy_depth_le _ _ 187 9 1 2 1
  all_goals norm_num [patersonMu, patersonDelta4,
    logLower, logUpper, logApprox, logError, Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem depth_bound_level5 :
    patersonHalverDepthBound (32 * patersonMu) patersonDelta5 ≤ 217 := by
  unfold patersonHalverDepthBound
  apply entropy_depth_le _ _ 217 8 1 1 2
  all_goals norm_num [patersonMu, patersonDelta5,
    logLower, logUpper, logApprox, logError, Finset.sum_range_succ]

/-- The proposed separator budget, with each local depth rounded up before
combining levels. This expression is not itself a separator construction. -/
noncomputable def separatorDepthBudget : ℕ :=
  max ⌈patersonHalverDepthBound patersonAlpha0 patersonDelta0⌉₊
      ⌈patersonHalverDepthBound (2 * patersonMu) patersonDelta1⌉₊ +
    ⌈patersonHalverDepthBound (4 * patersonMu) patersonDelta2⌉₊ +
    ⌈patersonHalverDepthBound (8 * patersonMu) patersonDelta3⌉₊ +
    ⌈patersonHalverDepthBound (16 * patersonMu) patersonDelta4⌉₊ +
    ⌈patersonHalverDepthBound (32 * patersonMu) patersonDelta5⌉₊

/-- Kernel-checked upper bound on the rounded separator depth formula. -/
theorem separatorDepthBudget_le_989 : separatorDepthBudget ≤ 989 := by
  have h0 : ⌈patersonHalverDepthBound patersonAlpha0 patersonDelta0⌉₊ ≤ 262 :=
    Nat.ceil_le.mpr depth_bound_level0
  have h1 : ⌈patersonHalverDepthBound (2 * patersonMu) patersonDelta1⌉₊ ≤ 263 :=
    Nat.ceil_le.mpr depth_bound_level1
  have h2 : ⌈patersonHalverDepthBound (4 * patersonMu) patersonDelta2⌉₊ ≤ 155 :=
    Nat.ceil_le.mpr depth_bound_level2
  have h3 : ⌈patersonHalverDepthBound (8 * patersonMu) patersonDelta3⌉₊ ≤ 167 :=
    Nat.ceil_le.mpr depth_bound_level3
  have h4 : ⌈patersonHalverDepthBound (16 * patersonMu) patersonDelta4⌉₊ ≤ 187 :=
    Nat.ceil_le.mpr depth_bound_level4
  have h5 : ⌈patersonHalverDepthBound (32 * patersonMu) patersonDelta5⌉₊ ≤ 217 :=
    Nat.ceil_le.mpr depth_bound_level5
  unfold separatorDepthBudget
  omega

end Paterson
