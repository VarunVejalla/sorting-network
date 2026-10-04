import AKS.Bounds.AsymptoticAdditive
import AKS.Separator.PatersonForestSorts

/-! # A complete bound below 7000 from the rounded Paterson bags

The forest, root rebuilds, child recursion and final rank correction are all
kernel checked. Bitonic sorting covers the finite startup range. -/

namespace SortingDepth

open Paterson.Bags

noncomputable def tightPatersonNetwork (n : ℕ) : ComparatorNetwork n :=
  if Nat.clog 2 n ≤ 13979 then bitonicNetwork n
  else (correctedForest (Nat.clog 2 n)).restrictWires n
    (Nat.le_pow_clog (by omega) n)

theorem tightPatersonNetwork_sorts (n : ℕ) : (tightPatersonNetwork n).Sorts := by
  unfold tightPatersonNetwork
  split_ifs
  · exact bitonicNetwork_sorts n
  · exact restrictWires_sorts _ _ _ (fun v ↦ correctedForest_sorts _ _ v)

theorem tightPatersonNetwork_depth_le (n : ℕ) :
    (tightPatersonNetwork n).depth ≤ 6991 * Nat.clog 2 n := by
  unfold tightPatersonNetwork
  split_ifs with hk
  · have hd := bitonicNetwork_depth_le_budget n
    have hb := bitonicDepthBudget_double (Nat.clog 2 n)
    have hm : Nat.clog 2 n * (Nat.clog 2 n + 1) ≤ Nat.clog 2 n * 13982 :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · have hd := restrictWires_depth_le (correctedForest (Nat.clog 2 n)) n
      (Nat.le_pow_clog (by omega) n)
    have hf := correctedForest_depth_double (Nat.clog 2 n)
    omega

theorem minimum_depth_le_6991 (n : ℕ) : minimum n ≤ 6991 * Nat.clog 2 n :=
  (minimum_le _ (tightPatersonNetwork_sorts n)).trans (tightPatersonNetwork_depth_le n)

theorem minimum_depth_le_7000 (n : ℕ) : minimum n ≤ 7000 * Nat.clog 2 n :=
  (minimum_depth_le_6991 n).trans (Nat.mul_le_mul_right _ (by omega))

theorem limsup_minimum_div_logb_le_6991 :
    Filter.limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) Filter.atTop ≤
      (6991 : ℝ) := by
  exact limsup_of_depth_bound 6991 minimum_depth_le_6991

theorem minimum_depth_double_le (n : ℕ) :
    2 * minimum n ≤ 13981 * Nat.clog 2 n + 13979 := by
  let net := (correctedForest (Nat.clog 2 n)).restrictWires n
    (Nat.le_pow_clog (by omega) n)
  have hs : net.Sorts := restrictWires_sorts _ _ _ (fun v ↦ correctedForest_sorts _ _ v)
  have hm := minimum_le net hs
  have hd := restrictWires_depth_le (correctedForest (Nat.clog 2 n)) n
    (Nat.le_pow_clog (by omega) n)
  change net.depth ≤ _ at hd
  have hf := correctedForest_depth_double (Nat.clog 2 n)
  omega

theorem minimum_depth_real_le (n : ℕ) :
    (minimum n : ℝ) ≤ (13981 / 2 : ℝ) * (Nat.clog 2 n : ℝ) + 13979 / 2 := by
  have h : (2 : ℝ) * minimum n ≤ 13981 * (Nat.clog 2 n : ℝ) + 13979 := by
    exact_mod_cast minimum_depth_double_le n
  linarith

theorem limsup_minimum_div_logb_le_6990_5 :
    Filter.limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) Filter.atTop ≤
      (13981 / 2 : ℝ) :=
  limsup_of_additive_depth_bound _ _ (by norm_num) minimum_depth_real_le

theorem minimum_depth_le_7000_logb {n : ℕ} (hn : 2 ≤ n)
    (hl : (1472 : ℝ) ≤ Real.logb 2 n) : (minimum n : ℝ) ≤ 7000 * Real.logb 2 n := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hpos := Real.logb_pos (by norm_num : (1 : ℝ) < 2) hnR
  have hceil : (Nat.clog 2 n : ℝ) < Real.logb 2 n + 1 := by
    rw [← Real.natCeil_logb_natCast]
    exact Nat.ceil_lt_add_one hpos.le
  have hd := minimum_depth_real_le n
  linarith

theorem eventually_minimum_depth_le_7000_logb :
    ∀ᶠ n : ℕ in Filter.atTop, (minimum n : ℝ) ≤ 7000 * Real.logb 2 n := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.logb 2 (n : ℝ)) Filter.atTop Filter.atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 2,
    hlog.eventually (Filter.eventually_ge_atTop (1472 : ℝ))] with n hn hl
  exact minimum_depth_le_7000_logb hn hl

end SortingDepth
