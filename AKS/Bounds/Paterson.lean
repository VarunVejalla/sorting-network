import AKS.Bounds.Asymptotic
import AKS.Separator.PatersonProvider

/-! # A complete million-coefficient bound using Paterson halvers

This uses the proved Paterson matching/entropy existence theorem with full
cohort support, the prefix-doubling separator, and the established Seiferas
bag scheduler. The finer rounded Paterson bag construction is separate.
The network is selected classically; every correctness and depth proof is
kernel checked, with no assumption imported from a published theorem.
-/

namespace SortingDepth

noncomputable def patersonParams : Params where
  γ := 1 / 63
  ε := 89 / 5000
  ν := 8203 / 10000
  A := 397 / 50
  hγ_pos := by norm_num
  hγ_half := by norm_num
  hε_pos := by norm_num
  hε_lt := by norm_num
  hA := by norm_num
  hν_pos := by norm_num
  hν_lt := by norm_num
  h2εA := by norm_num
  hC3 := by norm_num
  hC4_gt1 := by norm_num
  hC4_eq1 := by norm_num
  hC_bound := by norm_num
  hA2_le := by norm_num
  separators := Paterson.bagProvider

theorem patersonParams_depth : patersonParams.depth = 999189 := by decide +kernel

noncomputable def patersonNetwork (n : ℕ) : ComparatorNetwork n :=
  if h : 1024 ≤ n then
    (seiferasNetwork patersonParams (Nat.clog 2 n)).restrictWires n
      (Nat.le_pow_clog (by omega) n)
  else bitonicNetwork n

theorem patersonNetwork_sorts (n : ℕ) : (patersonNetwork n).Sorts := by
  unfold patersonNetwork
  split
  · rename_i h
    have hk : 10 ≤ Nat.clog 2 n :=
      (show (10 : ℕ) = Nat.clog 2 1024 by decide +kernel) ▸ Nat.clog_mono_right 2 h
    exact restrictWires_sorts _ _ _ (fun v ↦ (seiferasNetwork_sorts _ _ hk) _ v)
  · exact bitonicNetwork_sorts n

theorem patersonNetwork_depth_le (n : ℕ) :
    (patersonNetwork n).depth ≤ 10 ^ 6 * Nat.clog 2 n := by
  unfold patersonNetwork
  split
  · rename_i h
    have hk : 10 ≤ Nat.clog 2 n :=
      (show (10 : ℕ) = Nat.clog 2 1024 by decide +kernel) ▸ Nat.clog_mono_right 2 h
    apply (restrictWires_depth_le _ _ _).trans
    apply (seiferasNetwork_depth_le _ _ hk).trans
    apply Nat.mul_le_mul_right
    rw [patersonParams_depth]
    norm_num
  · rename_i h
    set k := Nat.clog 2 n
    calc (bitonicNetwork n).depth
        ≤ k ^ 2 := bitonicNetwork_depth_le n
      _ = k * k := by ring
      _ ≤ (10 ^ 6) * k := by
        apply Nat.mul_le_mul_right
        calc k ≤ Nat.clog 2 1023 := Nat.clog_mono_right 2 (by omega)
          _ ≤ 10 ^ 6 := by decide +kernel

theorem minimum_depth_le_million (n : ℕ) :
    minimum n ≤ 10 ^ 6 * Nat.clog 2 n :=
  (minimum_le (patersonNetwork n) (patersonNetwork_sorts n)).trans
    (patersonNetwork_depth_le n)

theorem limsup_minimum_div_logb_le_million :
    Filter.limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) Filter.atTop ≤
      (10 ^ 6 : ℝ) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    limsup_of_depth_bound (10 ^ 6) minimum_depth_le_million

end SortingDepth
