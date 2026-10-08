import AKS.Bounds.Chvatal1830Batcher
import AKS.Chvatal.RealSorter

/-! # Unconditional `limsup D(n)/log₂ n ≤ 1830`

The Chvátal DCS-TR-294 sorting network (`Chvatal.chvatal_sorter_exists`) discharges the
`Limsup1830Residual` obligation, so the limsup bound holds with no hypotheses. -/

namespace SortingDepth

open Chvatal Filter

theorem limsup1830Residual_holds : Limsup1830Residual := by
  intro d hd
  exact chvatal_sorter_exists (by
    have : batcherFitsTotalDepthMax = 603 := rfl
    omega)

/-- **`limsup D(n)/log₂ n ≤ 1830`**, unconditionally. -/
theorem limsup_minimum_div_logb_le_1830 :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ (1830 : ℝ) :=
  limsup_minimum_div_logb_le_1830_of_batcher_and_residual limsup1830Residual_holds

/-- **Pointwise bound.** For every `n ≥ 64^7`, `D(n) ≤ 1830 · log₂ n − 58657`. Small `clog`
(`≤ 603`) uses full-wire Batcher; larger uses Chvátal's network
(`chvatal_sorter_exists`); both are restricted to `n` wires. -/
theorem minimum_depth_le_1830_logb {n : ℕ} (hn64 : 64 ^ 7 ≤ n) :
    (minimum n : ℝ) ≤ 1830 * Real.logb 2 (n : ℝ) - 58657 := by
  have hn : 1 < n := lt_of_lt_of_le (by decide : 1 < 64 ^ 7) hn64
  have hd7 : 7 ≤ Nat.clog 64 n := by
    have hmono : Nat.clog 64 (64 ^ 7) ≤ Nat.clog 64 n := Nat.clog_mono_right 64 hn64
    rwa [Chvatal.clog64_pow_eq 7] at hmono
  by_cases hmax : Nat.clog 64 n ≤ batcherFitsTotalDepthMax
  · exact minimum_depth_le_1830_logb_of_batcher_range hn hd7 hmax
  · set d := Nat.clog 64 n with hdd
    have hd14 : 14 ≤ d := by
      have : batcherFitsTotalDepthMax = 603 := rfl
      omega
    obtain ⟨net0, hs0, hdep0⟩ := chvatal_sorter_exists hd14
    have hle_pow : n ≤ 64 ^ d := Nat.le_pow_clog (by decide : 1 < 64) n
    let net := net0.restrictWires n hle_pow
    have hs : ComparatorNetwork.Sorts.{0} net :=
      restrictWires_sorts net0 n hle_pow (fun v ↦ hs0 (α := Bool) v)
    have hdep : net.depth ≤ totalDepth d := (restrictWires_depth_le _ _ _).trans hdep0
    have hm : (minimum n : ℝ) ≤ (net.depth : ℝ) := by exact_mod_cast minimum_le net hs
    have h1 : (net.depth : ℝ) ≤ (totalDepth d : ℝ) := by exact_mod_cast hdep
    exact hm.trans (h1.trans (totalDepth_logb_le hd7 rfl hn))

/-- `D(n) ≤ 1830 · log₂ n − 58657` for all sufficiently large `n`. -/
theorem eventually_minimum_depth_le_1830_logb :
    ∀ᶠ n : ℕ in atTop, (minimum n : ℝ) ≤ 1830 * Real.logb 2 (n : ℝ) - 58657 := by
  filter_upwards [eventually_ge_atTop (64 ^ 7)] with n hn
  exact minimum_depth_le_1830_logb hn

end SortingDepth
