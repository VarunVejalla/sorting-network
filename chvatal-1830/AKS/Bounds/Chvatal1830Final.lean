import AKS.Bounds.Minimum
import AKS.Chvatal.RealSorter
import AKS.Chvatal.DepthSkeleton
import AKS.Sort.Shrink
import Mathlib.Topology.Order.LiminfLimsup

/-! # Chvátal's 1830 bound

* `SortingDepth.minimum_depth_le_1830_logb`: for every `n ≥ 64^7`,
  `D(n) ≤ 1830 · log₂ n − 58657`.
* `SortingDepth.limsup_minimum_div_logb_le_1830`: `limsup D(n)/log₂ n ≤ 1830`.

For `7 ≤ d ≤ 13` the witness on `64^d` wires is full-wire Batcher (bitonic) sorting; for
`d ≥ 14` it is Chvátal's network (`Chvatal.chvatal_sorter_exists`). Both are restricted to `n`
wires, where `d = ⌈log₆₄ n⌉`. -/

namespace SortingDepth

open Chvatal Filter

/-- Full-wire bitonic sorting meets the §7 budget `totalDepth d` for `7 ≤ d ≤ 13`. -/
theorem exists_small_sorter {d : ℕ} (hd7 : 7 ≤ d) (hd13 : d ≤ 13) :
    ∃ net : ComparatorNetwork (64 ^ d),
      ComparatorNetwork.Sorts.{0} net ∧ net.depth ≤ totalDepth d := by
  refine ⟨bitonicNetwork (64 ^ d), bitonicNetwork_sorts _, ?_⟩
  have hc : Nat.clog 2 (64 ^ d) = 6 * d := by
    have h64 : (64 : ℕ) = 2 ^ 6 := by decide
    rw [h64, ← pow_mul]
    exact Nat.clog_pow 2 (6 * d) (by decide)
  refine (bitonicNetwork_depth_le_budget _).trans ?_
  rw [hc]
  interval_cases d <;> decide +kernel

/-- A sorter on `64^d` wires of depth `≤ totalDepth d`, for every `d ≥ 7`. -/
theorem exists_sorter {d : ℕ} (hd : 7 ≤ d) :
    ∃ net : ComparatorNetwork (64 ^ d),
      ComparatorNetwork.Sorts.{0} net ∧ net.depth ≤ totalDepth d := by
  by_cases h : d ≤ 13
  · exact exists_small_sorter hd h
  · exact chvatal_sorter_exists (by omega)

/-- **Pointwise bound.** For every `n ≥ 64^7`, `D(n) ≤ 1830 · log₂ n − 58657`. -/
theorem minimum_depth_le_1830_logb {n : ℕ} (hn64 : 64 ^ 7 ≤ n) :
    (minimum n : ℝ) ≤ 1830 * Real.logb 2 (n : ℝ) - 58657 := by
  have hn : 1 < n := lt_of_lt_of_le (by decide : 1 < 64 ^ 7) hn64
  have hd7 : 7 ≤ Nat.clog 64 n := by
    have hmono : Nat.clog 64 (64 ^ 7) ≤ Nat.clog 64 n := Nat.clog_mono_right 64 hn64
    rwa [Nat.clog_pow 64 7 (by decide)] at hmono
  set d := Nat.clog 64 n with hdd
  obtain ⟨net0, hs0, hdep0⟩ := exists_sorter hd7
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

/-- **`limsup D(n)/log₂ n ≤ 1830`.** -/
theorem limsup_minimum_div_logb_le_1830 :
    limsup (fun n : ℕ ↦ (minimum n : ℝ) / Real.logb 2 n) atTop ≤ (1830 : ℝ) := by
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ (minimum n : ℝ) / Real.logb 2 n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact div_nonneg (Nat.cast_nonneg _) (Real.logb_pos (by norm_num) hnR).le
  have hle : ∀ᶠ n : ℕ in atTop, (minimum n : ℝ) / Real.logb 2 n ≤ (1830 : ℝ) := by
    filter_upwards [eventually_ge_atTop (64 ^ 7)] with n hn64
    have hn : 1 < n := lt_of_lt_of_le (by decide : 1 < 64 ^ 7) hn64
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn
    have hl : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) hnR
    have hb := minimum_depth_le_1830_logb hn64
    exact (div_le_iff₀ hl).mpr (by linarith)
  exact (limsup_le_limsup hle
    (isCoboundedUnder_le_of_eventually_le atTop hnonneg)
    isBoundedUnder_const).trans (le_of_eq (limsup_const (1830 : ℝ)))

end SortingDepth
