import AKS.Bounds.ConditionalLimit
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Order.LiminfLimsup

/-! # Passing a dyadic sorting-depth limit to all input counts

Monotonicity and dyadic squeezing suffice. The bounded-defect corollary
remains conditional on an unproved composition hypothesis.
-/

namespace SortingDepth

open Filter
open scoped Topology

theorem minimum_monotone : Monotone minimum := by
  intro m n hmn
  obtain ⟨net, hs, hd⟩ := minimum_attained n
  have hr := minimum_le (net.restrictWires m hmn)
    (restrictWires_sorts net m hmn (fun v => hs Bool v))
  exact hr.trans ((restrictWires_depth_le net m hmn).trans hd.le)

theorem depth_limit_of_dyadic_limit {L : ℝ}
    (h : Tendsto (fun k : ℕ => (minimum (2^k) : ℝ) / k) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (minimum n : ℝ) / Real.logb 2 n) atTop (𝓝 L) := by
  let a : ℕ → ℝ := fun k => minimum (2^k)
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hinv' : Tendsto (fun k : ℕ => ((k+1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    hinv.comp (tendsto_add_atTop_nat 1)
  have hrlo : Tendsto (fun k : ℕ => (k : ℝ) / (k+1)) atTop (𝓝 1) := by
    have he : (fun k : ℕ => (k : ℝ) / (k+1)) =
        (fun k : ℕ => 1 - ((k+1 : ℕ) : ℝ)⁻¹) := by
      funext k
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    rw [he]
    simpa using tendsto_const_nhds.sub hinv'
  have hlo : Tendsto (fun k : ℕ => a k / (k+1)) atTop (𝓝 L) := by
    have he : (fun k : ℕ => a k / (k+1)) =ᶠ[atTop]
        (fun k : ℕ => (a k / k) * ((k : ℝ)/(k+1))) := by
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      field_simp
    have ht : Tendsto (fun k : ℕ => (a k / k) * ((k : ℝ)/(k+1)))
        atTop (𝓝 L) := by simpa [a] using h.mul hrlo
    exact ht.congr' he.symm
  have hrhi : Tendsto (fun k : ℕ => 1 + (k : ℝ)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hinv
  have hhi : Tendsto (fun k : ℕ => a (k+1) / k) atTop (𝓝 L) := by
    have he : (fun k : ℕ => a (k+1) / k) =ᶠ[atTop]
        (fun k : ℕ => (a (k+1) / (k+1)) * (1+(k : ℝ)⁻¹)) := by
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    have hs := h.comp (tendsto_add_atTop_nat 1)
    have ht : Tendsto (fun k : ℕ => (a (k+1) / (k+1)) * (1+(k : ℝ)⁻¹))
        atTop (𝓝 L) := by simpa [a] using hs.mul hrhi
    exact ht.congr' he.symm
  have hk : Tendsto (fun n : ℕ => Nat.log 2 n) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (2^k)] with n hn
    exact Nat.le_log_of_pow_le (by decide) hn
  have hp (k : ℕ) : Real.logb 2 ((2^k : ℕ) : ℝ) = k := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  have bounds : ∀ᶠ n : ℕ in atTop,
      a (Nat.log 2 n) / ((Nat.log 2 n : ℝ)+1) ≤
        (minimum n : ℝ) / Real.logb 2 n ∧
      (minimum n : ℝ) / Real.logb 2 n ≤ a (Nat.log 2 n + 1) / Nat.log 2 n := by
    filter_upwards [eventually_ge_atTop 2, hk.eventually (eventually_ge_atTop 1)]
      with n hn hkn
    have hn0 : n ≠ 0 := by omega
    have hkpos : (0 : ℝ) < Nat.log 2 n := by exact_mod_cast (show 0 < Nat.log 2 n by omega)
    have hl : 0 < Real.logb 2 n := Real.logb_pos (by norm_num)
      (by exact_mod_cast (show 1 < n by omega))
    have hpowlo := Nat.pow_log_le_self 2 hn0
    have hpowhi := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
    have hloglo : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := by
      have hh : Real.logb 2 ((2^(Nat.log 2 n) : ℕ) : ℝ) ≤ Real.logb 2 (n : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by positivity : (0 : ℝ) < ((2^(Nat.log 2 n) : ℕ) : ℝ))
        (by exact_mod_cast hpowlo)
      simpa only [hp] using hh
    have hloghi : Real.logb 2 n ≤ (Nat.log 2 n : ℝ)+1 := by
      have hh : Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((2^(Nat.log 2 n + 1) : ℕ) : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by positivity : (0 : ℝ) < n) (by exact_mod_cast hpowhi)
      simpa only [hp, Nat.cast_add, Nat.cast_one] using hh
    have halo : a (Nat.log 2 n) ≤ (minimum n : ℝ) := by
      dsimp [a]
      exact_mod_cast minimum_monotone hpowlo
    have hahi : (minimum n : ℝ) ≤ a (Nat.log 2 n + 1) := by
      dsimp [a]
      exact_mod_cast minimum_monotone hpowhi
    constructor
    · calc
        _ ≤ a (Nat.log 2 n) / Real.logb 2 n :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) hl hloghi
        _ ≤ _ := div_le_div_of_nonneg_right halo hl.le
    · calc
        _ ≤ a (Nat.log 2 n + 1) / Real.logb 2 n :=
          div_le_div_of_nonneg_right hahi hl.le
        _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hkpos hloglo
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlo.comp hk) (hhi.comp hk)
    (bounds.mono fun _ h => h.1) (bounds.mono fun _ h => h.2)

/-- A sufficient condition for the full limit, with the missing mathematical
composition hypothesis explicit in the theorem statement. -/
theorem exists_depth_limit_of_bounded_defect (C : ℕ)
    (hdefect : ∀ j k, minimum (2^(j+k)) ≤
      minimum (2^j) + minimum (2^k) + C) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (minimum n : ℝ) / Real.logb 2 n)
      atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_dyadic_depth_limit_of_bounded_defect C hdefect
  exact ⟨L, depth_limit_of_dyadic_limit hL⟩

theorem liminf_eq_limsup_of_bounded_defect (C : ℕ)
    (hdefect : ∀ j k, minimum (2^(j+k)) ≤
      minimum (2^j) + minimum (2^k) + C) :
    liminf (fun n : ℕ => (minimum n : ℝ) / Real.logb 2 n) atTop =
      limsup (fun n : ℕ => (minimum n : ℝ) / Real.logb 2 n) atTop := by
  obtain ⟨L, hL⟩ := exists_depth_limit_of_bounded_defect C hdefect
  rw [hL.liminf_eq, hL.limsup_eq]

end SortingDepth
