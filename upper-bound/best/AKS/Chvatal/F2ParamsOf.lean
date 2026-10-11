module

public import AKS.Chvatal.F2Defs

/-! # The two-round fringe parameters for general `f`

`F2Params.ofF f` : `g1 = 2f/5`, `g2 = 4f/5`, `c = 1/3`, `b = 17000`, `J = 86·10⁶`, valid for
`131040 ≤ f < 8.5·10⁹` (the upper bound is only needed for the field `hκ`, which holds for
`f ≤ 1.6·10¹³`). -/

@[expose] public section

namespace Chvatal

/-- Floor bounds for `2f/5` and `4f/5` as real inequalities. -/
theorem ofF_floor_bounds (f : ℕ) :
    (5 * ((2 * f / 5 : ℕ) : ℝ) ≤ 2 * (f : ℝ)) ∧ (2 * (f : ℝ) ≤ 5 * ((2 * f / 5 : ℕ) : ℝ) + 4) ∧
    (5 * ((4 * f / 5 : ℕ) : ℝ) ≤ 4 * (f : ℝ)) ∧ (4 * (f : ℝ) ≤ 5 * ((4 * f / 5 : ℕ) : ℝ) + 4) := by
  have h1 : 5 * (2 * f / 5) ≤ 2 * f := by omega
  have h2 : 2 * f ≤ 5 * (2 * f / 5) + 4 := by omega
  have h3 : 5 * (4 * f / 5) ≤ 4 * f := by omega
  have h4 : 4 * f ≤ 5 * (4 * f / 5) + 4 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4

/-- The general-`f` parameter set. -/
noncomputable def F2Params.ofF (f : ℕ) (hf : 131040 ≤ f) (hf2 : f < 8500000000) : F2Params where
  f := f
  g1 := 2 * f / 5
  g2 := 4 * f / 5
  J := 86000000
  c := 1 / 3
  b := 17000
  hg1 := by omega
  hg12 := by omega
  hg2f := by omega
  hJ := by norm_num
  hc0 := by norm_num
  hb0 := by norm_num
  hc_half := by norm_num
  hD1 := by
    obtain ⟨a1, a2, a3, a4⟩ := ofF_floor_bounds f
    have hlt : 2 * f / 5 < 4 * f / 5 := by omega
    have hfR : (131040 : ℝ) ≤ f := by exact_mod_cast hf
    rw [Nat.cast_sub hlt.le]
    linarith
  hD2 := by
    obtain ⟨a1, a2, a3, a4⟩ := ofF_floor_bounds f
    have hlt : 2 * f / 5 ≤ f := by omega
    have hfR : (131040 : ℝ) ≤ f := by exact_mod_cast hf
    rw [Nat.cast_sub hlt]
    linarith
  hD3 := by
    obtain ⟨a1, a2, a3, a4⟩ := ofF_floor_bounds f
    have hfR : (131040 : ℝ) ≤ f := by exact_mod_cast hf
    have : (0.39 : ℝ) * f ≤ ((2 * f / 5 : ℕ) : ℝ) + 1 := by linarith
    nlinarith
  hcΔ := by
    obtain ⟨a1, a2, a3, a4⟩ := ofF_floor_bounds f
    have hlt : 2 * f / 5 < 4 * f / 5 := by omega
    have hfR : (131040 : ℝ) ≤ f := by exact_mod_cast hf
    rw [Nat.cast_sub hlt.le, div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  hbJ := by
    obtain ⟨a1, a2, a3, a4⟩ := ofF_floor_bounds f
    have hfR : (131040 : ℝ) ≤ f := by exact_mod_cast hf
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  hΦ := by
    obtain ⟨a1, a2, a3, a4⟩ := ofF_floor_bounds f
    have hlt : 4 * f / 5 ≤ f := by omega
    have hfR : (131040 : ℝ) ≤ f := by exact_mod_cast hf
    rw [Nat.cast_sub hlt, div_le_iff₀ (by norm_num)]
    push_cast
    nlinarith
  hκ := by
    have hfR : (131040 : ℝ) ≤ f := by exact_mod_cast hf
    have hfR2 : (f : ℝ) ≤ 8500000000 := by exact_mod_cast hf2.le
    rw [le_div_iff₀ (by positivity)]
    push_cast
    nlinarith

@[simp] theorem F2Params.ofF_f (f : ℕ) (hf : 131040 ≤ f) (hf2 : f < 8500000000) :
    (F2Params.ofF f hf hf2).f = f := rfl

end Chvatal
