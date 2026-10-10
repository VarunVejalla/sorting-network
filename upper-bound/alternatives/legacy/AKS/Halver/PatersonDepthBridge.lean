module

public import AKS.Halver.PatersonMonotonicity
public import AKS.Halver.PatersonEntropy
public import AKS.Bags.PatersonParams

/-! # Applying the entropy depth to discrete trap sizes -/

@[expose] public section

namespace Paterson

theorem depthBound_eq_ratio (a e : ℚ) :
    patersonHalverDepthBound a e = 1 + depthRatio (a : ℝ) (e : ℝ) := by
  simp only [patersonHalverDepthBound, depthRatio, patersonEntropy_eq_binEntropy]

/-- A witness of sizes `r,s` covered by `(epsilon,alpha)` satisfies the
single-term entropy budget whenever the matching count meets the advertised
depth. The `r ≤ s` hypothesis excludes traps impossible for a bijection. -/
theorem witness_entropy_budget {a e : ℚ} {m r s c : ℕ}
    (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 < e) (hehalf : e ≤ 1 / 2)
    (hr : 0 < r) (hrs : r ≤ s) (hsm : r + s ≤ m)
    (hcovered : ((r + s : ℕ) : ℝ) ≤ (a : ℝ) * m)
    (herr : (e : ℝ) * (r + s : ℕ) ≤ r)
    (hc : patersonHalverDepthBound a e ≤ c) :
    (m : ℝ) * (Real.binEntropy ((r : ℝ) / m) +
      Real.binEntropy ((s : ℝ) / m)) ≤
      -((c : ℝ) - 1) * r * Real.log ((s : ℝ) / m) := by
  have hkNat : 0 < r + s := by omega
  have hmNat : 0 < m := by omega
  have hk : (0 : ℝ) < (r + s : ℕ) := by exact_mod_cast hkNat
  have hm : (0 : ℝ) < m := by exact_mod_cast hmNat
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast (hr.trans_le hrs)
  have hsn : s < m := by omega
  have hq : (0 : ℝ) < (s : ℝ) / m := div_pos hsR hm
  have hq1 : (s : ℝ) / m < 1 := (div_lt_one hm).mpr (by exact_mod_cast hsn)
  have haa : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have ha1R : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hhalf : (e : ℝ) ≤ 1 / 2 := by
    have h : (e : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hehalf
    norm_num at h ⊢
    exact h
  have halpha : (0 : ℝ) < (r + s : ℕ) / m := div_pos hk hm
  have hAlphaLe : ((r + s : ℕ) : ℝ) / m ≤ (a : ℝ) :=
    (div_le_iff₀ hm).mpr hcovered
  have hEps : (e : ℝ) ≤ (r : ℝ) / (r + s : ℕ) :=
    (le_div_iff₀ hk).mpr herr
  have hEpsHalf : (r : ℝ) / (r + s : ℕ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hk).mpr
    have hh : (2 : ℝ) * r ≤ (r + s : ℕ) := by
      exact_mod_cast (show 2 * r ≤ r + s by omega)
    linarith
  have hmono := depthRatio_le halpha hAlphaLe ha1R heR hEps hEpsHalf
  have hdepth : 1 + depthRatio (a : ℝ) (e : ℝ) ≤ c := by
    rwa [depthBound_eq_ratio] at hc
  have hratio : depthRatio ((r + s : ℕ) / (m : ℝ))
      ((r : ℝ) / (r + s : ℕ)) ≤ (c : ℝ) - 1 := by linarith
  have hp : ((r : ℝ) / (r + s : ℕ)) * ((r + s : ℕ) / (m : ℝ)) =
      (r : ℝ) / m := by field_simp [hk.ne', hm.ne'] <;> ring
  have hqq : (1 - (r : ℝ) / (r + s : ℕ)) *
      ((r + s : ℕ) / (m : ℝ)) = (s : ℝ) / m := by
    field_simp [hk.ne', hm.ne'] <;> push_cast <;> ring
  dsimp [depthRatio] at hratio
  rw [hp, hqq] at hratio
  have hden : 0 < -((r : ℝ) / m) * Real.log ((s : ℝ) / m) :=
    mul_pos_of_neg_of_neg (neg_neg_of_pos (div_pos hrR hm))
      (Real.log_neg hq hq1)
  have hbudget := (div_le_iff₀ hden).mp hratio
  have hmBudget := mul_le_mul_of_nonneg_left hbudget hm.le
  convert hmBudget using 1 <;> field_simp [hm.ne'] <;> ring

/-- The published depth expression bounds each covered, nontrivial trap
contribution by the summable sharp-Stirling term. -/
theorem witness_failure_term_le {a e : ℚ} {m r s c : ℕ}
    (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 < e) (hehalf : e ≤ 1 / 2)
    (hr : 0 < r) (hrs : r ≤ s) (hsm : r + s ≤ m)
    (hcovered : ((r + s : ℕ) : ℝ) ≤ (a : ℝ) * m)
    (herr : (e : ℝ) * (r + s : ℕ) ≤ r)
    (hc : patersonHalverDepthBound a e ≤ c) :
    (m.choose r : ℝ) * m.choose s * ((s : ℝ) / m) ^ (r * c) ≤
      ((s : ℝ) / m) ^ r / (Real.pi * r) := by
  exact failure_term_le hr hrs hsm
    (witness_entropy_budget ha ha1 he hehalf hr hrs hsm hcovered herr hc)

end Paterson
