import AKS.Sub800.R1Table

/-! # Invariants of design P (W1, step 16): schedule facts and the `θ` algebra -/

namespace R1T

open Finset
open Chvatal (KBag subtreeBags)

/-! ### Schedule facts -/

section Sched

variable (d : ℕ)

/-- The top moves by exactly one level per stage. -/
theorem alpha_step_exact (hd : 10 ≤ d) (t : ℕ) :
    alpha d (t + 1) = alpha d t + 1 ∨ alpha d t = alpha d (t + 1) + 1 := by
  have h1 := alpha_step d t hd
  have h2 := alpha_parity d t
  have h3 := alpha_parity d (t + 1)
  omega

/-- The bottom moves by exactly one level per stage. -/
theorem omega_step_exact (t : ℕ) : omega (t + 1) = omega t + 1 ∨ omega t = omega (t + 1) + 1 := by
  have h1 := omega_step t
  have h2 := omega_parity t
  have h3 := omega_parity (t + 1)
  omega

/-- A descending bottom has room below it: `3 ω(t) ≤ t + 4`. -/
theorem botD_room (t : ℕ) (h2 : 2 ≤ t) (hs : omega t < omega (t + 1)) : 3 * omega t ≤ t + 4 := by
  simp only [omega, ceilParity, omegaLo] at *
  split_ifs at * <;> omega

/-- A rising bottom: `3 ω(t) = t + 6`, i.e. `R/c = 2^-12`. -/
theorem botR_ratio (t : ℕ) (h2 : 2 ≤ t) (hs : ¬ omega t < omega (t + 1)) : 3 * omega t = t + 6 := by
  simp only [omega, ceilParity, omegaLo] at *
  split_ifs at * <;> omega

/-- A descending bottom: `3 ω(t) ∈ {t + 2, t + 4}`, i.e. `R/c ∈ {1, 2^-6}`. -/
theorem botD_ratio (t : ℕ) (h2 : 2 ≤ t) (hs : omega t < omega (t + 1)) :
    3 * omega t = t + 2 ∨ 3 * omega t = t + 4 := by
  simp only [omega, ceilParity, omegaLo] at *
  split_ifs at * <;> omega

/-- The root, when active, is a descending top. -/
theorem root_topD (hd : 10 ≤ d) (t : ℕ) (ht : alpha d t = 0) : alpha d t < alpha d (t + 1) := by
  have := alpha_step_exact d hd t
  omega

end Sched

/-! ### Units -/

theorem pow_sub_mul (e k : ℕ) (h : k ≤ e) : (2 : ℤ) ^ e = 2 ^ k * 2 ^ (e - k) := by
  rw [← pow_add, Nat.add_sub_cancel' h]

/-! ### The design-P rule as integer algebra -/

/-- Design P, child `j` (`0 ≤ j < 16`). -/
def thetaP (π G s : ℤ) (j : ℕ) : ℤ :=
  if j = 0 ∨ j = 15 then π / 2 + G - s
  else (2 * s - G) / 14 + (if ((j : ℤ) - 1) < (2 * s - G) % 14 then 1 else 0)

theorem thetaP_zero (π G s : ℤ) : thetaP π G s 0 = π / 2 + G - s := by simp [thetaP]
theorem thetaP_fifteen (π G s : ℤ) : thetaP π G s 15 = π / 2 + G - s := by simp [thetaP]

theorem thetaP_int_bounds (π G s : ℤ) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 14) :
    (2 * s - G) / 14 ≤ thetaP π G s j ∧ thetaP π G s j ≤ (2 * s - G) / 14 + 1 := by
  unfold thetaP
  rw [if_neg (by omega)]
  split_ifs <;> constructor <;> linarith

theorem count_lt (m : ℤ) (h0 : 0 ≤ m) (h1 : m < 14) :
    ∑ j ∈ Ico (1 : ℕ) 15, (if ((j : ℕ) : ℤ) - 1 < m then (1 : ℤ) else 0) = m := by
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, m = r := ⟨m.toNat, (Int.toNat_of_nonneg h0).symm⟩
  have hr : r < 14 := by omega
  interval_cases r <;> decide

/-- The interior shares sum to `I = 2s − G`. -/
theorem sum_interior (π G s : ℤ) :
    ∑ j ∈ Ico (1 : ℕ) 15, thetaP π G s j = 2 * s - G := by
  set I := 2 * s - G with hI
  have hterm : ∀ j ∈ Ico (1 : ℕ) 15, thetaP π G s j =
      I / 14 + (if ((j : ℕ) : ℤ) - 1 < I % 14 then 1 else 0) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    unfold thetaP
    rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
    count_lt _ (Int.emod_nonneg I (by norm_num)) (Int.emod_lt_of_pos I (by norm_num))]
  have := Int.emod_add_ediv I 14
  simp only [show (15 : ℕ) - 1 = 14 from rfl, nsmul_eq_mul]
  push_cast
  linarith

theorem sum_range16_split (f : ℕ → ℤ) :
    ∑ j ∈ range 16, f j = f 0 + ∑ j ∈ Ico (1 : ℕ) 15, f j + f 15 := by
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (by norm_num : 0 ≤ 1) (by norm_num : 1 ≤ 16),
    Finset.sum_Ico_succ_top (by norm_num : 1 ≤ 15)]
  simp
  ring

/-- **`Σ θ = π + G`.** -/
theorem sum_thetaP (π G s : ℤ) (hπ : 2 ∣ π) :
    ∑ j ∈ range 16, thetaP π G s j = π + G := by
  rw [sum_range16_split, sum_interior, thetaP_zero, thetaP_fifteen]
  obtain ⟨p, rfl⟩ := hπ
  rw [show 2 * p / 2 = p by omega]
  ring

/-- **The residual of design P (I4).** -/
theorem resid_thetaP (π G s : ℤ) (hπ : 2 ∣ π) (hπ0 : 0 ≤ π) (hG : 0 ≤ G) (hs : 0 ≤ s)
    (hE : s ≤ π / 2 + G) (hI : 0 ≤ 2 * s - G) (hgap : G - (2 * s - G) / 14 ≤ s)
    (j : ℕ) (hj : j < 16) :
    max 0 (∑ h ∈ range j, thetaP π G s h - π / 2) +
      max 0 (∑ h ∈ Ico (j + 1) 16, thetaP π G s h - π / 2) ≤ s := by
  set E := π / 2 + G - s with hEdef
  set I := 2 * s - G with hIdef
  have hθ0 : thetaP π G s 0 = E := thetaP_zero π G s
  have hθ15 : thetaP π G s 15 = E := thetaP_fifteen π G s
  have hint_nonneg : ∀ h, 1 ≤ h → h ≤ 14 → 0 ≤ thetaP π G s h := fun h h1 h2 =>
    le_trans (Int.ediv_nonneg hI (by norm_num)) (thetaP_int_bounds π G s h h1 h2).1
  have hsumI := sum_interior π G s
  have hπ2 : π / 2 + π / 2 = π := by obtain ⟨p, rfl⟩ := hπ; omega
  have hR16 : ∀ a, a ≤ 15 → ∑ h ∈ Ico a 16, thetaP π G s h = ∑ h ∈ Ico a 15, thetaP π G s h + E := by
    intro a ha; rw [Finset.sum_Ico_succ_top ha, hθ15]
  have hL1 : ∀ b, 1 ≤ b → ∑ h ∈ range b, thetaP π G s h = E + ∑ h ∈ Ico 1 b, thetaP π G s h := by
    intro b hb
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (by norm_num : 0 ≤ 1) hb]
    simp [hθ0]
  rcases Nat.lt_or_ge j 1 with hj0 | hj1
  · obtain rfl : j = 0 := by omega
    rw [hR16 1 (by norm_num), hsumI]
    simp only [Finset.range_zero, Finset.sum_empty, zero_sub]
    rw [max_eq_left (by omega : -(π / 2) ≤ 0)]
    have : I + E - π / 2 = s := by rw [hIdef, hEdef]; ring
    rw [this, max_eq_right hs]; simp
  rcases Nat.lt_or_ge j 15 with hj14 | hj15
  · rw [hL1 j hj1, hR16 (j + 1) (by omega)]
    have hsplit : ∑ h ∈ Ico 1 15, thetaP π G s h =
        ∑ h ∈ Ico 1 j, thetaP π G s h + thetaP π G s j + ∑ h ∈ Ico (j + 1) 15, thetaP π G s h := by
      rw [← Finset.sum_Ico_consecutive _ hj1 (by omega : j ≤ 15),
        ← Finset.sum_Ico_consecutive _ (by omega : j ≤ j + 1) (by omega : j + 1 ≤ 15),
        Finset.sum_Ico_succ_top (le_refl j)]
      simp
      ring
    set P := ∑ h ∈ Ico 1 j, thetaP π G s h
    set Q := ∑ h ∈ Ico (j + 1) 15, thetaP π G s h
    have hP : 0 ≤ P := Finset.sum_nonneg fun h hh => by
      rw [Finset.mem_Ico] at hh; exact hint_nonneg h hh.1 (by omega)
    have hQ : 0 ≤ Q := Finset.sum_nonneg fun h hh => by
      rw [Finset.mem_Ico] at hh; exact hint_nonneg h (by omega) (by omega)
    have hθj := thetaP_int_bounds π G s j hj1 (by omega)
    have hθj0 := hint_nonneg j hj1 (by omega)
    rw [hsumI] at hsplit
    have hEq : E - π / 2 = G - s := by rw [hEdef]; ring
    rcases le_or_gt (E + P - π / 2) 0 with h1 | h1 <;>
      rcases le_or_gt (Q + E - π / 2) 0 with h2 | h2
    · rw [max_eq_left h1, max_eq_left h2]; linarith
    · rw [max_eq_left h1, max_eq_right h2.le]; linarith
    · rw [max_eq_right h1.le, max_eq_left h2]; linarith
    · rw [max_eq_right h1.le, max_eq_right h2.le]; linarith
  · obtain rfl : j = 15 := by omega
    rw [hL1 15 (by norm_num), hsumI]
    simp only [show Ico (15 + 1) 16 = ∅ from rfl, Finset.sum_empty, zero_sub]
    rw [max_eq_left (by omega : -(π / 2) ≤ 0)]
    have : E + I - π / 2 = s := by rw [hIdef, hEdef]; ring
    rw [this, max_eq_right hs]; simp

end R1T
