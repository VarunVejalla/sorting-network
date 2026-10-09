module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # Two-sided geometric tail sum (Chvátal Lemma 6.2, claim (i))

If `g ≥ 0` decays by the factor `ρ < 1` going away from `a`, then `∑_{1≤s≤n} g(s) ≤ (g a + g (a+1))/(1-ρ)`. -/

@[expose] public section

namespace Chvatal

/-- Left tail: if `g s ≤ ρ g (s+1)` for `1 ≤ s < a` then `∑_{1≤s≤a} g s ≤ g a/(1-ρ)`. -/
theorem geom_left_sum (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) (g : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n) (a : ℕ)
    (h_dec : ∀ s, 1 ≤ s → s < a → g s ≤ ρ * g (s + 1)) :
    ∑ s ∈ Finset.Icc 1 a, g s ≤ g a / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith
  induction a with
  | zero => simpa using div_nonneg (hg 0) h1.le
  | succ a ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simpa using le_div_self (hg 1) h1 (by linarith)
    · have := ih fun s hs hsa => h_dec s hs (by omega)
      have hd := h_dec a ha (by omega)
      calc _ ≤ ρ * g (a + 1) / (1 - ρ) + g (a + 1) := by
            gcongr
            exact this.trans (by gcongr)
        _ = g (a + 1) / (1 - ρ) := by field_simp; ring

/-- Right tail: if `g (s+1) ≤ ρ g s` for `c ≤ s < n` then `∑_{c≤s≤n} g s ≤ g c/(1-ρ)`. -/
theorem geom_right_sum (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) (g : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n) (c n : ℕ)
    (h_dec : ∀ s, c ≤ s → s < n → g (s + 1) ≤ ρ * g s) :
    ∑ s ∈ Finset.Icc c n, g s ≤ g c / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith
  rcases lt_or_ge n c with hn | hn
  · simpa [Finset.Icc_eq_empty_of_lt hn] using div_nonneg (hg c) h1.le
  · have key : ∑ s ∈ Finset.Icc c n, g s ≤ (g c - ρ * g n) / (1 - ρ) := by
      induction n, hn using Nat.le_induction with
      | base => simp; rw [le_div_iff₀ h1]; exact le_of_eq (by ring)
      | succ n hn ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have := ih fun s hs hsn => h_dec s hs (by omega)
        have hd := h_dec n hn (by omega)
        calc _ ≤ (g c - ρ * g n) / (1 - ρ) + g (n + 1) := by gcongr
          _ = (g c - ρ * g n + (1 - ρ) * g (n + 1)) / (1 - ρ) := by field_simp
          _ ≤ _ := by gcongr; nlinarith
    exact key.trans (by gcongr; nlinarith [mul_nonneg hρ_pos.le (hg n)])

theorem geom_two_sided_sum (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) (g : ℕ → ℝ)
    (hg : ∀ n, 0 ≤ g n) (a n : ℕ) (ha_succ : a + 1 ≤ n)
    (h_dec_left : ∀ s, 1 ≤ s → s < a → g s ≤ ρ * g (s + 1))
    (h_dec_right : ∀ s, a + 1 ≤ s → s < n → g (s + 1) ≤ ρ * g s) :
    ∑ s ∈ Finset.Icc 1 n, g s ≤ (g a + g (a + 1)) / (1 - ρ) := by
  have hsplit : Finset.Icc 1 n = Finset.Icc 1 a ∪ Finset.Icc (a + 1) n := by
    ext s; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 a) (Finset.Icc (a + 1) n) := by
    rw [Finset.disjoint_left]; intro s h1 h2
    simp only [Finset.mem_Icc] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj, add_div]
  exact add_le_add (geom_left_sum ρ hρ_pos hρ_lt g hg a h_dec_left)
    (geom_right_sum ρ hρ_pos hρ_lt g hg (a + 1) n h_dec_right)

end Chvatal
