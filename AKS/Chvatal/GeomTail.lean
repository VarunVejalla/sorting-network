module
/-
  # Two-sided geometric tail sum (Chvátal Lemma 6.2, claim (i))

  Geometric series bounds for sums with multiplicative constraints:
  - Left tail: if g(s) decreases geometrically left, then ∑_{1≤s≤a} g(s) ≤ g(a)/(1-ρ)
  - Right tail: if g(s) decreases geometrically right, then ∑_{c≤s≤n} g(s) ≤ g(c)/(1-ρ)
  - Both tails: combined bound using midpoint a
-/

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.Field.GeomSum

@[expose] public section

namespace Chvatal

/-! # Left geometric tail (decreasing left from a) -/

/-- If g(s) ≤ ρ·g(s+1) for 1 ≤ s < a, then g(a-i) ≤ ρ^i · g(a) for i < a. -/
lemma geom_left_backward (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) (g : ℕ → ℝ)
    (hg_nonneg : ∀ n, 0 ≤ g n) (a : ℕ)
    (h_dec : ∀ s, 1 ≤ s → s < a → g s ≤ ρ * g (s + 1)) (i : ℕ) (hi : i < a) :
    g (a - i) ≤ ρ ^ i * g a := by
  induction i generalizing a with
  | zero =>
    norm_num
  | succ k hk =>
    have hi_succ : k < a := Nat.lt_trans (Nat.lt_succ_self k) hi
    have h_a_ge_k_plus_2 : k + 2 ≤ a := by omega
    have h_a_sub_k_ge_2 : 2 ≤ a - k := by omega
    have hak_succ : 1 ≤ a - k - 1 := by omega
    have h_s_lt_a_succ : a - k - 1 < a := by
      have : a - k - 1 + (k + 1) = a := by omega
      omega
    have h_apply := h_dec (a - k - 1) hak_succ h_s_lt_a_succ
    have h_eq : (a - k - 1 : ℕ) + 1 = a - k := by omega
    have h_a_minus_k_eq : a - (k + 1) = (a - k) - 1 := by omega
    rw [h_a_minus_k_eq]
    have h_eq' : g (a - k - 1 + 1) = g (a - k) := by rw [h_eq]
    have ih_result : g (a - k) ≤ ρ ^ k * g a := hk a h_dec hi_succ
    exact calc g ((a - k) - 1)
        ≤ ρ * g (a - k - 1 + 1) := h_apply
        _ = ρ * g (a - k) := by rw [h_eq']
        _ ≤ ρ * (ρ ^ k * g a) := by
          apply mul_le_mul_of_nonneg_left ih_result
          exact hρ_pos.le
        _ = ρ ^ (k + 1) * g a := by ring

/-- `Σ_{i<a} ρ^i ≤ 1/(1-ρ)`. -/
lemma geom_sum_le_inv (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) (a : ℕ) :
    ∑ i ∈ Finset.range a, ρ ^ i ≤ 1 / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith
  rw [le_div_iff₀ h1, mul_comm, mul_neg_geom_sum]
  have : 0 ≤ ρ ^ a := pow_nonneg hρ_pos.le a
  linarith

theorem geom_left_sum (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) (g : ℕ → ℝ)
    (hg_nonneg : ∀ n, 0 ≤ g n) (a : ℕ) (ha : 1 ≤ a)
    (h_dec : ∀ s, 1 ≤ s → s < a → g s ≤ ρ * g (s + 1)) :
    ∑ s ∈ Finset.Icc 1 a, g s ≤ g a / (1 - ρ) := by
  have hre : ∑ s ∈ Finset.Icc 1 a, g s = ∑ i ∈ Finset.range a, g (a - i) := by
    refine Finset.sum_nbij' (fun s => a - s) (fun i => a - i) ?_ ?_ ?_ ?_ ?_
    · intro s hs; simp only [Finset.mem_Icc] at hs; simp only [Finset.mem_range]; omega
    · intro i hi; simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
    · intro s hs; simp only [Finset.mem_Icc] at hs; show a - (a - s) = s; omega
    · intro i hi; simp only [Finset.mem_range] at hi; show a - (a - i) = i; omega
    · intro s hs; simp only [Finset.mem_Icc] at hs; show g s = g (a - (a - s)); congr 1; omega
  rw [hre]
  calc ∑ i ∈ Finset.range a, g (a - i)
      ≤ ∑ i ∈ Finset.range a, ρ ^ i * g a :=
        Finset.sum_le_sum fun i hi =>
          geom_left_backward ρ hρ_pos hρ_lt g hg_nonneg a h_dec i (Finset.mem_range.mp hi)
    _ = (∑ i ∈ Finset.range a, ρ ^ i) * g a := by rw [Finset.sum_mul]
    _ ≤ (1 / (1 - ρ)) * g a :=
        mul_le_mul_of_nonneg_right (geom_sum_le_inv ρ hρ_pos hρ_lt a) (hg_nonneg a)
    _ = g a / (1 - ρ) := by ring

lemma geom_right_forward (ρ : ℝ) (hρ_pos : 0 < ρ) (g : ℕ → ℝ) (c n : ℕ)
    (h_dec : ∀ s, c ≤ s → s < n → g (s + 1) ≤ ρ * g s) :
    ∀ i, c + i ≤ n → g (c + i) ≤ ρ ^ i * g c := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := h_dec (c + k) (by omega) (by omega)
    have h2 := ih (by omega)
    calc g (c + (k + 1)) = g (c + k + 1) := by rw [Nat.add_assoc]
      _ ≤ ρ * g (c + k) := h1
      _ ≤ ρ * (ρ ^ k * g c) := mul_le_mul_of_nonneg_left h2 hρ_pos.le
      _ = ρ ^ (k + 1) * g c := by ring

theorem geom_right_sum (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) (g : ℕ → ℝ)
    (hg_nonneg : ∀ n, 0 ≤ g n) (c n : ℕ)
    (h_dec : ∀ s, c ≤ s → s < n → g (s + 1) ≤ ρ * g s) :
    ∑ s ∈ Finset.Icc c n, g s ≤ g c / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith
  by_cases hcn : c ≤ n
  · have hre : ∑ s ∈ Finset.Icc c n, g s = ∑ i ∈ Finset.range (n + 1 - c), g (c + i) := by
      rw [← Finset.sum_Ico_eq_sum_range]
      rfl
    rw [hre]
    calc ∑ i ∈ Finset.range (n + 1 - c), g (c + i)
        ≤ ∑ i ∈ Finset.range (n + 1 - c), ρ ^ i * g c :=
          Finset.sum_le_sum fun i hi =>
            geom_right_forward ρ hρ_pos g c n h_dec i (by
              have := Finset.mem_range.mp hi; omega)
      _ = (∑ i ∈ Finset.range (n + 1 - c), ρ ^ i) * g c := by rw [Finset.sum_mul]
      _ ≤ (1 / (1 - ρ)) * g c :=
          mul_le_mul_of_nonneg_right (geom_sum_le_inv ρ hρ_pos hρ_lt _) (hg_nonneg c)
      _ = g c / (1 - ρ) := by ring
  · have : Finset.Icc c n = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, Finset.sum_empty]
    exact div_nonneg (hg_nonneg c) h1.le

/-! # Two-sided geometric tail -/

theorem geom_two_sided_sum (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1) (g : ℕ → ℝ)
    (hg_nonneg : ∀ n, 0 ≤ g n) (a n : ℕ) (ha : 1 ≤ a) (ha_succ : a + 1 ≤ n)
    (h_dec_left : ∀ s, 1 ≤ s → s < a → g s ≤ ρ * g (s + 1))
    (h_dec_right : ∀ s, a + 1 ≤ s → s < n → g (s + 1) ≤ ρ * g s) :
    ∑ s ∈ Finset.Icc 1 n, g s ≤ (g a + g (a + 1)) / (1 - ρ) := by
  have hsplit : Finset.Icc 1 n = Finset.Icc 1 a ∪ Finset.Icc (a + 1) n := by
    ext s; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Finset.Icc 1 a) (Finset.Icc (a + 1) n) := by
    rw [Finset.disjoint_left]; intro s h1 h2
    simp only [Finset.mem_Icc] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj, add_div]
  exact add_le_add (geom_left_sum ρ hρ_pos hρ_lt g hg_nonneg a ha h_dec_left)
    (geom_right_sum ρ hρ_pos hρ_lt g hg_nonneg (a + 1) n h_dec_right)

end Chvatal
