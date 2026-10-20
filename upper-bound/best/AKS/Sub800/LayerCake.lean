import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Discrete layer-cake bound for an exponential moment (W4 of LEAN-PLAN.md)

For a nonnegative `Y` on a finite sample `s` with a geometric tail beyond level `k₀ δ`,

  `Σ_ω e^{t Y ω} ≤ #s · e^{tδ} · (e^{t k₀ δ} + C (1 - e^{-tδ}) r^{k₀} / (1 - r))`,
  `r = e^{(t-θ)δ} < 1`,

given `#{Y ≥ k δ} ≤ C e^{-θ k δ} #s` for every `k ≥ k₀`. -/

open Finset BigOperators

namespace LayerCake

/-- Pointwise slicing: `e^{t y} ≤ e^{tδ} (1 + Σ_{1 ≤ k < N} a_k [kδ ≤ y])`, with
`a_k = e^{tkδ} - e^{t(k-1)δ}`, whenever `y < N δ`. -/
theorem exp_le_slices (t δ y : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ) (hy : 0 ≤ y) (N : ℕ)
    (hN : y < N * δ) :
    Real.exp (t * y) ≤ Real.exp (t * δ) * (1 + ∑ k ∈ Finset.range N,
      if 1 ≤ k ∧ (k : ℝ) * δ ≤ y then
        Real.exp (t * (k * δ)) - Real.exp (t * ((k - 1 : ℝ) * δ)) else 0) := by
  set K := ⌊y / δ⌋₊ with hK
  have hKy : (K : ℝ) * δ ≤ y := by
    have := Nat.floor_le (div_nonneg hy hδ.le)
    rw [← hK] at this
    calc (K : ℝ) * δ ≤ y / δ * δ := by gcongr
      _ = y := by field_simp
  have hyK : y < ((K : ℝ) + 1) * δ := by
    have := Nat.lt_floor_add_one (y / δ)
    rw [← hK] at this
    calc y = y / δ * δ := by field_simp
      _ < ((K : ℝ) + 1) * δ := by gcongr
  have hKN : K < N := by
    by_contra h
    push_neg at h
    have : (N : ℝ) * δ ≤ K * δ := by gcongr
    linarith
  -- the indicator selects exactly 1 ≤ k ≤ K
  have hsel : ∀ k ∈ Finset.range N, (1 ≤ k ∧ (k : ℝ) * δ ≤ y) ↔ k ∈ Finset.Icc 1 K := by
    intro k _
    rw [Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_contra h
      push_neg at h
      have : ((K : ℝ) + 1) * δ ≤ k * δ := by
        gcongr; exact_mod_cast h
      linarith
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      calc (k : ℝ) * δ ≤ K * δ := by gcongr
        _ ≤ y := hKy
  have hsum : ∑ k ∈ Finset.range N,
      (if 1 ≤ k ∧ (k : ℝ) * δ ≤ y then
        Real.exp (t * (k * δ)) - Real.exp (t * ((k - 1 : ℝ) * δ)) else 0) =
      Real.exp (t * (K * δ)) - 1 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfilt : (Finset.range N).filter (fun k : ℕ => 1 ≤ k ∧ (k : ℝ) * δ ≤ y) = Finset.Icc 1 K := by
      ext k
      constructor
      · intro hk
        rw [Finset.mem_filter] at hk
        exact (hsel k hk.1).1 hk.2
      · intro hk
        rw [Finset.mem_filter]
        have hkN : k ∈ Finset.range N := by
          rw [Finset.mem_range]; rw [Finset.mem_Icc] at hk; omega
        exact ⟨hkN, (hsel k hkN).2 hk⟩
    rw [hfilt]
    -- telescoping over Icc 1 K
    have tele : ∀ K : ℕ, ∑ k ∈ Finset.Icc 1 K,
        (Real.exp (t * (k * δ)) - Real.exp (t * ((k - 1 : ℝ) * δ))) =
        Real.exp (t * (K * δ)) - 1 := by
      intro K
      induction K with
      | zero => simp
      | succ K ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        push_cast
        ring_nf
    exact tele K
  rw [hsum]
  calc Real.exp (t * y) ≤ Real.exp (t * (((K : ℝ) + 1) * δ)) := by
        apply Real.exp_le_exp.2
        exact mul_le_mul_of_nonneg_left hyK.le ht
    _ = Real.exp (t * δ) * (1 + (Real.exp (t * (K * δ)) - 1)) := by
        rw [add_sub_cancel, ← Real.exp_add]; congr 1; ring

/-- Telescoping sum of the slice increments. -/
theorem tele (t δ : ℝ) : ∀ K : ℕ, ∑ k ∈ Finset.Icc 1 K,
    (Real.exp (t * (k * δ)) - Real.exp (t * ((k - 1 : ℝ) * δ))) = Real.exp (t * (K * δ)) - 1 := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring_nf

theorem slice_nonneg (t δ : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ) (k : ℕ) :
    0 ≤ Real.exp (t * (k * δ)) - Real.exp (t * ((k - 1 : ℝ) * δ)) := by
  have : t * ((k - 1 : ℝ) * δ) ≤ t * (k * δ) := by
    apply mul_le_mul_of_nonneg_left _ ht
    nlinarith
  linarith [Real.exp_le_exp.2 this]

theorem slice_eq (t δ : ℝ) (k : ℕ) :
    Real.exp (t * (k * δ)) - Real.exp (t * ((k - 1 : ℝ) * δ)) =
      (1 - Real.exp (-(t * δ))) * Real.exp (t * (k * δ)) := by
  have : Real.exp (t * ((k - 1 : ℝ) * δ)) = Real.exp (-(t * δ)) * Real.exp (t * (k * δ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring

theorem one_sub_exp_neg_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ 1 - Real.exp (-x) := by
  have : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

/-- **Discrete layer cake.** -/
theorem layer_cake {Ω : Type*} (s : Finset Ω) (Y : Ω → ℝ) (hY : ∀ ω ∈ s, 0 ≤ Y ω)
    (t θ δ C : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ) (htθ : t < θ) (hC : 0 ≤ C) (k₀ : ℕ)
    (htail : ∀ k : ℕ, k₀ < k →
      ((s.filter fun ω => (k : ℝ) * δ ≤ Y ω).card : ℝ) ≤
        C * Real.exp (-(θ * (k * δ))) * (s.card : ℝ)) :
    ∑ ω ∈ s, Real.exp (t * Y ω) ≤ (s.card : ℝ) * Real.exp (t * δ) *
      (Real.exp (t * (k₀ * δ)) + C * (1 - Real.exp (-(t * δ))) *
        Real.exp ((t - θ) * δ) ^ k₀ / (1 - Real.exp ((t - θ) * δ))) := by
  classical
  set r := Real.exp ((t - θ) * δ) with hr_def
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have hneg : (t - θ) * δ < 0 := by nlinarith
    calc r = Real.exp ((t - θ) * δ) := hr_def
      _ < Real.exp 0 := Real.exp_lt_exp.2 hneg
      _ = 1 := Real.exp_zero
  set a : ℕ → ℝ := fun k => Real.exp (t * (k * δ)) - Real.exp (t * ((k - 1 : ℝ) * δ)) with ha_def
  have ha0 : ∀ k, 0 ≤ a k := slice_nonneg t δ ht hδ
  have hq : 0 ≤ 1 - Real.exp (-(t * δ)) := one_sub_exp_neg_nonneg _ (by positivity)
  set N : ℕ := (s.sup fun ω => ⌊Y ω / δ⌋₊) + k₀ + 2 with hN_def
  have hYN : ∀ ω ∈ s, Y ω < N * δ := by
    intro ω hω
    have h1 : ⌊Y ω / δ⌋₊ ≤ s.sup fun ω => ⌊Y ω / δ⌋₊ :=
      Finset.le_sup (f := fun ω => ⌊Y ω / δ⌋₊) hω
    have h2 : Y ω / δ < (⌊Y ω / δ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : ((⌊Y ω / δ⌋₊ : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
      have : ⌊Y ω / δ⌋₊ + 1 ≤ N := by omega
      exact_mod_cast this
    have : Y ω / δ < N := by linarith
    calc Y ω = Y ω / δ * δ := by field_simp
      _ < N * δ := by gcongr
  have hk0N : k₀ + 1 ≤ N := by omega
  set cnt : ℕ → ℝ := fun k => ((s.filter fun ω => (k : ℝ) * δ ≤ Y ω).card : ℝ) with hcnt
  set b : ℕ → ℝ := fun k => (if 1 ≤ k then a k else 0) * cnt k with hb
  have step1 : ∑ ω ∈ s, Real.exp (t * Y ω) ≤
      Real.exp (t * δ) * ((s.card : ℝ) + ∑ k ∈ Finset.range N, b k) := by
    calc ∑ ω ∈ s, Real.exp (t * Y ω)
        ≤ ∑ ω ∈ s, Real.exp (t * δ) * (1 + ∑ k ∈ Finset.range N,
            if 1 ≤ k ∧ (k : ℝ) * δ ≤ Y ω then a k else 0) :=
          Finset.sum_le_sum fun ω hω => exp_le_slices t δ (Y ω) ht hδ (hY ω hω) N (hYN ω hω)
      _ = Real.exp (t * δ) * ((s.card : ℝ) + ∑ k ∈ Finset.range N, ∑ ω ∈ s,
            if 1 ≤ k ∧ (k : ℝ) * δ ≤ Y ω then a k else 0) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]
          simp
      _ = Real.exp (t * δ) * ((s.card : ℝ) + ∑ k ∈ Finset.range N, b k) := by
          congr 2
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [hb, hcnt]
          rw [Finset.card_filter]
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ω _ => ?_
          by_cases h1 : 1 ≤ k <;> by_cases h2 : (k : ℝ) * δ ≤ Y ω <;> simp [h1, h2]
  have hsplit : ∑ k ∈ Finset.range (k₀ + 1), b k + ∑ k ∈ Finset.Ico (k₀ + 1) N, b k =
      ∑ k ∈ Finset.range N, b k := Finset.sum_range_add_sum_Ico b hk0N
  have low : ∑ k ∈ Finset.range (k₀ + 1), b k ≤ (s.card : ℝ) * (Real.exp (t * (k₀ * δ)) - 1) := by
    have hcl : ∀ k, cnt k ≤ (s.card : ℝ) := fun k => by
      simp only [hcnt]; exact_mod_cast Finset.card_filter_le _ _
    calc ∑ k ∈ Finset.range (k₀ + 1), b k
        ≤ ∑ k ∈ Finset.range (k₀ + 1), (if 1 ≤ k then a k else 0) * (s.card : ℝ) := by
          refine Finset.sum_le_sum fun k _ => ?_
          simp only [hb]
          apply mul_le_mul_of_nonneg_left (hcl k)
          split_ifs
          · exact ha0 k
          · exact le_rfl
      _ = (s.card : ℝ) * ∑ k ∈ Finset.Icc 1 k₀, a k := by
          rw [Finset.mul_sum]
          have hf : Finset.Icc 1 k₀ = (Finset.range (k₀ + 1)).filter (fun k => 1 ≤ k) := by
            ext k; simp [Finset.mem_Icc]; omega
          rw [hf, Finset.sum_filter]
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> ring
      _ = (s.card : ℝ) * (Real.exp (t * (k₀ * δ)) - 1) := by rw [tele]
  have high : ∑ k ∈ Finset.Ico (k₀ + 1) N, b k ≤
      (s.card : ℝ) * (C * (1 - Real.exp (-(t * δ))) * r ^ k₀ / (1 - r)) := by
    have hterm : ∀ k ∈ Finset.Ico (k₀ + 1) N,
        b k ≤ (s.card : ℝ) * (C * (1 - Real.exp (-(t * δ)))) * r ^ k := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hk1 : 1 ≤ k := by omega
      simp only [hb, if_pos hk1]
      have hexp : Real.exp (t * (k * δ)) * Real.exp (-(θ * (k * δ))) = r ^ k := by
        rw [← Real.exp_add, hr_def, ← Real.exp_nat_mul]; congr 1; ring
      calc a k * cnt k ≤ a k * (C * Real.exp (-(θ * (k * δ))) * (s.card : ℝ)) :=
            mul_le_mul_of_nonneg_left (htail k (by omega)) (ha0 k)
        _ = (s.card : ℝ) * (C * (1 - Real.exp (-(t * δ)))) *
              (Real.exp (t * (k * δ)) * Real.exp (-(θ * (k * δ)))) := by
            simp only [ha_def]; rw [slice_eq]; ring
        _ = _ := by rw [hexp]
    calc ∑ k ∈ Finset.Ico (k₀ + 1) N, b k
        ≤ ∑ k ∈ Finset.Ico (k₀ + 1) N, (s.card : ℝ) * (C * (1 - Real.exp (-(t * δ)))) * r ^ k :=
          Finset.sum_le_sum hterm
      _ = (s.card : ℝ) * (C * (1 - Real.exp (-(t * δ)))) *
            ∑ k ∈ Finset.Ico (k₀ + 1) N, r ^ k := by rw [Finset.mul_sum]
      _ ≤ (s.card : ℝ) * (C * (1 - Real.exp (-(t * δ)))) * (r ^ (k₀ + 1) / (1 - r)) := by
          apply mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1)
          positivity
      _ ≤ (s.card : ℝ) * (C * (1 - Real.exp (-(t * δ)))) * (r ^ k₀ / (1 - r)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div_of_nonneg_right _ (by linarith)
          rw [pow_succ]
          nlinarith [pow_nonneg hr0 k₀]
      _ = _ := by ring
  have hE : 0 ≤ Real.exp (t * δ) := (Real.exp_pos _).le
  calc ∑ ω ∈ s, Real.exp (t * Y ω)
      ≤ Real.exp (t * δ) * ((s.card : ℝ) + ∑ k ∈ Finset.range N, b k) := step1
    _ ≤ Real.exp (t * δ) * ((s.card : ℝ) +
        ((s.card : ℝ) * (Real.exp (t * (k₀ * δ)) - 1) +
          (s.card : ℝ) * (C * (1 - Real.exp (-(t * δ))) * r ^ k₀ / (1 - r)))) := by
        apply mul_le_mul_of_nonneg_left _ hE
        rw [← hsplit]
        linarith
    _ = _ := by ring

end LayerCake
