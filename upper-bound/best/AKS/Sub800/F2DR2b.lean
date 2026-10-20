import AKS.Sub800.F2DR2

/-! # R2 for `F2PD`: closed bounds on `Zν` and `Yν`

* `Znu_le`: `Zν ≤ e²ν · e^G + 2 e^{-e²ν}`, given `g(s) ≤ G` for the integers `1 ≤ s < e²ν`, where
  `g(s) = s log(eν/s) + T_s log(e M s/(ν T_s))`; the terms `s ≥ e²ν` are summed geometrically.
* `Ynu_le`: `Yν ≤ (κ+1) (e² M ν / κ²)^κ` when `1 ≤ κ` and `κ² ≤ M ν`. -/

namespace Chvatal

open Finset

theorem pow_div_fact_le (ν : ℝ) (hν : 0 ≤ ν) (s : ℕ) (hs : 1 ≤ s) :
    ν ^ s / s.factorial ≤ (Real.exp 1 * ν / s) ^ s := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have h := Real.pow_div_factorial_le_exp (s : ℝ) hs0.le s
  have hf : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  rw [← Real.exp_one_pow, div_le_iff₀ hf] at h
  rw [div_pow, mul_pow, le_div_iff₀ (by positivity), div_mul_eq_mul_div, div_le_iff₀ hf]
  calc ν ^ s * (s : ℝ) ^ s ≤ ν ^ s * (Real.exp 1 ^ s * s.factorial) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
theorem Znu_le (n Φ E M : ℕ) (ν G : ℝ) (hν : 0 < ν) (hΦ : 1 ≤ Φ)
    (hR : Real.exp 1 * M ≤ ν * Φ)
    (hG : ∀ s : ℕ, 1 ≤ s → (s : ℝ) < Real.exp 2 * ν →
      (s : ℝ) * Real.log (Real.exp 1 * ν / s) +
        ((Φ * s + E : ℕ) : ℝ) * Real.log (Real.exp 1 * M * s / (ν * ((Φ * s + E : ℕ) : ℝ))) ≤ G) :
    Znu n Φ E M ν ≤ Real.exp 2 * ν * Real.exp G + 2 * Real.exp (-(Real.exp 2 * ν)) := by
  classical
  set X := Real.exp 2 * ν with hX
  have hX0 : 0 < X := by positivity
  set t : ℕ → ℝ := fun s => (ν ^ s / s.factorial) *
    (Real.exp 1 * M * s / (ν * ((Φ * s + E : ℕ) : ℝ))) ^ (Φ * s + E) with htdef
  have hsplit := Finset.sum_filter_add_sum_filter_not (Icc 1 n) (fun s : ℕ => (s : ℝ) < X) t
  unfold Znu
  rw [← hsplit]
  have hbase_nn : ∀ s : ℕ, 0 ≤ Real.exp 1 * M * s / (ν * ((Φ * s + E : ℕ) : ℝ)) := fun s => by
    positivity
  have hbase1 : ∀ s : ℕ, 1 ≤ s → Real.exp 1 * M * s / (ν * ((Φ * s + E : ℕ) : ℝ)) ≤ 1 := by
    intro s hs
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    have hT : (0 : ℝ) < ((Φ * s + E : ℕ) : ℝ) := by
      have : 0 < Φ * s + E := by have := Nat.mul_pos (by omega : 0 < Φ) hs; omega
      exact_mod_cast this
    rw [div_le_one (by positivity)]
    push_cast
    have hE : (0 : ℝ) ≤ E := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hR hs0.le, mul_nonneg hν.le hE]
  -- small s
  have h1 : ∑ s ∈ (Icc 1 n).filter (fun s : ℕ => (s : ℝ) < X), t s ≤ X * Real.exp G := by
    have hterm : ∀ s ∈ (Icc 1 n).filter (fun s : ℕ => (s : ℝ) < X), t s ≤ Real.exp G := by
      intro s hs
      obtain ⟨hs1, hsX⟩ := Finset.mem_filter.mp hs
      have hs1' := (Finset.mem_Icc.mp hs1).1
      have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1'
      have hT : (0 : ℝ) < ((Φ * s + E : ℕ) : ℝ) := by
        have : 0 < Φ * s + E := by have := Nat.mul_pos (by omega : 0 < Φ) hs1'; omega
        exact_mod_cast this
      have hb : 0 < Real.exp 1 * M * s / (ν * ((Φ * s + E : ℕ) : ℝ)) ∨ M = 0 := by
        rcases Nat.eq_zero_or_pos M with h | h
        · right; exact h
        · left; have : (0 : ℝ) < M := by exact_mod_cast h
          positivity
      have hp := pow_div_fact_le ν hν.le s hs1'
      rcases hb with hb | hM0
      · have heq : (Real.exp 1 * ν / s) ^ s *
            (Real.exp 1 * M * s / (ν * ((Φ * s + E : ℕ) : ℝ))) ^ (Φ * s + E) =
            Real.exp ((s : ℝ) * Real.log (Real.exp 1 * ν / s) +
              ((Φ * s + E : ℕ) : ℝ) * Real.log (Real.exp 1 * M * s / (ν * ((Φ * s + E : ℕ) : ℝ)))) := by
          rw [Real.exp_add, ← Real.log_rpow (by positivity), ← Real.log_rpow hb,
            Real.exp_log (by positivity), Real.exp_log (by positivity), Real.rpow_natCast,
            Real.rpow_natCast]
        calc t s ≤ (Real.exp 1 * ν / s) ^ s *
              (Real.exp 1 * M * s / (ν * ((Φ * s + E : ℕ) : ℝ))) ^ (Φ * s + E) :=
            mul_le_mul_of_nonneg_right hp (pow_nonneg (hbase_nn s) _)
          _ = _ := heq
          _ ≤ Real.exp G := Real.exp_le_exp.mpr (hG s hs1' hsX)
      · have hpos : 0 < Φ * s + E := by have := Nat.mul_pos (by omega : 0 < Φ) hs1'; omega
        simp only [htdef, hM0, Nat.cast_zero, mul_zero, zero_mul, zero_div,
          zero_pow hpos.ne', mul_zero]
        exact (Real.exp_pos G).le
    have hcard : (((Icc 1 n).filter (fun s : ℕ => (s : ℝ) < X)).card : ℝ) ≤ X := by
      have hsub : (Icc 1 n).filter (fun s : ℕ => (s : ℝ) < X) ⊆ Ico 1 ⌈X⌉₊ := by
        intro s hs
        obtain ⟨hs1, hsX⟩ := Finset.mem_filter.mp hs
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hs1).1, Nat.lt_ceil.mpr hsX⟩
      have h := Finset.card_le_card hsub
      rw [Nat.card_Ico] at h
      have hc : (⌈X⌉₊ : ℝ) < X + 1 := Nat.ceil_lt_add_one hX0.le
      have h' : ((((Icc 1 n).filter (fun s : ℕ => (s : ℝ) < X)).card : ℕ) : ℝ) ≤
          ((⌈X⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast h
      have h1c : 1 ≤ ⌈X⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
        rw [Ne, Nat.ceil_eq_zero, not_le]; exact hX0)
      rw [Nat.cast_sub h1c, Nat.cast_one] at h'
      linarith
    calc _ ≤ ∑ s ∈ (Icc 1 n).filter (fun s : ℕ => (s : ℝ) < X), Real.exp G := Finset.sum_le_sum hterm
      _ = (((Icc 1 n).filter (fun s : ℕ => (s : ℝ) < X)).card : ℝ) * Real.exp G := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ X * Real.exp G := mul_le_mul_of_nonneg_right hcard (Real.exp_pos G).le
  -- large s
  have h2 : ∑ s ∈ (Icc 1 n).filter (fun s : ℕ => ¬ (s : ℝ) < X), t s ≤ 2 * Real.exp (-X) := by
    set r : ℝ := Real.exp (-1) with hr
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := by rw [hr]; exact Real.exp_lt_one_iff.mpr (by norm_num) |>.trans_le' le_rfl
    have hterm : ∀ s ∈ (Icc 1 n).filter (fun s : ℕ => ¬ (s : ℝ) < X), t s ≤ r ^ s := by
      intro s hs
      obtain ⟨hs1, hsX⟩ := Finset.mem_filter.mp hs
      push_neg at hsX
      have hs1' := (Finset.mem_Icc.mp hs1).1
      have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1'
      have hp := pow_div_fact_le ν hν.le s hs1'
      have hq : Real.exp 1 * ν / s ≤ r := by
        rw [div_le_iff₀ hs0, hr]
        have : Real.exp 1 * ν * Real.exp 1 = Real.exp 2 * ν := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; ring
        have he := Real.exp_pos 1
        have h3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
        nlinarith [mul_le_mul_of_nonneg_left hsX (Real.exp_pos (-1)).le]
      calc t s ≤ (Real.exp 1 * ν / s) ^ s * 1 := by
            refine mul_le_mul hp ?_ (pow_nonneg (hbase_nn s) _) (by positivity)
            exact pow_le_one₀ (hbase_nn s) (hbase1 s hs1')
        _ ≤ r ^ s := by rw [mul_one]; exact pow_le_pow_left₀ (by positivity) hq _
    have hsub : (Icc 1 n).filter (fun s : ℕ => ¬ (s : ℝ) < X) ⊆ Ico ⌈X⌉₊ (n + 1) := by
      intro s hs
      obtain ⟨hs1, hsX⟩ := Finset.mem_filter.mp hs
      push_neg at hsX
      exact Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr hsX, Nat.lt_succ_of_le (Finset.mem_Icc.mp hs1).2⟩
    have hgeo := geom_sum_Ico_le_of_lt_one (m := ⌈X⌉₊) (n := n + 1) hr0 hr1
    have hrX : r ^ ⌈X⌉₊ ≤ Real.exp (-X) := by
      rw [hr, ← Real.exp_nat_mul, Real.exp_le_exp]
      have := Nat.le_ceil X
      linarith
    have hden : 1 / 2 ≤ 1 - r := by
      have : r ≤ 1 / 2 := by
        have he : (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
        rw [hr, Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
        linarith
      linarith
    calc _ ≤ ∑ s ∈ (Icc 1 n).filter (fun s : ℕ => ¬ (s : ℝ) < X), r ^ s := Finset.sum_le_sum hterm
      _ ≤ ∑ s ∈ Ico ⌈X⌉₊ (n + 1), r ^ s :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg hr0 _
      _ ≤ r ^ ⌈X⌉₊ / (1 - r) := hgeo
      _ ≤ Real.exp (-X) / (1 / 2) := div_le_div₀ (Real.exp_pos _).le hrX (by norm_num) hden
      _ = 2 * Real.exp (-X) := by ring
  linarith

theorem Ynu_le (κ M : ℕ) (ν : ℝ) (hν : 0 < ν) (hκ : 1 ≤ κ) (hκM : (κ : ℝ) ^ 2 ≤ M * ν) :
    Ynu κ M ν ≤ (κ + 1) * (Real.exp 2 * M * ν / (κ : ℝ) ^ 2) ^ κ := by
  have hMν : 0 < (M : ℝ) * ν := lt_of_lt_of_le (by positivity) hκM
  have hκ0 : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hkf : ∀ k : ℕ, (0 : ℝ) < k.factorial := fun k => by exact_mod_cast Nat.factorial_pos k
  have hterm : ∀ k ∈ range (κ + 1), (M.choose k : ℝ) * (ν ^ k / k.factorial) ≤
      ((M : ℝ) * ν) ^ κ / ((κ.factorial : ℝ) ^ 2) := by
    intro k hk
    have hk' : k ≤ κ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h1 : (M.choose k : ℝ) ≤ (M : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k M
    -- κ! ≤ k! κ^(κ-k)
    have hdf : (κ.factorial : ℝ) ≤ k.factorial * (κ : ℝ) ^ (κ - k) := by
      have e := Nat.factorial_mul_descFactorial (Nat.sub_le κ k)
      rw [Nat.sub_sub_self hk'] at e
      have h := Nat.descFactorial_le_pow κ (κ - k)
      have : κ.factorial ≤ k.factorial * κ ^ (κ - k) := by
        rw [← e]; exact Nat.mul_le_mul_left _ h
      exact_mod_cast this
    have hpow : ((κ : ℝ) ^ (κ - k)) ^ 2 ≤ ((M : ℝ) * ν) ^ (κ - k) := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by positivity) hκM _
    have hsplit : ((M : ℝ) * ν) ^ κ = ((M : ℝ) * ν) ^ k * ((M : ℝ) * ν) ^ (κ - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hk']
    calc (M.choose k : ℝ) * (ν ^ k / k.factorial)
        ≤ ((M : ℝ) ^ k / k.factorial) * (ν ^ k / k.factorial) :=
          mul_le_mul_of_nonneg_right h1 (by have := hkf k; positivity)
      _ = ((M : ℝ) * ν) ^ k / ((k.factorial : ℝ) ^ 2) := by rw [mul_pow]; ring
      _ ≤ ((M : ℝ) * ν) ^ κ / ((κ.factorial : ℝ) ^ 2) := by
          rw [div_le_div_iff₀ (by have := hkf k; positivity) (by have := hkf κ; positivity), hsplit]
          have hk2 : (κ.factorial : ℝ) ^ 2 ≤ (k.factorial : ℝ) ^ 2 * ((κ : ℝ) ^ (κ - k)) ^ 2 := by
            rw [← mul_pow]; exact pow_le_pow_left₀ (by have := hkf κ; positivity) hdf 2
          have hA : (0 : ℝ) ≤ ((M : ℝ) * ν) ^ k := by positivity
          calc ((M : ℝ) * ν) ^ k * (κ.factorial : ℝ) ^ 2
              ≤ ((M : ℝ) * ν) ^ k * ((k.factorial : ℝ) ^ 2 * ((κ : ℝ) ^ (κ - k)) ^ 2) :=
                mul_le_mul_of_nonneg_left hk2 hA
            _ ≤ ((M : ℝ) * ν) ^ k * ((k.factorial : ℝ) ^ 2 * ((M : ℝ) * ν) ^ (κ - k)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) hA
            _ = _ := by ring
  have hfac : ((M : ℝ) * ν) ^ κ / ((κ.factorial : ℝ) ^ 2) ≤ (Real.exp 2 * M * ν / (κ : ℝ) ^ 2) ^ κ := by
    have h := Real.pow_div_factorial_le_exp (κ : ℝ) hκ0.le κ
    have hf := hkf κ
    rw [div_le_iff₀ hf] at h
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have e2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have hk2 : ((κ : ℝ) ^ 2) ^ κ ≤ (Real.exp 1 ^ κ) ^ 2 * (κ.factorial : ℝ) ^ 2 := by
      rw [← pow_mul, mul_comm 2 κ, pow_mul, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by rw [Real.exp_one_pow] at *; linarith) 2
    calc ((M : ℝ) * ν) ^ κ * ((κ : ℝ) ^ 2) ^ κ
        ≤ ((M : ℝ) * ν) ^ κ * ((Real.exp 1 ^ κ) ^ 2 * (κ.factorial : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hk2 (by positivity)
      _ = (Real.exp 2 * M * ν) ^ κ * (κ.factorial : ℝ) ^ 2 := by
          rw [e2, mul_assoc, mul_pow (Real.exp 1 ^ 2), ← pow_mul, ← pow_mul, mul_comm 2 κ]; ring
  calc Ynu κ M ν ≤ ∑ _k ∈ range (κ + 1), ((M : ℝ) * ν) ^ κ / ((κ.factorial : ℝ) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = (κ + 1) * (((M : ℝ) * ν) ^ κ / ((κ.factorial : ℝ) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfac (by positivity)

end Chvatal
