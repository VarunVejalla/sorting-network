module

public import AKS.Chvatal.F2R2Count
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Numerics for the R2 failure bound at `b = 17000`, `c = 1/3`, `Φ ≥ 26208`

Per-`E` closed form (`F2ROUND.md` §4-§5, crude version): with `R = e B / (n Φ) ≤ 1/5000`,
`|ycap| · R^E · (exp(n R^20) - 1) ≤ (10^9 / 5000^19) · (27/50)^E`.
All constants are rational; `e` is bounded by `Real.exp_one_lt_d9`. -/

@[expose] public section

namespace Chvatal

theorem pow10_le (E κ : ℕ) (h : 3 * κ ≤ E + 2) : (10 : ℕ) ^ (10 * κ) ≤ 5000000 * 2200 ^ E := by
  have h3 : (10 ^ (10 * κ)) ^ 3 ≤ (5000000 * 2200 ^ E) ^ 3 := by
    calc (10 ^ (10 * κ)) ^ 3 = 10 ^ (30 * κ) := by rw [← pow_mul]; ring_nf
      _ ≤ 10 ^ (10 * E + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 10 ^ 20 * (10 ^ 10) ^ E := by rw [pow_add, ← pow_mul]; ring
      _ ≤ 5000000 ^ 3 * (2200 ^ 3) ^ E := by
          have : (10 ^ 10) ^ E ≤ (2200 ^ 3) ^ E := Nat.pow_le_pow_left (by norm_num) E
          calc 10 ^ 20 * (10 ^ 10) ^ E ≤ 10 ^ 20 * (2200 ^ 3) ^ E := Nat.mul_le_mul_left _ this
            _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)
      _ = (5000000 * 2200 ^ E) ^ 3 := by rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h3

theorem exp_sub_one_le_mul (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos x]

theorem exp_mul_nat_le (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 100) (E : ℕ) :
    Real.exp (t * E) ≤ (100 / 99 : ℝ) ^ E := by
  have h1 : Real.exp t ≤ 100 / 99 := by
    have h := Real.add_one_le_exp (-t)
    have h2 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos t]
  rw [mul_comm, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos t).le h1 E

theorem nat_le_geom (E : ℕ) : (E : ℝ) ≤ 10 * (11 / 10 : ℝ) ^ E := by
  have h := one_add_mul_le_pow (a := (1 / 10 : ℝ)) (by norm_num) E
  have : (1 + 1 / 10 : ℝ) = 11 / 10 := by norm_num
  rw [this] at h
  nlinarith

theorem count_R_le (n E κ B Φ : ℕ) (R : ℝ) (hE : 2 ≤ E) (hκ1 : E ≤ 3 * κ) (hκ2 : 3 * κ ≤ E + 2)
    (hB : B = 17000 * E) (hΦ : 26208 ≤ Φ) (hn2 : 2 * κ ≤ n) (hn : 0 < n)
    (hRdef : R = Real.exp 1 * B / (n * Φ)) (hR : R ≤ 1 / 5000) :
    ((ycap n κ (B - 1)).card : ℝ) * R ^ E ≤ E * (5000000 * (11 / 25 : ℝ) ^ E) := by
  have hκ : 1 ≤ κ := by omega
  have hY := ycap_card_le_real n κ (B - 1) B hκ hn2 (by omega) (Nat.sub_le _ _)
  have hκR : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hΦR : (26208 : ℝ) ≤ Φ := by exact_mod_cast hΦ
  have hnR0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hBR : (B : ℝ) = 17000 * E := by rw [hB]; push_cast; ring
  have hER : (E : ℝ) ≤ 3 * κ := by exact_mod_cast hκ1
  have hE2 : (2 : ℝ) ≤ E := by exact_mod_cast hE
  have hBpos : (0 : ℝ) < B := by rw [hBR]; linarith
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hκE : κ ≤ E := by omega
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hnR : (n : ℝ) * R = Real.exp 1 * B / Φ := by
    rw [hRdef]; field_simp
  have hbase : Real.exp 1 ^ 2 * n * B / (κ : ℝ) ^ 2 * R ≤ 2000000 := by
    have e1 : Real.exp 1 ^ 2 * n * B / (κ : ℝ) ^ 2 * R =
        Real.exp 1 ^ 2 * B / (κ : ℝ) ^ 2 * ((n : ℝ) * R) := by ring
    rw [e1, hnR, div_mul_div_comm, div_le_iff₀ (by positivity)]
    have hB2 : (B : ℝ) ≤ 51000 * κ := by rw [hBR]; linarith
    have hB3 : (B : ℝ) ^ 2 ≤ 51000 ^ 2 * (κ : ℝ) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hBpos.le hB2 2
    have he3 : Real.exp 1 ^ 3 ≤ 20.1 := by
      have : Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := pow_le_pow_left₀ he0.le he.le 3
      linarith [show (2.7182818286 : ℝ) ^ 3 ≤ 20.1 by norm_num]
    have hk2 : (0 : ℝ) ≤ (κ : ℝ) ^ 2 := by positivity
    calc Real.exp 1 ^ 2 * B * (Real.exp 1 * B) = Real.exp 1 ^ 3 * (B : ℝ) ^ 2 := by ring
      _ ≤ 20.1 * (51000 ^ 2 * (κ : ℝ) ^ 2) :=
          mul_le_mul he3 hB3 (by positivity) (by norm_num)
      _ ≤ 2000000 * ((κ : ℝ) ^ 2 * Φ) := by nlinarith [mul_nonneg hk2 (sub_nonneg.mpr hΦR)]
  have hkE : E = κ + (E - κ) := by omega
  have hRE : R ^ E = R ^ κ * R ^ (E - κ) := by rw [← pow_add]; congr 1
  have h1 : (Real.exp 1 ^ 2 * n * B / (κ : ℝ) ^ 2) ^ κ * R ^ E ≤
      (2000000 : ℝ) ^ κ * (1 / 5000 : ℝ) ^ (E - κ) := by
    rw [hRE, ← mul_assoc, ← mul_pow]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase κ)
      (pow_le_pow_left₀ hRpos.le hR _) (by positivity) (by positivity)
  have h2 : (2000000 : ℝ) ^ κ * (1 / 5000 : ℝ) ^ (E - κ) ≤ 5000000 * (11 / 25 : ℝ) ^ E := by
    have e1 : (2000000 : ℝ) ^ κ * (1 / 5000 : ℝ) ^ (E - κ) =
        ((10 : ℝ) ^ (10 * κ)) * (1 / 5000 : ℝ) ^ E := by
      have : (1 / 5000 : ℝ) ^ E = (1 / 5000) ^ κ * (1 / 5000) ^ (E - κ) := by
        rw [← pow_add]; congr 1
      rw [this, pow_mul, show (10 : ℝ) ^ 10 = 2000000 * 5000 by norm_num, mul_pow,
        mul_assoc, ← mul_assoc ((5000 : ℝ) ^ κ), ← mul_pow]
      rw [show (5000 : ℝ) * (1 / 5000) = 1 by norm_num, one_pow, one_mul]
    rw [e1]
    have h10 : ((10 : ℝ) ^ (10 * κ)) ≤ 5000000 * 2200 ^ E := by exact_mod_cast pow10_le E κ hκ2
    calc ((10 : ℝ) ^ (10 * κ)) * (1 / 5000 : ℝ) ^ E
        ≤ (5000000 * 2200 ^ E) * (1 / 5000 : ℝ) ^ E :=
          mul_le_mul_of_nonneg_right h10 (by positivity)
      _ = 5000000 * (11 / 25 : ℝ) ^ E := by
          rw [mul_assoc, ← mul_pow]; norm_num
  have hκ1R : ((κ : ℝ) + 1) ≤ E := by exact_mod_cast (by omega : κ + 1 ≤ E)
  calc ((ycap n κ (B - 1)).card : ℝ) * R ^ E
      ≤ (((κ : ℝ) + 1) * (Real.exp 1 ^ 2 * n * B / (κ : ℝ) ^ 2) ^ κ) * R ^ E :=
        mul_le_mul_of_nonneg_right hY (by positivity)
    _ = ((κ : ℝ) + 1) * ((Real.exp 1 ^ 2 * n * B / (κ : ℝ) ^ 2) ^ κ * R ^ E) := by ring
    _ ≤ ((κ : ℝ) + 1) * (5000000 * (11 / 25 : ℝ) ^ E) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hκ1R (by positivity)

theorem exp_factor_le (n E B Φ : ℕ) (R : ℝ) (hE : 2 ≤ E) (hB : B = 17000 * E) (hΦ : 26208 ≤ Φ) (hn : 0 < n)
    (hRdef : R = Real.exp 1 * B / (n * Φ)) (hR : R ≤ 1 / 5000) :
    Real.exp (n * R ^ 20) - 1 ≤ (2 / 5000 ^ 19) * E * (100 / 99 : ℝ) ^ E := by
  have hΦR : (26208 : ℝ) ≤ Φ := by exact_mod_cast hΦ
  have hnR0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hBR : (B : ℝ) = 17000 * E := by rw [hB]; push_cast; ring
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have he := Real.exp_one_lt_d9
  have hRpos : 0 < R := by
    rw [hRdef]
    have : (0 : ℝ) < Φ := by linarith
    have : (0 : ℝ) < B := by
      rw [hBR]; have : (2 : ℝ) ≤ E := by exact_mod_cast hE
      linarith
    positivity
  have hnR : (n : ℝ) * R = Real.exp 1 * B / Φ := by
    rw [hRdef]; field_simp
  have h1 : (n : ℝ) * R ≤ 2 * E := by
    rw [hnR, div_le_iff₀ (by linarith), hBR]
    have : Real.exp 1 * (17000 * (E : ℝ)) ≤ 2.7182818286 * (17000 * E) :=
      mul_le_mul_of_nonneg_right he.le (by positivity)
    nlinarith [mul_nonneg hE0 (sub_nonneg.mpr hΦR)]
  have hR19 : R ^ 19 ≤ (1 / 5000 : ℝ) ^ 19 := pow_le_pow_left₀ hRpos.le hR 19
  have hx : (n : ℝ) * R ^ 20 ≤ (2 / 5000 ^ 19) * E := by
    have : (n : ℝ) * R ^ 20 = ((n : ℝ) * R) * R ^ 19 := by ring
    rw [this]
    calc ((n : ℝ) * R) * R ^ 19 ≤ (2 * E) * (1 / 5000 : ℝ) ^ 19 :=
          mul_le_mul h1 hR19 (by positivity) (by positivity)
      _ = _ := by norm_num; ring
  have hx0 : 0 ≤ (n : ℝ) * R ^ 20 := by positivity
  have hε : (2 / 5000 ^ 19 : ℝ) ≤ 1 / 100 := by norm_num
  calc Real.exp (n * R ^ 20) - 1 ≤ (n * R ^ 20) * Real.exp (n * R ^ 20) :=
        exp_sub_one_le_mul _
    _ ≤ ((2 / 5000 ^ 19) * E) * Real.exp ((2 / 5000 ^ 19) * E) :=
        mul_le_mul hx (Real.exp_le_exp.mpr hx) (Real.exp_pos _).le (by positivity)
    _ ≤ ((2 / 5000 ^ 19) * E) * (100 / 99 : ℝ) ^ E :=
        mul_le_mul_of_nonneg_left (exp_mul_nat_le _ (by positivity) hε E) (by positivity)

/-- **Per-`E` closed form.** -/
theorem perE_le (n E κ B Φ : ℕ) (R : ℝ) (hE : 2 ≤ E) (hκ1 : E ≤ 3 * κ) (hκ2 : 3 * κ ≤ E + 2)
    (hB : B = 17000 * E) (hΦ : 26208 ≤ Φ) (hn2 : 2 * κ ≤ n) (hn : 0 < n)
    (hRdef : R = Real.exp 1 * B / (n * Φ)) (hR : R ≤ 1 / 5000) :
    ((ycap n κ (B - 1)).card : ℝ) * (R ^ E * (Real.exp (n * R ^ 20) - 1)) ≤
      (10 ^ 9 / 5000 ^ 19) * (27 / 50 : ℝ) ^ E := by
  have h1 := count_R_le n E κ B Φ R hE hκ1 hκ2 hB hΦ hn2 hn hRdef hR
  have h2 := exp_factor_le n E B Φ R hE hB hΦ hn hRdef hR
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have h3 : (E : ℝ) * E ≤ 100 * (121 / 100 : ℝ) ^ E := by
    have := nat_le_geom E
    calc (E : ℝ) * E ≤ (10 * (11 / 10 : ℝ) ^ E) * (10 * (11 / 10 : ℝ) ^ E) :=
          mul_le_mul this this hE0 (by positivity)
      _ = 100 * (121 / 100 : ℝ) ^ E := by
          rw [show (121 / 100 : ℝ) = 11 / 10 * (11 / 10) by norm_num, mul_pow]; ring
  have hexp0 : 0 ≤ Real.exp (n * R ^ 20) - 1 := by
    have : 1 ≤ Real.exp (n * R ^ 20) := Real.one_le_exp (by
      have : 0 ≤ R := by rw [hRdef]; positivity
      positivity)
    linarith
  calc ((ycap n κ (B - 1)).card : ℝ) * (R ^ E * (Real.exp (n * R ^ 20) - 1))
      = (((ycap n κ (B - 1)).card : ℝ) * R ^ E) * (Real.exp (n * R ^ 20) - 1) := by ring
    _ ≤ (E * (5000000 * (11 / 25 : ℝ) ^ E)) * ((2 / 5000 ^ 19) * E * (100 / 99 : ℝ) ^ E) :=
        mul_le_mul h1 h2 hexp0 (by positivity)
    _ = (10 ^ 7 / 5000 ^ 19) * ((E : ℝ) * E) * ((11 / 25 : ℝ) ^ E * (100 / 99 : ℝ) ^ E) := by
        ring
    _ ≤ (10 ^ 7 / 5000 ^ 19) * (100 * (121 / 100 : ℝ) ^ E) *
          ((11 / 25 : ℝ) ^ E * (100 / 99 : ℝ) ^ E) := by
        gcongr
    _ = (10 ^ 9 / 5000 ^ 19) * ((121 / 100 : ℝ) * (11 / 25) * (100 / 99)) ^ E := by
        rw [mul_pow, mul_pow]; ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) E)
          (by norm_num)

/-- Case `n < 2κ` (small `n` relative to `E`): support-free count `C(B-1+n, n)`. -/
theorem caseB_le (n E κ B Φ : ℕ) (R : ℝ) (hE : 2 ≤ E) (hκ2 : 3 * κ ≤ E + 2)
    (hB : B = 17000 * E) (hΦ : 26208 ≤ Φ) (hn : 16 ≤ n) (hnκ : n < 2 * κ)
    (hEn : 5 * E ≤ 16 * n)
    (hRdef : R = Real.exp 1 * B / (n * Φ)) (hR : R ≤ 1 / 5900) :
    ((ycap n κ (B - 1)).card : ℝ) * (R ^ E * (Real.exp (n * R ^ 20) - 1)) ≤
      (10 ^ 9 / 5000 ^ 19) * (17 / 20 : ℝ) ^ E := by
  have hn0 : 0 < n := by omega
  have hnR0 : (0 : ℝ) < n := by exact_mod_cast hn0
  have hΦR : (26208 : ℝ) ≤ Φ := by exact_mod_cast hΦ
  have hBR : (B : ℝ) = 17000 * E := by rw [hB]; push_cast; ring
  have hE2 : (2 : ℝ) ≤ E := by exact_mod_cast hE
  have hRpos : 0 < R := by rw [hRdef]; have : (0 : ℝ) < B := by rw [hBR]; linarith
                           positivity
  have hR5 : R ≤ 1 / 5000 := hR.trans (by norm_num)
  have h2 := exp_factor_le n E B Φ R hE hB hΦ hn0 hRdef hR5
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  -- count
  have hc1 : ((ycap n κ (B - 1)).card : ℝ) ≤ 148000 ^ n := by
    have h := ycap_card_le_choose n κ (B - 1)
    have h' : ((Nat.choose (B - 1 + n) n : ℕ) : ℝ) ≤
        (Real.exp 1 * ((B - 1 + n : ℕ) : ℝ) / n) ^ n := choose_le_exp_pow _ (by omega)
    have h3 : B - 1 + n ≤ 54401 * n := by omega
    have h4 : ((B - 1 + n : ℕ) : ℝ) / n ≤ 54401 := by
      rw [div_le_iff₀ hnR0]; exact_mod_cast h3
    have h5 : Real.exp 1 * ((B - 1 + n : ℕ) : ℝ) / n ≤ 148000 := by
      rw [mul_div_assoc]
      calc Real.exp 1 * (((B - 1 + n : ℕ) : ℝ) / n) ≤ 2.7182818286 * 54401 :=
            mul_le_mul he.le h4 (by positivity) (by norm_num)
        _ ≤ 148000 := by norm_num
    calc ((ycap n κ (B - 1)).card : ℝ) ≤ ((Nat.choose (B - 1 + n) n : ℕ) : ℝ) := by
          exact_mod_cast h
      _ ≤ _ := h'
      _ ≤ 148000 ^ n := pow_le_pow_left₀ (by positivity) h5 n
  -- main
  have h3n : 3 * n ≤ 2 * E + 3 := by omega
  have hsq : ((148000 : ℝ) ^ n * R ^ E) ^ 2 ≤ (500000 * (33 / 100 : ℝ) ^ n) ^ 2 := by
    have hRE : R ^ E ≤ (1 / 5900 : ℝ) ^ E := pow_le_pow_left₀ hRpos.le hR E
    have h1 : ((148000 : ℝ) ^ n * R ^ E) ^ 2 ≤ ((148000 : ℝ) ^ n * (1 / 5900 : ℝ) ^ E) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hRE (by positivity)) 2
    refine h1.trans ?_
    have h6 : (1 / 5900 : ℝ) ^ (2 * E) ≤ (1 / 5900 : ℝ) ^ (3 * n - 3) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h7 : (1 / 5900 : ℝ) ^ (3 * n - 3) = 5900 ^ 3 * ((1 / 5900 : ℝ) ^ 3) ^ n := by
      have : (1 / 5900 : ℝ) ^ (3 * n) = (1 / 5900 : ℝ) ^ (3 * n - 3) * (1 / 5900) ^ 3 := by
        rw [← pow_add]; congr 1; omega
      have hpow3 : (1 / 5900 : ℝ) ^ (3 * n) = ((1 / 5900 : ℝ) ^ 3) ^ n := by
        rw [← pow_mul, mul_comm]
      have hc : (5900 : ℝ) ^ 3 * (1 / 5900) ^ 3 = 1 := by norm_num
      rw [← hpow3, this, ← mul_assoc, mul_comm ((5900 : ℝ) ^ 3), mul_assoc, hc, mul_one]
    have h8 : ((148000 : ℝ) ^ n * (1 / 5900 : ℝ) ^ E) ^ 2 =
        ((148000 : ℝ) ^ 2) ^ n * (1 / 5900 : ℝ) ^ (2 * E) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm n 2, Nat.mul_comm E 2]
    rw [h8]
    calc ((148000 : ℝ) ^ 2) ^ n * (1 / 5900 : ℝ) ^ (2 * E)
        ≤ ((148000 : ℝ) ^ 2) ^ n * (5900 ^ 3 * ((1 / 5900 : ℝ) ^ 3) ^ n) :=
          mul_le_mul_of_nonneg_left (h6.trans h7.le) (by positivity)
      _ = 5900 ^ 3 * (((148000 : ℝ) ^ 2) * (1 / 5900 : ℝ) ^ 3) ^ n := by rw [mul_pow]; ring
      _ ≤ 500000 ^ 2 * (((33 / 100 : ℝ)) ^ 2) ^ n := by
          refine mul_le_mul (by norm_num) (pow_le_pow_left₀ (by positivity) (by norm_num) n)
            (by positivity) (by positivity)
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n 2]
  have hmain : (148000 : ℝ) ^ n * R ^ E ≤ 500000 * (33 / 100 : ℝ) ^ n :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (two_ne_zero)).mp hsq
  have hqr : (33 / 100 : ℝ) ^ n ≤ (18 / 25 : ℝ) ^ E := by
    have h16 : ((33 / 100 : ℝ) ^ n) ^ 16 ≤ ((18 / 25 : ℝ) ^ E) ^ 16 := by
      rw [← pow_mul, ← pow_mul, mul_comm n 16, mul_comm E 16]
      calc (33 / 100 : ℝ) ^ (16 * n) ≤ (33 / 100 : ℝ) ^ (5 * E) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hEn
        _ = ((33 / 100 : ℝ) ^ 5) ^ E := by rw [← pow_mul]
        _ ≤ ((18 / 25 : ℝ) ^ 16) ^ E :=
            pow_le_pow_left₀ (by positivity) (by norm_num) E
        _ = (18 / 25 : ℝ) ^ (16 * E) := by rw [← pow_mul]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h16
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hexp0 : 0 ≤ Real.exp (n * R ^ 20) - 1 := by
    have : 1 ≤ Real.exp (n * R ^ 20) := Real.one_le_exp (by positivity)
    linarith
  have hE10 := nat_le_geom E
  calc ((ycap n κ (B - 1)).card : ℝ) * (R ^ E * (Real.exp (n * R ^ 20) - 1))
      = (((ycap n κ (B - 1)).card : ℝ) * R ^ E) * (Real.exp (n * R ^ 20) - 1) := by ring
    _ ≤ (500000 * (18 / 25 : ℝ) ^ E) * ((2 / 5000 ^ 19) * E * (100 / 99 : ℝ) ^ E) := by
        refine mul_le_mul ?_ h2 hexp0 (by positivity)
        calc ((ycap n κ (B - 1)).card : ℝ) * R ^ E ≤ 148000 ^ n * R ^ E :=
              mul_le_mul_of_nonneg_right hc1 (by positivity)
          _ ≤ _ := hmain.trans (mul_le_mul_of_nonneg_left hqr (by norm_num))
    _ = (10 ^ 6 / 5000 ^ 19) * (E : ℝ) * ((18 / 25 : ℝ) ^ E * (100 / 99 : ℝ) ^ E) := by ring
    _ ≤ (10 ^ 6 / 5000 ^ 19) * (10 * (11 / 10 : ℝ) ^ E) * ((18 / 25 : ℝ) ^ E * (100 / 99 : ℝ) ^ E) := by
        gcongr
    _ = (10 ^ 7 / 5000 ^ 19) * ((11 / 10 : ℝ) * (18 / 25) * (100 / 99)) ^ E := by
        rw [mul_pow, mul_pow]; ring
    _ ≤ _ := by
        refine mul_le_mul (by norm_num) (pow_le_pow_left₀ (by norm_num) (by norm_num) E)
          (by positivity) (by norm_num)

/-- Either case: the per-`E` closed form with ratio `17/20`. -/
theorem perE_all (n E κ B Φ : ℕ) (R : ℝ) (hE : 2 ≤ E) (hκ1 : E ≤ 3 * κ) (hκ2 : 3 * κ ≤ E + 2)
    (hB : B = 17000 * E) (hΦ : 26208 ≤ Φ) (hn : 16 ≤ n) (hEn : 5 * E ≤ 16 * n)
    (hRdef : R = Real.exp 1 * B / (n * Φ)) (hR : R ≤ 1 / 5900) :
    ((ycap n κ (B - 1)).card : ℝ) * (R ^ E * (Real.exp (n * R ^ 20) - 1)) ≤
      (10 ^ 9 / 5000 ^ 19) * (17 / 20 : ℝ) ^ E := by
  by_cases h : 2 * κ ≤ n
  · refine (perE_le n E κ B Φ R hE hκ1 hκ2 hB hΦ h (by omega) hRdef (hR.trans (by norm_num))).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) E) (by norm_num)
  · exact caseB_le n E κ B Φ R hE hκ2 hB hΦ hn (by omega) hEn hRdef hR

end Chvatal
