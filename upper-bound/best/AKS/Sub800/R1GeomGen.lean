import Mathlib.Tactic

/-! # Separator geometry, generic in the fringe class and the row window

A sender of capacity `c = 2^19 X` with `π/2 = K X` and `aL X ≤ a ≤ aH X` gets the padded rectangle
with `n = ⌊(π/2)/(f+1)⌋` columns and `m + 1 = ⌈a/n⌉` rows. `GeomOK` collects the rational checks
under which, for every `X ≥ X0`, this rectangle lies in the row window `[Mlo, 2^q]`, protects the
fringe (`(f+1) n ≤ π/2`), supports the fringe range (`μ c ≤ δ_F f n`) and fits the Property-B
budget (`ε_B/2 (m+1) n + n ≤ (ε_B η + γ) c/2`); `geom` proves those consequences.

`BonlyOK` is the same for the B-only rectangle of a large root (`n = ⌈a/2^q⌉`, `2^s < a ≤ 4104 c/4096`).
-/

namespace R1T

/-- The checks of one fringe class. -/
def GeomOK (f K aL aH X0 Mlo q : ℕ) (mu dF epsB eta gam : ℚ) : Prop :=
  16 * (f + 1) ≤ K * X0 ∧ (Mlo - 1) * K < aL * (f + 1) ∧ f + 1 ≤ Mlo ∧ K ≤ aL ∧ 0 < X0 ∧
    aH * (f + 1) ≤ 2 ^ q * K ∧ aH * X0 * (f + 1) + 2 ^ q * f ≤ 2 ^ q * K * X0 ∧
    mu * 524288 * (f + 1) ≤ dF * f * K ∧
    mu * 524288 * X0 * (f + 1) + dF * f * f ≤ dF * f * K * X0 ∧
    epsB / 2 * aH + (epsB / 2 + 1) * K / (f + 1) ≤ (epsB * eta + gam) * 262144 ∧
    0 ≤ epsB ∧ 0 ≤ dF

instance (f K aL aH X0 Mlo q : ℕ) (mu dF epsB eta gam : ℚ) :
    Decidable (GeomOK f K aL aH X0 Mlo q mu dF epsB eta gam) := by
  unfold GeomOK; infer_instance

/-- **Generic geometry.** -/
theorem geom {f K aL aH X0 Mlo q : ℕ} {mu dF epsB eta gam : ℚ}
    (h : GeomOK f K aL aH X0 Mlo q mu dF epsB eta gam)
    (a π X : ℕ) (hπ : π / 2 = K * X) (hL : aL * X ≤ a) (hH : a ≤ aH * X) (hX : X0 ≤ X) :
    ∃ m n : ℕ, 16 ≤ n ∧ a ≤ (m + 1) * n ∧ m * n ≤ a ∧ f ≤ m ∧ Mlo ≤ m + 1 ∧ m + 1 ≤ 2 ^ q ∧
      π / 2 ≤ a ∧ (f + 1) * n ≤ π / 2 ∧
      ((mu : ℚ) : ℝ) * ((524288 * X : ℕ) : ℝ) ≤ (dF : ℝ) * ((f : ℝ) * n) ∧
      (epsB : ℝ) / 2 * (((m + 1 : ℕ) : ℝ) * n) + n ≤
        ((((epsB * eta + gam) * ((524288 * X : ℕ) : ℚ) / 2 : ℚ)) : ℝ) := by
  obtain ⟨h16, hlo, hfM, hKa, hX0, hq1, hq2, hs1, hs2, heb, hepsB, hdF⟩ := h
  have hf1 : 0 < f + 1 := by omega
  set n := π / 2 / (f + 1) with hn
  -- `n (f+1) ≤ K X < (n+1)(f+1)`
  have hn1 : n * (f + 1) ≤ K * X := by rw [← hπ]; exact Nat.div_mul_le_self _ _
  have hn2 : K * X < (f + 1) * (n + 1) := by rw [← hπ]; exact Nat.lt_mul_div_succ _ hf1
  have hKX0 : K * X0 ≤ K * X := Nat.mul_le_mul_left K hX
  have hn16 : 16 ≤ n := by
    rw [hn, Nat.le_div_iff_mul_le hf1, hπ]; nlinarith
  have hnpos : 0 < n := by omega
  have hKaX : K * X ≤ aL * X := Nat.mul_le_mul_right X hKa
  have hapos : 0 < a := by nlinarith
  set m := (a - 1) / n with hm
  have hm1 : m * n ≤ a - 1 := Nat.div_mul_le_self _ _
  have hm2 : a - 1 < n * (m + 1) := Nat.lt_mul_div_succ _ hnpos
  have hamn : a ≤ (m + 1) * n := by rw [Nat.mul_comm] at hm2; omega
  have hmna : m * n ≤ a := by omega
  -- lower window
  have hXpos : 0 < X := by omega
  have hMlo : Mlo ≤ m + 1 := by
    by_contra hc
    have h1 : m + 1 ≤ Mlo - 1 := by omega
    have h2 : a * (f + 1) ≤ (Mlo - 1) * (n * (f + 1)) := by
      calc a * (f + 1) ≤ (m + 1) * n * (f + 1) := Nat.mul_le_mul_right _ hamn
        _ ≤ (Mlo - 1) * n * (f + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
        _ = (Mlo - 1) * (n * (f + 1)) := by ring
    have h3 : (Mlo - 1) * (n * (f + 1)) ≤ (Mlo - 1) * (K * X) := Nat.mul_le_mul_left _ hn1
    have h4 : aL * X * (f + 1) ≤ a * (f + 1) := Nat.mul_le_mul_right _ hL
    have h5 : (Mlo - 1) * K * X < aL * (f + 1) * X := Nat.mul_lt_mul_of_pos_right hlo hXpos
    have e1 : (Mlo - 1) * (K * X) = (Mlo - 1) * K * X := by ring
    have e2 : aL * X * (f + 1) = aL * (f + 1) * X := by ring
    omega
  -- upper window: `2^q n ≥ aH X ≥ a > m n`
  have hup : aH * X ≤ 2 ^ q * n := by
    have hlin : aH * X * (f + 1) + 2 ^ q * f ≤ 2 ^ q * K * X := by
      have hc : aH * (f + 1) ≤ 2 ^ q * K := hq1
      have : (2 ^ q * K - aH * (f + 1)) * X0 ≤ (2 ^ q * K - aH * (f + 1)) * X :=
        Nat.mul_le_mul_left _ hX
      have e3 : (2 ^ q * K - aH * (f + 1)) * X0 + aH * X0 * (f + 1) = 2 ^ q * K * X0 := by
        have : aH * X0 * (f + 1) = aH * (f + 1) * X0 := by ring
        rw [this, ← Nat.add_mul, Nat.sub_add_cancel hc]
      have e4 : (2 ^ q * K - aH * (f + 1)) * X + aH * X * (f + 1) = 2 ^ q * K * X := by
        have : aH * X * (f + 1) = aH * (f + 1) * X := by ring
        rw [this, ← Nat.add_mul, Nat.sub_add_cancel hc]
      omega
    have hKX : K * X ≤ (f + 1) * n + f := by
      have e : (f + 1) * (n + 1) = (f + 1) * n + f + 1 := by ring
      omega
    have h6 : 2 ^ q * (K * X) ≤ 2 ^ q * ((f + 1) * n + f) := Nat.mul_le_mul_left _ hKX
    have e5 : 2 ^ q * ((f + 1) * n + f) = 2 ^ q * n * (f + 1) + 2 ^ q * f := by ring
    have e6 : 2 ^ q * (K * X) = 2 ^ q * K * X := by ring
    have h7 : aH * X * (f + 1) ≤ 2 ^ q * n * (f + 1) := by omega
    exact Nat.le_of_mul_le_mul_right h7 hf1
  have hmq : m + 1 ≤ 2 ^ q := by
    have h8 : m * n < 2 ^ q * n := by
      calc m * n ≤ a - 1 := hm1
        _ < a := by omega
        _ ≤ aH * X := hH
        _ ≤ 2 ^ q * n := hup
    have := Nat.lt_of_mul_lt_mul_right h8
    omega
  have hfr : (f + 1) * n ≤ π / 2 := by rw [hπ, Nat.mul_comm]; exact hn1
  refine ⟨m, n, hn16, hamn, hmna, by omega, hMlo, hmq, by rw [hπ]; exact hKaX.trans hL, hfr, ?_, ?_⟩
  · -- support: `μ 2^19 X (f+1) ≤ δ_F f (K X − f) ≤ δ_F f n (f+1)`
    have hnK : (K : ℚ) * X ≤ (f + 1) * n + f := by
      have : K * X ≤ (f + 1) * n + f := by
        have e : (f + 1) * (n + 1) = (f + 1) * n + f + 1 := by ring
        omega
      exact_mod_cast this
    have hXq : (X0 : ℚ) ≤ X := by exact_mod_cast hX
    have hs1' : (mu * 524288 * (f + 1) : ℚ) ≤ dF * f * K := by exact_mod_cast hs1
    have hs2' : (mu * 524288 * X0 * (f + 1) + dF * f * f : ℚ) ≤ dF * f * K * X0 := by exact_mod_cast hs2
    have hf0 : (0 : ℚ) ≤ f := by positivity
    have hkey : mu * 524288 * X * (f + 1) ≤ dF * f * ((f + 1) * n) := by
      have hA : mu * 524288 * X * (f + 1) + dF * f * f ≤ dF * f * K * X := by
        linarith [mul_le_mul_of_nonneg_left hXq (sub_nonneg.2 hs1')]
      have hB : dF * f * (K * X) ≤ dF * f * ((f + 1) * n + f) :=
        mul_le_mul_of_nonneg_left hnK (mul_nonneg hdF hf0)
      linarith
    have hf1q : (0 : ℚ) < f + 1 := by positivity
    have : mu * ((524288 * X : ℕ) : ℚ) ≤ dF * (f * n) := by
      push_cast
      have := (mul_le_mul_iff_of_pos_right hf1q).1 (by linarith : mu * (524288 * X) * (f + 1) ≤
        dF * (f * n) * (f + 1))
      exact this
    exact_mod_cast this
  · -- budget: `(m+1) n ≤ aH X + n` and `n (f+1) ≤ K X`
    have hmn : ((m + 1 : ℕ) : ℚ) * n ≤ aH * X + n := by
      have : (m + 1) * n ≤ aH * X + n := by
        have e : (m + 1) * n = m * n + n := by ring
        omega
      exact_mod_cast this
    have hnf : (n : ℚ) * (f + 1) ≤ K * X := by exact_mod_cast hn1
    have hf1q : (0 : ℚ) < f + 1 := by positivity
    have hnle : (n : ℚ) ≤ K / (f + 1) * X := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hf1q]; linarith
    have hX0q : (0 : ℚ) ≤ X := by positivity
    have heb' : (epsB / 2 * aH + (epsB / 2 + 1) * K / (f + 1) : ℚ) ≤ (epsB * eta + gam) * 262144 := by
      exact_mod_cast heb
    have : (epsB : ℚ) / 2 * (((m + 1 : ℕ) : ℚ) * n) + n ≤
        (epsB * eta + gam) * ((524288 * X : ℕ) : ℚ) / 2 := by
      push_cast
      have h1 : epsB / 2 * (((m : ℚ) + 1) * n) ≤ epsB / 2 * (aH * X + n) := by
        push_cast at hmn; exact mul_le_mul_of_nonneg_left hmn (by linarith)
      have h2 := mul_le_mul_of_nonneg_right heb' hX0q
      have e : (epsB / 2 * aH + (epsB / 2 + 1) * K / (f + 1)) * X =
          epsB / 2 * aH * X + (epsB / 2 + 1) * (K / (f + 1) * X) := by ring
      rw [e] at h2
      have h3 : (epsB / 2 + 1) * n ≤ (epsB / 2 + 1) * (K / (f + 1) * X) :=
        mul_le_mul_of_nonneg_left hnle (by linarith)
      linarith
    exact_mod_cast this

/-- The checks of the B-only rectangle (`2^s < a ≤ 4104 · 2^e/4096`, `n = ⌈a/2^q⌉`). -/
def BonlyOK (s Mlo q : ℕ) (epsB eta gam : ℚ) : Prop :=
  q + 4 ≤ s ∧ 1 ≤ Mlo ∧ Mlo ≤ 2 ^ q ∧ (Mlo - 1) * (2 ^ q - 1) < 2 ^ s * (2 ^ q + 1 - Mlo) ∧
    0 ≤ epsB ∧
    (4104 / 4096 : ℚ) * (epsB / 2 * (1 + 1 / 2 ^ q) + 1 / 2 ^ q + (epsB / 2 + 1) / 2 ^ s) ≤
      (epsB * eta + gam) / 2

instance (s Mlo q : ℕ) (epsB eta gam : ℚ) : Decidable (BonlyOK s Mlo q epsB eta gam) := by
  unfold BonlyOK; infer_instance

/-- **The B-only rectangle.** -/
theorem bonly {s Mlo q : ℕ} {epsB eta gam : ℚ} (h : BonlyOK s Mlo q epsB eta gam)
    (a e : ℕ) (hbig : 2 ^ s < a) (ha : (a : ℚ) ≤ 4104 * 2 ^ e / 4096) :
    ∃ m n : ℕ, 16 ≤ n ∧ a ≤ (m + 1) * n ∧ Mlo ≤ m + 1 ∧ m + 1 ≤ 2 ^ q ∧
      (epsB : ℝ) / 2 * (((m + 1 : ℕ) : ℝ) * n) + n ≤ (((epsB * eta + gam) * 2 ^ e / 2 : ℚ) : ℝ) := by
  obtain ⟨hqs, hM1, hMq, hMs, hepsB, heb⟩ := h
  have hQ : 0 < 2 ^ q := by positivity
  set Q := 2 ^ q with hQdef
  have hsQ : 16 * Q ≤ 2 ^ s := by
    rw [hQdef, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  set n := (a + Q - 1) / Q with hn
  have hn1 : n * Q ≤ a + Q - 1 := Nat.div_mul_le_self _ _
  have hn2 : a + Q - 1 < Q * (n + 1) := Nat.lt_mul_div_succ _ hQ
  have hnQ : a ≤ n * Q := by
    have e : Q * (n + 1) = n * Q + Q := by ring
    omega
  have hn16 : 16 ≤ n := by
    rw [hn, Nat.le_div_iff_mul_le hQ]; omega
  have hnpos : 0 < n := by omega
  set m := (a - 1) / n with hm
  have hm1 : m * n ≤ a - 1 := Nat.div_mul_le_self _ _
  have hm2 : a - 1 < n * (m + 1) := Nat.lt_mul_div_succ _ hnpos
  have hamn : a ≤ (m + 1) * n := by rw [Nat.mul_comm] at hm2; omega
  have hmq : m + 1 ≤ Q := by
    have h8 : m * n < Q * n := by
      calc m * n ≤ a - 1 := hm1
        _ < a := by omega
        _ ≤ n * Q := hnQ
        _ = Q * n := Nat.mul_comm _ _
    have := Nat.lt_of_mul_lt_mul_right h8
    omega
  have hMlo : Mlo ≤ m + 1 := by
    by_contra hc
    have h1 : m + 1 ≤ Mlo - 1 := by omega
    -- in `ℤ`: `Q a ≤ (Mlo−1) n Q ≤ (Mlo−1)(a + Q − 1)`, so `(Q + 1 − Mlo) a ≤ (Mlo−1)(Q−1)`
    have hz1 : (a : ℤ) ≤ ((Mlo : ℤ) - 1) * n := by
      have : a ≤ (Mlo - 1) * n := hamn.trans (Nat.mul_le_mul_right _ h1)
      have := (Nat.cast_le (α := ℤ)).2 this
      push_cast [Nat.cast_sub (show 1 ≤ Mlo by omega)] at this; exact this
    have hz2 : (n : ℤ) * Q ≤ a + Q - 1 := by
      have := (Nat.cast_le (α := ℤ)).2 hn1
      push_cast [Nat.cast_sub (show 1 ≤ a + Q by omega)] at this; linarith
    have hz3 : ((2 : ℤ) ^ s) * ((Q : ℤ) + 1 - Mlo) < a * ((Q : ℤ) + 1 - Mlo) := by
      apply mul_lt_mul_of_pos_right (by exact_mod_cast hbig); have : (Mlo : ℤ) ≤ Q := by exact_mod_cast hMq
      linarith
    have hz4 : ((Mlo : ℤ) - 1) * ((Q : ℤ) - 1) < (2 : ℤ) ^ s * ((Q : ℤ) + 1 - Mlo) := by
      have := (Nat.cast_lt (α := ℤ)).2 hMs
      push_cast [Nat.cast_sub (show 1 ≤ Mlo by omega), Nat.cast_sub (show 1 ≤ Q by omega),
        Nat.cast_sub (show Mlo ≤ Q + 1 by omega)] at this
      linarith
    have hM0 : (0 : ℤ) ≤ (Mlo : ℤ) - 1 := sub_nonneg.2 (by exact_mod_cast hM1)
    nlinarith [mul_le_mul_of_nonneg_left hz2 hM0, mul_le_mul_of_nonneg_right hz1 (by positivity : (0 : ℤ) ≤ Q)]
  refine ⟨m, n, hn16, hamn, hMlo, hmq, ?_⟩
  -- budget
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hmn : ((m + 1 : ℕ) : ℚ) * n ≤ a + n := by
    have : (m + 1) * n ≤ a + n := by
      have e : (m + 1) * n = m * n + n := by ring
      omega
    exact_mod_cast this
  have hnle : (n : ℚ) ≤ a / Q + 1 := by
    have : (n : ℚ) * Q ≤ a + Q := by
      have : n * Q ≤ a + Q := by omega
      exact_mod_cast this
    rw [div_add_one hQq.ne', le_div_iff₀ hQq]; exact this
  have hs : (2 : ℚ) ^ s < a := by exact_mod_cast hbig
  have hs0 : (0 : ℚ) < 2 ^ s := by positivity
  have h1le : (1 : ℚ) ≤ a / 2 ^ s := by rw [le_div_iff₀ hs0]; linarith
  have hQe : (Q : ℚ) = 2 ^ q := by rw [hQdef]; push_cast; rfl
  have : (epsB : ℚ) / 2 * (((m + 1 : ℕ) : ℚ) * n) + n ≤ (epsB * eta + gam) * 2 ^ e / 2 := by
    have hc2 : (0 : ℚ) ≤ epsB / 2 + 1 := by linarith
    have hA : (epsB : ℚ) / 2 * (((m + 1 : ℕ) : ℚ) * n) + n ≤ epsB / 2 * a + (epsB / 2 + 1) * n := by
      nlinarith [mul_le_mul_of_nonneg_left hmn (by linarith : (0 : ℚ) ≤ epsB / 2)]
    have hB : (epsB / 2 + 1) * (n : ℚ) ≤ (epsB / 2 + 1) * (a / Q) + (epsB / 2 + 1) * (a / 2 ^ s) := by
      have := mul_le_mul_of_nonneg_left hnle hc2
      have := mul_le_mul_of_nonneg_left h1le hc2
      linarith
    have ha0 : (0 : ℚ) ≤ a := by positivity
    have hC : epsB / 2 * a + ((epsB / 2 + 1) * (a / Q) + (epsB / 2 + 1) * (a / 2 ^ s)) =
        a * (epsB / 2 * (1 + 1 / 2 ^ q) + 1 / 2 ^ q + (epsB / 2 + 1) / 2 ^ s) := by
      rw [hQe]; field_simp; ring
    have hK : (0 : ℚ) ≤ epsB / 2 * (1 + 1 / 2 ^ q) + 1 / 2 ^ q + (epsB / 2 + 1) / 2 ^ s := by positivity
    have hD := mul_le_mul_of_nonneg_right ha hK
    have hE := mul_le_mul_of_nonneg_left heb (by positivity : (0 : ℚ) ≤ 2 ^ e)
    have hF : 4104 * 2 ^ e / 4096 * (epsB / 2 * (1 + 1 / 2 ^ q) + 1 / 2 ^ q + (epsB / 2 + 1) / 2 ^ s) =
        2 ^ e * (4104 / 4096 * (epsB / 2 * (1 + 1 / 2 ^ q) + 1 / 2 ^ q + (epsB / 2 + 1) / 2 ^ s)) := by ring
    have hG : (2 : ℚ) ^ e * ((epsB * eta + gam) / 2) = (epsB * eta + gam) * 2 ^ e / 2 := by ring
    linarith
  exact_mod_cast this

end R1T
