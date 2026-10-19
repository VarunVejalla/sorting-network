import F2DR2b

/-! # R2 for `F2PD`: the per-`E` bound with block constants

`R2E_le`: for `E ≥ 2` with `(E-1) J ≤ jmax n`, with `D = δ f`,

  `#badE ≤ (cE+2) e^{(cE+1) LY} (e² (E J/D) e^{E H} + 2 e^{-e² (E-1) J/D}) · #Scramble`,

given the block constants `κ1 ≥ M/ν`, `LY ≥ log(e² b J/(D c²))`, `L0 ≥ log(e J Φ / D)` and a bound
`H` on `h(θ) = (θ/Φ)(L0 - log θ) + (θ+1)(1 + log(κ1/Φ) + log(θ/(θ+1)))` for `θ ≥ θmin`,
`θmin E ≤ Φ` (`θ = Φ s / E` with `s ≥ 1`). -/

namespace Chvatal

open Finset

/-- `x ↦ x log(A/x²)` is nondecreasing while `e² x² ≤ A`. -/
theorem xlog_mono (κ x A : ℝ) (hκ : 0 < κ) (hκx : κ ≤ x) (hA : Real.exp 2 * x ^ 2 ≤ A) :
    κ * Real.log (A / κ ^ 2) ≤ x * Real.log (A / x ^ 2) := by
  have hx : 0 < x := lt_of_lt_of_le hκ hκx
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  rw [Real.log_div hA0.ne' (by positivity), Real.log_div hA0.ne' (by positivity), Real.log_pow,
    Real.log_pow]
  -- κ log κ ≥ x log x + (κ - x)(log x + 1)
  have h1 : κ - x ≤ κ * (Real.log κ - Real.log x) := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < κ / x by positivity)
    rw [Real.log_div hκ.ne' hx.ne', inv_div] at h
    have : κ * (1 - x / κ) = κ - x := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h hκ.le]
  have h2 : 2 + 2 * Real.log x ≤ Real.log A := by
    have := Real.log_le_log (by positivity) hA
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow] at this
    push_cast at this
    linarith
  have hxk : 0 ≤ x - κ := by linarith
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left h2 hxk]

set_option maxHeartbeats 2000000 in
theorem R2E_le (P : F2PD) {m n : ℕ} (hn : 0 < n) (E : ℕ) (hE : 2 ≤ E)
    (hEn : (E - 1) * P.J ≤ P.jmax n) (κ1 LY L0 H θmin : ℝ)
    (hc2 : P.c ≤ 1 / 2) (hb1 : 1 ≤ P.b)
    (hY : (P.c + 1 / 2) ^ 2 ≤ (P.b - 1 / 2) * P.J / (2 * (P.δ * P.f)))
    (hk1 : P.b * (P.δ * P.f) * E ≤ κ1 * ((E : ℝ) - 1) * P.J)
    (hΦ : 1 ≤ P.Φ) (heκ : Real.exp 1 * κ1 ≤ P.Φ)
    (hLY : Real.log (Real.exp 2 * P.b * P.J / (P.δ * P.f * P.c ^ 2)) ≤ LY)
    (hL0 : Real.log (Real.exp 1 * P.J * P.Φ / (P.δ * P.f)) ≤ L0)
    (hθmin : θmin * E ≤ P.Φ)
    (hθ : ∀ θ : ℝ, 0 < θ → θmin ≤ θ →
      θ / P.Φ * (L0 - Real.log θ) +
        (θ + 1) * (1 + Real.log (κ1 / P.Φ) + Real.log (θ / (θ + 1))) ≤ H) :
    ((badE (m := m) (n := n) P.g2 P.Φ E (P.κ E) (P.B E)).card : ℝ) ≤
      (P.c * E + 2) * Real.exp ((P.c * E + 1) * LY) *
        (Real.exp 2 * (E * P.J / (P.δ * P.f)) * Real.exp (E * H) +
          2 * Real.exp (-(Real.exp 2 * (((E : ℝ) - 1) * P.J / (P.δ * P.f))))) *
        Fintype.card (Scramble m n) := by
  classical
  have hδ := P.hδ
  have hf0 : (0 : ℝ) < P.f := by
    have : 0 < P.f := by have := P.hg2f; omega
    exact_mod_cast this
  set D : ℝ := P.δ * P.f with hDdef
  have hD : 0 < D := by positivity
  have hJ : (0 : ℝ) < P.J := by exact_mod_cast P.hJ
  have hE2 : (2 : ℝ) ≤ E := by exact_mod_cast hE
  have hE0 : (0 : ℝ) < E := by linarith
  have hE1 : (0 : ℝ) < (E : ℝ) - 1 := by linarith
  set ν : ℝ := ((E : ℝ) - 1) * P.J / D with hνdef
  have hν : 0 < ν := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hνn : ν ≤ n := by
    have h1 : (((E - 1) * P.J : ℕ) : ℝ) ≤ P.jmax n := by exact_mod_cast hEn
    have h2 : (P.jmax n : ℝ) ≤ P.δ * (P.f * n) := Nat.floor_le (by positivity)
    have h3 : (((E - 1) * P.J : ℕ) : ℝ) = ((E : ℝ) - 1) * P.J := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ E), Nat.cast_one]
    rw [hνdef, div_le_iff₀ hD]
    rw [h3] at h1
    calc ((E : ℝ) - 1) * P.J ≤ P.δ * (P.f * n) := h1.trans h2
      _ = n * D := by rw [hDdef]; ring
  have hΦr : (1 : ℝ) ≤ P.Φ := by exact_mod_cast hΦ
  -- the integers B, M, κ
  have hbE : P.b * E ≤ (P.B E : ℝ) := Nat.le_ceil _
  have hBlt : (P.B E : ℝ) < P.b * E + 1 := Nat.ceil_lt_add_one (by positivity)
  have hB2 : 2 ≤ P.B E := by
    have : (2 : ℝ) ≤ P.B E := by nlinarith
    exact_mod_cast this
  set M : ℕ := P.B E - 1 with hMdef
  have hMr : (M : ℝ) = (P.B E : ℝ) - 1 := by rw [hMdef, Nat.cast_sub (by omega)]; simp
  have hMb : (M : ℝ) ≤ P.b * E := by linarith
  have hMlo : P.b * E - 1 ≤ (M : ℝ) := by linarith
  have hM1 : (1 : ℝ) ≤ M := by
    have : (2 : ℝ) ≤ P.B E := by exact_mod_cast hB2
    rw [hMr]; linarith
  have hκle : P.κ E ≤ E := by
    unfold F2PD.κ; refine Nat.ceil_le.mpr ?_
    nlinarith [P.hc0]
  have hκ1 : 1 ≤ P.κ E := by
    unfold F2PD.κ; exact Nat.one_le_iff_ne_zero.mpr (by
      rw [Ne, Nat.ceil_eq_zero, not_le]; have := P.hc0; positivity)
  have hκlo : P.c * E ≤ (P.κ E : ℝ) := Nat.le_ceil _
  have hκhi : (P.κ E : ℝ) < P.c * E + 1 := Nat.ceil_lt_add_one (by have := P.hc0; positivity)
  -- M / ν ≤ κ1 and the Chernoff validity
  have hMν : (M : ℝ) ≤ κ1 * ν := by
    rw [hνdef, mul_div_assoc', le_div_iff₀ hD]
    calc (M : ℝ) * D ≤ P.b * E * D := mul_le_mul_of_nonneg_right hMb hD.le
      _ = P.b * D * E := by ring
      _ ≤ κ1 * ((E : ℝ) - 1) * P.J := hk1
      _ = _ := by ring
  have hκ10 : 0 < κ1 := by
    have : (0 : ℝ) < M := by linarith
    have := this.trans_le hMν
    exact pos_of_mul_pos_left this hν.le
  have hR : Real.exp 1 * M ≤ ν * P.Φ := by
    have := mul_le_mul_of_nonneg_left hMν (Real.exp_pos 1).le
    nlinarith [mul_le_mul_of_nonneg_right heκ hν.le]
  have hmain := badE_card_le_nu (m := m) hn P.g2 P.Φ E (P.κ E) (P.B E) ν hν hνn hΦ hκle hB2
    (by rw [← hMdef]; exact hR)
  rw [← hMdef] at hmain
  -- Y
  have hMνlo : (P.c * E + 1) ^ 2 ≤ (M : ℝ) * ν := by
    have h1 : (P.c * E + 1) ^ 2 ≤ (P.c + 1 / 2) ^ 2 * E ^ 2 := by
      have : P.c * E + 1 ≤ (P.c + 1 / 2) * E := by nlinarith
      have h0 : 0 ≤ P.c * E + 1 := by have := P.hc0; positivity
      nlinarith
    have h2 : (P.c + 1 / 2) ^ 2 * E ^ 2 ≤ (P.b - 1 / 2) * P.J / (2 * D) * E ^ 2 :=
      mul_le_mul_of_nonneg_right hY (by positivity)
    have h3 : (P.b - 1 / 2) * P.J / (2 * D) * E ^ 2 ≤ (P.b * E - 1) * ν := by
      have hb12 : 0 ≤ P.b - 1 / 2 := by linarith
      have hA : (P.b - 1 / 2) * E ≤ P.b * E - 1 := by nlinarith
      have hB : (E : ℝ) / 2 ≤ E - 1 := by linarith
      calc (P.b - 1 / 2) * P.J / (2 * D) * E ^ 2 = ((P.b - 1 / 2) * E) * (E / 2) * P.J / D := by
            field_simp
        _ ≤ (P.b * E - 1) * (E - 1) * P.J / D := by
            have := mul_nonneg hb12 hE0.le
            have : 0 ≤ P.b * E - 1 := by nlinarith
            gcongr
        _ = (P.b * E - 1) * ν := by rw [hνdef]; ring
    have h4 : (P.b * E - 1) * ν ≤ (M : ℝ) * ν := mul_le_mul_of_nonneg_right hMlo hν.le
    linarith
  have hκM : ((P.κ E : ℕ) : ℝ) ^ 2 ≤ M * ν := by
    have : ((P.κ E : ℕ) : ℝ) ^ 2 ≤ (P.c * E + 1) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hκhi.le 2
    linarith
  have hYle := Ynu_le (P.κ E) M ν hν hκ1 hκM
  have hY2 : Ynu (P.κ E) M ν ≤ (P.c * E + 2) * Real.exp ((P.c * E + 1) * LY) := by
    refine hYle.trans ?_
    have hκ0 : (0 : ℝ) < (P.κ E : ℕ) := by exact_mod_cast hκ1
    set A : ℝ := Real.exp 2 * M * ν with hAdef
    have hA0 : 0 < A := by positivity
    have hpow : (A / ((P.κ E : ℕ) : ℝ) ^ 2) ^ (P.κ E) =
        Real.exp (((P.κ E : ℕ) : ℝ) * Real.log (A / ((P.κ E : ℕ) : ℝ) ^ 2)) := by
      rw [← Real.log_rpow (by positivity), Real.exp_log (by positivity), Real.rpow_natCast]
    rw [hpow]
    have hx : ((P.κ E : ℕ) : ℝ) * Real.log (A / ((P.κ E : ℕ) : ℝ) ^ 2) ≤
        (P.c * E + 1) * Real.log (A / (P.c * E + 1) ^ 2) :=
      xlog_mono _ _ _ hκ0 hκhi.le (by rw [hAdef, mul_assoc]; gcongr)
    have hlog : Real.log (A / (P.c * E + 1) ^ 2) ≤ LY := by
      have hc0 := P.hc0
      refine le_trans (Real.log_le_log (div_pos hA0 (by positivity)) ?_) hLY
      rw [hAdef, div_le_div_iff₀ (by positivity) (by positivity)]
      have hνE : ν ≤ E * P.J / D := by
        rw [hνdef]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hJ.le) hD.le
      have hcE : P.c ^ 2 * E ^ 2 ≤ (P.c * E + 1) ^ 2 := by
        have := P.hc0; nlinarith
      calc Real.exp 2 * M * ν * (D * P.c ^ 2)
          ≤ Real.exp 2 * (P.b * E) * (E * P.J / D) * (D * P.c ^ 2) := by
            gcongr
        _ = Real.exp 2 * P.b * P.J * (P.c ^ 2 * E ^ 2) := by field_simp
        _ ≤ Real.exp 2 * P.b * P.J * (P.c * E + 1) ^ 2 := by gcongr
    have hκ2 : ((P.κ E : ℕ) : ℝ) + 1 ≤ P.c * E + 2 := by linarith
    have hx0 : 0 ≤ P.c * E + 1 := by have := P.hc0; positivity
    exact mul_le_mul hκ2 (Real.exp_le_exp.mpr (hx.trans (mul_le_mul_of_nonneg_left hlog hx0)))
      (Real.exp_pos _).le (by have := P.hc0; positivity)
  -- Z
  have hg : ∀ s : ℕ, 1 ≤ s → (s : ℝ) < Real.exp 2 * ν →
      (s : ℝ) * Real.log (Real.exp 1 * ν / s) +
        ((P.Φ * s + E : ℕ) : ℝ) * Real.log (Real.exp 1 * M * s / (ν * ((P.Φ * s + E : ℕ) : ℝ))) ≤
        E * H := by
    intro s hs _
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    have hΦ0 : (0 : ℝ) < P.Φ := by linarith
    set θ : ℝ := P.Φ * s / E with hθdef
    have hθ0 : 0 < θ := by positivity
    have hθm : θmin ≤ θ := by
      rw [hθdef, le_div_iff₀ hE0]
      have hs1r : (1 : ℝ) ≤ s := by exact_mod_cast hs
      nlinarith [hθmin, mul_le_mul_of_nonneg_left hs1r hΦ0.le]
    have hT : ((P.Φ * s + E : ℕ) : ℝ) = E * (θ + 1) := by
      rw [hθdef]; push_cast; field_simp
    have hTpos : (0 : ℝ) < E * (θ + 1) := by positivity
    -- first part
    have hA : (s : ℝ) * Real.log (Real.exp 1 * ν / s) ≤ E * (θ / P.Φ * (L0 - Real.log θ)) := by
      have e1 : E * (θ / P.Φ * (L0 - Real.log θ)) = s * (L0 - Real.log θ) := by
        rw [hθdef]; field_simp
      rw [e1]
      refine mul_le_mul_of_nonneg_left ?_ hs0.le
      have hνE : ν ≤ E * P.J / D := by
        rw [hνdef]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hJ.le) hD.le
      have : Real.log (Real.exp 1 * ν / s) ≤ Real.log (Real.exp 1 * P.J * P.Φ / D / θ) := by
        refine Real.log_le_log (by positivity) ?_
        rw [hθdef]
        have e2 : Real.exp 1 * P.J * P.Φ / D / (P.Φ * s / E) = Real.exp 1 * (E * P.J / D) / s := by
          field_simp
        rw [e2]
        gcongr
      rw [Real.log_div (by positivity) hθ0.ne'] at this
      linarith
    -- second part
    have hB : ((P.Φ * s + E : ℕ) : ℝ) * Real.log (Real.exp 1 * M * s / (ν * ((P.Φ * s + E : ℕ) : ℝ))) ≤
        E * ((θ + 1) * (1 + Real.log (κ1 / P.Φ) + Real.log (θ / (θ + 1)))) := by
      rw [hT, mul_assoc]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) hE0.le
      have hM0 : (0 : ℝ) < M := by linarith
      have : Real.exp 1 * M * s / (ν * (E * (θ + 1))) ≤ Real.exp 1 * (κ1 / P.Φ) * (θ / (θ + 1)) := by
        rw [hθdef]
        have e3 : Real.exp 1 * (κ1 / P.Φ) * (P.Φ * s / E / (P.Φ * s / E + 1)) =
            Real.exp 1 * κ1 * s / (P.Φ * s + E) := by
          field_simp
        have e4 : ν * (E * (P.Φ * s / E + 1)) = ν * (P.Φ * s + E) := by field_simp
        rw [e3, e4, div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left hMν (show (0 : ℝ) ≤ Real.exp 1 * s * (P.Φ * s + E) by
          positivity)
        nlinarith
      have hl := Real.log_le_log (by positivity) this
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_exp] at hl
      linarith
    have := hθ θ hθ0 hθm
    nlinarith [mul_le_mul_of_nonneg_left this hE0.le]
  have hZ := Znu_le n P.Φ E M ν (E * H) hν hΦ hR hg
  have hZ2 : Znu n P.Φ E M ν ≤ Real.exp 2 * (E * P.J / D) * Real.exp (E * H) +
      2 * Real.exp (-(Real.exp 2 * ν)) := by
    refine hZ.trans ?_
    have hνE : ν ≤ E * P.J / D := by
      rw [hνdef]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hJ.le) hD.le
    gcongr
  have hYnn : 0 ≤ Ynu (P.κ E) M ν := by
    unfold Ynu
    refine Finset.sum_nonneg (fun k _ => ?_)
    positivity
  have hZnn : 0 ≤ Znu n P.Φ E M ν := by
    unfold Znu
    refine Finset.sum_nonneg (fun s _ => ?_)
    exact mul_nonneg (by positivity) (pow_nonneg (by positivity) _)
  have hScr : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  calc _ ≤ Ynu (P.κ E) M ν * Znu n P.Φ E M ν * Fintype.card (Scramble m n) := hmain
    _ ≤ (P.c * E + 2) * Real.exp ((P.c * E + 1) * LY) *
        (Real.exp 2 * (E * P.J / D) * Real.exp (E * H) + 2 * Real.exp (-(Real.exp 2 * ν))) *
        Fintype.card (Scramble m n) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul hY2 hZ2 hZnn (by have := P.hc0; positivity)) hScr

end Chvatal
