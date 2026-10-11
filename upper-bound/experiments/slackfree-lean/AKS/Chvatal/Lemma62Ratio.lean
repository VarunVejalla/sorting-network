module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Chvátal Lemma 6.2, claim (i): ratio bounds for the two majorants

The per-`s` tail bound `p(s) ≤ C(n,s)(e j s/(n T(s)))^{T(s)}` is majorised by
`G1 s = (e n/s)^s (e s/(ε n))^E` for `s ≤ b` and `G2 s = (e n/s)^s (2 e j/(f n))^{f s/2}` for `s ≥ b`,
with `E = ε j`, `b = 2E/f`.  We prove `(ln G1)' ≥ 5` on `(0,b]`, `(ln G2)' ≤ -5` on `[b,∞)`, the
two-sided sum `∑_{s=1}^n g(s) ≤ (1+e^-5)/(1-e^-5)·G1(b)` and `C(n,s)(e j s/(n T))^T ≤ g(s)`. -/

@[expose] public section

namespace Chvatal

/-! ## Two-sided geometric tail sum -/

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

/-! ## Binomial estimates -/

section
open Nat

open Nat

/-- `C(a,k) ≤ (e·a/k)^k` for `k ≥ 1`. -/
theorem choose_le_exp_pow (a : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (Nat.choose a k : ℝ) ≤ (Real.exp 1 * a / k) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hf : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2 : (k : ℝ) ^ k ≤ Real.exp 1 ^ k * (k ! : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
    rwa [div_le_iff₀ hf, show Real.exp (k : ℝ) = Real.exp 1 ^ k by
      rw [← Real.exp_nat_mul, mul_one]] at h
  refine (Nat.choose_le_pow_div k a).trans ?_
  rw [div_pow, mul_pow, div_le_div_iff₀ hf (pow_pos hkpos k)]
  calc (a : ℝ) ^ k * (k : ℝ) ^ k ≤ (a : ℝ) ^ k * (Real.exp 1 ^ k * (k ! : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg (Nat.cast_nonneg a) k)
    _ = _ := by ring

/-- `C(n,k)·C(J,k) ≤ (e²·n·j/k²)^k` for `k ≥ 1` and `J ≤ j`. -/
theorem choose_mul_choose_le_of_le (n : ℕ) {J j : ℕ} (hJ : J ≤ j) {k : ℕ} (hk : 1 ≤ k) :
    (Nat.choose n k : ℝ) * (Nat.choose J k : ℝ) ≤
      (Real.exp 1 ^ 2 * n * j / (k : ℝ) ^ 2) ^ k := by
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have h := mul_le_mul (choose_le_exp_pow n hk) (choose_le_exp_pow J hk)
    (Nat.cast_nonneg _) (by positivity)
  refine h.trans ?_
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  rw [show Real.exp 1 * n / k * (Real.exp 1 * J / k) = Real.exp 1 ^ 2 * n * J / (k : ℝ) ^ 2 by
    field_simp]
  gcongr

end

noncomputable def eps : ℝ := 1 / (86 * 10 ^ 6)

lemma eps_pos : 0 < eps := by unfold eps; positivity

noncomputable def bpt (f j : ℝ) : ℝ := 2 * (eps * j) / f

/-- `G1(s) = (e n/s)^s (e s/(ε n))^{ε j}` and `G2(s) = (e n/s)^s (2 e j/(f n))^{f s/2}`
(majorants of the per-`s` tail), with logarithms `L1`, `L2`. -/
noncomputable def G1 (N j x : ℝ) : ℝ :=
  (Real.exp 1 * N / x) ^ x * (Real.exp 1 * x / (eps * N)) ^ (eps * j)

noncomputable def G2 (N f j x : ℝ) : ℝ :=
  (Real.exp 1 * N / x) ^ x * (2 * Real.exp 1 * j / (f * N)) ^ (f * x / 2)

noncomputable def L1 (N j x : ℝ) : ℝ :=
  x * (1 + Real.log N - Real.log x) + eps * j * (1 + Real.log x - Real.log eps - Real.log N)

noncomputable def L2 (N f j x : ℝ) : ℝ :=
  x * (1 + Real.log N - Real.log x) + f * x / 2 * Real.log (2 * Real.exp 1 * j / (f * N))

structure Lemma62Params (n : ℕ) (f j : ℝ) : Prop where
  hn : 16 ≤ n
  hf : 85 * 10 ^ 8 ≤ f
  hj : 0 < j
  hjf : j ≤ f * n / 31

lemma Lemma62Params.f_pos {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) : 0 < f :=
  lt_of_lt_of_le (by norm_num) P.hf

lemma Lemma62Params.N_pos {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) : (0 : ℝ) < n :=
  Nat.cast_pos.2 (by have := P.hn; omega)

lemma G1_eq_exp (N j x : ℝ) (hN : 0 < N) (hx : 0 < x) : G1 N j x = Real.exp (L1 N j x) := by
  have := eps_pos
  unfold G1 L1
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
    ← Real.exp_add]
  congr 1
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_exp]
  ring

lemma G2_eq_exp (N f j x : ℝ) (hN : 0 < N) (hx : 0 < x) (hf : 0 < f) (hj : 0 < j) :
    G2 N f j x = Real.exp (L2 N f j x) := by
  unfold G2 L2
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
    ← Real.exp_add]
  congr 1
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp]
  ring

lemma G1_nonneg (N j x : ℝ) (hN : 0 ≤ N) (hx : 0 ≤ x) : 0 ≤ G1 N j x := by
  have := eps_pos
  unfold G1; positivity

lemma hasDerivAt_xlog (A x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => t * (A - Real.log t)) (A - 1 - Real.log x) x := by
  have h := (hasDerivAt_id x).mul ((hasDerivAt_const x A).sub (Real.hasDerivAt_log hx.ne'))
  convert h using 1
  simp only [Pi.sub_apply, id, one_mul]
  field_simp
  ring

lemma le_of_deriv_nonneg_aux {F F' : ℝ → ℝ} {a x y : ℝ}
    (hd : ∀ t, a < t → HasDerivAt F (F' t) t) (hx : a < x) (hxy : x ≤ y)
    (hpos : ∀ t, x < t → t < y → 0 ≤ F' t) : F x ≤ F y := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := F') (convex_Icc x y)
    (fun t ht => (hd t (hx.trans_le ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => ?_) (fun t ht => ?_) ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
  · rw [interior_Icc] at ht
    exact (hd t (hx.trans ht.1)).hasDerivWithinAt
  · rw [interior_Icc] at ht
    exact hpos t ht.1 ht.2

lemma bpt_pos {f j : ℝ} (hf : 0 < f) (hj : 0 < j) : 0 < bpt f j := by
  have := eps_pos
  unfold bpt; positivity

lemma bpt_le_eps_N {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) : bpt f j ≤ eps * n := by
  have hf := P.f_pos
  have hN := P.N_pos
  have hep := eps_pos
  unfold bpt
  rw [div_le_iff₀ hf]
  nlinarith [mul_le_mul_of_nonneg_left P.hjf hep.le, mul_pos (mul_pos hep hf) hN]

lemma bpt_succ_le {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) : bpt f j + 1 ≤ n := by
  have h := bpt_le_eps_N P
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast P.hn
  have : eps ≤ 1 / (86 * 10 ^ 6) := le_refl _
  nlinarith

/-- Key inequality: `ln n - ln b + (f/2) ln(2 e j/(f n)) ≤ -5`. -/
lemma key_right {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) :
    Real.log n - Real.log (bpt f j) + f / 2 * Real.log (2 * Real.exp 1 * j / (f * n)) ≤ -5 := by
  have hf := P.f_pos
  have hN := P.N_pos
  have hj := P.hj
  have hep := eps_pos
  set N : ℝ := (n : ℝ) with hNdef
  set u : ℝ := 2 * j / (f * N) with hu
  have hu_pos : 0 < u := by positivity
  have hu_le : u ≤ 1 / 8 := by
    rw [hu, div_le_iff₀ (by positivity)]
    nlinarith [P.hjf, mul_pos hf hN]
  have hlu : Real.log u ≤ -2 := by
    have h2 : Real.log (1 / 8 : ℝ) = -(3 * Real.log 2) := by
      rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast; ring
    linarith [Real.log_le_log hu_pos hu_le, Real.log_two_gt_d9]
  have hk : Real.log (2 * Real.exp 1 * j / (f * N)) = 1 + Real.log u := by
    rw [show 2 * Real.exp 1 * j / (f * N) = Real.exp 1 * u by rw [hu]; ring,
      Real.log_mul (by positivity) hu_pos.ne', Real.log_exp]
  have hb : Real.log N - Real.log (bpt f j) = -Real.log eps - Real.log u := by
    rw [show bpt f j = eps * (u * N) by unfold bpt; rw [hu]; field_simp,
      Real.log_mul hep.ne' (by positivity), Real.log_mul hu_pos.ne' hN.ne']
    ring
  have heps : -Real.log eps ≤ 86 * 10 ^ 6 := by
    rw [show eps = (86 * 10 ^ 6 : ℝ)⁻¹ by unfold eps; rw [one_div], Real.log_inv, neg_neg]
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 86 * 10 ^ 6 by norm_num)]
  have hprod : (f / 2 - 1) * (Real.log u + 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [P.hf]) (by linarith)
  rw [hb, hk]
  nlinarith [P.hf]

lemma G1_step {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ bpt f j) :
    G1 n j x ≤ Real.exp (-5 * (y - x)) * G1 n j y := by
  have hf := P.f_pos
  have hN := P.N_pos
  have hj := P.hj
  have hep := eps_pos
  have hb := bpt_pos hf hj
  have he1 : eps ≤ 1 := by unfold eps; norm_num
  have hbN : bpt f j ≤ n := (bpt_le_eps_N P).trans (by nlinarith)
  have hEb : eps * j / bpt f j = f / 2 := by unfold bpt; field_simp
  rw [G1_eq_exp _ _ _ hN hx, G1_eq_exp _ _ _ hN (hx.trans_le hxy), ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have key : L1 n j x - 5 * x ≤ L1 n j y - 5 * y := by
    refine le_of_deriv_nonneg_aux (F := fun t => L1 n j t - 5 * t)
      (F' := fun t => Real.log n - Real.log t + eps * j / t - 5) (a := 0) ?_ hx hxy ?_
    · intro t ht
      have h1 := hasDerivAt_xlog (1 + Real.log n) t ht
      have h2 : HasDerivAt (fun t => eps * j * (1 + Real.log t - Real.log eps - Real.log n))
          (eps * j * t⁻¹) t := by
        have := (((hasDerivAt_const t (1 : ℝ)).add (Real.hasDerivAt_log ht.ne')).sub
          (hasDerivAt_const t (Real.log eps))).sub (hasDerivAt_const t (Real.log n))
        simpa using this.const_mul (eps * j)
      have h := (h1.add h2).sub ((hasDerivAt_id t).const_mul (5 : ℝ))
      have hfun : (fun t => L1 n j t - 5 * t) = fun t => (t * ((1 + Real.log n) - Real.log t) +
          eps * j * (1 + Real.log t - Real.log eps - Real.log n)) - 5 * id t := by
        funext t; simp only [L1, id]
      rw [hfun]
      refine h.congr_deriv ?_
      field_simp
      ring
    · intro t ht1 ht2
      have ht0 : 0 < t := hx.trans ht1
      have htb : t ≤ bpt f j := ht2.le.trans hy
      have h1 : Real.log t ≤ Real.log n := Real.log_le_log ht0 (htb.trans hbN)
      have h2 : eps * j / bpt f j ≤ eps * j / t :=
        div_le_div_of_nonneg_left (by positivity) ht0 htb
      linarith [P.hf]
  linarith

lemma G2_step {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) {x y : ℝ}
    (hx : bpt f j ≤ x) (hxy : x ≤ y) :
    G2 n f j y ≤ Real.exp (-5 * (y - x)) * G2 n f j x := by
  have hf := P.f_pos
  have hN := P.N_pos
  have hj := P.hj
  have hb := bpt_pos hf hj
  have hx0 : 0 < x := hb.trans_le hx
  have hK := key_right P
  rw [G2_eq_exp _ _ _ _ hN (hx0.trans_le hxy) hf hj, G2_eq_exp _ _ _ _ hN hx0 hf hj,
    ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have key : -L2 n f j x - 5 * x ≤ -L2 n f j y - 5 * y := by
    refine le_of_deriv_nonneg_aux (F := fun t => -L2 n f j t - 5 * t)
      (F' := fun t => -(Real.log n - Real.log t +
        f / 2 * Real.log (2 * Real.exp 1 * j / (f * n))) - 5) (a := 0) ?_ hx0 hxy ?_
    · intro t ht
      have h1 := hasDerivAt_xlog (1 + Real.log n) t ht
      have h2 : HasDerivAt (fun t => f * t / 2 * Real.log (2 * Real.exp 1 * j / (f * n)))
          (f / 2 * Real.log (2 * Real.exp 1 * j / (f * n))) t := by
        simpa using (((hasDerivAt_id t).const_mul f).div_const 2).mul_const
          (Real.log (2 * Real.exp 1 * j / (f * n)))
      have h := ((h1.add h2).neg).sub ((hasDerivAt_id t).const_mul (5 : ℝ))
      have hfun : (fun t => -L2 n f j t - 5 * t) = fun t => -(t * ((1 + Real.log n) - Real.log t) +
          f * t / 2 * Real.log (2 * Real.exp 1 * j / (f * n))) - 5 * id t := by
        funext t; simp only [L2, id]
      rw [hfun]
      refine h.congr_deriv ?_
      ring
    · intro t ht1 ht2
      have := Real.log_le_log hb (hx.trans ht1.le)
      linarith
  linarith

lemma G1_bpt_eq_G2_bpt {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) :
    G1 n j (bpt f j) = G2 n f j (bpt f j) := by
  have hf := P.f_pos
  have hN := P.N_pos
  have hj := P.hj
  have hep := eps_pos
  unfold G1 G2
  rw [show f * bpt f j / 2 = eps * j by unfold bpt; field_simp,
    show Real.exp 1 * bpt f j / (eps * n) = 2 * Real.exp 1 * j / (f * n) by
      unfold bpt; field_simp]

/-- The combined majorant `g(s) = G1(s)` for `s ≤ b`, `G2(s)` for `s > b`. -/
noncomputable def gfun (n : ℕ) (f j : ℝ) (s : ℕ) : ℝ :=
  if (s : ℝ) ≤ bpt f j then G1 n j s else G2 n f j s

lemma G1_zero {N j : ℝ} (hj : 0 < j) : G1 N j 0 = 0 := by
  have := (mul_pos eps_pos hj).ne'
  simp [G1, Real.zero_rpow this]

lemma gfun_nonneg {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) (s : ℕ) : 0 ≤ gfun n f j s := by
  have := P.f_pos.le
  have := P.hj.le
  unfold gfun G1 G2
  have := eps_pos
  split_ifs <;> positivity

lemma exp_neg5_pos_lt : 0 < Real.exp (-5) ∧ Real.exp (-5) < 1 :=
  ⟨Real.exp_pos _, by simp⟩

/-- `∑_{s=1}^n g(s) ≤ (1+e^-5)/(1-e^-5) · G1(b)`. -/
theorem gfun_sum_le_G1 {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) :
    ∑ s ∈ Finset.Icc 1 n, gfun n f j s ≤
      (1 + Real.exp (-5)) / (1 - Real.exp (-5)) * G1 n j (bpt f j) := by
  have hb := bpt_pos P.f_pos P.hj
  have hρ := exp_neg5_pos_lt
  have h1ρ : 0 < 1 - Real.exp (-5) := by linarith [hρ.2]
  set a := ⌊bpt f j⌋₊ with ha
  have hab : (a : ℝ) ≤ bpt f j := Nat.floor_le hb.le
  have hba : bpt f j < (a : ℝ) + 1 := Nat.lt_floor_add_one _
  have han : a + 1 ≤ n := by
    have : ((a + 1 : ℕ) : ℝ) ≤ n := by push_cast; linarith [bpt_succ_le P]
    exact_mod_cast this
  have h0 := geom_two_sided_sum (Real.exp (-5)) hρ.1 hρ.2 _ (gfun_nonneg P) a n han
    (fun s hs1 hsa => by
      have h1 : (s : ℝ) + 1 ≤ a := by exact_mod_cast hsa
      have h2 : (s : ℝ) ≤ bpt f j := by linarith
      have h3 : ((s + 1 : ℕ) : ℝ) ≤ bpt f j := by push_cast; linarith
      unfold gfun
      rw [if_pos h2, if_pos h3]
      simpa using G1_step P (by exact_mod_cast hs1 : (0 : ℝ) < s) (by linarith)
        (by linarith : (s : ℝ) + 1 ≤ bpt f j))
    (fun s hs1 hsn => by
      have h1 : (a : ℝ) + 1 ≤ s := by exact_mod_cast hs1
      have h2 : ¬ (s : ℝ) ≤ bpt f j := by linarith
      have h3 : ¬ ((s + 1 : ℕ) : ℝ) ≤ bpt f j := by push_cast; linarith
      unfold gfun
      rw [if_neg h2, if_neg h3]
      simpa using G2_step P (by linarith : bpt f j ≤ (s : ℝ)) (by linarith : (s : ℝ) ≤ s + 1))
  set t : ℝ := bpt f j - a with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have ht1 : t ≤ 1 := by rw [ht]; linarith
  have hG : 0 ≤ G1 n j (bpt f j) := G1_nonneg _ _ _ P.N_pos.le hb.le
  have hga : gfun n f j a ≤ Real.exp (-5 * t) * G1 n j (bpt f j) := by
    unfold gfun
    rw [if_pos hab]
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h]; simp [G1_zero P.hj]; positivity
    · exact G1_step P (by exact_mod_cast h) hab le_rfl
  have hga1 : gfun n f j (a + 1) ≤ Real.exp (-5 * (1 - t)) * G1 n j (bpt f j) := by
    unfold gfun
    rw [if_neg (by push_cast; linarith), G1_bpt_eq_G2_bpt P]
    have := G2_step P (le_refl (bpt f j)) (by push_cast; linarith : bpt f j ≤ ((a + 1 : ℕ) : ℝ))
    rwa [show ((a + 1 : ℕ) : ℝ) - bpt f j = 1 - t by rw [ht]; push_cast; ring] at this
  have hc1 : Real.exp (-5 * t) ≤ (1 - t) + t * Real.exp (-5) := by
    have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-5 : ℝ))
      (by linarith : 0 ≤ 1 - t) ht0 (by ring)
    simpa [smul_eq_mul, mul_comm] using this
  have hc2 : Real.exp (-5 * (1 - t)) ≤ t + (1 - t) * Real.exp (-5) := by
    have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-5 : ℝ))
      ht0 (by linarith : 0 ≤ 1 - t) (by ring)
    simpa [smul_eq_mul, mul_comm] using this
  calc _ ≤ _ := h0
    _ ≤ (1 + Real.exp (-5)) * G1 n j (bpt f j) / (1 - Real.exp (-5)) := by
        gcongr
        nlinarith [mul_le_mul_of_nonneg_right hc1 hG, mul_le_mul_of_nonneg_right hc2 hG]
    _ = _ := by ring

/-- `x ↦ (c/x)^x` is decreasing for `x ≥ c/e`. -/
lemma rpow_div_self_antitone {c x y : ℝ} (hc : 0 < c) (hx : c / Real.exp 1 ≤ x) (hxy : x ≤ y) :
    (c / y) ^ y ≤ (c / x) ^ x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hy0 : 0 < y := hx0.trans_le hxy
  have hexp : ∀ t : ℝ, 0 < t → (c / t) ^ t = Real.exp (t * (Real.log c - Real.log t)) := by
    intro t ht
    rw [Real.rpow_def_of_pos (by positivity), Real.log_div hc.ne' ht.ne', mul_comm]
  rw [hexp x hx0, hexp y hy0]
  refine Real.exp_le_exp.mpr ?_
  have key : -(x * (Real.log c - Real.log x)) ≤ -(y * (Real.log c - Real.log y)) := by
    refine le_of_deriv_nonneg_aux (F := fun t => -(t * (Real.log c - Real.log t)))
      (F' := fun t => -(Real.log c - 1 - Real.log t)) (a := 0)
      (fun t ht => (hasDerivAt_xlog (Real.log c) t ht).neg) hx0 hxy fun t ht1 _ => ?_
    have h1 : Real.log (c / Real.exp 1) ≤ Real.log t :=
      Real.log_le_log (by positivity) (hx.trans ht1.le)
    rw [Real.log_div hc.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
    linarith
  linarith

/-- The per-`s` bound `C(n,s)·(e j s/(n T(s)))^{T(s)}`, `T(s) = f s/2 + ε j`. -/
noncomputable def pbound (n : ℕ) (f j : ℝ) (s : ℕ) : ℝ :=
  (n.choose s : ℝ) *
    (Real.exp 1 * j * s / (n * (f * s / 2 + eps * j))) ^ (f * s / 2 + eps * j)

/-- `C(n,s)(e j s/(n T))^T ≤ g(s)` for `1 ≤ s`. -/
theorem pbound_le_gfun {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) (s : ℕ)
    (hs : 1 ≤ s) : pbound n f j s ≤ gfun n f j s := by
  have hf := P.f_pos
  have hN := P.N_pos
  have hj := P.hj
  have hep := eps_pos
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hC : (n.choose s : ℝ) ≤ (Real.exp 1 * n / s) ^ (s : ℝ) := by
    rw [Real.rpow_natCast]; exact choose_le_exp_pow n hs
  have hA : 0 ≤ (Real.exp 1 * n / s) ^ (s : ℝ) := by positivity
  have hT : 0 < f * s / 2 + eps * j := by positivity
  have hdiv : Real.exp 1 * j * s / (n * (f * s / 2 + eps * j)) =
      (Real.exp 1 * j * s / n) / (f * s / 2 + eps * j) := by rw [div_div]
  have hcpos : 0 < Real.exp 1 * j * s / n := by positivity
  have hce : Real.exp 1 * j * s / n / Real.exp 1 = j * s / n := by field_simp
  unfold pbound gfun
  split_ifs with hsb
  · unfold G1
    have hsE : (s : ℝ) ≤ eps * n := hsb.trans (bpt_le_eps_N P)
    have hcE : Real.exp 1 * j * s / n / Real.exp 1 ≤ eps * j := by
      rw [hce, div_le_iff₀ hN]
      nlinarith [mul_le_mul_of_nonneg_left hsE hj.le]
    have hmono := rpow_div_self_antitone hcpos hcE
      (by have := mul_pos hf hs0; nlinarith : eps * j ≤ f * s / 2 + eps * j)
    rw [show Real.exp 1 * j * s / n / (eps * j) = Real.exp 1 * s / (eps * n) by field_simp] at hmono
    rw [hdiv]
    exact mul_le_mul hC hmono (by positivity) hA
  · unfold G2
    have hcE : Real.exp 1 * j * s / n / Real.exp 1 ≤ f * s / 2 := by
      rw [hce, div_le_iff₀ hN]
      nlinarith [P.hjf, mul_pos hf hs0, mul_pos hf hN]
    have hmono := rpow_div_self_antitone hcpos hcE
      (by nlinarith : f * s / 2 ≤ f * s / 2 + eps * j)
    rw [show Real.exp 1 * j * s / n / (f * s / 2) = 2 * Real.exp 1 * j / (f * n) by
      field_simp] at hmono
    rw [hdiv]
    exact mul_le_mul hC hmono (by positivity) hA

end Chvatal
