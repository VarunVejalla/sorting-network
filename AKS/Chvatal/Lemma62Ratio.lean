module

/-
  # Chvátal Lemma 6.2, claim (i): ratio bounds for the two majorants

  Source: Chvátal, DCS-TR-294, proof of Lemma 6.2 (i).  The per-`s` tail bound
  `p(s) ≤ C(n,s)(e j s/(n T(s)))^{T(s)}` (`scramble_tail_union_top`) is majorised by

  * `G1 s = (e n/s)^s (e s/(ε n))^E`  for `s ≤ b`,
  * `G2 s = (e n/s)^s (2 e j/(f n))^{f s/2}`  for `s ≥ b`,

  with `E = ε j`, `b = 2E/f`.  We prove `(ln G1)' ≥ 5` on `(0,b]`, `(ln G2)' ≤ -5`
  on `[b,∞)`, the discrete ratio bounds (R1, R2), the two-sided sum
  `∑_{s=1}^n g(s) ≤ (1+e^-5)/(1-e^-5)·G1(b)` (R3) and the assembly
  `C(n,s)(e j s/(n T))^T ≤ g(s)` (R4).
-/

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import AKS.Chvatal.GeomTail
public import AKS.Chvatal.Lemma62TopsAnalytic

@[expose] public section

namespace Chvatal

/-- `ε_F = 1/(8·10^7)`. -/
noncomputable def eps : ℝ := 1 / (8 * 10 ^ 7)

lemma eps_pos : 0 < eps := by unfold eps; positivity

/-- `b = 2 ε j / f`. -/
noncomputable def bpt (f j : ℝ) : ℝ := 2 * (eps * j) / f

/-- `G1(s) = (e n/s)^s (e s/(ε n))^{ε j}`. -/
noncomputable def G1 (N j x : ℝ) : ℝ :=
  (Real.exp 1 * N / x) ^ x * (Real.exp 1 * x / (eps * N)) ^ (eps * j)

/-- `G2(s) = (e n/s)^s (2 e j/(f n))^{f s/2}`. -/
noncomputable def G2 (N f j x : ℝ) : ℝ :=
  (Real.exp 1 * N / x) ^ x * (2 * Real.exp 1 * j / (f * N)) ^ (f * x / 2)

/-- `ln G1`. -/
noncomputable def L1 (N j x : ℝ) : ℝ :=
  x * (1 + Real.log N - Real.log x) + eps * j * (1 + Real.log x - Real.log eps - Real.log N)

/-- `ln G2`. -/
noncomputable def L2 (N f j x : ℝ) : ℝ :=
  x * (1 + Real.log N - Real.log x) + f * x / 2 * Real.log (2 * Real.exp 1 * j / (f * N))

/-- Parameter range of Lemma 6.2 (claim (i)). -/
structure Lemma62Params (n : ℕ) (f j : ℝ) : Prop where
  hn : 16 ≤ n
  hf : 17 * 10 ^ 9 ≤ f
  hj : 0 < j
  hjf : j ≤ 128 / 4095 * f * n

lemma log_e_div (N x : ℝ) (hN : 0 < N) (hx : 0 < x) :
    Real.log (Real.exp 1 * N / x) = 1 + Real.log N - Real.log x := by
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp]

lemma G1_eq_exp (N j x : ℝ) (hN : 0 < N) (hx : 0 < x) : G1 N j x = Real.exp (L1 N j x) := by
  have := eps_pos
  have h2 : Real.log (Real.exp 1 * x / (eps * N)) = 1 + Real.log x - Real.log eps - Real.log N := by
    have := eps_pos
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, Real.log_mul (by positivity) (by positivity)]
    ring
  unfold G1 L1
  rw [Real.rpow_def_of_pos (by have := eps_pos; positivity),
    Real.rpow_def_of_pos (by positivity), ← Real.exp_add, log_e_div N x hN hx, h2]
  congr 1
  ring

lemma G2_eq_exp (N f j x : ℝ) (hN : 0 < N) (hx : 0 < x) (hf : 0 < f) (hj : 0 < j) :
    G2 N f j x = Real.exp (L2 N f j x) := by
  unfold G2 L2
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
    ← Real.exp_add, log_e_div N x hN hx]
  congr 1
  ring

lemma G1_nonneg (N j x : ℝ) (hN : 0 ≤ N) (hx : 0 ≤ x) : 0 ≤ G1 N j x := by
  have := eps_pos
  unfold G1
  positivity

lemma G2_nonneg (N f j x : ℝ) (hN : 0 ≤ N) (hx : 0 ≤ x) (hf : 0 ≤ f) (hj : 0 ≤ j) :
    0 ≤ G2 N f j x := by
  unfold G2
  positivity

/-! ## Derivatives -/

lemma hasDerivAt_xlog (A x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => t * (A - Real.log t)) (A - 1 - Real.log x) x := by
  have h := (hasDerivAt_id x).mul ((hasDerivAt_const x A).sub (Real.hasDerivAt_log hx.ne'))
  convert h using 1
  simp only [Pi.sub_apply, id, one_mul]
  field_simp
  ring

lemma hasDerivAt_L1 (N j x : ℝ) (hx : 0 < x) :
    HasDerivAt (L1 N j) (Real.log N - Real.log x + eps * j / x) x := by
  have h1 := hasDerivAt_xlog (1 + Real.log N) x hx
  have h2 : HasDerivAt (fun t => eps * j * (1 + Real.log t - Real.log eps - Real.log N))
      (eps * j * (x⁻¹)) x := by
    have := (((hasDerivAt_const x (1:ℝ)).add (Real.hasDerivAt_log hx.ne')).sub
      (hasDerivAt_const x (Real.log eps))).sub (hasDerivAt_const x (Real.log N))
    simpa using this.const_mul (eps * j)
  have h := h1.add h2
  have hfun : L1 N j = fun t => t * ((1 + Real.log N) - Real.log t) +
      eps * j * (1 + Real.log t - Real.log eps - Real.log N) := by
    funext t; unfold L1; ring
  rw [hfun]
  refine h.congr_deriv ?_
  field_simp
  ring

lemma hasDerivAt_L2 (N f j x : ℝ) (hx : 0 < x) :
    HasDerivAt (L2 N f j) (Real.log N - Real.log x + f / 2 * Real.log (2 * Real.exp 1 * j / (f * N))) x := by
  have h1 := hasDerivAt_xlog (1 + Real.log N) x hx
  have h2 : HasDerivAt (fun t => f * t / 2 * Real.log (2 * Real.exp 1 * j / (f * N)))
      (f / 2 * Real.log (2 * Real.exp 1 * j / (f * N))) x := by
    have := ((hasDerivAt_id x).const_mul f).div_const 2 |>.mul_const
      (Real.log (2 * Real.exp 1 * j / (f * N)))
    simpa using this
  have h := h1.add h2
  have hfun : L2 N f j = fun t => t * ((1 + Real.log N) - Real.log t) +
      f * t / 2 * Real.log (2 * Real.exp 1 * j / (f * N)) := by
    funext t; unfold L2; ring
  rw [hfun]
  refine h.congr_deriv ?_
  ring

/-- Monotonicity from a derivative sign on the open interval. -/
lemma le_of_deriv_nonneg_aux {F F' : ℝ → ℝ} {a x y : ℝ}
    (hd : ∀ t, a < t → HasDerivAt F (F' t) t) (hx : a < x) (hxy : x ≤ y)
    (hpos : ∀ t, x < t → t < y → 0 ≤ F' t) : F x ≤ F y := by
  have hmono : MonotoneOn F (Set.Icc x y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y)
    · intro t ht
      exact (hd t (lt_of_lt_of_le hx ht.1)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t (lt_trans hx ht.1)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t (lt_trans hx ht.1)).deriv]
      exact hpos t ht.1 ht.2
  exact hmono ⟨le_refl x, hxy⟩ ⟨hxy, le_refl y⟩ hxy

lemma bpt_pos {f j : ℝ} (hf : 0 < f) (hj : 0 < j) : 0 < bpt f j := by
  have := eps_pos
  unfold bpt; positivity

lemma Lemma62Params.f_pos {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) : 0 < f :=
  lt_of_lt_of_le (by norm_num) P.hf

lemma Lemma62Params.N_pos {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) : (0 : ℝ) < n := by
  have := P.hn
  exact_mod_cast (by omega : 0 < n)

lemma bpt_le_N {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) : bpt f j ≤ n := by
  have hf := P.f_pos
  have hN := P.N_pos
  have he : eps ≤ 1 / (8 * 10 ^ 7) := le_refl _
  have hep := eps_pos
  unfold bpt
  rw [div_le_iff₀ hf]
  have h1 : eps * j ≤ eps * (128 / 4095 * f * n) := mul_le_mul_of_nonneg_left P.hjf hep.le
  have h2 : eps * (128 / 4095 * f * n) ≤ 1 / (8 * 10 ^ 7) * (128 / 4095 * f * n) :=
    mul_le_mul_of_nonneg_right he (by positivity)
  nlinarith [mul_pos hf hN]

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
    have h1 : Real.log u ≤ Real.log (1 / 8) := Real.log_le_log hu_pos hu_le
    have h2 : Real.log (1 / 8 : ℝ) = -(3 * Real.log 2) := by
      rw [one_div, Real.log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast; ring
    have := Real.log_two_gt_d9
    linarith
  have hk : Real.log (2 * Real.exp 1 * j / (f * N)) = 1 + Real.log u := by
    have : 2 * Real.exp 1 * j / (f * N) = Real.exp 1 * u := by rw [hu]; ring
    rw [this, Real.log_mul (by positivity) hu_pos.ne', Real.log_exp]
  have hbeq : bpt f j = eps * (u * N) := by
    unfold bpt; rw [hu]; field_simp
  have hb : Real.log N - Real.log (bpt f j) = -Real.log eps - Real.log u := by
    rw [hbeq, Real.log_mul hep.ne' (by positivity), Real.log_mul hu_pos.ne' hN.ne']
    ring
  have heps : -Real.log eps ≤ 8 * 10 ^ 7 := by
    have : eps = (8 * 10 ^ 7 : ℝ)⁻¹ := by unfold eps; rw [one_div]
    rw [this, Real.log_inv, neg_neg]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 8 * 10 ^ 7 by norm_num)
    linarith
  have hf2 : 0 ≤ f / 2 - 1 := by have := P.hf; linarith
  have hprod : (f / 2 - 1) * (Real.log u + 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hf2 (by linarith)
  rw [hb, hk]
  have := P.hf
  nlinarith

/-- `(ln G1)' ≥ 5` on `(0, b]`, in integrated form. -/
lemma L1_step {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ bpt f j) :
    L1 n j x + 5 * (y - x) ≤ L1 n j y := by
  have hf := P.f_pos
  have hN := P.N_pos
  have hj := P.hj
  have hep := eps_pos
  have hb := bpt_pos hf hj
  have hbN := bpt_le_N P
  have hEb : eps * j / bpt f j = f / 2 := by unfold bpt; field_simp
  have key : L1 n j x - 5 * x ≤ L1 n j y - 5 * y := by
    refine le_of_deriv_nonneg_aux (F := fun t => L1 n j t - 5 * t)
      (F' := fun t => Real.log n - Real.log t + eps * j / t - 5) (a := 0) ?_ hx hxy ?_
    · intro t ht
      have := (hasDerivAt_L1 n j t ht).sub ((hasDerivAt_id t).const_mul (5 : ℝ))
      simpa using this
    · intro t ht1 ht2
      have ht0 : 0 < t := lt_trans hx ht1
      have htb : t ≤ bpt f j := le_trans ht2.le hy
      have h1 : Real.log t ≤ Real.log n := Real.log_le_log ht0 (htb.trans hbN)
      have h2 : eps * j / bpt f j ≤ eps * j / t :=
        div_le_div_of_nonneg_left (by positivity) ht0 htb
      have := P.hf
      linarith
  linarith

/-- `(ln G2)' ≤ -5` on `[b, ∞)`, in integrated form. -/
lemma L2_step {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) {x y : ℝ}
    (hx : bpt f j ≤ x) (hxy : x ≤ y) :
    L2 n f j y + 5 * (y - x) ≤ L2 n f j x := by
  have hf := P.f_pos
  have hN := P.N_pos
  have hj := P.hj
  have hb := bpt_pos hf hj
  have hx0 : 0 < x := lt_of_lt_of_le hb hx
  have hK := key_right P
  have key : -L2 n f j x - 5 * x ≤ -L2 n f j y - 5 * y := by
    refine le_of_deriv_nonneg_aux (F := fun t => -L2 n f j t - 5 * t)
      (F' := fun t => -(Real.log n - Real.log t +
        f / 2 * Real.log (2 * Real.exp 1 * j / (f * n))) - 5) (a := 0) ?_ hx0 hxy ?_
    · intro t ht
      have := (hasDerivAt_L2 n f j t ht).neg.sub ((hasDerivAt_id t).const_mul (5 : ℝ))
      simpa using this
    · intro t ht1 ht2
      have ht0 : 0 < t := lt_trans hx0 ht1
      have h1 : Real.log (bpt f j) ≤ Real.log t := Real.log_le_log hb (le_trans hx ht1.le)
      linarith
  linarith

lemma G1_step {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ bpt f j) :
    G1 n j x ≤ Real.exp (-5 * (y - x)) * G1 n j y := by
  have hN := P.N_pos
  rw [G1_eq_exp _ _ _ hN hx, G1_eq_exp _ _ _ hN (lt_of_lt_of_le hx hxy), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := L1_step P hx hxy hy
  linarith

lemma G2_step {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) {x y : ℝ}
    (hx : bpt f j ≤ x) (hxy : x ≤ y) :
    G2 n f j y ≤ Real.exp (-5 * (y - x)) * G2 n f j x := by
  have hN := P.N_pos
  have hf := P.f_pos
  have hb := bpt_pos hf P.hj
  have hx0 : 0 < x := lt_of_lt_of_le hb hx
  rw [G2_eq_exp _ _ _ _ hN (lt_of_lt_of_le hx0 hxy) hf P.hj, G2_eq_exp _ _ _ _ hN hx0 hf P.hj,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := L2_step P hx hxy
  linarith

/-- **R1** (discrete, left). -/
theorem ratio_left {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) (s : ℕ) (hs : 1 ≤ s)
    (hsb : (s : ℝ) + 1 ≤ bpt f j) :
    G1 n j s ≤ Real.exp (-5) * G1 n j ((s : ℝ) + 1) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have := G1_step P hs0 (by linarith : (s : ℝ) ≤ (s : ℝ) + 1) hsb
  simpa using this

/-- **R2** (discrete, right). -/
theorem ratio_right {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) (s : ℕ)
    (hsb : bpt f j ≤ (s : ℝ)) :
    G2 n f j ((s : ℝ) + 1) ≤ Real.exp (-5) * G2 n f j s := by
  have := G2_step P hsb (by linarith : (s : ℝ) ≤ (s : ℝ) + 1)
  simpa using this

/-- `G1(b) = G2(b)` at the breakpoint `b = 2εj/f`. -/
lemma G1_bpt_eq_G2_bpt {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) :
    G1 n j (bpt f j) = G2 n f j (bpt f j) := by
  have hf := P.f_pos
  have hN := P.N_pos
  have hj := P.hj
  have hep := eps_pos
  have e1 : f * bpt f j / 2 = eps * j := by unfold bpt; field_simp
  have e2 : Real.exp 1 * bpt f j / (eps * n) = 2 * Real.exp 1 * j / (f * n) := by
    unfold bpt; field_simp
  unfold G1 G2
  rw [e1, e2]

/-- The combined majorant `g(s) = G1(s)` for `s ≤ b`, `G2(s)` for `s > b`. -/
noncomputable def gfun (n : ℕ) (f j : ℝ) (s : ℕ) : ℝ :=
  if (s : ℝ) ≤ bpt f j then G1 n j s else G2 n f j s

lemma gfun_nonneg {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) (s : ℕ) : 0 ≤ gfun n f j s := by
  unfold gfun
  split_ifs
  · exact G1_nonneg _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact G2_nonneg _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) P.f_pos.le P.hj.le

lemma exp_neg5_pos_lt : 0 < Real.exp (-5) ∧ Real.exp (-5) < 1 :=
  ⟨Real.exp_pos _, (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by norm_num))⟩

/-- **R3a.** Two-sided geometric bound for `g`. -/
theorem gfun_sum_le {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) (a : ℕ)
    (ha : a = ⌊bpt f j⌋₊) (ha1 : 1 ≤ a) (han : a + 1 ≤ n) :
    ∑ s ∈ Finset.Icc 1 n, gfun n f j s ≤
      (gfun n f j a + gfun n f j (a + 1)) / (1 - Real.exp (-5)) := by
  have hb := bpt_pos P.f_pos P.hj
  have hab : (a : ℝ) ≤ bpt f j := by rw [ha]; exact Nat.floor_le hb.le
  have hba : bpt f j < (a : ℝ) + 1 := by rw [ha]; exact Nat.lt_floor_add_one _
  refine geom_two_sided_sum (Real.exp (-5)) exp_neg5_pos_lt.1 exp_neg5_pos_lt.2 _
    (gfun_nonneg P) a n ha1 han ?_ ?_
  · intro s hs1 hsa
    have hsa' : (s : ℝ) + 1 ≤ a := by exact_mod_cast hsa
    have h1 : (s : ℝ) ≤ bpt f j := by linarith
    have h2 : ((s + 1 : ℕ) : ℝ) ≤ bpt f j := by push_cast; linarith
    unfold gfun
    rw [if_pos h1, if_pos h2]
    have := ratio_left P s hs1 (by linarith)
    simpa using this
  · intro s hs1 hsn
    have hs' : (a : ℝ) + 1 ≤ s := by exact_mod_cast hs1
    have h1 : ¬ (s : ℝ) ≤ bpt f j := by linarith
    have h2 : ¬ ((s + 1 : ℕ) : ℝ) ≤ bpt f j := by push_cast; linarith
    unfold gfun
    rw [if_neg h1, if_neg h2]
    have := ratio_right P s (by linarith)
    simpa using this

/-- **R3b.** `∑_{s=1}^n g(s) ≤ (1+e^-5)/(1-e^-5) · G1(b)`. -/
theorem gfun_sum_le_G1 {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) (a : ℕ)
    (ha : a = ⌊bpt f j⌋₊) (ha1 : 1 ≤ a) (han : a + 1 ≤ n) :
    ∑ s ∈ Finset.Icc 1 n, gfun n f j s ≤
      (1 + Real.exp (-5)) / (1 - Real.exp (-5)) * G1 n j (bpt f j) := by
  have hb := bpt_pos P.f_pos P.hj
  have hN := P.N_pos
  have hab : (a : ℝ) ≤ bpt f j := by rw [ha]; exact Nat.floor_le hb.le
  have hba : bpt f j < (a : ℝ) + 1 := by rw [ha]; exact Nat.lt_floor_add_one _
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
  have h0 := gfun_sum_le P a ha ha1 han
  have hρ := exp_neg5_pos_lt
  have h1ρ : 0 < 1 - Real.exp (-5) := by linarith [hρ.2]
  set t : ℝ := bpt f j - a with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have ht1 : t ≤ 1 := by rw [ht]; linarith
  have hga : gfun n f j a ≤ Real.exp (-5 * t) * G1 n j (bpt f j) := by
    unfold gfun
    rw [if_pos hab]
    exact G1_step P ha0 hab le_rfl
  have hga1 : gfun n f j (a + 1) ≤ Real.exp (-5 * (1 - t)) * G1 n j (bpt f j) := by
    have h2 : ¬ ((a + 1 : ℕ) : ℝ) ≤ bpt f j := by push_cast; linarith
    unfold gfun
    rw [if_neg h2, G1_bpt_eq_G2_bpt P]
    have := G2_step P (le_refl (bpt f j)) (by push_cast; linarith : bpt f j ≤ ((a + 1 : ℕ) : ℝ))
    have e : ((a + 1 : ℕ) : ℝ) - bpt f j = 1 - t := by rw [ht]; push_cast; ring
    rw [e] at this
    exact this
  have hc1 : Real.exp (-5 * t) ≤ (1 - t) + t * Real.exp (-5) := by
    have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-5 : ℝ))
      (by linarith : 0 ≤ 1 - t) ht0 (by ring)
    have e : (1 - t) • (0 : ℝ) + t • (-5 : ℝ) = -5 * t := by simp [smul_eq_mul]; ring
    rw [e] at this
    simpa [smul_eq_mul] using this
  have hc2 : Real.exp (-5 * (1 - t)) ≤ t + (1 - t) * Real.exp (-5) := by
    have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-5 : ℝ))
      ht0 (by linarith : 0 ≤ 1 - t) (by ring)
    have e : t • (0 : ℝ) + (1 - t) • (-5 : ℝ) = -5 * (1 - t) := by simp [smul_eq_mul]; ring
    rw [e] at this
    simpa [smul_eq_mul] using this
  have hG : 0 ≤ G1 n j (bpt f j) := G1_nonneg _ _ _ hN.le hb.le
  have hsum : gfun n f j a + gfun n f j (a + 1) ≤ (1 + Real.exp (-5)) * G1 n j (bpt f j) := by
    nlinarith [mul_le_mul_of_nonneg_right hc1 hG, mul_le_mul_of_nonneg_right hc2 hG]
  calc _ ≤ _ := h0
    _ ≤ (1 + Real.exp (-5)) * G1 n j (bpt f j) / (1 - Real.exp (-5)) :=
        div_le_div_of_nonneg_right hsum h1ρ.le
    _ = _ := by ring

/-! ## Assembly (R4) -/

/-- `x ↦ (c/x)^x` is decreasing for `x ≥ c/e`. -/
lemma rpow_div_self_antitone {c x y : ℝ} (hc : 0 < c) (hx : c / Real.exp 1 ≤ x) (hxy : x ≤ y) :
    (c / y) ^ y ≤ (c / x) ^ x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hexp : ∀ t : ℝ, 0 < t → (c / t) ^ t = Real.exp (t * (Real.log c - Real.log t)) := by
    intro t ht
    rw [Real.rpow_def_of_pos (by positivity), Real.log_div hc.ne' ht.ne', mul_comm]
  rw [hexp x hx0, hexp y hy0]
  apply Real.exp_le_exp.mpr
  have key : -(x * (Real.log c - Real.log x)) ≤ -(y * (Real.log c - Real.log y)) := by
    refine le_of_deriv_nonneg_aux (F := fun t => -(t * (Real.log c - Real.log t)))
      (F' := fun t => -(Real.log c - 1 - Real.log t)) (a := 0) ?_ hx0 hxy ?_
    · intro t ht
      exact (hasDerivAt_xlog (Real.log c) t ht).neg
    · intro t ht1 _
      have ht0 : 0 < t := lt_trans hx0 ht1
      have h1 : Real.log (c / Real.exp 1) ≤ Real.log t :=
        Real.log_le_log (by positivity) (le_trans hx ht1.le)
      rw [Real.log_div hc.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
      linarith
  linarith

/-- The per-`s` bound `C(n,s)·(e j s/(n T(s)))^{T(s)}`, `T(s) = f s/2 + ε j`. -/
noncomputable def pbound (n : ℕ) (f j : ℝ) (s : ℕ) : ℝ :=
  (n.choose s : ℝ) *
    (Real.exp 1 * j * s / (n * (f * s / 2 + eps * j))) ^ (f * s / 2 + eps * j)

/-- **R4.** `C(n,s)(e j s/(n T))^T ≤ g(s)` for `1 ≤ s ≤ n`. -/
theorem pbound_le_gfun {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) (s : ℕ)
    (hs : 1 ≤ s) (_hsn : s ≤ n) : pbound n f j s ≤ gfun n f j s := by
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
  · -- s ≤ b
    unfold G1
    have hbe : bpt f j ≤ eps * n := by
      have := bpt_le_N P
      unfold bpt
      rw [div_le_iff₀ hf]
      nlinarith [P.hjf, mul_pos hf hN, mul_pos hep hN, mul_pos hf hj]
    have hsE : (s : ℝ) ≤ eps * n := le_trans hsb hbe
    have hcE : Real.exp 1 * j * s / n / Real.exp 1 ≤ eps * j := by
      rw [hce, div_le_iff₀ hN]
      nlinarith [mul_le_mul_of_nonneg_left hsE hj.le]
    have hmono := rpow_div_self_antitone hcpos hcE
      (by have := mul_pos hf hs0; nlinarith : eps * j ≤ f * s / 2 + eps * j)
    have hbase : Real.exp 1 * j * s / n / (eps * j) = Real.exp 1 * s / (eps * n) := by
      field_simp
    rw [hbase] at hmono
    rw [hdiv]
    exact mul_le_mul hC hmono (by positivity) hA
  · -- s > b
    unfold G2
    have hcE : Real.exp 1 * j * s / n / Real.exp 1 ≤ f * s / 2 := by
      rw [hce, div_le_iff₀ hN]
      nlinarith [P.hjf, mul_pos hf hs0, mul_pos hf hN]
    have hmono := rpow_div_self_antitone hcpos hcE
      (by nlinarith : f * s / 2 ≤ f * s / 2 + eps * j)
    have hbase : Real.exp 1 * j * s / n / (f * s / 2) = 2 * Real.exp 1 * j / (f * n) := by
      field_simp
    rw [hbase] at hmono
    rw [hdiv]
    exact mul_le_mul hC hmono (by positivity) hA

end Chvatal
