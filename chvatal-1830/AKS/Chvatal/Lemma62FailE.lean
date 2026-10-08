module

/-
  # Chvátal Lemma 6.2: the per-`E` failure bound (T2b)

  Source: V. Chvátal, DCS-TR-294 (1992), end of the proof of Lemma 6.2.

  Assembles the union bound over tops (`badSetF_card_le`), the per-matrix tail sum
  (`scramble_tail_union_top`, `pbound_le_gfun`), the two-sided geometric sum
  (`gfun_sum_le_G1'`, now also for `⌊b⌋ = 0`), the closed form for the number of tops and the
  numeric bound `x ≤ 3/10` into `fail_prob_at_E`.
-/

public import AKS.Chvatal.Lemma62FailReduce
public import AKS.Chvatal.Lemma62Ratio
public import AKS.Chvatal.Lemma62TopsClosed
public import AKS.Chvatal.Lemma62Numerics
public import AKS.Chvatal.GeomTail

@[expose] public section

namespace Chvatal

/-! ## (2) Geometric sum without `1 ≤ ⌊b⌋` -/

lemma bpt_le_eps_N {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) : bpt f j ≤ eps * n := by
  have hf := P.f_pos
  have hN := P.N_pos
  have hj := P.hj
  have hep := eps_pos
  have := bpt_le_N P
  unfold bpt
  rw [div_le_iff₀ hf]
  nlinarith [P.hjf, mul_pos hf hN, mul_pos hep hN, mul_pos hf hj]

lemma bpt_succ_le {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) : bpt f j + 1 ≤ n := by
  have h := bpt_le_eps_N P
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast P.hn
  have : eps ≤ 1 / (8 * 10 ^ 7) := le_refl _
  nlinarith

theorem gfun_sum_le_G1' {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) :
    ∑ s ∈ Finset.Icc 1 n, gfun n f j s ≤
      (1 + Real.exp (-5)) / (1 - Real.exp (-5)) * G1 n j (bpt f j) := by
  have hb := bpt_pos P.f_pos P.hj
  have hN := P.N_pos
  have hρ := exp_neg5_pos_lt
  have h1ρ : 0 < 1 - Real.exp (-5) := by linarith [hρ.2]
  have hbs := bpt_succ_le P
  by_cases ha1 : 1 ≤ ⌊bpt f j⌋₊
  · refine gfun_sum_le_G1 P _ rfl ha1 ?_
    have h1 : (⌊bpt f j⌋₊ : ℝ) ≤ bpt f j := Nat.floor_le hb.le
    have : ((⌊bpt f j⌋₊ + 1 : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  · have ha0 : ⌊bpt f j⌋₊ = 0 := by omega
    have hb1 : bpt f j < 1 := (Nat.floor_eq_zero.mp ha0)
    have hG : 0 ≤ G1 n j (bpt f j) := G1_nonneg _ _ _ hN.le hb.le
    have hgeom := geom_right_sum (Real.exp (-5)) hρ.1 hρ.2 (gfun n f j) (gfun_nonneg P) 1 n
      (by
        intro s hs1 _
        have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
        have h1 : ¬ (s : ℝ) ≤ bpt f j := by linarith
        have h2 : ¬ ((s + 1 : ℕ) : ℝ) ≤ bpt f j := by push_cast; linarith
        unfold gfun
        rw [if_neg h1, if_neg h2]
        have := ratio_right P s (by linarith)
        simpa using this)
    have hg1 : gfun n f j 1 ≤ G1 n j (bpt f j) := by
      have h1 : ¬ (((1 : ℕ)) : ℝ) ≤ bpt f j := by push_cast; linarith
      unfold gfun
      rw [if_neg h1, G1_bpt_eq_G2_bpt P]
      have := G2_step P (le_refl (bpt f j)) (by push_cast; linarith : bpt f j ≤ ((1 : ℕ) : ℝ))
      have h5 : Real.exp (-5 * (((1 : ℕ) : ℝ) - bpt f j)) ≤ 1 := by
        rw [← Real.exp_zero]; apply Real.exp_le_exp.mpr; push_cast; linarith
      have hG2 : 0 ≤ G2 n f j (bpt f j) :=
        G2_nonneg _ _ _ _ hN.le hb.le P.f_pos.le P.hj.le
      calc _ ≤ _ := this
        _ ≤ 1 * G2 n f j (bpt f j) := mul_le_mul_of_nonneg_right h5 hG2
        _ = _ := one_mul _
    have hsum_eq : ∑ s ∈ Finset.Icc 1 n, gfun n f j s = ∑ s ∈ Finset.Icc 1 n, gfun n f j s := rfl
    calc ∑ s ∈ Finset.Icc 1 n, gfun n f j s ≤ gfun n f j 1 / (1 - Real.exp (-5)) := hgeom
      _ ≤ G1 n j (bpt f j) / (1 - Real.exp (-5)) := div_le_div_of_nonneg_right hg1 h1ρ.le
      _ ≤ (1 + Real.exp (-5)) * G1 n j (bpt f j) / (1 - Real.exp (-5)) := by
          apply div_le_div_of_nonneg_right _ h1ρ.le
          nlinarith [hρ.1]
      _ = _ := by ring

/-! ## (5) Constants -/

lemma exp_five_ge : (148.41 : ℝ) ≤ Real.exp 5 := by
  have h1 := Real.exp_one_gt_d9
  have h : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  have h2 : (2.7182818283 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 :=
    pow_le_pow_left₀ (by norm_num) h1.le 5
  have : (148.41 : ℝ) ≤ 2.7182818283 ^ 5 := by norm_num
  linarith

lemma const_bound :
    90 / 89 * ((1 + Real.exp (-5)) / (1 - Real.exp (-5))) ≤ (1.025 : ℝ) := by
  have h := exp_five_ge
  have hx : Real.exp (-5) = (Real.exp 5)⁻¹ := Real.exp_neg 5
  set x := Real.exp 5
  have hxpos : 0 < x := by linarith
  have e : (1 + Real.exp (-5)) / (1 - Real.exp (-5)) = 1 + 2 / (x - 1) := by
    rw [hx]
    have : x - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [e]
  have h2 : 2 / (x - 1) ≤ 2 / 147.41 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have : 90 / 89 * (1 + 2 / 147.41) ≤ (1.025 : ℝ) := by norm_num
  nlinarith

/-! ## (1) Per-matrix tail sum -/

theorem tail_sum_le {m n f : ℕ} (j : ℕ) (P : Lemma62Params n (f : ℝ) (j : ℝ))
    (c : MonotoneColumnSums m n) (hc : totalColumnOnes c = j) :
    ∑ s ∈ Finset.Icc 1 n,
      ((tailBadSet c (topRows m (f / 2)) s ((f / 2 : ℝ) * s + eps * j)).card : ℝ) ≤
        (∑ s ∈ Finset.Icc 1 n, pbound n (f : ℝ) j s) * (Fintype.card (Scramble m n) : ℝ) := by
  have hcard : (0 : ℝ) < Fintype.card (Scramble m n) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble m n))
  have hn : 0 < n := by have := P.hn; omega
  have hj0 : 0 < j := by
    have := P.hj; exact_mod_cast this
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun s hs => ?_
  rw [Finset.mem_Icc] at hs
  have hs0 : 0 < s := hs.1
  have hsR : (s : ℝ) ≤ n := by exact_mod_cast hs.2
  have hN := P.N_pos
  have hT : (totalColumnOnes c : ℝ) * s / n ≤ (f : ℝ) / 2 * s + eps * j := by
    rw [hc, div_le_iff₀ hN]
    have hep := eps_pos
    have hj' := P.hj
    have hf := P.f_pos
    have hjf := P.hjf
    have hs' : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    have : (j:ℝ) * s ≤ f * n / 31 * s := mul_le_mul_of_nonneg_right hjf hs'
    have h2 : (f : ℝ) / 2 * s * n ≥ f * s * n / 31 := by nlinarith [mul_nonneg (mul_nonneg hf.le hs') hN.le]
    nlinarith [mul_nonneg hep.le hj'.le, mul_nonneg (mul_nonneg hep.le hj'.le) hN.le,
      mul_nonneg hs' hN.le]
  have key := scramble_tail_union_top hn c (f / 2) s ((f : ℝ) / 2 * s + eps * j) (by rw [hc]; exact hj0) hs0 hT
  rw [div_le_iff₀ hcard] at key
  refine key.trans (le_of_eq ?_)
  rw [hc]
  unfold pbound
  rw [show (f : ℝ) / 2 * s = f * s / 2 by ring]

/-! ## (4) Closed form of `G1(b)` and the tops-times-`G1` bound -/

theorem G1_bpt_closed {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) :
    G1 n j (bpt f j) =
      ((Real.exp 1 * f * n / (2 * eps * j)) ^ (2 / f) * (2 * Real.exp 1 * j / (f * n))) ^
        (eps * j) := by
  have hf := P.f_pos
  have hN := P.N_pos
  have hj := P.hj
  have hep := eps_pos
  have e1 : Real.exp 1 * n / bpt f j = Real.exp 1 * f * n / (2 * eps * j) := by
    unfold bpt; field_simp
  have e2 : Real.exp 1 * bpt f j / (eps * n) = 2 * Real.exp 1 * j / (f * n) := by
    unfold bpt; field_simp
  have e3 : bpt f j = 2 / f * (eps * j) := by unfold bpt; field_simp
  have hK : 0 ≤ Real.exp 1 * f * n / (2 * eps * j) := by positivity
  unfold G1
  rw [e1, e2, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hK, ← e3]

theorem tops_mul_G1_le {n j f : ℕ} (hf : Even f) (P : Lemma62Params n (f : ℝ) (j : ℝ))
    (E : ℕ) (hE : (E : ℝ) = eps * j) :
    ((tops (f / 2) n j).card : ℝ) * G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ)) ≤
      90 / 89 * xval (n : ℝ) (f : ℝ) (j : ℝ) ^ E := by
  have hfp := P.f_pos
  have hN := P.N_pos
  have hj := P.hj
  have hep := eps_pos
  have htops := tops_card_le_closed n j f P hf
  have hnum := params_numeric P
  set Y : ℝ := Real.exp 1 ^ 2 * ((f : ℝ) + 2) ^ 2 * n / (4 * j) with hY
  have hY1 : 1 ≤ Y := by
    have h1 : (90 : ℝ) ≤ ((f : ℝ) + 2) ^ 2 * n / (4 * j) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2 : (1 : ℝ) ≤ Real.exp 1 ^ 2 := by
      have := Real.add_one_le_exp (1 : ℝ)
      nlinarith
    have : Y = Real.exp 1 ^ 2 * (((f : ℝ) + 2) ^ 2 * n / (4 * j)) := by rw [hY]; ring
    rw [this]; nlinarith
  have hexp : 2 * (j : ℝ) / ((f : ℝ) + 2) ≤ 2 / (eps * f) * (eps * j) := by
    have : 2 / (eps * (f : ℝ)) * (eps * j) = 2 * j / f := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_left (by positivity) hfp (by linarith)
  have hY2 : Y ^ (2 * (j : ℝ) / ((f : ℝ) + 2)) ≤ (Y ^ (2 / (eps * (f : ℝ)))) ^ (eps * (j : ℝ)) := by
    rw [← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hY1 hexp
  have hG := G1_bpt_closed P
  have hGnn : 0 ≤ G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ)) :=
    G1_nonneg _ _ _ hN.le (bpt_pos hfp hj).le
  have hx : xval (n : ℝ) (f : ℝ) (j : ℝ) ^ E =
      (Y ^ (2 / (eps * (f : ℝ)))) ^ (eps * (j : ℝ)) *
        G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ)) := by
    rw [hG, ← Real.rpow_natCast, hE, ← Real.mul_rpow (by positivity) (by positivity)]
    unfold xval
    rw [mul_assoc]
  rw [hx]
  calc ((tops (f / 2) n j).card : ℝ) * G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ))
      ≤ (90 / 89 * Y ^ (2 * (j : ℝ) / ((f : ℝ) + 2))) * G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ)) :=
        mul_le_mul_of_nonneg_right htops hGnn
    _ ≤ (90 / 89 * (Y ^ (2 / (eps * (f : ℝ)))) ^ (eps * (j : ℝ))) *
          G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hGnn
        exact mul_le_mul_of_nonneg_left hY2 (by norm_num)
    _ = _ := by ring

/-! ## (6) Main theorem -/

theorem fail_prob_at_E {m n f : ℕ} (hf : Even f) (deltaF : ℝ) (j E : ℕ) (hE1 : 1 ≤ E)
    (hE : (E : ℝ) = eps * j) (P : Lemma62Params n (f : ℝ) (j : ℝ)) :
    ((badSetF (m := m) (n := n) hf deltaF eps j).card : ℝ) ≤
      1.025 * (3 / 10 : ℝ) ^ E * (Fintype.card (Scramble m n) : ℝ) := by
  have hep := eps_pos
  have hj0 : 0 < j := by have := P.hj; exact_mod_cast this
  have hjE : (8 * 10 ^ 7 : ℝ) ≤ j := by
    have h1 : (1 : ℝ) ≤ E := by exact_mod_cast hE1
    rw [hE] at h1
    have : eps = 1 / (8 * 10 ^ 7) := rfl
    rw [this] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)] at h1
    linarith
  have hb := bpt_pos P.f_pos P.hj
  have hN := P.N_pos
  have hρ := exp_neg5_pos_lt
  have h1ρ : 0 < 1 - Real.exp (-5) := by linarith [hρ.2]
  set C : ℝ := (1 + Real.exp (-5)) / (1 - Real.exp (-5)) with hC
  have hC0 : 0 ≤ C := by rw [hC]; apply div_nonneg <;> linarith [hρ.1]
  have hG := G1_nonneg n (j : ℝ) (bpt (f : ℝ) (j : ℝ)) hN.le hb.le
  have hmain := badSetF_card_le (m := m) (n := n) hf deltaF eps eps_pos j hj0
    (C * G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ))) (mul_nonneg hC0 hG) (by
      intro c hc
      refine (tail_sum_le j P c hc).trans ?_
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      refine le_trans (Finset.sum_le_sum fun s hs => ?_) (gfun_sum_le_G1' P)
      rw [Finset.mem_Icc] at hs
      exact pbound_le_gfun P s hs.1 hs.2)
  refine hmain.trans ?_
  have hcard : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  have h1 := tops_mul_G1_le hf P E hE
  have h2 := xval_pow_le P hjE E
  have hCc := const_bound
  have hT : (0 : ℝ) ≤ ((tops (f / 2) n j).card : ℝ) := Nat.cast_nonneg _
  calc ((tops (f / 2) n j).card : ℝ) * (C * G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ))) *
        (Fintype.card (Scramble m n) : ℝ)
      = C * (((tops (f / 2) n j).card : ℝ) * G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ))) *
        (Fintype.card (Scramble m n) : ℝ) := by ring
    _ ≤ C * (90 / 89 * xval (n : ℝ) (f : ℝ) (j : ℝ) ^ E) * (Fintype.card (Scramble m n) : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hcard
        exact mul_le_mul_of_nonneg_left h1 hC0
    _ ≤ C * (90 / 89 * (3 / 10 : ℝ) ^ E) * (Fintype.card (Scramble m n) : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hcard
        apply mul_le_mul_of_nonneg_left _ hC0
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = (90 / 89 * C) * (3 / 10 : ℝ) ^ E * (Fintype.card (Scramble m n) : ℝ) := by ring
    _ ≤ 1.025 * (3 / 10 : ℝ) ^ E * (Fintype.card (Scramble m n) : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hcard
        exact mul_le_mul_of_nonneg_right hCc (by positivity)

end Chvatal
