module

public import AKS.Chvatal.Lemma62Ratio
public import AKS.Chvatal.Lemma62TopsCount
public import AKS.Chvatal.Lemma62TopsAnalytic

/-! # Chvátal Lemma 6.2 (ii): closed form for the number of tops, display (6.3)

With `h = f/2` we bound `Σ_k C(n,k)·C(j - h k, k)` by `(90/89)·(e²(f+2)² n/(4j))^{2j/(f+2)}`.
Terms with `k > j/(h+1)` vanish; the rest are at most `y(k) = (e² n j/k²)^k`, and
`y(k+1) ≥ 90·y(k)` for `k+1 ≤ 2j/(f+2)`, so the sum is dominated by `(90/89)·y(K)`;
finally `y` is monotone on `[1, 2j/(f+2)]` because `(ln y)' = ln(n j/x²) ≥ 0` there. -/

@[expose] public section

namespace Chvatal

/-- `y(k) = (e² c/k²)^k` with natural exponent (`c = n j`). -/
noncomputable def topYn (c : ℝ) (k : ℕ) : ℝ := (Real.exp 1 ^ 2 * c / (k : ℝ) ^ 2) ^ k

/-- `y(x) = (e² c/x²)^x` with real exponent. -/
noncomputable def topY (c x : ℝ) : ℝ := (Real.exp 1 ^ 2 * c / x ^ 2) ^ x

lemma topYn_ratio (c : ℝ) (hc : 0 < c) (k : ℕ) :
    c / ((k : ℝ) + 1) ^ 2 * topYn c k ≤ topYn c (k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [topYn]
    norm_num
    nlinarith [Real.one_le_exp (show (0 : ℝ) ≤ 2 by norm_num)]
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hexp : (((k : ℝ) + 1) / k) ^ k ≤ Real.exp 1 := by
      have h1 : ((k : ℝ) + 1) / k ≤ Real.exp (1 / (k : ℝ)) := by
        have := Real.add_one_le_exp (1 / (k : ℝ))
        have e : ((k : ℝ) + 1) / k = 1 / k + 1 := by field_simp; ring
        linarith
      calc _ ≤ (Real.exp (1 / (k : ℝ))) ^ k := pow_le_pow_left₀ (by positivity) h1 k
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; field_simp
    set B : ℝ := Real.exp 1 ^ 2 * c / ((k : ℝ) + 1) ^ 2 with hB
    have e1 : Real.exp 1 ^ 2 * c / (k : ℝ) ^ 2 = B * (((k : ℝ) + 1) / k) ^ 2 := by
      rw [hB]; field_simp
    have e2 : topYn c k ≤ B ^ k * Real.exp 1 ^ 2 := by
      unfold topYn
      rw [e1, mul_pow, ← pow_mul, pow_mul']
      gcongr
    have e3 : topYn c (k + 1) = B * B ^ k := by
      unfold topYn
      push_cast
      rw [← hB, pow_succ]; ring
    rw [e3]
    calc c / ((k : ℝ) + 1) ^ 2 * topYn c k
        ≤ c / ((k : ℝ) + 1) ^ 2 * (B ^ k * Real.exp 1 ^ 2) :=
          mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = B * B ^ k := by rw [hB]; field_simp

/-- Geometric domination. -/
lemma geom_sum_le (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) :
    ∀ K : ℕ, (∀ k, k < K → 90 * a k ≤ a (k + 1)) →
      ∑ k ∈ Finset.range (K + 1), a k ≤ 90 / 89 * a K := by
  intro K
  induction K with
  | zero => intro _; simp; nlinarith [ha 0]
  | succ K ih =>
    intro h
    have := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have := h K (Nat.lt_succ_self K)
    rw [Finset.sum_range_succ]
    linarith

lemma topY_mono (c : ℝ) (hc : 0 < c) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ^ 2 ≤ c) :
    topY c a ≤ topY c b := by
  have key : ∀ x : ℝ, 0 < x →
      topY c x = Real.exp (2 * (x * (1 + Real.log c / 2 - Real.log x))) := fun x hx => by
    rw [topY, Real.rpow_def_of_pos (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow, Real.log_exp]
    congr 1
    push_cast
    ring
  rw [key a (by linarith), key b (by linarith)]
  refine Real.exp_le_exp.mpr ?_
  have := le_of_deriv_nonneg_aux (F := fun t => t * ((1 + Real.log c / 2) - Real.log t))
    (F' := fun t => (1 + Real.log c / 2) - 1 - Real.log t) (a := 0)
    (fun t ht => hasDerivAt_xlog _ t ht) (by linarith) hab fun t ht1 ht2 => by
      have ht0 : 0 < t := by linarith
      have : 2 * Real.log t = Real.log (t ^ 2) := by rw [Real.log_pow]; norm_num
      have : Real.log (t ^ 2) ≤ Real.log c :=
        Real.log_le_log (by positivity) (by nlinarith)
      linarith
  linarith

lemma params_numeric {n : ℕ} {f j : ℝ} (hp : Lemma62Params n f j) :
    90 * (4 * j) ≤ (f + 2) ^ 2 * n := by
  obtain ⟨hn, hf, hj, hjf⟩ := hp
  have hn' : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 ≤ f ^ 2 - 8 * f + 4 := by nlinarith
  nlinarith [mul_nonneg h1 (by linarith : (0 : ℝ) ≤ n), mul_nonneg (by linarith : (0 : ℝ) ≤ f) (by linarith : (0 : ℝ) ≤ n)]

/-- Closed-form bound on the number of distinct tops (Chvátal (6.3)). -/
theorem tops_card_le_closed (n j f : ℕ) (hp : Lemma62Params n (f : ℝ) (j : ℝ)) (hf : Even f) :
    ((tops (f / 2) n j).card : ℝ) ≤
      90 / 89 * (Real.exp 1 ^ 2 * ((f : ℝ) + 2) ^ 2 * n / (4 * j)) ^
        (2 * (j : ℝ) / ((f : ℝ) + 2)) := by
  obtain ⟨h, hfh⟩ := hf
  have hf2 : f / 2 = h := by omega
  have h1 : ((tops (f / 2) n j).card : ℝ) ≤
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((j - (f / 2) * k).choose k : ℝ) := by
    have := tops_card_le (f / 2) n j
    unfold topClosed at this
    exact_mod_cast this
  refine h1.trans ?_
  rw [hf2]
  have hfr : (f : ℝ) = 2 * h := by rw [hfh]; push_cast; ring
  have hnum := params_numeric hp
  have hj : (0 : ℝ) < j := hp.hj
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := hp.hn; omega : 0 < n)
  have hfpos : (0 : ℝ) < (f : ℝ) + 2 := by have := hp.hf; linarith
  set c : ℝ := (n : ℝ) * j with hcdef
  have hc : 0 < c := by positivity
  set x0 : ℝ := 2 * (j : ℝ) / ((f : ℝ) + 2) with hx0
  have hx0pos : 0 < x0 := by positivity
  have hc2 : c / x0 ^ 2 = ((f : ℝ) + 2) ^ 2 * n / (4 * j) := by
    rw [hx0, hcdef]; field_simp; norm_num
  have hbig : 90 ≤ c / x0 ^ 2 := by
    rw [hc2, le_div_iff₀ (by positivity)]; linarith
  have hx0sq : x0 ^ 2 ≤ c := by
    have := (le_div_iff₀ (by positivity : 0 < x0 ^ 2)).mp hbig
    nlinarith [sq_nonneg x0]
  set K : ℕ := j / (h + 1) with hK
  have hKx : (K : ℝ) ≤ x0 := by
    have h1 : (K : ℝ) ≤ (j : ℝ) / ((h : ℝ) + 1) := by
      simpa using Nat.cast_div_le (α := ℝ) (m := j) (n := h + 1)
    have h2 : x0 = (j : ℝ) / ((h : ℝ) + 1) := by
      rw [hx0, hfr]; field_simp
    rw [h2]; exact h1
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * ((j - h * k).choose k : ℝ) ≤ if k ≤ K then topYn c k else 0 := by
    intro k _
    by_cases hkK : k ≤ K
    · rw [if_pos hkK]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [topYn]
      · calc _ ≤ _ := choose_mul_choose_le_of_le n (J := j - h * k) (j := j) (Nat.sub_le _ _) hk
          _ = topYn c k := by rw [topYn, hcdef, mul_assoc]
    · rw [if_neg hkK]
      have hlt : j < k * (h + 1) := (Nat.div_lt_iff_lt_mul (by omega)).mp (not_le.mp hkK)
      have : j - h * k < k := by
        obtain ⟨m, hm⟩ : ∃ m, m = h * k := ⟨_, rfl⟩
        have h3 : j < h * k + k := by nlinarith [hlt]
        have hk0 : 0 < k := lt_of_le_of_lt (Nat.zero_le _) (not_le.mp hkK)
        rw [← hm] at h3 ⊢; omega
      rw [Nat.choose_eq_zero_of_lt this]; simp
  have hYnn : ∀ k, 0 ≤ topYn c k := fun k => by unfold topYn; positivity
  have hsum1 : (∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * ((j - h * k).choose k : ℝ)) ≤
      ∑ k ∈ Finset.range (K + 1), topYn c k := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hYnn k)
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  have hgeom := geom_sum_le (topYn c) hYnn K fun k hk => by
    have h2 : 90 ≤ c / ((k : ℝ) + 1) ^ 2 := by
      refine hbig.trans (div_le_div_of_nonneg_left hc.le (by positivity) ?_)
      have : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
      nlinarith
    exact (mul_le_mul_of_nonneg_right h2 (hYnn k)).trans (topYn_ratio c hc k)
  have hbase : Real.exp 1 ^ 2 * c / x0 ^ 2 =
      Real.exp 1 ^ 2 * ((f : ℝ) + 2) ^ 2 * n / (4 * j) := by
    rw [mul_div_assoc, hc2]; ring
  have hY : topYn c K ≤ (Real.exp 1 ^ 2 * ((f : ℝ) + 2) ^ 2 * n / (4 * j)) ^ x0 := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0]
      simp only [topYn, pow_zero]
      apply Real.one_le_rpow _ hx0pos.le
      rw [← hbase, mul_div_assoc]
      nlinarith [one_le_pow₀ (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)) (n := 2)]
    · have := topY_mono c hc (a := (K : ℝ)) (b := x0) (by exact_mod_cast h0) hKx hx0sq
      refine (le_of_eq (Real.rpow_natCast _ _).symm).trans (this.trans (le_of_eq ?_))
      unfold topY
      rw [hbase]
  calc _ ≤ ∑ k ∈ Finset.range (K + 1), topYn c k := hsum1
    _ ≤ 90 / 89 * topYn c K := hgeom
    _ ≤ _ := by gcongr

end Chvatal
