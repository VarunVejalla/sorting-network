module

/-
  # Chvátal Lemma 6.2, claim (ii): closed form for the number of tops

  Source: Chvátal, DCS-TR-294, proof of Lemma 6.2 (ii), display (6.3).

  With `h = f/2` we bound `Σ_k C(n,k)·C(j - h k, k)` (from `tops_card_le`) by
  `(90/89)·(e²(f+2)² n/(4j))^{2j/(f+2)}`.  Terms with `k > j/(h+1)` vanish; the rest are
  at most `y(k) = (e² n j/k²)^k`, and `y(k+1) ≥ n j/(k+1)² · y(k) ≥ 90·y(k)` for
  `k+1 ≤ 2j/(f+2)`, so the sum is dominated by `(90/89)·y(K)`; finally `y` is monotone on
  `[1, 2j/(f+2)]` because `(ln y)' = ln(n j/x²) ≥ 0` there.
-/

public import AKS.Chvatal.Lemma62Ratio
public import AKS.Chvatal.Lemma62TopsCount
public import AKS.Chvatal.Lemma62TopsAnalytic

@[expose] public section

namespace Chvatal

/-- `y(k) = (e² c/k²)^k` with natural exponent (`c = n j`). -/
noncomputable def topYn (c : ℝ) (k : ℕ) : ℝ := (Real.exp 1 ^ 2 * c / (k : ℝ) ^ 2) ^ k

/-- `y(x) = (e² c/x²)^x` with real exponent. -/
noncomputable def topY (c x : ℝ) : ℝ := (Real.exp 1 ^ 2 * c / x ^ 2) ^ x

lemma topYn_eq (c : ℝ) (k : ℕ) : topYn c k = topY c k :=
  (Real.rpow_natCast _ _).symm

lemma pow_ratio_le (k : ℕ) (hk : 1 ≤ k) : (((k : ℝ) + 1) / k) ^ k ≤ Real.exp 1 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : ((k : ℝ) + 1) / k ≤ Real.exp (1 / (k : ℝ)) := by
    have := Real.add_one_le_exp (1 / (k : ℝ))
    have e : ((k : ℝ) + 1) / k = 1 / k + 1 := by field_simp; ring
    linarith
  calc (((k : ℝ) + 1) / k) ^ k ≤ (Real.exp (1 / (k : ℝ))) ^ k :=
        pow_le_pow_left₀ (by positivity) h1 k
    _ = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp

lemma topYn_ratio (c : ℝ) (hc : 0 < c) (k : ℕ) :
    c / ((k : ℝ) + 1) ^ 2 * topYn c k ≤ topYn c (k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [topYn]
    have h2 : (1 : ℝ) ≤ Real.exp 2 := by
      exact Real.one_le_exp (by norm_num)
    norm_num
    nlinarith
  · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hBpos : 0 < Real.exp 1 ^ 2 * c / ((k : ℝ) + 1) ^ 2 := by positivity
    obtain ⟨B, hB⟩ : ∃ B, B = Real.exp 1 ^ 2 * c / ((k : ℝ) + 1) ^ 2 := ⟨_, rfl⟩
    rw [← hB] at hBpos
    have e1 : Real.exp 1 ^ 2 * c / (k : ℝ) ^ 2 = B * (((k : ℝ) + 1) / k) ^ 2 := by
      rw [hB]; field_simp
    have e2 : topYn c k ≤ B ^ k * Real.exp 1 ^ 2 := by
      unfold topYn
      rw [e1, mul_pow, ← pow_mul, pow_mul']
      gcongr
      exact pow_ratio_le k hk
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
    have h1 := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have h2 := h K (Nat.lt_succ_self K)
    rw [Finset.sum_range_succ]
    linarith

/-- Monotonicity of `x ↦ x (2 + ln c - 2 ln x)` on `[a, b]` when `b² ≤ c`. -/
lemma phi_mono (c : ℝ) (hc : 0 < c) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ^ 2 ≤ c) :
    a * (2 + Real.log c - 2 * Real.log a) ≤ b * (2 + Real.log c - 2 * Real.log b) := by
  have hd : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun x : ℝ => x * (2 + Real.log c - 2 * Real.log x))
        (Real.log c - 2 * Real.log x) x := by
    intro x hx
    have h1 := (hasDerivAt_id x).mul
      ((hasDerivAt_const x (2 + Real.log c)).sub ((Real.hasDerivAt_log hx.ne').const_mul 2))
    convert h1 using 1
    simp only [id, Pi.sub_apply]
    field_simp
    ring
  have hmono : MonotoneOn (fun x : ℝ => x * (2 + Real.log c - 2 * Real.log x)) (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro x hx
      exact (hd x (by linarith [hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x (by linarith [hx.1])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      rw [(hd x hx0).deriv]
      have : 2 * Real.log x = Real.log (x ^ 2) := by rw [Real.log_pow]; norm_num
      have h3 : Real.log (x ^ 2) ≤ Real.log c :=
        Real.log_le_log (by positivity) (by nlinarith [hx.2])
      linarith
  exact hmono ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab

lemma topY_eq_exp (c x : ℝ) (hc : 0 < c) (hx : 0 < x) :
    topY c x = Real.exp (x * (2 + Real.log c - 2 * Real.log x)) := by
  unfold topY
  rw [Real.rpow_def_of_pos (by positivity)]
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    ]
  simp only [Real.log_pow, Real.log_exp]
  congr 1
  push_cast
  ring

lemma topY_mono (c : ℝ) (hc : 0 < c) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ^ 2 ≤ c) :
    topY c a ≤ topY c b := by
  rw [topY_eq_exp c a hc (by linarith), topY_eq_exp c b hc (by linarith)]
  exact Real.exp_le_exp.mpr (phi_mono c hc ha hab hb)

lemma params_numeric {n : ℕ} {f j : ℝ} (hp : Lemma62Params n f j) :
    90 * (4 * j) ≤ (f + 2) ^ 2 * n := by
  obtain ⟨hn, hf, hj, hjf⟩ := hp
  have hn' : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 ≤ f ^ 2 - 8 * f + 4 := by nlinarith
  have h2 := mul_nonneg h1 (by linarith : (0 : ℝ) ≤ n)
  have h3 : 0 ≤ f * (n : ℝ) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- **A5a** (closed form for the tops count sum, Chvátal (6.3)). -/
theorem tops_closed_bound (n j f : ℕ) (hp : Lemma62Params n (f : ℝ) (j : ℝ)) (hf : Even f) :
    (∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * ((j - (f / 2) * k).choose k : ℝ)) ≤
      90 / 89 * (Real.exp 1 ^ 2 * ((f : ℝ) + 2) ^ 2 * n / (4 * j)) ^
        (2 * (j : ℝ) / ((f : ℝ) + 2)) := by
  obtain ⟨h, hfh⟩ := hf
  have hf2 : f / 2 = h := by omega
  rw [hf2]
  have hfr : (f : ℝ) = 2 * h := by rw [hfh]; push_cast; ring
  have hnum := params_numeric hp
  have hj : (0 : ℝ) < j := hp.hj
  have hn0 : (0 : ℝ) < n := by
    have := hp.hn; exact_mod_cast (by omega : 0 < n)
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
      have := Nat.cast_div_le (α := ℝ) (m := j) (n := h + 1)
      simpa using this
    have h2 : x0 = (j : ℝ) / ((h : ℝ) + 1) := by
      rw [hx0, hfr]; field_simp
    rw [h2]; exact h1
  -- termwise bound
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * ((j - h * k).choose k : ℝ) ≤ if k ≤ K then topYn c k else 0 := by
    intro k _
    by_cases hkK : k ≤ K
    · rw [if_pos hkK]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [topYn]
      · have := choose_mul_choose_le_of_le n (J := j - h * k) (j := j) (Nat.sub_le _ _) hk
        calc _ ≤ _ := this
          _ = topYn c k := by rw [topYn, hcdef, mul_assoc]
    · rw [if_neg hkK]
      have hlt : j < k * (h + 1) := (Nat.div_lt_iff_lt_mul (by omega)).mp (not_le.mp hkK)
      have h3 : j < h * k + k := by nlinarith [hlt]
      have : j - h * k < k := by
        obtain ⟨m, hm⟩ : ∃ m, m = h * k := ⟨_, rfl⟩
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
  have hgeom := geom_sum_le (topYn c) hYnn K (by
    intro k hk
    have h1 := topYn_ratio c hc k
    have h2 : 90 ≤ c / ((k : ℝ) + 1) ^ 2 := by
      refine hbig.trans ?_
      apply div_le_div_of_nonneg_left hc.le (by positivity)
      have : ((k : ℝ) + 1) ≤ x0 := by
        have : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
        linarith
      nlinarith
    exact (mul_le_mul_of_nonneg_right h2 (hYnn k)).trans h1)
  have hbase : Real.exp 1 ^ 2 * c / x0 ^ 2 =
      Real.exp 1 ^ 2 * ((f : ℝ) + 2) ^ 2 * n / (4 * j) := by
    rw [mul_div_assoc, hc2]; ring
  have hY : topYn c K ≤ (Real.exp 1 ^ 2 * ((f : ℝ) + 2) ^ 2 * n / (4 * j)) ^ x0 := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0]
      simp only [topYn, pow_zero]
      apply Real.one_le_rpow _ hx0pos.le
      rw [← hbase, mul_div_assoc]
      have : (1 : ℝ) ≤ Real.exp 1 ^ 2 := one_le_pow₀ (Real.one_le_exp (by norm_num))
      nlinarith
    · rw [topYn_eq]
      have := topY_mono c hc (a := (K : ℝ)) (b := x0) (by exact_mod_cast h0) hKx hx0sq
      refine this.trans (le_of_eq ?_)
      unfold topY
      rw [hbase]
  calc _ ≤ ∑ k ∈ Finset.range (K + 1), topYn c k := hsum1
    _ ≤ 90 / 89 * topYn c K := hgeom
    _ ≤ _ := by gcongr

/-- **A5a, corollary**: closed-form bound on the number of distinct tops. -/
theorem tops_card_le_closed (n j f : ℕ) (hp : Lemma62Params n (f : ℝ) (j : ℝ)) (hf : Even f) :
    ((tops (f / 2) n j).card : ℝ) ≤
      90 / 89 * (Real.exp 1 ^ 2 * ((f : ℝ) + 2) ^ 2 * n / (4 * j)) ^
        (2 * (j : ℝ) / ((f : ℝ) + 2)) := by
  have h1 : ((tops (f / 2) n j).card : ℝ) ≤
      ((∑ k ∈ Finset.range (n + 1), Nat.choose n k * Nat.choose (j - (f / 2) * k) k : ℕ) : ℝ) :=
    by exact_mod_cast tops_card_le (f / 2) n j
  push_cast at h1
  exact h1.trans (tops_closed_bound n j f hp hf)

end Chvatal
