import Round2Union
import Round1Num

/-! # Round 2: from per-cell checks to the failure bound for every `n ≥ 16`, `M ≤ m ≤ M_hi`

Cells cover `p ∈ [0, 1/2]`. For a size `s` with `s/n ≤ 1/2` the cell containing `s/n` supplies
`(λ, t, α, β)`; for `s/n > 1/2` the cell containing `1 - s/n` supplies `(λ, t, β, α)` (the rate
conditions and the budget are symmetric under `p ↔ 1-p`). The base rows are the multiples of an
odd spacing `g = 2g'+1`, clamped at `m`. -/

open Finset BigOperators Chvatal Real

namespace Round2Num

open Round2Col

/-- The grid of base rows. -/
def grid (m g : ℕ) : Finset ℕ := (Finset.range (m / g + 2)).image fun k => min (k * g) m

theorem grid_le (m g : ℕ) : ∀ b ∈ grid m g, b ≤ m := by
  intro b hb
  simp only [grid, Finset.mem_image] at hb
  obtain ⟨k, _, rfl⟩ := hb
  exact min_le_right _ _

theorem grid_card (m g : ℕ) : (grid m g).card ≤ m / g + 2 := by
  calc (grid m g).card ≤ (Finset.range (m / g + 2)).card := Finset.card_image_le
    _ = m / g + 2 := Finset.card_range _

theorem grid_cover (m g' : ℕ) (i : ℕ) (hi : i ≤ m) :
    ∃ b ∈ grid m (2 * g' + 1), |(i : ℝ) - b| ≤ g' := by
  set g := 2 * g' + 1 with hgdef
  have hg : 0 < g := by omega
  set k := (i + g') / g with hkdef
  have hk1 : k * g ≤ i + g' := Nat.div_mul_le_self _ _
  have hk2 : i + g' < k * g + g := Nat.lt_div_mul_add hg
  have hk3 : i ≤ k * g + g' := by omega
  have hkm : k < m / g + 2 := by
    have h1 : k ≤ (m + g) / g := Nat.div_le_div_right (by omega)
    have h2 : (m + g) / g = m / g + 1 := Nat.add_div_right m hg
    omega
  refine ⟨min (k * g) m, Finset.mem_image.2 ⟨k, Finset.mem_range.2 hkm, rfl⟩, ?_⟩
  have e1 : ((k * g : ℕ) : ℝ) ≤ i + g' := by exact_mod_cast hk1
  have e3 : (i : ℝ) ≤ ((k * g : ℕ) : ℝ) + g' := by exact_mod_cast hk3
  rcases le_total (k * g) m with h | h
  · rw [min_eq_left h, abs_le]
    constructor <;> linarith
  · rw [min_eq_right h, abs_le]
    have e4 : (m : ℝ) ≤ ((k * g : ℕ) : ℝ) := by exact_mod_cast h
    have him : (i : ℝ) ≤ m := by exact_mod_cast hi
    constructor <;> linarith

theorem Lb_ge_one (t θ δ : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ) (htθ : t < θ) : 1 ≤ Lb t θ δ := by
  unfold Lb
  have h1 : Real.exp ((t - θ) * δ) < 1 := by
    have hneg : (t - θ) * δ < 0 := by nlinarith
    calc Real.exp ((t - θ) * δ) < Real.exp 0 := Real.exp_lt_exp.2 hneg
      _ = 1 := Real.exp_zero
  have h2 : 0 ≤ 1 - Real.exp (-(t * δ)) := by
    have : Real.exp (-(t * δ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    linarith
  have h3 : 1 ≤ Real.exp (t * δ) := Real.one_le_exp (by positivity)
  have : 0 ≤ (1 - Real.exp (-(t * δ))) / (1 - Real.exp ((t - θ) * δ)) :=
    div_nonneg h2 (by linarith)
  nlinarith

/-- The per-cell checks of round 2, on `p ∈ [pa, pb] ⊆ [0, 1/2]`. -/
structure CellOK2 (E1 d g' M η lnG pa pb lam tt al be : ℝ) : Prop where
  pa_nonneg : 0 ≤ pa
  pb_half : pb ≤ 1 / 2
  lam_nonneg : 0 ≤ lam
  t_pos : 0 < tt
  t_lt_al : tt < al
  t_lt_be : tt < be
  lamE : lam * E1 ≤ d / 2
  rate_a : Real.log (1 + pa * (Real.exp al - 1)) ≤ al * (pa + lam)
  rate_b : Real.log (1 + pa * (Real.exp al - 1)) +
      (pb - pa) * (Real.exp al - 1) / (1 + pa * (Real.exp al - 1)) ≤ al * (pb + lam)
  rate_c : Real.log (1 + (1 - pb) * (Real.exp be - 1)) ≤ be * ((1 - pb) + lam)
  rate_d : Real.log (1 + (1 - pb) * (Real.exp be - 1)) +
      ((1 - pa) - (1 - pb)) * (Real.exp be - 1) / (1 + (1 - pb) * (Real.exp be - 1)) ≤
        be * ((1 - pa) + lam)
  budget : ∀ p, pa ≤ p → p ≤ pb →
    lam * (E1 * M + g') + (binEntropy p +
      Real.log (Lb tt al (1 / 1000 / tt) + Lb tt be (1 / 1000 / tt) - 1) +
      (lnG + Real.log (15 / η)) / 16) / tt ≤ d / 2 * M

open Classical in
/-- **Round 2 numerics, assembled.** -/
theorem round2_bound (E1 d M η lnG : ℝ) (g' : ℕ) (hE1 : 0 < E1) (hd : 0 < d) (hη0 : 0 < η)
    (hη : η ≤ 1 / 100)
    {K : ℕ} (pa pb lam tt al be : Fin K → ℝ)
    (hcover : ∀ p : ℝ, 0 ≤ p → p ≤ 1 / 2 → ∃ i, pa i ≤ p ∧ p ≤ pb i)
    (hok : ∀ i, CellOK2 E1 d g' M η lnG (pa i) (pb i) (lam i) (tt i) (al i) (be i))
    {m n : ℕ} (hn : 16 ≤ n) (hmM : M ≤ m) (hm : 0 < m)
    (hG : Real.log ((grid m (2 * g' + 1)).card : ℝ) ≤ lnG) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyB2 σ E1 d).card : ℝ) ≤
      η * ((Fintype.card (Scramble m n) : ℕ) : ℝ) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hKpos : 0 < K := by
    obtain ⟨i, _⟩ := hcover 0 le_rfl (by norm_num)
    exact lt_of_le_of_lt (Nat.zero_le _) i.isLt
  -- choose a cell for every size: the cell of s/n, or of 1 - s/n
  have hc : ∀ s : ℕ, ∃ i : Fin K,
      ((s : ℝ) / n ≤ 1 / 2 → pa i ≤ (s : ℝ) / n ∧ (s : ℝ) / n ≤ pb i) ∧
      (1 / 2 < (s : ℝ) / n → s ≤ n → pa i ≤ 1 - (s : ℝ) / n ∧ 1 - (s : ℝ) / n ≤ pb i) := by
    intro s
    by_cases h : (s : ℝ) / n ≤ 1 / 2
    · obtain ⟨i, hi⟩ := hcover ((s : ℝ) / n) (by positivity) h
      exact ⟨i, fun _ => hi, fun h' => absurd h (not_le.2 h')⟩
    · push_neg at h
      by_cases hs : s ≤ n
      · have h1 : (s : ℝ) / n ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast hs
        obtain ⟨i, hi⟩ := hcover (1 - (s : ℝ) / n) (by linarith) (by linarith)
        exact ⟨i, fun h' => absurd h' (not_le.2 h), fun _ _ => hi⟩
      · exact ⟨⟨0, hKpos⟩, fun h' => absurd h' (not_le.2 h), fun _ h' => absurd h' hs⟩
  choose ci hci using hc
  set low : ℕ → Prop := fun s => (s : ℝ) / n ≤ 1 / 2
  set Lam : ℕ → ℝ := fun s => lam (ci s)
  set T : ℕ → ℝ := fun s => tt (ci s)
  set Al : ℕ → ℝ := fun s => if low s then al (ci s) else be (ci s)
  set Be : ℕ → ℝ := fun s => if low s then be (ci s) else al (ci s)
  set Dl : ℕ → ℝ := fun s => 1 / 1000 / tt (ci s)
  set Mc : ℕ → ℝ := fun s => Lb (T s) (Al s) (Dl s) + Lb (T s) (Be s) (Dl s) - 1
  set Gc : ℝ := ((grid m (2 * g' + 1)).card : ℝ)
  set X : ℕ → ℝ := fun s => (Real.log (n.choose s) + n * Real.log (Mc s) + Real.log Gc +
    Real.log ((n - 1) / η)) / T s
  have hT : ∀ s, 0 < T s := fun s => (hok (ci s)).t_pos
  have hDl : ∀ s, 0 < Dl s := fun s => by
    have := hT s; simp only [Dl, T] at this ⊢; positivity
  have hTA : ∀ s, T s < Al s := fun s => by
    simp only [T, Al]; split_ifs
    · exact (hok (ci s)).t_lt_al
    · exact (hok (ci s)).t_lt_be
  have hTB : ∀ s, T s < Be s := fun s => by
    simp only [T, Be]; split_ifs
    · exact (hok (ci s)).t_lt_be
    · exact (hok (ci s)).t_lt_al
  have hMc : ∀ s, 1 ≤ Mc s := fun s => by
    have h1 := Lb_ge_one (T s) (Al s) (Dl s) (hT s).le (hDl s) (hTA s)
    have h2 := Lb_ge_one (T s) (Be s) (Dl s) (hT s).le (hDl s) (hTB s)
    simp only [Mc]; linarith
  have hMcsym : ∀ s, Mc s = Lb (tt (ci s)) (al (ci s)) (Dl s) + Lb (tt (ci s)) (be (ci s)) (Dl s) - 1 := by
    intro s; simp only [Mc, T, Al, Be]; split_ifs <;> ring
  have hGc : 1 ≤ Gc := by
    have : 0 < (grid m (2 * g' + 1)).card := by
      rw [Finset.card_pos]; exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.succ_pos _))⟩
    simp only [Gc]; exact_mod_cast this
  have hfail := Round2Union.round2_fail (m := m) (n := n) hn0 E1 d hd hm (grid m (2 * g' + 1))
    (grid_le m _) g' (fun i _ hi => grid_cover m g' i hi) Lam T Al Be X Dl hDl
    (fun s => (hok (ci s)).lam_nonneg) (fun s => (hT s).le) hTA hTB
    (fun s hs1 hsn => by
      have hok' := hok (ci s)
      by_cases hl : low s
      · have hcell := (hci s).1 hl
        simp only [Al, if_pos hl]
        exact NumGlue.rate_of_tangent _ _ _ _ (le_trans (hT s).le hok'.t_lt_al.le) hok'.pa_nonneg
          hok'.rate_a hok'.rate_b _ hcell.1 hcell.2
      · have hcell := (hci s).2 (not_le.1 hl) hsn.le
        simp only [Al, if_neg hl]
        have hpb : (0 : ℝ) ≤ 1 - pb (ci s) := by linarith [hok'.pb_half]
        exact NumGlue.rate_of_tangent _ _ _ _ (le_trans (hT s).le hok'.t_lt_be.le) hpb
          hok'.rate_c hok'.rate_d _ (by linarith [hcell.2]) (by linarith [hcell.1]))
    (fun s hs1 hsn => by
      have hok' := hok (ci s)
      by_cases hl : low s
      · have hcell := (hci s).1 hl
        simp only [Be, if_pos hl]
        have hpb : (0 : ℝ) ≤ 1 - pb (ci s) := by linarith [hok'.pb_half]
        exact NumGlue.rate_of_tangent _ _ _ _ (le_trans (hT s).le hok'.t_lt_be.le) hpb
          hok'.rate_c hok'.rate_d _ (by linarith [hcell.2]) (by linarith [hcell.1])
      · have hcell := (hci s).2 (not_le.1 hl) hsn.le
        simp only [Be, if_neg hl]
        exact NumGlue.rate_of_tangent _ _ _ _ (le_trans (hT s).le hok'.t_lt_al.le) hok'.pa_nonneg
          hok'.rate_a hok'.rate_b _ hcell.1 hcell.2)
    (fun s hs1 hsn => by
      have hok' := hok (ci s)
      -- the cell point p' (p or 1 - p) and the entropy symmetry
      obtain ⟨p', hp'1, hp'2, hH⟩ : ∃ p', pa (ci s) ≤ p' ∧ p' ≤ pb (ci s) ∧
          binEntropy ((s : ℝ) / n) = binEntropy p' := by
        by_cases hl : low s
        · exact ⟨_, ((hci s).1 hl).1, ((hci s).1 hl).2, rfl⟩
        · have hcell := (hci s).2 (not_le.1 hl) hsn.le
          exact ⟨_, hcell.1, hcell.2, by rw [binEntropy_one_sub]⟩
      have hb := hok'.budget p' hp'1 hp'2
      rw [← hH, ← hMcsym s] at hb
      have hlc := NumGlue.log_choose_le n s hs1 hsn
      have hlu := NumGlue.log_union_le n hn η hη0 hη
      have hTs := hT s
      have hlogG0 : 0 ≤ Real.log Gc := Real.log_nonneg hGc
      have hlogGn : Real.log Gc ≤ n * (lnG / 16) := by
        have : (16 : ℝ) ≤ n := by exact_mod_cast hn
        have h1 : Real.log Gc ≤ lnG := hG
        nlinarith
      have hx : X s ≤ n * ((binEntropy ((s : ℝ) / n) + Real.log (Mc s) +
          (lnG + Real.log (15 / η)) / 16) / T s) := by
        simp only [X]
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hTs]
        have : Real.log ((n - 1) / η) ≤ n * (Real.log (15 / η) / 16) := by
          have := (div_le_iff₀ hnR).1 hlu; linarith
        nlinarith
      have hmR : M ≤ (m : ℝ) := hmM
      have hlE := hok'.lamE
      have hb' : Lam s * (E1 * m + g') + (binEntropy ((s : ℝ) / n) + Real.log (Mc s) +
          (lnG + Real.log (15 / η)) / 16) / T s ≤ d / 2 * m := by
        have : Lam s * E1 * (m - M) ≤ d / 2 * (m - M) :=
          mul_le_mul_of_nonneg_right (by simp only [Lam]; linarith) (by linarith)
        simp only [Lam, T] at hb this ⊢
        nlinarith
      calc Lam s * (E1 * m * n + n * g') + X s
          ≤ Lam s * (E1 * m * n + n * g') + n * ((binEntropy ((s : ℝ) / n) + Real.log (Mc s) +
              (lnG + Real.log (15 / η)) / 16) / T s) := by linarith
        _ = n * (Lam s * (E1 * m + g') + (binEntropy ((s : ℝ) / n) + Real.log (Mc s) +
              (lnG + Real.log (15 / η)) / 16) / T s) := by ring
        _ ≤ n * (d / 2 * m) := mul_le_mul_of_nonneg_left hb' hnR.le
        _ = d / 2 * (m * n) := by ring)
  refine hfail.trans ?_
  have hterm : ∀ s ∈ Finset.Ico 1 n, ((n.choose s : ℕ) : ℝ) * ((grid m (2 * g' + 1)).card : ℝ) *
      (Real.exp (-(T s * X s)) * ((Fintype.card (Scramble m n) : ℕ) : ℝ) *
        (Lb (T s) (Al s) (Dl s) + Lb (T s) (Be s) (Dl s) - 1) ^ n) =
      η / (n - 1) * ((Fintype.card (Scramble m n) : ℕ) : ℝ) := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hC : (0 : ℝ) < ((n.choose s : ℕ) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    have hn1 : (0 : ℝ) < n - 1 := by
      have : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      linarith
    have hq : (0 : ℝ) < (n - 1) / η := div_pos hn1 hη0
    have hMs : 0 < Mc s := lt_of_lt_of_le one_pos (hMc s)
    have hGs : 0 < Gc := lt_of_lt_of_le one_pos hGc
    have hTX : T s * X s = Real.log (((n.choose s : ℕ) : ℝ) * Mc s ^ n * Gc * ((n - 1) / η)) := by
      simp only [X]
      rw [Real.log_mul (by positivity) hq.ne', Real.log_mul (by positivity) hGs.ne',
        Real.log_mul hC.ne' (by positivity), Real.log_pow]
      field_simp [(hT s).ne']
    rw [hTX, Real.exp_neg, Real.exp_log (by positivity)]
    have hne : Mc s ≠ 0 := hMs.ne'
    have hne2 : Gc ≠ 0 := hGs.ne'
    simp only [Mc, Gc] at hne hne2 ⊢
    field_simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hn1]
  have : (0 : ℝ) < n - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    linarith
  field_simp
  exact le_rfl

end Round2Num
