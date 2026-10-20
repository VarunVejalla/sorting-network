import AKS.Sub800.Round1
import AKS.Sub800.NumGlue

/-! # Round 1: from per-cell checks to the failure bound for every `n ≥ 16`, `m ≥ M`

A cell `i` carries rationals `pa i ≤ pb i` and parameters `lam i`, `tt i`, `al i`. The checks
`CellOK1` are the ones generated per cell. Then for each size `s` of an `n`-column scramble we use
the cell containing `s/n`, `δ = (1/1000)/t`, and
`x_s = (log C(n,s) + n log Lb + log((n-1)/η))/t`, so each union term is exactly `η/(n-1)`. -/

open Finset BigOperators Chvatal Real

namespace Round1Num

open Round2Col

/-- The per-cell checks (proved numerically for the concrete cells). -/
structure CellOK1 (E1 M η pa pb lam tt al : ℝ) : Prop where
  pa_nonneg : 0 ≤ pa
  lam_nonneg : 0 ≤ lam
  t_pos : 0 < tt
  t_lt : tt < al
  lam_le : lam ≤ E1 / 2
  rate_a : Real.log (1 + pa * (Real.exp al - 1)) ≤ al * (pa + lam)
  rate_b : Real.log (1 + pa * (Real.exp al - 1)) +
      (pb - pa) * (Real.exp al - 1) / (1 + pa * (Real.exp al - 1)) ≤ al * (pb + lam)
  budget : ∀ p, pa ≤ p → p ≤ pb →
    lam * M + (binEntropy p + Real.log (Lb tt al (1 / 1000 / tt)) + Real.log (15 / η) / 16) / tt ≤
      E1 / 2 * M

theorem Lb_pos (t θ δ : ℝ) (ht : 0 < t) (hδ : 0 < δ) (htθ : t < θ) : 0 < Lb t θ δ := by
  unfold Lb
  have h1 : Real.exp ((t - θ) * δ) < 1 := by
    have hneg : (t - θ) * δ < 0 := by nlinarith
    calc Real.exp ((t - θ) * δ) < Real.exp 0 := Real.exp_lt_exp.2 hneg
      _ = 1 := Real.exp_zero
  have h2 : 0 ≤ 1 - Real.exp (-(t * δ)) := by
    have : Real.exp (-(t * δ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    linarith
  have : 0 < 1 - Real.exp ((t - θ) * δ) := by linarith
  positivity

open Classical in
/-- **Round 1 numerics, assembled.** -/
theorem round1_bound (E1 M η : ℝ) (hE1 : 0 < E1) (hη0 : 0 < η) (hη : η ≤ 1 / 100)
    {K : ℕ} (pa pb lam tt al : Fin K → ℝ)
    (hcover : ∀ p : ℝ, 0 ≤ p → p ≤ 1 → ∃ i, pa i ≤ p ∧ p ≤ pb i)
    (hok : ∀ i, CellOK1 E1 M η (pa i) (pb i) (lam i) (tt i) (al i))
    {m n : ℕ} (hn : 16 ≤ n) (hmM : M ≤ m) (hm : 0 < m) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyBOnPipeline σ E1).card : ℝ) ≤
      η * ((Fintype.card (Scramble m n) : ℕ) : ℝ) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  -- the cell of each size
  have hc : ∀ s : ℕ, ∃ i, pa i ≤ (s : ℝ) / n ∧ (s : ℝ) / n ≤ pb i ∨ ¬ (s ≤ n) := by
    intro s
    by_cases hs : s ≤ n
    · obtain ⟨i, h⟩ := hcover ((s : ℝ) / n) (by positivity) (by
        rw [div_le_one hnR]; exact_mod_cast hs)
      exact ⟨i, Or.inl h⟩
    · by_cases hK : 0 < K
      · exact ⟨⟨0, hK⟩, Or.inr hs⟩
      · -- no cells at all: impossible, since 0 must be covered
        exfalso
        obtain ⟨i, _⟩ := hcover 0 le_rfl zero_le_one
        exact hK (lt_of_le_of_lt (Nat.zero_le _) i.isLt)
  choose ci hci using hc
  set Lam : ℕ → ℝ := fun s => lam (ci s)
  set T : ℕ → ℝ := fun s => tt (ci s)
  set Al : ℕ → ℝ := fun s => al (ci s)
  set Dl : ℕ → ℝ := fun s => 1 / 1000 / tt (ci s)
  set LB : ℕ → ℝ := fun s => Lb (T s) (Al s) (Dl s)
  set X : ℕ → ℝ := fun s => (Real.log (n.choose s) + n * Real.log (LB s) +
    Real.log ((n - 1) / η)) / T s
  have hT : ∀ s, 0 < T s := fun s => (hok (ci s)).t_pos
  have hDl : ∀ s, 0 < Dl s := fun s => by
    have := hT s; simp only [Dl, T] at this ⊢; positivity
  have hLB : ∀ s, 0 < LB s := fun s => Lb_pos _ _ _ (hT s) (hDl s) (hok (ci s)).t_lt
  have hfail := Round1.round1_fail (m := m) (n := n) hn0 hm E1 hE1 Lam T Al X Dl hDl
    (fun s => (hok (ci s)).lam_nonneg) (fun s => (hT s).le) (fun s => (hok (ci s)).t_lt)
    (fun s hs1 hsn => by
      have hcell := (hci s).resolve_right (by omega)
      have ok := hok (ci s)
      exact NumGlue.rate_of_tangent (pa (ci s)) (pb (ci s)) (lam (ci s)) (al (ci s))
        (le_trans (hT s).le ok.t_lt.le) ok.pa_nonneg ok.rate_a ok.rate_b _ hcell.1 hcell.2)
    (fun s hs1 hsn => by
      have hcell := (hci s).resolve_right (by omega)
      have ok := hok (ci s)
      have hb := ok.budget _ hcell.1 hcell.2
      have hlc := NumGlue.log_choose_le n s hs1 hsn
      have hlu := NumGlue.log_union_le n hn η hη0 hη
      have hTs := hT s
      have hmR : M ≤ (m : ℝ) := hmM
      -- X s / n ≤ (H + log Lb + log(15/η)/16) / t
      have hx : X s ≤ n * ((binEntropy ((s : ℝ) / n) + Real.log (LB s) + Real.log (15 / η) / 16) / T s) := by
        simp only [X]
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hTs]
        have : Real.log ((n - 1) / η) ≤ n * (Real.log (15 / η) / 16) := by
          have := (div_le_iff₀ hnR).1 hlu; linarith
        nlinarith
      have hlam := ok.lam_le
      have hb' : Lam s * m + (binEntropy ((s : ℝ) / n) + Real.log (LB s) + Real.log (15 / η) / 16) / T s ≤
          E1 / 2 * m := by
        have : (E1 / 2 - Lam s) * M ≤ (E1 / 2 - Lam s) * m :=
          mul_le_mul_of_nonneg_left hmR (by simp only [Lam]; linarith)
        simp only [Lam, T, LB, Al, Dl] at hb this ⊢
        linarith
      calc (n : ℝ) * Lam s * m + X s
          ≤ n * Lam s * m + n * ((binEntropy ((s : ℝ) / n) + Real.log (LB s) + Real.log (15 / η) / 16) / T s) := by
            linarith
        _ = n * (Lam s * m + (binEntropy ((s : ℝ) / n) + Real.log (LB s) + Real.log (15 / η) / 16) / T s) := by
            ring
        _ ≤ n * (E1 / 2 * m) := mul_le_mul_of_nonneg_left hb' hnR.le
        _ = E1 / 2 * (m * n) := by ring)
  refine hfail.trans ?_
  -- each union term equals η/(n-1) · #Scramble
  have hterm : ∀ s ∈ Finset.Ico 1 n, ((n.choose s : ℕ) : ℝ) *
      (Real.exp (-(T s * X s)) * (((Fintype.card (Scramble m n) : ℕ) : ℝ) * Lb (T s) (Al s) (Dl s) ^ n)) =
      η / (n - 1) * ((Fintype.card (Scramble m n) : ℕ) : ℝ) := by
    intro s hs
    rw [Finset.mem_Ico] at hs
    have hC : (0 : ℝ) < ((n.choose s : ℕ) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
    have hn1 : (0 : ℝ) < n - 1 := by
      have : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
      linarith
    have hLBs := hLB s
    have hq : (0 : ℝ) < (n - 1) / η := div_pos hn1 hη0
    have hTX : T s * X s = Real.log (((n.choose s : ℕ) : ℝ) * LB s ^ n * ((n - 1) / η)) := by
      simp only [X]
      rw [Real.log_mul (by positivity) hq.ne', Real.log_mul hC.ne' (by positivity), Real.log_pow]
      field_simp [(hT s).ne']
    rw [hTX, Real.exp_neg, Real.exp_log (by positivity)]
    have hne : Lb (T s) (Al s) (Dl s) ≠ 0 := hLBs.ne'
    simp only [LB]
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

end Round1Num
