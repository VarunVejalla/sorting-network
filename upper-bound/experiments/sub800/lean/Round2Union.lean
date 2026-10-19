import Round2Fixed
import AKS.Chvatal.Bulk2Count

/-! # Round 2 of the walk bound: union bound and the package's Property B2

`HasCombinatorialPropertyB2 σ E1 d` holds unless, for some size `1 ≤ s ≤ n-1`, output set
`S` of size `s` and grid row `b ∈ G`, the dual sum `Σ_j Y_j^{S,b}(λ_s)` reaches `x_s`.
The numerics enter only through the per-size hypotheses `hx` and `hbudget`. -/

open Finset BigOperators Chvatal

namespace Round2Union

variable {m n : ℕ}

theorem card_rows_top (h : ℕ) (hh : h ≤ m) :
  (Finset.univ.filter fun r : Fin m => m - h ≤ r.val).card = h := by
  trans (Finset.Ico (m - h) m).card
  · refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      exact Finset.mem_Ico.2 ⟨hr, r.isLt⟩
    · intro a _ b _ hab; exact Fin.ext hab
    · intro x hx
      rw [Finset.mem_Ico] at hx
      refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx.1
  · rw [Nat.card_Ico]; omega

theorem onesAboveBottom_eq_zero_of_univ (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : ℕ)
    (hmass : totalColumnOnes c = n * i)
    (hS : Round2.Sstar c σ i = Finset.univ) : (onesAboveBottom c σ i : ℝ) = 0 := by
  rw [Round2.onesAboveBottom_eq_sum, hS, Finset.sum_sub_distrib, ← Nat.cast_sum,
    Round2.sum_scrambledColSum_eq]
  -- the walks over all columns count every one exactly once
  have hall : ∑ j : Fin n, Round2.walkN σ Finset.univ j (c j).val = totalColumnOnes c := by
    simp only [Round2.walkN, Finset.mem_univ, and_true, totalColumnOnes]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact card_rows_top (c j).val (Nat.lt_succ_iff.1 (c j).isLt)
  rw [hall, hmass, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- **Round 2, deterministic step from the good event to Property B2.** -/
theorem B2_of_good (σ : Scramble m n) (hn : 0 < n) (E1 d : ℝ) (hd : 0 < d) (hmn : 0 < m)
    (G : Finset ℕ) (hGm : ∀ b ∈ G, b ≤ m) (g' : ℝ) (hcover : ∀ i, 1 ≤ i → i ≤ m → ∃ b ∈ G, |(i : ℝ) - b| ≤ g')
    (lam x : ℕ → ℝ) (hlam : ∀ s, 0 ≤ lam s)
    (hbudget : ∀ s, 1 ≤ s → s < n → lam s * (E1 * m * n + n * g') + x s ≤ (d / 2) * (m * n))
    (hgood : ∀ s, 1 ≤ s → s < n → ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, ∀ b ∈ G,
      ∑ j : Fin n, Round2.Ydual σ S j b (lam s) < x s) :
    HasCombinatorialPropertyB2 σ E1 d := by
  classical
  intro c i hmass hi1 him hexc
  set S := Round2.Sstar c σ i
  have hmnpos : (0 : ℝ) < (d / 2) * (m * n) := by
    have : (0 : ℝ) < m := by exact_mod_cast hmn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  by_cases hs0 : S.card = 0
  · rw [Finset.card_eq_zero] at hs0
    rw [Round2.onesAboveBottom_eq_sum]
    show ∑ T ∈ S, _ < _
    rw [hs0, Finset.sum_empty]; exact hmnpos
  by_cases hsn : S.card = n
  · have hS : S = Finset.univ := by
      apply Finset.eq_univ_of_card; rw [hsn, Fintype.card_fin]
    rw [onesAboveBottom_eq_zero_of_univ c σ i hmass hS]; exact hmnpos
  have hs1 : 1 ≤ S.card := by omega
  have hsn' : S.card < n := lt_of_le_of_ne (by simpa using Finset.card_le_univ S) hsn
  obtain ⟨b, hbG, hib⟩ := hcover i hi1 him
  have hb := hGm b hbG
  have hdual := Round2.onesAboveBottom_le_dual c σ i hn hmass b hb (lam S.card)
  have hdisp := Round2.sum_abs_base_le c i b hmass
  have hY := hgood S.card hs1 hsn' S (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩) b hbG
  have hbud := hbudget S.card hs1 hsn'
  have hl := hlam S.card
  have hnn : (0 : ℝ) ≤ n := by positivity
  calc (onesAboveBottom c σ i : ℝ)
      ≤ lam S.card * ∑ j : Fin n, |((c j).val : ℝ) - b| +
          ∑ j : Fin n, Round2.Ydual σ S j b (lam S.card) := hdual
    _ ≤ lam S.card * (E1 * m * n + n * g') + ∑ j : Fin n, Round2.Ydual σ S j b (lam S.card) := by
        gcongr
        calc ∑ j : Fin n, |((c j).val : ℝ) - b| ≤ 2 * (excessAbove c i : ℝ) + n * |(i : ℝ) - b| :=
              hdisp
          _ ≤ E1 * m * n + n * g' := by
              have h2 : 2 * (excessAbove c i : ℝ) ≤ E1 * m * n := by nlinarith
              have h3 : (n : ℝ) * |(i : ℝ) - b| ≤ n * g' := mul_le_mul_of_nonneg_left hib hnn
              linarith
    _ < lam S.card * (E1 * m * n + n * g') + x S.card := by linarith
    _ ≤ (d / 2) * (m * n) := hbud

open Classical in
/-- **Round 2 failure count.** -/
theorem round2_fail (hn : 0 < n) (E1 d : ℝ) (hd : 0 < d) (hmn : 0 < m)
    (G : Finset ℕ) (hGm : ∀ b ∈ G, b ≤ m) (g' : ℝ)
    (hcover : ∀ i, 1 ≤ i → i ≤ m → ∃ b ∈ G, |(i : ℝ) - b| ≤ g')
    (lam t α β x : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (hlam : ∀ s, 0 ≤ lam s)
    (ht : ∀ s, 0 ≤ t s) (htα : ∀ s, t s < α s) (htβ : ∀ s, t s < β s)
    (hα : ∀ s, 1 ≤ s → s < n → 1 - (s : ℝ) / n + (s : ℝ) / n * Real.exp (α s) ≤
      Real.exp (α s * ((s : ℝ) / n + lam s)))
    (hβ : ∀ s, 1 ≤ s → s < n → 1 - (1 - (s : ℝ) / n) + (1 - (s : ℝ) / n) * Real.exp (β s) ≤
      Real.exp (β s * ((1 - (s : ℝ) / n) + lam s)))
    (hbudget : ∀ s, 1 ≤ s → s < n → lam s * (E1 * m * n + n * g') + x s ≤ (d / 2) * (m * n)) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyB2 σ E1 d).card : ℝ) ≤
      ∑ s ∈ Finset.Ico 1 n, ((n.choose s : ℕ) : ℝ) * (G.card : ℝ) *
        (Real.exp (-(t s * x s)) * ((Fintype.card (Scramble m n) : ℕ) : ℝ) *
          (Round2Col.Lb (t s) (α s) δ + Round2Col.Lb (t s) (β s) δ - 1) ^ n) := by
  classical
  -- the bad set is covered by the union of the fixed (s, S, b) events
  let ev : ℕ → Finset (Fin n) → ℕ → Finset (Scramble m n) := fun s S b =>
    Finset.univ.filter fun σ => x s ≤ ∑ j : Fin n, Round2.Ydual σ S j b (lam s)
  have hsub : (Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyB2 σ E1 d) ⊆
      (Finset.Ico 1 n).biUnion fun s =>
        ((Finset.univ : Finset (Fin n)).powersetCard s).biUnion fun S => G.biUnion fun b => ev s S b := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    by_contra hnot
    apply hσ.2
    refine B2_of_good σ hn E1 d hd hmn G hGm g' hcover lam x hlam hbudget ?_
    intro s hs1 hsn S hS b hb
    by_contra hge
    push_neg at hge
    apply hnot
    simp only [Finset.mem_biUnion, Finset.mem_Ico]
    exact ⟨s, ⟨hs1, hsn⟩, S, hS, b, hb, by simp [ev, hge]⟩
  have hnat : (Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyB2 σ E1 d).card ≤
      ∑ s ∈ Finset.Ico 1 n, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
        ∑ b ∈ G, (ev s S b).card := by
    refine (Finset.card_le_card hsub).trans ?_
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun s _ => ?_)
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun S _ => ?_)
    exact Finset.card_biUnion_le
  set K : ℕ → ℝ := fun s => Real.exp (-(t s * x s)) * ((Fintype.card (Scramble m n) : ℕ) : ℝ) *
    (Round2Col.Lb (t s) (α s) δ + Round2Col.Lb (t s) (β s) δ - 1) ^ n
  calc ((Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyB2 σ E1 d).card : ℝ)
      ≤ ∑ s ∈ Finset.Ico 1 n, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
          ∑ b ∈ G, ((ev s S b).card : ℝ) := by exact_mod_cast hnat
    _ ≤ ∑ s ∈ Finset.Ico 1 n, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, ∑ b ∈ G, K s := by
        refine Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun S hS => Finset.sum_le_sum fun b hb => ?_
        rw [Finset.mem_Ico] at hs
        have hSc := (Finset.mem_powersetCard.1 hS).2
        exact Round2Fixed.fixed_fail S b (hGm b hb) hn (lam s) (t s) (α s) (β s) δ (x s) (ht s) hδ
          (htα s) (htβ s) (by rw [hSc]; exact hα s hs.1 hs.2) (by rw [hSc]; exact hβ s hs.1 hs.2)
    _ = ∑ s ∈ Finset.Ico 1 n, ((n.choose s : ℕ) : ℝ) * (G.card : ℝ) * K s := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring

end Round2Union
