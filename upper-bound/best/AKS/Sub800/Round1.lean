import AKS.Sub800.Round2Union

/-! # Round 1 of the walk bound, by the same Ville / negative-association route

The package's round-1 predicate is `HasCombinatorialPropertyBOnPipeline σ E1`: for every state of
mass at most `n i`, the excess above `i` after one scramble is below `(E1/2) m n`. With base row
`b = 0` the dual walk has no backward part, and for a drift `λ` with
`1 - p + p e^α ≤ e^{α(p+λ)}`,

  `excess ≤ n λ m + Σ_j Y_j^{S,0}(λ)`,   `E e^{t Y_j} ≤ Lb t α δ`. -/

open Finset BigOperators Chvatal

namespace Round1

variable {m n : ℕ}

open Round2Col

theorem Yminus_zero (p lam : ℝ) (j : Fin n) (ζ : Fin m → Finset (Fin n)) :
    Yminus p lam j 0 ζ = 0 := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro h _
    simp only [Ville.prefixSum, Dbwd]
    apply le_of_eq
    refine Finset.sum_eq_zero fun r _ => ?_
    have : ¬ m - 0 ≤ r.val := by have := r.isLt; omega
    simp [this]
  · exact Yminus_nonneg p lam j 0 ζ

/-- One column, base row 0. -/
theorem column_mgf0 (s : ℕ) (hn : 0 < n) (j : Fin n) (lam t α δ : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ)
    (htα : t < α)
    (hα : 1 - (s : ℝ) / n + (s : ℝ) / n * Real.exp α ≤ Real.exp (α * ((s : ℝ) / n + lam))) :
    ∑ ζ ∈ Zs m 0 s n, Real.exp (t * max (Yplus ((s : ℝ) / n) lam j 0 ζ)
        (Yminus ((s : ℝ) / n) lam j 0 ζ)) ≤ ((Zs m 0 s n).card : ℝ) * Lb t α δ := by
  have hα0 : 0 ≤ α := by linarith
  simp_rw [Yminus_zero, max_eq_left (Yplus_nonneg _ _ _ _ _)]
  exact mgf_of_tail (Zs m 0 s n) (Yplus ((s : ℝ) / n) lam j 0)
    (fun ζ _ => Yplus_nonneg _ _ _ _ ζ) t α δ ht hδ htα (tail_plus 0 s (Nat.zero_le m) hn j lam α hα0 hα)

theorem fixed_fail0 (S : Finset (Fin n)) (hn : 0 < n) (lam t α δ x : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ)
    (htα : t < α)
    (hα : 1 - (S.card : ℝ) / n + (S.card : ℝ) / n * Real.exp α ≤
      Real.exp (α * ((S.card : ℝ) / n + lam))) :
    ((Finset.univ.filter fun σ : Scramble m n => x ≤ ∑ j : Fin n, Round2.Ydual σ S j 0 lam).card : ℝ) ≤
      Real.exp (-(t * x)) * (((Fintype.card (Scramble m n) : ℕ) : ℝ) * Lb t α δ ^ n) :=
  Round2Fixed.fail_of_mgf S 0 lam t x _ ht
    (Round2Fixed.fixed_mgf_core S 0 (Nat.zero_le m) lam t (Lb t α δ) ht fun j =>
      column_mgf0 S.card hn j lam t α δ ht hδ htα hα)

theorem walkW_zero (σ : Scramble m n) (S : Finset (Fin n)) (j : Fin n) : Round2.walkW σ S j 0 = 0 := by
  classical
  simp only [Round2.walkW, Round2.walkN, Nat.cast_zero, mul_zero, sub_zero, Nat.sub_zero]
  have : (Finset.univ.filter fun r : Fin m => m ≤ r.val ∧ σ r j ∈ S) = ∅ := by
    ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro h; have := r.isLt; omega
  rw [this]; simp

/-- Deterministic step, mass at most `n i`. -/
theorem onesAboveBottom_le_round1 (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : ℕ)
    (hn : 0 < n) (hmass : totalColumnOnes c ≤ n * i) (lam : ℝ) (hlam : 0 ≤ lam) :
    (onesAboveBottom c σ i : ℝ) ≤
      n * lam * m + ∑ j : Fin n, Round2.Ydual σ (Round2.Sstar c σ i) j 0 lam := by
  classical
  set S := Round2.Sstar c σ i
  have hS : (S.card : ℝ) ≤ n := by exact_mod_cast (by simpa using Finset.card_le_univ S)
  rw [Round2.onesAboveBottom_eq_sum, Finset.sum_sub_distrib, ← Nat.cast_sum,
    Round2.sum_scrambledColSum_eq, Finset.sum_const, nsmul_eq_mul]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (∑ j : Fin n, ((c j).val : ℝ)) ≤ n * i := by
    have := (Nat.cast_le (α := ℝ)).2 hmass
    simp only [totalColumnOnes] at this
    push_cast at this
    exact this
  -- Σ_j N_j(c_j) - #S i ≤ Σ_j W_j(c_j)
  have hstep : (∑ j : Fin n, (Round2.walkN σ S j (c j).val : ℝ)) - (S.card : ℝ) * i ≤
      ∑ j : Fin n, Round2.walkW σ S j (c j).val := by
    simp only [Round2.walkW, Finset.sum_sub_distrib]
    have : (∑ j : Fin n, (S.card : ℝ) / n * (c j).val) ≤ (S.card : ℝ) * i := by
      rw [← Finset.mul_sum]
      calc (S.card : ℝ) / n * ∑ j : Fin n, ((c j).val : ℝ) ≤ (S.card : ℝ) / n * (n * i) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = (S.card : ℝ) * i := by field_simp
    push_cast
    linarith
  have hcol : ∀ j : Fin n, Round2.walkW σ S j (c j).val ≤ lam * m + Round2.Ydual σ S j 0 lam := by
    intro j
    have := Round2.walk_le_dual σ S j 0 lam 0 (by simp) (c j).val (Nat.lt_succ_iff.1 (c j).isLt)
    rw [walkW_zero, sub_zero] at this
    have hc : ((c j).val : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.1 (c j).isLt
    have habs : |((c j).val : ℝ) - 0| = (c j).val := by simp
    rw [habs] at this
    nlinarith
  push_cast
  calc (∑ j : Fin n, (Round2.walkN σ S j (c j).val : ℝ)) - (S.card : ℝ) * i
      ≤ ∑ j : Fin n, Round2.walkW σ S j (c j).val := hstep
    _ ≤ ∑ j : Fin n, (lam * m + Round2.Ydual σ S j 0 lam) := Finset.sum_le_sum fun j _ => hcol j
    _ = n * lam * m + ∑ j : Fin n, Round2.Ydual σ S j 0 lam := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; ring

open Classical in
/-- **Round 1 failure count.** -/
theorem round1_fail (hn : 0 < n) (hmn : 0 < m) (E1 : ℝ) (hE1 : 0 < E1)
    (lam t α x : ℕ → ℝ) (δ : ℕ → ℝ) (hδ : ∀ s, 0 < δ s) (hlam : ∀ s, 0 ≤ lam s)
    (ht : ∀ s, 0 ≤ t s) (htα : ∀ s, t s < α s)
    (hα : ∀ s, 1 ≤ s → s < n → 1 - (s : ℝ) / n + (s : ℝ) / n * Real.exp (α s) ≤
      Real.exp (α s * ((s : ℝ) / n + lam s)))
    (hbudget : ∀ s, 1 ≤ s → s < n → n * lam s * m + x s ≤ (E1 / 2) * (m * n)) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyBOnPipeline σ E1).card : ℝ) ≤
      ∑ s ∈ Finset.Ico 1 n, ((n.choose s : ℕ) : ℝ) *
        (Real.exp (-(t s * x s)) * (((Fintype.card (Scramble m n) : ℕ) : ℝ) * Lb (t s) (α s) (δ s) ^ n)) := by
  classical
  let ev : ℕ → Finset (Fin n) → Finset (Scramble m n) := fun s S =>
    Finset.univ.filter fun σ => x s ≤ ∑ j : Fin n, Round2.Ydual σ S j 0 (lam s)
  have hpos : (0 : ℝ) < (E1 / 2) * (m * n) := by
    have : (0 : ℝ) < m := by exact_mod_cast hmn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hsub : (Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyBOnPipeline σ E1) ⊆
      (Finset.Ico 1 n).biUnion fun s =>
        ((Finset.univ : Finset (Fin n)).powersetCard s).biUnion fun S => ev s S := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    by_contra hnot
    apply hσ.2
    intro c i hmass hi1 him
    set S := Round2.Sstar c σ i
    by_cases hs0 : S.card = 0
    · rw [Finset.card_eq_zero] at hs0
      rw [Round2.onesAboveBottom_eq_sum]
      show ∑ T ∈ S, _ < _
      rw [hs0, Finset.sum_empty]; exact hpos
    by_cases hsn : S.card = n
    · have hS : S = Finset.univ := by
        apply Finset.eq_univ_of_card; rw [hsn, Fintype.card_fin]
      have hle := onesAboveBottom_le_round1 c σ i hn hmass 0 le_rfl
      -- with S = univ the excess is total - n i ≤ 0
      have h0 : (onesAboveBottom c σ i : ℝ) ≤ 0 := by
        rw [Round2.onesAboveBottom_eq_sum]
        show ∑ T ∈ S, _ ≤ _
        rw [hS, Finset.sum_sub_distrib, ← Nat.cast_sum, Round2.sum_scrambledColSum_eq]
        have hall : ∑ j : Fin n, Round2.walkN σ Finset.univ j (c j).val = totalColumnOnes c := by
          simp only [Round2.walkN, Finset.mem_univ, and_true, totalColumnOnes]
          exact Finset.sum_congr rfl fun j _ =>
            Round2Union.card_rows_top (c j).val (Nat.lt_succ_iff.1 (c j).isLt)
        rw [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have := (Nat.cast_le (α := ℝ)).2 hmass
        push_cast at this
        linarith
      linarith
    have hs1 : 1 ≤ S.card := by omega
    have hsn' : S.card < n := lt_of_le_of_ne (by simpa using Finset.card_le_univ S) hsn
    have hY : ∑ j : Fin n, Round2.Ydual σ S j 0 (lam S.card) < x S.card := by
      by_contra hge
      push_neg at hge
      apply hnot
      simp only [Finset.mem_biUnion, Finset.mem_Ico]
      exact ⟨S.card, ⟨hs1, hsn'⟩, S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩,
        by simp [ev, hge]⟩
    have hle := onesAboveBottom_le_round1 c σ i hn hmass (lam S.card) (hlam S.card)
    have hb := hbudget S.card hs1 hsn'
    linarith
  have hnat : (Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyBOnPipeline σ E1).card ≤
      ∑ s ∈ Finset.Ico 1 n, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s, (ev s S).card := by
    refine (Finset.card_le_card hsub).trans ?_
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun s _ => ?_)
    exact Finset.card_biUnion_le
  calc ((Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyBOnPipeline σ E1).card : ℝ)
      ≤ ∑ s ∈ Finset.Ico 1 n, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
          ((ev s S).card : ℝ) := by exact_mod_cast hnat
    _ ≤ ∑ s ∈ Finset.Ico 1 n, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
          Real.exp (-(t s * x s)) * (((Fintype.card (Scramble m n) : ℕ) : ℝ) * Lb (t s) (α s) (δ s) ^ n) := by
        refine Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun S hS => ?_
        rw [Finset.mem_Ico] at hs
        have hSc := (Finset.mem_powersetCard.1 hS).2
        exact fixed_fail0 S hn (lam s) (t s) (α s) (δ s) (x s) (ht s) (hδ s) (htα s)
          (by rw [hSc]; exact hα s hs.1 hs.2)
    _ = _ := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

end Round1
