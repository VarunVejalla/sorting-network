module

public import AKS.Chvatal.Lemma62Tail
public import AKS.Chvatal.Lemma62TopsCount
public import AKS.Chvatal.Lemma62TopsClosed
public import AKS.Chvatal.Lemma62Numerics

/-! # Chvátal Lemma 6.2: the per-`E` failure bound `fail_prob_at_E`

`badSetF f j` is the set of scrambles on which some `c` with `totalColumnOnes c = j` and some column
set `S` realise `fringeColumnEventBad`; `badSetF_card_le` is a union bound over the tops of `c`
(the fringe count only depends on the top), each top being represented by one matrix.
`fail_prob_at_E` assembles it with the per-matrix tail sum
(`scramble_tail_union_top`, `pbound_le_gfun`), the two-sided geometric sum (`gfun_sum_le_G1`), the
closed form for the number of tops and the numeric bound `x ≤ 3/10`. -/

@[expose] public section

namespace Chvatal

/-- Failure set: some monotone `c` with exactly `j` ones and some `S` realise the fringe event. -/
noncomputable def badSetF {m n : Nat} (f j : Nat) :
    Finset (Scramble m n) := by
  classical
  exact Finset.univ.filter fun σ =>
    ∃ c : MonotoneColumnSums m n, totalColumnOnes c = j ∧
      ∃ S : Finset (Fin n), fringeColumnEventBad f c σ j S

/-- The fringe count depends only on the tops `(c col) - f/2`. -/
theorem event_depends_only_on_top {m n f : Nat}
    (c c' : MonotoneColumnSums m n)
    (htop : ∀ col, (c col).val - f / 2 = (c' col).val - f / 2)
    (σ : Scramble m n) (S : Finset (Fin n)) :
    onesAboveHalfFringe f c σ S = onesAboveHalfFringe f c' σ S := by
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r.val < m - f / 2 := by simpa [topRows] using hr
  have hrow : monotoneRowOnes c r = monotoneRowOnes c' r := by
    ext col
    simp only [monotoneRowOnes, Finset.mem_filter, Finset.mem_univ, true_and]
    have := htop col
    omega
  unfold rowHit
  rw [hrow]

/-- The top of a monotone matrix as a function `Fin n → ℕ`. -/
def topOf {m n : Nat} (h : Nat) (c : MonotoneColumnSums m n) : Fin n → ℕ :=
  fun col => (c col).val - h

/-- `|badSetF| ≤ |tops| · B · |Scramble|`, given the per-matrix tail-sum bound `B` for matrices with
exactly `j` ones (and `0 < j`, `0 ≤ B`). -/
theorem badSetF_card_le {m n f : Nat}
    (j : Nat) (hj : 0 < j) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ c : MonotoneColumnSums m n, totalColumnOnes c = j →
      ∑ s ∈ Finset.Icc 1 n,
        ((tailBadSet c (topRows m (f / 2)) s ((f / 2 : ℝ) * s + eps * j)).card : ℝ) ≤
          B * (Fintype.card (Scramble m n) : ℝ)) :
    ((badSetF (m := m) (n := n) f j).card : ℝ) ≤
      ((tops (f / 2) n j).card : ℝ) * B * (Fintype.card (Scramble m n) : ℝ) := by
  classical
  let P : (Fin n → ℕ) → Prop := fun t =>
    ∃ c : MonotoneColumnSums m n, totalColumnOnes c = j ∧ topOf (f / 2) c = t
  let rep : (Fin n → ℕ) → MonotoneColumnSums m n := fun t =>
    if h : P t then Classical.choose h else fun _ => 0
  have hrep : ∀ t, P t → totalColumnOnes (rep t) = j ∧ topOf (f / 2) (rep t) = t := fun t ht => by
    simp only [rep, dif_pos ht]
    exact Classical.choose_spec ht
  let I : Finset (Fin n → ℕ) := (tops (f / 2) n j).filter P
  let U : (Fin n → ℕ) → ℕ → Finset (Scramble m n) := fun t s =>
    tailBadSet (rep t) (topRows m (f / 2)) s ((f / 2 : ℝ) * s + eps * j)
  have hsub : badSetF f j ⊆ I.biUnion fun t => (Finset.Icc 1 n).biUnion (U t) := by
    intro σ hσ
    simp only [badSetF, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨c, hc, S, hS⟩ := hσ
    have hPt : P (topOf (f / 2) c) := ⟨c, hc, rfl⟩
    obtain ⟨-, hrt⟩ := hrep _ hPt
    have hS' : fringeColumnEventBad f (rep (topOf (f / 2) c)) σ j S := by
      unfold fringeColumnEventBad at hS ⊢
      rwa [event_depends_only_on_top _ c
        (fun col => by simpa [topOf] using congrFun hrt col) σ S]
    have h' : (f / 2 : ℝ) * S.card + eps * j ≤
        (onesInRows (rep (topOf (f / 2) c)) σ (topRows m (f / 2)) S : ℝ) := hS'
    have hne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      have := mul_pos eps_pos (show (0 : ℝ) < j by exact_mod_cast hj)
      simp [onesInRows] at h'
      linarith
    refine Finset.mem_biUnion.mpr ⟨_, Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨fun col => (c col).val, mem_sset.mpr hc.le, rfl⟩, hPt⟩,
      Finset.mem_biUnion.mpr ⟨S.card, ?_, ?_⟩⟩
    · rw [Finset.mem_Icc]
      exact ⟨hne.card_pos, by simpa using Finset.card_le_univ S⟩
    · simp only [U, tailBadSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩, h'⟩
  have h2 : ((badSetF (m := m) (n := n) f j).card : ℝ) ≤
      ∑ t ∈ I, ∑ s ∈ Finset.Icc 1 n, ((U t s).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans
      ((Finset.card_biUnion_le).trans (Finset.sum_le_sum fun t _ => Finset.card_biUnion_le))
  have hN : (0 : ℝ) ≤ B * (Fintype.card (Scramble m n) : ℝ) := by positivity
  calc ((badSetF f j).card : ℝ)
      ≤ ∑ t ∈ I, B * (Fintype.card (Scramble m n) : ℝ) :=
        h2.trans (Finset.sum_le_sum fun t ht => hB (rep t) (hrep t (Finset.mem_filter.mp ht).2).1)
    _ = (I.card : ℝ) * (B * (Fintype.card (Scramble m n) : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((tops (f / 2) n j).card : ℝ) * (B * (Fintype.card (Scramble m n) : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) hN
    _ = _ := by ring

lemma const_bound :
    90 / 89 * ((1 + Real.exp (-5)) / (1 - Real.exp (-5))) ≤ (1.025 : ℝ) := by
  have h : (148.41 : ℝ) ≤ Real.exp 5 := by
    have h2 : (2.7182818283 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 5
    rw [show Real.exp 5 = Real.exp 1 ^ 5 by rw [← Real.exp_nat_mul]; norm_num]
    linarith [show (148.41 : ℝ) ≤ 2.7182818283 ^ 5 by norm_num]
  rw [Real.exp_neg 5]
  set x := Real.exp 5
  have hx1 : x - 1 ≠ 0 := by linarith
  have e : (1 + x⁻¹) / (1 - x⁻¹) = 1 + 2 / (x - 1) := by
    have : x ≠ 0 := by linarith
    field_simp
    ring
  rw [e]
  have h2 : 2 / (x - 1) ≤ 2 / 147.41 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  nlinarith [show 90 / 89 * (1 + 2 / 147.41) ≤ (1.025 : ℝ) by norm_num]

/-- Per-matrix tail sum. -/
theorem tail_sum_le {m n f : ℕ} (j : ℕ) (P : Lemma62Params n (f : ℝ) (j : ℝ))
    (c : MonotoneColumnSums m n) (hc : totalColumnOnes c = j) :
    ∑ s ∈ Finset.Icc 1 n,
      ((tailBadSet c (topRows m (f / 2)) s ((f / 2 : ℝ) * s + eps * j)).card : ℝ) ≤
        (∑ s ∈ Finset.Icc 1 n, pbound n (f : ℝ) j s) * (Fintype.card (Scramble m n) : ℝ) := by
  have hcard : (0 : ℝ) < Fintype.card (Scramble m n) := by exact_mod_cast Fintype.card_pos
  have hn : 0 < n := by have := P.hn; omega
  have hj0 : 0 < j := by exact_mod_cast P.hj
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun s hs => ?_
  rw [Finset.mem_Icc] at hs
  have hN := P.N_pos
  have hT : (totalColumnOnes c : ℝ) * s / n ≤ (f : ℝ) / 2 * s + eps * j := by
    rw [hc, div_le_iff₀ hN]
    have hep := eps_pos
    have hj' := P.hj
    have hf := P.f_pos
    have hs' : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_right P.hjf hs'
    nlinarith [mul_nonneg (mul_nonneg hf.le hs') hN.le, mul_nonneg hep.le hj'.le,
      mul_nonneg (mul_nonneg hep.le hj'.le) hN.le, mul_nonneg hs' hN.le]
  have key := scramble_tail_union_top hn c (f / 2) s ((f : ℝ) / 2 * s + eps * j)
    (by rw [hc]; exact hj0) hs.1 hT
  rw [div_le_iff₀ hcard] at key
  refine key.trans (le_of_eq ?_)
  rw [hc]
  unfold pbound
  rw [show (f : ℝ) / 2 * s = f * s / 2 by ring]

/-- Closed form of `G1(b)`. -/
theorem G1_bpt_closed {n : ℕ} {f j : ℝ} (P : Lemma62Params n f j) :
    G1 n j (bpt f j) =
      ((Real.exp 1 * f * n / (2 * eps * j)) ^ (2 / f) * (2 * Real.exp 1 * j / (f * n))) ^
        (eps * j) := by
  have hf := P.f_pos
  have hN := P.N_pos
  have hj := P.hj
  have hep := eps_pos
  have hK : 0 ≤ Real.exp 1 * f * n / (2 * eps * j) := by positivity
  unfold G1
  rw [show Real.exp 1 * n / bpt f j = Real.exp 1 * f * n / (2 * eps * j) by
      unfold bpt; field_simp,
    show Real.exp 1 * bpt f j / (eps * n) = 2 * Real.exp 1 * j / (f * n) by unfold bpt; field_simp,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hK,
    show 2 / f * (eps * j) = bpt f j by unfold bpt; field_simp]

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
    have h2 : (1 : ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
    rw [show Y = Real.exp 1 ^ 2 * (((f : ℝ) + 2) ^ 2 * n / (4 * j)) by rw [hY]; ring]
    nlinarith
  have hexp : 2 * (j : ℝ) / ((f : ℝ) + 2) ≤ 2 / (eps * f) * (eps * j) := by
    rw [show 2 / (eps * (f : ℝ)) * (eps * j) = 2 * j / f by field_simp]
    exact div_le_div_of_nonneg_left (by positivity) hfp (by linarith)
  have hY2 : Y ^ (2 * (j : ℝ) / ((f : ℝ) + 2)) ≤ (Y ^ (2 / (eps * (f : ℝ)))) ^ (eps * (j : ℝ)) := by
    rw [← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hY1 hexp
  have hGnn : 0 ≤ G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ)) :=
    G1_nonneg _ _ _ hN.le (bpt_pos hfp hj).le
  have hx : xval (n : ℝ) (f : ℝ) (j : ℝ) ^ E =
      (Y ^ (2 / (eps * (f : ℝ)))) ^ (eps * (j : ℝ)) *
        G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ)) := by
    rw [G1_bpt_closed P, ← Real.rpow_natCast, hE, ← Real.mul_rpow (by positivity) (by positivity)]
    unfold xval
    rw [mul_assoc]
  rw [hx]
  calc _ ≤ (90 / 89 * Y ^ (2 * (j : ℝ) / ((f : ℝ) + 2))) * G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ)) :=
        mul_le_mul_of_nonneg_right htops hGnn
    _ ≤ (90 / 89 * (Y ^ (2 / (eps * (f : ℝ)))) ^ (eps * (j : ℝ))) *
          G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY2 (by norm_num)) hGnn
    _ = _ := by ring

theorem fail_prob_at_E {m n f : ℕ} (hf : Even f) (j E : ℕ) (hE1 : 1 ≤ E)
    (hE : (E : ℝ) = eps * j) (P : Lemma62Params n (f : ℝ) (j : ℝ)) :
    ((badSetF (m := m) (n := n) f j).card : ℝ) ≤
      1.025 * (3 / 10 : ℝ) ^ E * (Fintype.card (Scramble m n) : ℝ) := by
  have hep := eps_pos
  have hj0 : 0 < j := by exact_mod_cast P.hj
  have hjE : (8 * 10 ^ 7 : ℝ) ≤ j := by
    have h1 : (1 : ℝ) ≤ E := by exact_mod_cast hE1
    rw [hE, show eps = 1 / (8 * 10 ^ 7) from rfl, div_mul_eq_mul_div,
      le_div_iff₀ (by norm_num)] at h1
    linarith
  have hb := bpt_pos P.f_pos P.hj
  have hρ := exp_neg5_pos_lt
  set C : ℝ := (1 + Real.exp (-5)) / (1 - Real.exp (-5)) with hC
  have hC0 : 0 ≤ C := by rw [hC]; apply div_nonneg <;> linarith [hρ.1, hρ.2]
  have hG := G1_nonneg n (j : ℝ) (bpt (f : ℝ) (j : ℝ)) P.N_pos.le hb.le
  have hmain := badSetF_card_le (m := m) (n := n) j hj0
    (C * G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ))) (mul_nonneg hC0 hG) (by
      intro c hc
      refine (tail_sum_le j P c hc).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact le_trans (Finset.sum_le_sum fun s hs => pbound_le_gfun P s (Finset.mem_Icc.mp hs).1)
        (gfun_sum_le_G1 P))
  refine hmain.trans ?_
  have hcard : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  have h1 := tops_mul_G1_le hf P E hE
  have h2 := xval_pow_le P hjE E
  calc _ = C * (((tops (f / 2) n j).card : ℝ) * G1 n (j : ℝ) (bpt (f : ℝ) (j : ℝ))) *
        (Fintype.card (Scramble m n) : ℝ) := by ring
    _ ≤ C * (90 / 89 * (3 / 10 : ℝ) ^ E) * (Fintype.card (Scramble m n) : ℝ) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))) hC0) hcard
    _ = (90 / 89 * C) * (3 / 10 : ℝ) ^ E * (Fintype.card (Scramble m n) : ℝ) := by ring
    _ ≤ 1.025 * (3 / 10 : ℝ) ^ E * (Fintype.card (Scramble m n) : ℝ) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right const_bound (by positivity)) hcard

end Chvatal
