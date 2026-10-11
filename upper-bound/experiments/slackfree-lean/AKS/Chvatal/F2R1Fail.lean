module

public import AKS.Chvatal.F2Defs
public import Mathlib.Algebra.Order.Field.GeomSum

/-! # Failure probability of the two-round predicate `F2R1` (R1a and R1b) -/

@[expose] public section

namespace Chvatal

open Finset

/-! ## Part 1: generic probabilistic and counting lemmas -/

/-- Union bound over `s`-subsets with a Chernoff bound, for a bound `J` on the total number of ones. -/
theorem tail_union_le {m n : ℕ} (hn : 0 < n) (c : MonotoneColumnSums m n) (h s : ℕ) (J T : ℝ)
    (hJ : 0 < J) (htot : (totalColumnOnes c : ℝ) ≤ J) (hs : 0 < s) (hT : J * s / n ≤ T) :
    ((tailBadSet c (topRows m h) s T).card : ℝ) ≤
      (n.choose s : ℝ) * (Real.exp 1 * J * s / (n * T)) ^ T * Fintype.card (Scramble m n) := by
  classical
  have htot' : (0 : ℝ) < Fintype.card (Scramble m n) := by exact_mod_cast Fintype.card_pos
  have hR : (∑ r ∈ topRows m h, ((monotoneRowOnes c r).card : ℝ)) ≤ J := by
    refine le_trans ?_ htot
    rw [show (totalColumnOnes c : ℝ) = ∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ) by
      exact_mod_cast totalColumnOnes_eq_sum_rowOnes c]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => Nat.cast_nonneg _
  set P := (Finset.univ : Finset (Fin n)).powersetCard s
  set B : Finset (Fin n) → Finset (Scramble m n) := fun S =>
    Finset.univ.filter fun σ => T ≤ (onesInRows c σ (topRows m h) S : ℝ)
  have hsub : tailBadSet c (topRows m h) s T ⊆ P.biUnion B := by
    intro σ hσ
    simp only [tailBadSet, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨S, hS, hX⟩ := hσ
    exact Finset.mem_biUnion.mpr ⟨S, hS, by simp [B, hX]⟩
  have hper : ∀ S ∈ P, ((B S).card : ℝ) ≤
      (Real.exp 1 * J * s / (n * T)) ^ T * Fintype.card (Scramble m n) := by
    intro S hS
    have hcS : S.card = s := (Finset.mem_powersetCard.mp hS).2
    have := scramble_tail_fixed_set hn c _ S J T hJ (by rwa [hcS]) hR
      (by rwa [hcS]) (B S) fun σ hσ => (Finset.mem_filter.mp hσ).2
    rw [hcS] at this
    exact (div_le_iff₀ htot').mp this
  calc ((tailBadSet c (topRows m h) s T).card : ℝ) ≤ ∑ S ∈ P, ((B S).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ S ∈ P, (Real.exp 1 * J * s / (n * T)) ^ T * Fintype.card (Scramble m n) :=
        Finset.sum_le_sum hper
    _ = _ := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring

open Classical in
/-- Union over the tops: an event family depending only on the top of `c`. -/
theorem bad_card_le_tops {m n : ℕ} (g j : ℕ) (Ev : MonotoneColumnSums m n → Finset (Scramble m n))
    (B : ℝ) (hB0 : 0 ≤ B)
    (hdep : ∀ c c', topOf g c = topOf g c' → Ev c = Ev c')
    (hB : ∀ c, totalColumnOnes c ≤ j → ((Ev c).card : ℝ) ≤ B * Fintype.card (Scramble m n)) :
    ((Finset.univ.filter fun σ : Scramble m n => ∃ c, totalColumnOnes c ≤ j ∧ σ ∈ Ev c).card : ℝ)
      ≤ ((tops g n j).card : ℝ) * B * Fintype.card (Scramble m n) := by
  classical
  let P : (Fin n → ℕ) → Prop := fun t => ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j ∧ topOf g c = t
  let rep : (Fin n → ℕ) → MonotoneColumnSums m n := fun t =>
    if h : P t then Classical.choose h else fun _ => 0
  have hrep : ∀ t, P t → totalColumnOnes (rep t) ≤ j ∧ topOf g (rep t) = t := fun t ht => by
    simp only [rep, dif_pos ht]
    exact Classical.choose_spec ht
  let I : Finset (Fin n → ℕ) := (tops g n j).filter P
  have hsub : (Finset.univ.filter fun σ : Scramble m n => ∃ c, totalColumnOnes c ≤ j ∧ σ ∈ Ev c)
      ⊆ I.biUnion fun t => Ev (rep t) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨c, hc, hσc⟩ := hσ
    have hPt : P (topOf g c) := ⟨c, hc, rfl⟩
    obtain ⟨-, hrt⟩ := hrep _ hPt
    refine Finset.mem_biUnion.mpr ⟨topOf g c, Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨fun col => (c col).val, mem_sset.mpr hc, rfl⟩, hPt⟩, ?_⟩
    rwa [hdep _ c hrt]
  have hN : (0 : ℝ) ≤ B * (Fintype.card (Scramble m n) : ℝ) := by positivity
  calc _ ≤ (∑ t ∈ I, ((Ev (rep t)).card : ℝ)) := by
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ t ∈ I, B * (Fintype.card (Scramble m n) : ℝ) :=
        Finset.sum_le_sum fun t ht => hB (rep t) (hrep t (Finset.mem_filter.mp ht).2).1
    _ = (I.card : ℝ) * (B * (Fintype.card (Scramble m n) : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((tops g n j).card : ℝ) * (B * (Fintype.card (Scramble m n) : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) hN
    _ = _ := by ring

/-- Closed form for the number of tops with an arbitrary bottom height `g`. -/
theorem tops_card_le_gen (g n j : ℕ) (hn : 0 < n) (hj : 0 < j) (hjg : j ≤ (g + 1) ^ 2 * n) :
    ((tops g n j).card : ℝ) ≤ ((j : ℝ) / (g + 1) + 1) *
      (Real.exp 1 ^ 2 * n * ((g : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / (g + 1)) := by
  have h1 : ((tops g n j).card : ℝ) ≤
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((j - g * k).choose k : ℝ) := by
    have := tops_card_le g n j
    unfold topClosed at this
    exact_mod_cast this
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hG : (0 : ℝ) < (g : ℝ) + 1 := by positivity
  set c : ℝ := (n : ℝ) * j with hcdef
  have hc : 0 < c := by positivity
  set x0 : ℝ := (j : ℝ) / ((g : ℝ) + 1) with hx0
  have hx0pos : 0 < x0 := by positivity
  have hx0sq : x0 ^ 2 ≤ c := by
    have hjg' : (j : ℝ) ≤ ((g : ℝ) + 1) ^ 2 * n := by exact_mod_cast hjg
    rw [hx0, div_pow, div_le_iff₀ (by positivity), hcdef]
    nlinarith
  have hbase : Real.exp 1 ^ 2 * c / x0 ^ 2 = Real.exp 1 ^ 2 * n * ((g : ℝ) + 1) ^ 2 / j := by
    rw [hx0, hcdef]; field_simp
  set K : ℕ := j / (g + 1) with hK
  have hKx : (K : ℝ) ≤ x0 := by
    simpa [hx0] using Nat.cast_div_le (α := ℝ) (m := j) (n := g + 1)
  have hbase1 : 1 ≤ Real.exp 1 ^ 2 * c / x0 ^ 2 := by
    rw [mul_div_assoc]
    have : 1 ≤ c / x0 ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith [one_le_pow₀ (Real.one_le_exp (show (0:ℝ) ≤ 1 by norm_num)) (n := 2)]
  have hM1 : 1 ≤ topY c x0 := Real.one_le_rpow hbase1 hx0pos.le
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * ((j - g * k).choose k : ℝ) ≤ if k ≤ K then topY c x0 else 0 := by
    intro k _
    by_cases hkK : k ≤ K
    · rw [if_pos hkK]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa using hM1
      · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have hkx : (k : ℝ) ≤ x0 := (Nat.cast_le.mpr hkK).trans hKx
        calc _ ≤ _ := choose_mul_choose_le_of_le n (J := j - g * k) (j := j) (Nat.sub_le _ _) hk
          _ = topYn c k := by rw [topYn, hcdef, mul_assoc]
          _ = topY c (k : ℝ) := by rw [topY, topYn, Real.rpow_natCast]
          _ ≤ topY c x0 := topY_mono c hc hk1 hkx hx0sq
    · rw [if_neg hkK]
      have hlt : j < k * (g + 1) := (Nat.div_lt_iff_lt_mul (by omega)).mp (not_le.mp hkK)
      have : j - g * k < k := by
        obtain ⟨m, hm⟩ : ∃ m, m = g * k := ⟨_, rfl⟩
        have h3 : j < g * k + k := by nlinarith [hlt]
        have hk0 : 0 < k := lt_of_le_of_lt (Nat.zero_le _) (not_le.mp hkK)
        rw [← hm] at h3 ⊢; omega
      rw [Nat.choose_eq_zero_of_lt this]; simp
  have hsum : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((j - g * k).choose k : ℝ)) ≤
      ∑ k ∈ Finset.range (K + 1), topY c x0 := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by linarith)
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  have hcount : ((K : ℝ) + 1) ≤ x0 + 1 := by linarith
  calc _ ≤ _ := h1
    _ ≤ _ := hsum
    _ = ((K : ℝ) + 1) * topY c x0 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ (x0 + 1) * topY c x0 := by gcongr
    _ = _ := by rw [topY, hbase]

/-! ## Part 2: real-analytic bounds -/

lemma pow_eq_exp' (y : ℝ) (hy : 0 < y) (s : ℕ) : y ^ s = Real.exp (s * Real.log y) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hy, mul_comm]

lemma log_le_div_exp {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / Real.exp 1 by positivity)
  rw [Real.log_div hx.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

lemma log_le_five_mul {x : ℝ} {E : ℕ} (hE : 2 ≤ E) (hx : 0 < x) (hxE : x ≤ 1642 * E) :
    Real.log x ≤ 5 * E := by
  have hE' : (2 : ℝ) ≤ E := by exact_mod_cast hE
  have h10 : (22000 : ℝ) ≤ Real.exp 10 := by
    have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
    have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (22000 : ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 10
  have h2 : (1 : ℝ) + 5 * (E - 2) ≤ Real.exp (5 * (E - 2)) := by
    linarith [Real.add_one_le_exp (5 * ((E : ℝ) - 2))]
  have h3 : Real.exp (5 * E) = Real.exp 10 * Real.exp (5 * (E - 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [Real.log_le_iff_le_exp hx, h3]
  have := mul_le_mul h10 h2 (by linarith) (by positivity)
  nlinarith

set_option maxHeartbeats 1600000 in
/-- The real-number core of R1(a): the bound `(K+1) X^K (e n/s)^s (e j/(n(Δ+1)))^{(Δ+1)s} ≤ e^{-10E}`. -/
theorem R1a_real {n j s E : ℕ} {G Dl D J c : ℝ}
    (hn : 0 < n) (hj : 1 ≤ j) (hjD : (j : ℝ) ≤ D * n) (hjE : (j : ℝ) ≤ E * J)
    (hs1 : 1 ≤ s) (hs : c * E + 1 ≤ s)
    (hG : 0 < G) (hDl : 0 < Dl) (hD : 0 < D) (hJ : 0 < J) (hc : 0 < c)
    (hαc : J / G ≤ c * Dl) (hα : J / G ≤ 1641)
    (h1 : 0 ≤ 2 + 2 * Real.log G - Real.log D)
    (h2 : 0 ≤ (Dl + 1) * (Real.log (Dl + 1) - 1) - 1 - Real.log (J / c) - Dl * Real.log D)
    (h3 : J / G * (2 + 2 * Real.log G - Real.log D) -
      c * ((Dl + 1) * (Real.log (Dl + 1) - 1) - 1 - Real.log (J / c) - Dl * Real.log D) ≤ -15)
    (hE : 2 ≤ E) :
    ((j : ℝ) / G + 1) * (Real.exp 1 ^ 2 * n * G ^ 2 / j) ^ ((j : ℝ) / G) *
      (Real.exp 1 * n / s) ^ s *
      (Real.exp 1 * j * s / (n * ((Dl + 1) * s))) ^ ((Dl + 1) * (s : ℝ)) ≤
        Real.exp (-10 * E) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hE2 : (2 : ℝ) ≤ E := by exact_mod_cast hE
  have hE0 : (0 : ℝ) < E := by linarith
  have he := Real.exp_pos 1
  have hDl1 : 0 < Dl + 1 := by linarith
  set Kr : ℝ := (j : ℝ) / G with hKr
  have hKr0 : 0 < Kr := by positivity
  set L : ℝ := Real.log n - Real.log j with hLdef
  have hL : -Real.log D ≤ L := by
    have := Real.log_le_log hj0 hjD
    rw [Real.log_mul hD.ne' hn0.ne'] at this
    rw [hLdef]; linarith
  set a0 : ℝ := 2 + 2 * Real.log G with ha0
  -- the three logarithms
  have hX : (0 : ℝ) < Real.exp 1 ^ 2 * n * G ^ 2 / j := by positivity
  have hlogX : Real.log (Real.exp 1 ^ 2 * n * G ^ 2 / j) = a0 + L := by
    rw [Real.log_div (by positivity) hj0.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_exp,
      hLdef, ha0]
    push_cast; ring
  have hY : (0 : ℝ) < Real.exp 1 * n / s := by positivity
  have hcj : c * j ≤ J * s := by
    have h1 : c * (j : ℝ) ≤ c * (E * J) := mul_le_mul_of_nonneg_left hjE hc.le
    nlinarith
  have hlogY : Real.log (Real.exp 1 * n / s) ≤ 1 + Real.log (J / c) + L := by
    rw [Real.log_div (by positivity) hs0.ne', Real.log_mul he.ne' hn0.ne', Real.log_exp,
      Real.log_div hJ.ne' hc.ne', hLdef]
    have := Real.log_le_log (by positivity) hcj
    rw [Real.log_mul hc.ne' hj0.ne', Real.log_mul hJ.ne' hs0.ne'] at this
    linarith
  have hZeq : Real.exp 1 * j * s / (n * ((Dl + 1) * s)) = Real.exp 1 * j / (n * (Dl + 1)) := by
    field_simp
  have hZ : (0 : ℝ) < Real.exp 1 * j * s / (n * ((Dl + 1) * s)) := by positivity
  have hlogZ : Real.log (Real.exp 1 * j * s / (n * ((Dl + 1) * s))) = 1 - L - Real.log (Dl + 1) := by
    rw [hZeq, Real.log_div (by positivity) (by positivity), Real.log_mul he.ne' hj0.ne',
      Real.log_mul hn0.ne' hDl1.ne', Real.log_exp, hLdef]
    ring
  -- rewrite the product as an exponential
  have hK1 : (0 : ℝ) < Kr + 1 := by linarith
  have hprod : (Kr + 1) * (Real.exp 1 ^ 2 * n * G ^ 2 / j) ^ Kr * (Real.exp 1 * n / s) ^ s *
      (Real.exp 1 * j * s / (n * ((Dl + 1) * s))) ^ ((Dl + 1) * (s : ℝ)) =
      Real.exp (Real.log (Kr + 1) + Real.log (Real.exp 1 ^ 2 * n * G ^ 2 / j) * Kr +
        s * Real.log (Real.exp 1 * n / s) +
        Real.log (Real.exp 1 * j * s / (n * ((Dl + 1) * s))) * ((Dl + 1) * s)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hK1, ← Real.rpow_def_of_pos hX,
      ← pow_eq_exp' _ hY, ← Real.rpow_def_of_pos hZ]
  rw [hprod]
  refine Real.exp_le_exp.mpr ?_
  rw [hlogX, hlogZ]
  -- the exponent
  have hd : 0 ≤ L + Real.log D := by linarith
  have hA : 0 ≤ a0 + L := by linarith
  set Q0 : ℝ := (Dl + 1) * (Real.log (Dl + 1) - 1) - 1 - Real.log (J / c) - Dl * Real.log D with hQ0
  have hKE : Kr ≤ E * J / G := by
    rw [hKr]; exact div_le_div_of_nonneg_right hjE hG.le
  have hP1 : Kr * (a0 + L) ≤ E * J / G * (a0 + L) := mul_le_mul_of_nonneg_right hKE hA
  have hP2 : c * E * Q0 ≤ s * Q0 := mul_le_mul_of_nonneg_right (by linarith) h2
  have hP3 : J / G * E * (L + Real.log D) ≤ s * (Dl * (L + Real.log D)) := by
    have e1 : J / G * E ≤ c * Dl * E := mul_le_mul_of_nonneg_right hαc hE0.le
    have e2 : J / G * E * (L + Real.log D) ≤ c * Dl * E * (L + Real.log D) :=
      mul_le_mul_of_nonneg_right e1 hd
    have e3 : c * E * (Dl * (L + Real.log D)) ≤ s * (Dl * (L + Real.log D)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e4 : c * Dl * E * (L + Real.log D) = c * E * (Dl * (L + Real.log D)) := by ring
    linarith [e2, e3, e4]
  have hYs : (s : ℝ) * Real.log (Real.exp 1 * n / s) ≤ s * (1 + Real.log (J / c) + L) :=
    mul_le_mul_of_nonneg_left hlogY hs0.le
  have hid : s * (1 + Real.log (J / c) + L) + (1 - L - Real.log (Dl + 1)) * ((Dl + 1) * s) =
      -(s * Q0) - s * (Dl * (L + Real.log D)) := by
    rw [hQ0]; ring
  have hH : E * (J / G * (a0 - Real.log D) - c * Q0) ≤ E * (-15) :=
    mul_le_mul_of_nonneg_left h3 hE0.le
  have hlogK : Real.log (Kr + 1) ≤ 5 * E := by
    refine log_le_five_mul hE hK1 ?_
    have : Kr ≤ 1641 * E := by
      calc Kr ≤ E * J / G := hKE
        _ = E * (J / G) := by ring
        _ ≤ E * 1641 := mul_le_mul_of_nonneg_left hα hE0.le
        _ = _ := by ring
    linarith
  have hexp : E * J / G * (a0 + L) = J / G * E * (a0 - Real.log D) + J / G * E * (L + Real.log D) := by
    ring
  have hcomm : (a0 + L) * Kr = Kr * (a0 + L) := mul_comm _ _
  linarith [hP1, hP2, hP3, hYs, hid, hH, hlogK, hexp, hcomm]

set_option maxHeartbeats 1600000 in
/-- The real-number core of R1(b): `(K+1) X^K (e n/s)^s (e j s/(n T))^T ≤ e^{-16E}` for
`T = Δ s + B` with `B ≥ b E`. -/
theorem R1b_real {n j s E : ℕ} {G Dl D J bb Bn : ℝ}
    (hn : 0 < n) (hj : 1 ≤ j) (hjD : (j : ℝ) ≤ D * n) (hjE : (j : ℝ) ≤ E * J)
    (hs1 : 1 ≤ s) (hsb : (s : ℝ) ≤ bb * E) (hB : bb * E ≤ Bn)
    (hG : 0 < G) (hDl : 1 ≤ Dl) (hD : 0 < D) (hDDl : D ≤ Dl + 1) (hJ : 0 < J) (hbb : 0 < bb)
    (hαb : J / G ≤ bb) (hα : J / G ≤ 1641)
    (h1 : 0 ≤ 2 + 2 * Real.log G - Real.log D)
    (hRs : 1 + Real.log J + Dl * (1 - Real.log Dl) + (1 - Dl) * (-Real.log D) ≤ 0)
    (hNb : J / G * (2 + 2 * Real.log G - Real.log D) +
      bb * (1 + Real.log D - Real.log Dl) ≤ -22)
    (hE : 2 ≤ E) :
    ((j : ℝ) / G + 1) * (Real.exp 1 ^ 2 * n * G ^ 2 / j) ^ ((j : ℝ) / G) *
      (Real.exp 1 * n / s) ^ s *
      (Real.exp 1 * j * s / (n * (Dl * s + Bn))) ^ (Dl * (s : ℝ) + Bn) ≤
        Real.exp (-16 * E) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hE2 : (2 : ℝ) ≤ E := by exact_mod_cast hE
  have hE0 : (0 : ℝ) < E := by linarith
  have he := Real.exp_pos 1
  have hDl0 : 0 < Dl := by linarith
  set Kr : ℝ := (j : ℝ) / G with hKr
  have hKr0 : 0 < Kr := by positivity
  set L : ℝ := Real.log n - Real.log j with hLdef
  have hL : -Real.log D ≤ L := by
    have := Real.log_le_log hj0 hjD
    rw [Real.log_mul hD.ne' hn0.ne'] at this
    rw [hLdef]; linarith
  set a0 : ℝ := 2 + 2 * Real.log G with ha0
  set T0 : ℝ := Dl * s + bb * E with hT0
  have hT0pos : 0 < T0 := by positivity
  have hT0T : T0 ≤ Dl * s + Bn := by rw [hT0]; linarith
  have hTpos : 0 < Dl * (s : ℝ) + Bn := lt_of_lt_of_le hT0pos hT0T
  -- Chernoff part: replace T by T0, then T0 by the cruder base
  set c0 : ℝ := Real.exp 1 * j * s / n with hc0def
  have hc0 : 0 < c0 := by positivity
  have hjn : (j : ℝ) / n ≤ D := by rw [div_le_iff₀ hn0]; linarith
  have hx : c0 / Real.exp 1 ≤ T0 := by
    have : c0 / Real.exp 1 = j / n * s := by rw [hc0def]; field_simp
    rw [this]
    have h1' : (j : ℝ) / n * s ≤ D * s := mul_le_mul_of_nonneg_right hjn hs0.le
    rw [hT0]; nlinarith
  have hanti := rpow_div_self_antitone hc0 hx hT0T
  have hZeq : Real.exp 1 * j * s / (n * (Dl * s + Bn)) = c0 / (Dl * s + Bn) := by
    rw [hc0def, div_div]
  rw [hZeq]
  set W : ℝ := Real.exp 1 * j / (n * Dl) with hWdef
  have hW : 0 < W := by positivity
  have hbase : c0 / T0 ≤ W := by
    rw [hc0def, hWdef, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : Dl * s ≤ T0 := by
      rw [hT0]; have : 0 ≤ bb * (E : ℝ) := by positivity
      linarith
    have h2 : 0 ≤ Real.exp 1 * j * n := by positivity
    have h3 := mul_le_mul_of_nonneg_left h0 h2
    calc Real.exp 1 * j * s * (n * Dl) = Real.exp 1 * j * n * (Dl * s) := by ring
      _ ≤ Real.exp 1 * j * n * T0 := h3
      _ = Real.exp 1 * j * (n * T0) := by ring
  have hW1 : (c0 / T0) ^ T0 ≤ W ^ T0 :=
    Real.rpow_le_rpow (by positivity) hbase hT0pos.le
  have hX : (0 : ℝ) < Real.exp 1 ^ 2 * n * G ^ 2 / j := by positivity
  have hlogX : Real.log (Real.exp 1 ^ 2 * n * G ^ 2 / j) = a0 + L := by
    rw [Real.log_div (by positivity) hj0.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_exp,
      hLdef, ha0]
    push_cast; ring
  have hY : (0 : ℝ) < Real.exp 1 * n / s := by positivity
  have hlogE : Real.log j ≤ Real.log E + Real.log J := by
    have := Real.log_le_log hj0 hjE
    rwa [Real.log_mul hE0.ne' hJ.ne'] at this
  have hEs : (s : ℝ) * (Real.log E - Real.log s) ≤ E := by
    have h := log_le_div_exp (show (0 : ℝ) < E / s by positivity)
    rw [Real.log_div hE0.ne' hs0.ne'] at h
    have h' : (s : ℝ) * (Real.log E - Real.log s) ≤ s * (E / s / Real.exp 1) :=
      mul_le_mul_of_nonneg_left h hs0.le
    have h2 : (s : ℝ) * (E / s / Real.exp 1) = E / Real.exp 1 := by field_simp
    have h3 : (E : ℝ) / Real.exp 1 ≤ E := by
      rw [div_le_iff₀ he]
      exact le_mul_of_one_le_right hE0.le (Real.one_le_exp (by norm_num))
    linarith
  have hlogY : (s : ℝ) * Real.log (Real.exp 1 * n / s) ≤
      s * (1 + Real.log J + L) + E := by
    rw [Real.log_div (by positivity) hs0.ne', Real.log_mul he.ne' hn0.ne', Real.log_exp, hLdef]
    have hh : (s : ℝ) * (Real.log j - Real.log J - Real.log s) ≤ s * (Real.log E - Real.log s) :=
      mul_le_mul_of_nonneg_left (by linarith) hs0.le
    have hid2 : (s : ℝ) * (1 + Real.log n - Real.log s) = s * (1 + Real.log J + (Real.log n - Real.log j)) + s * (Real.log j - Real.log J - Real.log s) := by ring
    linarith [hh, hEs, hid2]
  have hlogW : Real.log W = 1 - L - Real.log Dl := by
    rw [hWdef, Real.log_div (by positivity) (by positivity), Real.log_mul he.ne' hj0.ne',
      Real.log_mul hn0.ne' hDl0.ne', Real.log_exp, hLdef]
    ring
  have hK1 : (0 : ℝ) < Kr + 1 := by linarith
  have hprod : (Kr + 1) * (Real.exp 1 ^ 2 * n * G ^ 2 / j) ^ Kr * (Real.exp 1 * n / s) ^ s *
      W ^ T0 =
      Real.exp (Real.log (Kr + 1) + Real.log (Real.exp 1 ^ 2 * n * G ^ 2 / j) * Kr +
        s * Real.log (Real.exp 1 * n / s) + Real.log W * T0) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hK1, ← Real.rpow_def_of_pos hX,
      ← pow_eq_exp' _ hY, ← Real.rpow_def_of_pos hW]
  have hpos1 : 0 ≤ (Kr + 1) * (Real.exp 1 ^ 2 * n * G ^ 2 / j) ^ Kr * (Real.exp 1 * n / s) ^ s := by
    positivity
  calc (Kr + 1) * (Real.exp 1 ^ 2 * n * G ^ 2 / j) ^ Kr * (Real.exp 1 * n / s) ^ s *
        (c0 / (Dl * s + Bn)) ^ (Dl * (s : ℝ) + Bn)
      ≤ (Kr + 1) * (Real.exp 1 ^ 2 * n * G ^ 2 / j) ^ Kr * (Real.exp 1 * n / s) ^ s * W ^ T0 :=
        mul_le_mul_of_nonneg_left (hanti.trans hW1) hpos1
    _ = _ := hprod
    _ ≤ Real.exp (-16 * E) := by
      refine Real.exp_le_exp.mpr ?_
      rw [hlogX, hlogW]
      have hd : 0 ≤ L + Real.log D := by linarith
      have hA : 0 ≤ a0 + L := by linarith
      have hKE : Kr ≤ E * J / G := by
        rw [hKr]; exact div_le_div_of_nonneg_right hjE hG.le
      have hP1 : Kr * (a0 + L) ≤ E * J / G * (a0 + L) := mul_le_mul_of_nonneg_right hKE hA
      have hRL : 1 + Real.log J + L + Dl * (1 - L - Real.log Dl) ≤ 0 := by
        have : (1 - Dl) * L ≤ (1 - Dl) * (-Real.log D) :=
          mul_le_mul_of_nonpos_left hL (by linarith)
        linarith
      have hsR : (s : ℝ) * (1 + Real.log J + L + Dl * (1 - L - Real.log Dl)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hs0.le hRL
      have hid : s * (1 + Real.log J + L) + (1 - L - Real.log Dl) * T0 =
          s * (1 + Real.log J + L + Dl * (1 - L - Real.log Dl)) +
            bb * E * (1 + Real.log D - Real.log Dl) - bb * E * (L + Real.log D) := by
        rw [hT0]; ring
      have hH : E * (J / G * (a0 - Real.log D) + bb * (1 + Real.log D - Real.log Dl)) ≤ E * (-22) :=
        mul_le_mul_of_nonneg_left hNb hE0.le
      have hP4 : E * (J / G) * (L + Real.log D) ≤ bb * E * (L + Real.log D) := by
        have : E * (J / G) ≤ bb * E := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hαb hE0.le
        exact mul_le_mul_of_nonneg_right this hd
      have hlogK : Real.log (Kr + 1) ≤ 5 * E := by
        refine log_le_five_mul hE hK1 ?_
        have : Kr ≤ 1641 * E := by
          calc Kr ≤ E * J / G := hKE
            _ = E * (J / G) := by ring
            _ ≤ E * 1641 := mul_le_mul_of_nonneg_left hα hE0.le
            _ = _ := by ring
        linarith
      have hexp : E * J / G * (a0 + L) =
          E * (J / G * (a0 - Real.log D)) + E * (J / G) * (L + Real.log D) := by ring
      have hcomm : (a0 + L) * Kr = Kr * (a0 + L) := mul_comm _ _
      have hmul : E * (J / G * (a0 - Real.log D) + bb * (1 + Real.log D - Real.log Dl)) =
          E * (J / G * (a0 - Real.log D)) + bb * E * (1 + Real.log D - Real.log Dl) := by ring
      linarith [hP1, hid, hH, hP4, hlogK, hexp, hcomm, hsR, hlogY, hmul]


/-! ## Part 3: the per-`E` event bounds for R1(a), R1(b) -/

theorem onesInRows_le_total {m n : ℕ} (c : MonotoneColumnSums m n) (σ : Scramble m n)
    (R : Finset (Fin m)) (S : Finset (Fin n)) : onesInRows c σ R S ≤ totalColumnOnes c := by
  unfold onesInRows
  calc ∑ r ∈ R, (scrambledRowOnes c σ r ∩ S).card ≤ ∑ r ∈ R, (monotoneRowOnes c r).card := by
        refine Finset.sum_le_sum fun r _ => ?_
        exact (Finset.card_le_card Finset.inter_subset_left).trans Finset.card_image_le
    _ ≤ ∑ r : Fin m, (monotoneRowOnes c r).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := (totalColumnOnes_eq_sum_rowOnes c).symm

theorem tailBadSet_eq_of_top {m n g : ℕ} (c c' : MonotoneColumnSums m n)
    (h : topOf g c = topOf g c') (s : ℕ) (T : ℝ) :
    tailBadSet c (topRows m g) s T = tailBadSet c' (topRows m g) s T := by
  have htop : ∀ col, (c col).val - g = (c' col).val - g := fun col => congrFun h col
  ext σ
  simp only [tailBadSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨S, hS, hT⟩ <;> refine ⟨S, hS, ?_⟩
  · rwa [← onesInRows_topRows_depends_only_on_top c c' htop σ S]
  · rwa [onesInRows_topRows_depends_only_on_top c c' htop σ S]

theorem jE_facts (P : F2Params) (hf : 131040 ≤ P.f) {n : ℕ} (hn : 16 ≤ n) {E : ℕ} (hE : 2 ≤ E) :
    1 ≤ P.jE n E ∧ ((P.jE n E : ℕ) : ℝ) ≤ (128 / 4095 : ℝ) * P.f * n ∧
      ((P.jE n E : ℕ) : ℝ) ≤ E * P.J ∧ P.jE n E ≤ P.jmax n := by
  have hf' : (131040 : ℝ) ≤ P.f := by exact_mod_cast hf
  have hn' : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hjm1 : 1 ≤ P.jmax n := by
    unfold F2Params.jmax
    refine Nat.le_floor ?_
    push_cast
    nlinarith
  have hjmD : (P.jmax n : ℝ) ≤ (128 / 4095 : ℝ) * P.f * n := by
    unfold F2Params.jmax
    calc _ ≤ (128 / 4095 : ℝ) * (P.f * n) := Nat.floor_le (by positivity)
      _ = _ := by ring
  have hEJ : 1 ≤ E * P.J := by
    have := P.hJ
    nlinarith
  refine ⟨?_, ?_, ?_, min_le_right _ _⟩
  · unfold F2Params.jE; exact le_min hEJ hjm1
  · exact (Nat.cast_le.mpr (min_le_right _ _)).trans hjmD
  · have : P.jE n E ≤ E * P.J := min_le_left _ _
    exact_mod_cast this

/-- Numeric hypotheses for R1(a). -/
def R1aNum (P : F2Params) : Prop :=
  (P.J : ℝ) / ((P.g1 : ℝ) + 1) ≤ 1641 ∧
  0 ≤ ((P.Δ : ℝ) + 1) * (Real.log ((P.Δ : ℝ) + 1) - 1) - 1 - Real.log ((P.J : ℝ) / P.c)
      - (P.Δ : ℝ) * Real.log ((128 / 4095 : ℝ) * P.f) ∧
  (P.J : ℝ) / ((P.g1 : ℝ) + 1) *
      (2 + 2 * Real.log ((P.g1 : ℝ) + 1) - Real.log ((128 / 4095 : ℝ) * P.f)) -
    P.c * (((P.Δ : ℝ) + 1) * (Real.log ((P.Δ : ℝ) + 1) - 1) - 1 - Real.log ((P.J : ℝ) / P.c)
      - (P.Δ : ℝ) * Real.log ((128 / 4095 : ℝ) * P.f)) ≤ -15

/-- Numeric hypotheses for R1(b). -/
def R1bNum (P : F2Params) : Prop :=
  (P.J : ℝ) / ((P.g1 : ℝ) + 1) ≤ 1641 ∧
  1 + Real.log (P.J : ℝ) + (P.Δ : ℝ) * (1 - Real.log (P.Δ : ℝ)) +
      (1 - (P.Δ : ℝ)) * (-Real.log ((128 / 4095 : ℝ) * P.f)) ≤ 0 ∧
  (P.J : ℝ) / ((P.g1 : ℝ) + 1) *
      (2 + 2 * Real.log ((P.g1 : ℝ) + 1) - Real.log ((128 / 4095 : ℝ) * P.f)) +
    P.b * (1 + Real.log ((128 / 4095 : ℝ) * P.f) - Real.log (P.Δ : ℝ)) ≤ -22

lemma log_D_le (P : F2Params) :
    0 ≤ 2 + 2 * Real.log ((P.g1 : ℝ) + 1) - Real.log ((128 / 4095 : ℝ) * P.f) := by
  have hf : (0 : ℝ) < P.f := by
    have : 0 < P.f := by have := P.hg2f; have := P.hg12; have := P.hg1; omega
    exact_mod_cast this
  have hD0 : (0 : ℝ) < (128 / 4095 : ℝ) * P.f := by positivity
  have h := Real.log_le_log hD0 P.hD3
  rw [Real.log_pow] at h
  push_cast at h
  linarith

set_option maxHeartbeats 1600000 in
/-- Probability of the R1(a) event at a fixed `E`. -/
theorem R1a_event_card_le (P : F2Params) (hc : P.c = 1 / 3) (hf : 131040 ≤ P.f) (hnum : R1aNum P)
    {m n : ℕ} (hn : 16 ≤ n) {E : ℕ} (hE : 2 ≤ E) :
    ((Finset.univ.filter fun σ : Scramble m n => ∃ c : MonotoneColumnSums m n,
        totalColumnOnes c ≤ P.jE n E ∧ ∃ S : Finset (Fin n), S.card = P.κ E + 1 ∧
          (P.Δ + 1) * (P.κ E + 1) ≤ onesInRows c σ (topRows m P.g1) S).card : ℝ) ≤
      Real.exp (-10 * E) * Fintype.card (Scramble m n) := by
  classical
  have hn0 : 0 < n := by omega
  obtain ⟨hj1, hjD, hjE, -⟩ := jE_facts P hf hn hE
  obtain ⟨hα, h2, h3⟩ := hnum
  set j := P.jE n E with hjdef
  set s := P.κ E + 1 with hsdef
  have hs1 : 1 ≤ s := by omega
  have hs0 : 0 < s := hs1
  have hsE : P.c * E + 1 ≤ (s : ℝ) := by
    have := Nat.le_ceil (P.c * E)
    simp only [hsdef, F2Params.κ]; push_cast; linarith
  set T : ℕ := (P.Δ + 1) * s with hT
  set Ev : MonotoneColumnSums m n → Finset (Scramble m n) :=
    fun c => tailBadSet c (topRows m P.g1) s (T : ℝ) with hEv
  have hsub : (Finset.univ.filter fun σ : Scramble m n => ∃ c : MonotoneColumnSums m n,
        totalColumnOnes c ≤ j ∧ ∃ S : Finset (Fin n), S.card = s ∧
          (P.Δ + 1) * s ≤ onesInRows c σ (topRows m P.g1) S) ⊆
      Finset.univ.filter fun σ : Scramble m n => ∃ c, totalColumnOnes c ≤ j ∧ σ ∈ Ev c := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    obtain ⟨c, hc1, S, hS, hS2⟩ := hσ
    refine ⟨c, hc1, ?_⟩
    simp only [hEv, tailBadSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩, ?_⟩
    rw [hT]; exact_mod_cast hS2
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
  have hs0r : (0 : ℝ) < s := by exact_mod_cast hs0
  have hD1 : (128 / 4095 : ℝ) * P.f ≤ (P.Δ : ℝ) + 1 := P.hD1
  have hjn : (j : ℝ) / n ≤ (P.Δ : ℝ) + 1 := by
    rw [div_le_iff₀ hn0r]; nlinarith
  have hTr : (T : ℝ) = ((P.Δ : ℝ) + 1) * s := by rw [hT]; push_cast; ring
  have hB : ∀ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j →
      ((Ev c).card : ℝ) ≤
        ((n.choose s : ℝ) * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ)) *
          Fintype.card (Scramble m n) := by
    intro c hcj
    refine tail_union_le hn0 c P.g1 s (j : ℝ) (T : ℝ) hjpos (by exact_mod_cast hcj) hs0 ?_
    have h := (div_le_iff₀ hn0r).mp hjn
    rw [hTr, div_le_iff₀ hn0r]
    nlinarith [mul_le_mul_of_nonneg_right h hs0r.le]
  have hBnn : (0 : ℝ) ≤ (n.choose s : ℝ) * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ) := by
    positivity
  have hmain := bad_card_le_tops (m := m) (n := n) P.g1 j Ev _ hBnn
    (fun c c' h => tailBadSet_eq_of_top c c' h s (T : ℝ)) hB
  have hjg : j ≤ (P.g1 + 1) ^ 2 * n := by
    have h1 : (j : ℝ) ≤ ((P.g1 : ℝ) + 1) ^ 2 * n := by
      have := P.hD3
      calc (j : ℝ) ≤ (128 / 4095 : ℝ) * P.f * n := hjD
        _ ≤ _ := mul_le_mul_of_nonneg_right this hn0r.le
    exact_mod_cast h1
  have htops := tops_card_le_gen P.g1 n j hn0 hj1 hjg
  have hchoose : (n.choose s : ℝ) ≤ (Real.exp 1 * n / s) ^ s := choose_le_exp_pow n hs1
  have hreal := R1a_real (n := n) (j := j) (s := s) (E := E) (G := (P.g1 : ℝ) + 1)
    (Dl := (P.Δ : ℝ)) (D := (128 / 4095 : ℝ) * P.f) (J := (P.J : ℝ)) (c := P.c)
    hn0 hj1 hjD hjE hs1 hsE (by positivity) (by exact_mod_cast (show 0 < P.Δ from by
      unfold F2Params.Δ; have := P.hg12; omega))
    (by have : (0 : ℝ) < P.f := by exact_mod_cast (by have := P.hg2f; omega : 0 < P.f)
        positivity)
    (by exact_mod_cast P.hJ) P.hc0 P.hcΔ hα (log_D_le P) h2 h3 hE
  have hAnn : 0 ≤ ((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
      (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) := by
    positivity
  have hZnn : 0 ≤ (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ) := by positivity
  have hScr : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  calc _ ≤ ((Finset.univ.filter fun σ : Scramble m n =>
          ∃ c, totalColumnOnes c ≤ j ∧ σ ∈ Ev c).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := hmain
    _ ≤ (((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
        (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) *
          ((n.choose s : ℝ) * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ))) *
          Fintype.card (Scramble m n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htops hBnn) hScr
    _ ≤ (((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
        (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) *
          ((Real.exp 1 * n / s) ^ s * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ))) *
          Fintype.card (Scramble m n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hchoose hZnn) hAnn) hScr
    _ = (((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
        (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) *
          (Real.exp 1 * n / s) ^ s * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ)) *
          Fintype.card (Scramble m n) := by ring
    _ ≤ Real.exp (-10 * E) * Fintype.card (Scramble m n) := by
        refine mul_le_mul_of_nonneg_right ?_ hScr
        rw [hTr]; exact hreal

set_option maxHeartbeats 1600000 in
/-- Probability of the R1(b) event at a fixed `E`. -/
theorem R1b_event_card_le (P : F2Params) (hc : P.c = 1 / 3) (hb : P.b = 17000)
    (hf : 131040 ≤ P.f) (hnum : R1bNum P)
    {m n : ℕ} (hn : 16 ≤ n) {E : ℕ} (hE : 2 ≤ E) :
    ((Finset.univ.filter fun σ : Scramble m n => ∃ c : MonotoneColumnSums m n,
        totalColumnOnes c ≤ P.jE n E ∧ ∃ S : Finset (Fin n), 1 ≤ S.card ∧ S.card ≤ P.κ E ∧
          P.Δ * S.card + P.B E ≤ onesInRows c σ (topRows m P.g1) S).card : ℝ) ≤
      Real.exp (-10 * E) * Fintype.card (Scramble m n) := by
  classical
  have hn0 : 0 < n := by omega
  obtain ⟨hj1, hjD, hjE, -⟩ := jE_facts P hf hn hE
  obtain ⟨hα, hRs, hNb⟩ := hnum
  have hE2 : (2 : ℝ) ≤ E := by exact_mod_cast hE
  set j := P.jE n E with hjdef
  set κ := P.κ E with hκ
  have hκE : (κ : ℝ) < P.c * E + 1 := by
    simp only [hκ, F2Params.κ]; exact Nat.ceil_lt_add_one (by rw [hc]; positivity)
  have hκB : κ ≤ P.B E := by
    simp only [hκ, F2Params.κ, F2Params.B]
    exact Nat.ceil_mono (by rw [hc, hb]; nlinarith)
  have hBr : P.b * E ≤ (P.B E : ℝ) := Nat.le_ceil _
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
  have hD1 : (128 / 4095 : ℝ) * P.f ≤ (P.Δ : ℝ) + 1 := P.hD1
  have hjn : (j : ℝ) / n ≤ (P.Δ : ℝ) + 1 := by
    rw [div_le_iff₀ hn0r]; nlinarith
  have hjn' := (div_le_iff₀ hn0r).mp hjn
  have hjg : j ≤ (P.g1 + 1) ^ 2 * n := by
    have h1 : (j : ℝ) ≤ ((P.g1 : ℝ) + 1) ^ 2 * n := by
      have := P.hD3
      calc (j : ℝ) ≤ (128 / 4095 : ℝ) * P.f * n := hjD
        _ ≤ _ := mul_le_mul_of_nonneg_right this hn0r.le
    exact_mod_cast h1
  have htops := tops_card_le_gen P.g1 n j hn0 hj1 hjg
  have hScr : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  have hper : ∀ s ∈ Finset.Icc 1 κ,
      ((Finset.univ.filter fun σ : Scramble m n => ∃ c : MonotoneColumnSums m n,
        totalColumnOnes c ≤ j ∧ σ ∈ tailBadSet c (topRows m P.g1) s
          ((P.Δ * s + P.B E : ℕ) : ℝ)).card : ℝ) ≤
        Real.exp (-16 * E) * Fintype.card (Scramble m n) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    obtain ⟨hs1, hsκ⟩ := hs
    have hs0 : 0 < s := hs1
    have hs0r : (0 : ℝ) < s := by exact_mod_cast hs0
    have hsB : s ≤ P.B E := hsκ.trans hκB
    have hsb : (s : ℝ) ≤ P.b * E := by
      have : (s : ℝ) ≤ κ := by exact_mod_cast hsκ
      rw [hc] at hκE; rw [hb]; linarith
    set T : ℕ := P.Δ * s + P.B E with hT
    have hTr : (T : ℝ) = (P.Δ : ℝ) * s + (P.B E : ℝ) := by rw [hT]; push_cast; ring
    have hB : ∀ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j →
        ((tailBadSet c (topRows m P.g1) s (T : ℝ)).card : ℝ) ≤
          ((n.choose s : ℝ) * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ)) *
            Fintype.card (Scramble m n) := by
      intro c hcj
      refine tail_union_le hn0 c P.g1 s (j : ℝ) (T : ℝ) hjpos (by exact_mod_cast hcj) hs0 ?_
      have hsBr : (s : ℝ) ≤ (P.B E : ℝ) := by exact_mod_cast hsB
      rw [hTr, div_le_iff₀ hn0r]
      nlinarith [mul_le_mul_of_nonneg_right hjn' hs0r.le]
    have hBnn : (0 : ℝ) ≤ (n.choose s : ℝ) * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ) := by
      positivity
    have hmain := bad_card_le_tops (m := m) (n := n) P.g1 j
      (fun c => tailBadSet c (topRows m P.g1) s (T : ℝ)) _ hBnn
      (fun c c' h => tailBadSet_eq_of_top c c' h s (T : ℝ)) hB
    have hchoose : (n.choose s : ℝ) ≤ (Real.exp 1 * n / s) ^ s := choose_le_exp_pow n hs1
    have hreal := R1b_real (n := n) (j := j) (s := s) (E := E) (G := (P.g1 : ℝ) + 1)
      (Dl := (P.Δ : ℝ)) (D := (128 / 4095 : ℝ) * P.f) (J := (P.J : ℝ)) (bb := P.b)
      (Bn := (P.B E : ℝ))
      hn0 hj1 hjD hjE hs1 hsb hBr (by positivity)
      (by exact_mod_cast (show 1 ≤ P.Δ from by
        unfold F2Params.Δ; have := P.hg12; omega))
      (by have : (0 : ℝ) < P.f := by exact_mod_cast (by have := P.hg2f; omega : 0 < P.f)
          positivity)
      hD1 (by exact_mod_cast P.hJ) P.hb0 P.hbJ hα (log_D_le P) hRs hNb hE
    have hAnn : 0 ≤ ((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
        (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) := by
      positivity
    have hZnn : 0 ≤ (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ) := by positivity
    calc _ ≤ _ := hmain
      _ ≤ (((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
          (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) *
            ((n.choose s : ℝ) * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ))) *
            Fintype.card (Scramble m n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htops hBnn) hScr
      _ ≤ (((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
          (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) *
            ((Real.exp 1 * n / s) ^ s * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ))) *
            Fintype.card (Scramble m n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hchoose hZnn) hAnn) hScr
      _ = (((j : ℝ) / ((P.g1 : ℝ) + 1) + 1) *
          (Real.exp 1 ^ 2 * n * ((P.g1 : ℝ) + 1) ^ 2 / j) ^ ((j : ℝ) / ((P.g1 : ℝ) + 1)) *
            (Real.exp 1 * n / s) ^ s * (Real.exp 1 * j * s / (n * T)) ^ (T : ℝ)) *
            Fintype.card (Scramble m n) := by ring
      _ ≤ Real.exp (-16 * E) * Fintype.card (Scramble m n) := by
          refine mul_le_mul_of_nonneg_right ?_ hScr
          rw [hTr]; exact hreal
  have hsub : (Finset.univ.filter fun σ : Scramble m n => ∃ c : MonotoneColumnSums m n,
        totalColumnOnes c ≤ j ∧ ∃ S : Finset (Fin n), 1 ≤ S.card ∧ S.card ≤ κ ∧
          P.Δ * S.card + P.B E ≤ onesInRows c σ (topRows m P.g1) S) ⊆
      (Finset.Icc 1 κ).biUnion fun s => Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j ∧ σ ∈ tailBadSet c (topRows m P.g1) s
          ((P.Δ * s + P.B E : ℕ) : ℝ) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨c, hc1, S, hS1, hS2, hS3⟩ := hσ
    refine Finset.mem_biUnion.mpr ⟨S.card, Finset.mem_Icc.mpr ⟨hS1, hS2⟩, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨c, hc1, ?_⟩
    simp only [tailBadSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩, by exact_mod_cast hS3⟩
  have hκ_le : (κ : ℝ) ≤ E := by rw [hc] at hκE; linarith
  have hexpE : (E : ℝ) ≤ Real.exp (6 * E) := by
    have := Real.add_one_le_exp (6 * (E : ℝ))
    linarith
  calc _ ≤ (((Finset.Icc 1 κ).biUnion fun s => Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j ∧ σ ∈ tailBadSet c (topRows m P.g1) s
          ((P.Δ * s + P.B E : ℕ) : ℝ)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ s ∈ Finset.Icc 1 κ, ((Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j ∧ σ ∈ tailBadSet c (topRows m P.g1) s
          ((P.Δ * s + P.B E : ℕ) : ℝ)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ s ∈ Finset.Icc 1 κ, Real.exp (-16 * E) * Fintype.card (Scramble m n) :=
        Finset.sum_le_sum hper
    _ = κ * (Real.exp (-16 * E) * Fintype.card (Scramble m n)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ E * (Real.exp (-16 * E) * Fintype.card (Scramble m n)) :=
        mul_le_mul_of_nonneg_right hκ_le (by positivity)
    _ ≤ Real.exp (6 * E) * (Real.exp (-16 * E) * Fintype.card (Scramble m n)) :=
        mul_le_mul_of_nonneg_right hexpE (by positivity)
    _ = Real.exp (-10 * E) * Fintype.card (Scramble m n) := by
        rw [← mul_assoc, ← Real.exp_add]; ring_nf

/-! ## Part 4: summing over `E` -/

lemma exp_ten_ge : (22000 : ℝ) ≤ Real.exp 10 := by
  have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have : Real.exp 10 = Real.exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (22000 : ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 10

lemma sum_exp_Ico_le (N : ℕ) :
    ∑ E ∈ Finset.Ico 2 N, Real.exp (-10 * (E : ℝ)) ≤ 1 / 20000 := by
  set x : ℝ := Real.exp (-10) with hx
  have hx0 : 0 < x := Real.exp_pos _
  have hx1 : x ≤ 1 / 22000 := by
    rw [hx, Real.exp_neg, ← one_div, one_div_le_one_div (Real.exp_pos _) (by norm_num)]
    exact exp_ten_ge
  have hpow : ∀ E : ℕ, Real.exp (-10 * (E : ℝ)) = x ^ E := fun E => by
    rw [hx, ← Real.exp_nat_mul]; ring_nf
  simp_rw [hpow]
  refine (geom_sum_Ico_le_of_lt_one hx0.le (by linarith)).trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith

open Classical in
theorem F2R1a_fail (P : F2Params) (hc : P.c = 1 / 3) (hf : 131040 ≤ P.f) (hnum : R1aNum P)
    {m n : ℕ} (hn : 16 ≤ n) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ F2R1a P σ).card : ℝ) ≤
      (1 / 20000) * Fintype.card (Scramble m n) := by
  classical
  have hsub : (Finset.univ.filter fun σ : Scramble m n => ¬ F2R1a P σ) ⊆
      (Finset.Ico 2 (3 * P.jmax n)).biUnion fun E => Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E ∧
          ∃ S : Finset (Fin n), S.card = P.κ E + 1 ∧
            (P.Δ + 1) * (P.κ E + 1) ≤ onesInRows c σ (topRows m P.g1) S := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, F2R1a] at hσ
    push_neg at hσ
    obtain ⟨E, hE, c, hcj, S, hS, hS2⟩ := hσ
    refine Finset.mem_biUnion.mpr ⟨E, Finset.mem_Ico.mpr ⟨hE, ?_⟩, ?_⟩
    · by_contra hlt
      push_neg at hlt
      obtain ⟨hj1, -, -, hjm⟩ := jE_facts P hf hn hE
      have hκ : P.jmax n ≤ P.κ E := by
        have : (P.jmax n : ℝ) ≤ P.κ E := by
          have h1 : (3 * P.jmax n : ℝ) ≤ E := by exact_mod_cast hlt
          have h2 : P.c * E ≤ (P.κ E : ℝ) := Nat.le_ceil _
          rw [hc] at h2; linarith
        exact_mod_cast this
      have h3 : onesInRows c σ (topRows m P.g1) S ≤ P.jmax n :=
        (onesInRows_le_total _ _ _ _).trans (hcj.trans hjm)
      have h4 : P.κ E + 1 ≤ (P.Δ + 1) * (P.κ E + 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨c, hcj, S, hS, hS2⟩
  have hScr : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  calc _ ≤ (((Finset.Ico 2 (3 * P.jmax n)).biUnion fun E =>
        Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E ∧
          ∃ S : Finset (Fin n), S.card = P.κ E + 1 ∧
            (P.Δ + 1) * (P.κ E + 1) ≤ onesInRows c σ (topRows m P.g1) S).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ E ∈ Finset.Ico 2 (3 * P.jmax n), ((Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E ∧
          ∃ S : Finset (Fin n), S.card = P.κ E + 1 ∧
            (P.Δ + 1) * (P.κ E + 1) ≤ onesInRows c σ (topRows m P.g1) S).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ E ∈ Finset.Ico 2 (3 * P.jmax n), Real.exp (-10 * (E : ℝ)) *
          Fintype.card (Scramble m n) :=
        Finset.sum_le_sum fun E hE =>
          R1a_event_card_le P hc hf hnum hn (Finset.mem_Ico.mp hE).1
    _ = (∑ E ∈ Finset.Ico 2 (3 * P.jmax n), Real.exp (-10 * (E : ℝ))) *
          Fintype.card (Scramble m n) := by rw [Finset.sum_mul]
    _ ≤ (1 / 20000) * Fintype.card (Scramble m n) :=
        mul_le_mul_of_nonneg_right (sum_exp_Ico_le _) hScr

open Classical in
theorem F2R1b_fail (P : F2Params) (hc : P.c = 1 / 3) (hb : P.b = 17000) (hf : 131040 ≤ P.f)
    (hnum : R1bNum P) {m n : ℕ} (hn : 16 ≤ n) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ F2R1b P σ).card : ℝ) ≤
      (1 / 20000) * Fintype.card (Scramble m n) := by
  classical
  have hsub : (Finset.univ.filter fun σ : Scramble m n => ¬ F2R1b P σ) ⊆
      (Finset.Ico 2 (3 * P.jmax n)).biUnion fun E => Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E ∧
          ∃ S : Finset (Fin n), 1 ≤ S.card ∧ S.card ≤ P.κ E ∧
            P.Δ * S.card + P.B E ≤ onesInRows c σ (topRows m P.g1) S := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, F2R1b] at hσ
    push_neg at hσ
    obtain ⟨E, hE, c, hcj, S, hS1, hS2, hS3⟩ := hσ
    refine Finset.mem_biUnion.mpr ⟨E, Finset.mem_Ico.mpr ⟨hE, ?_⟩, ?_⟩
    · by_contra hlt
      push_neg at hlt
      obtain ⟨hj1, -, -, hjm⟩ := jE_facts P hf hn hE
      have hB : 3 * P.jmax n ≤ P.B E := by
        have h1 : (3 * P.jmax n : ℝ) ≤ E := by exact_mod_cast hlt
        have h2 : P.b * E ≤ (P.B E : ℝ) := Nat.le_ceil _
        have h3 : (E : ℝ) ≤ P.b * E := by rw [hb]; nlinarith
        exact_mod_cast h1.trans (h3.trans h2)
      have h3 : onesInRows c σ (topRows m P.g1) S ≤ P.jmax n :=
        (onesInRows_le_total _ _ _ _).trans (hcj.trans hjm)
      omega
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨c, hcj, S, hS1, hS2, hS3⟩
  have hScr : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  calc _ ≤ (((Finset.Ico 2 (3 * P.jmax n)).biUnion fun E =>
        Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E ∧
          ∃ S : Finset (Fin n), 1 ≤ S.card ∧ S.card ≤ P.κ E ∧
            P.Δ * S.card + P.B E ≤ onesInRows c σ (topRows m P.g1) S).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ E ∈ Finset.Ico 2 (3 * P.jmax n), ((Finset.univ.filter fun σ : Scramble m n =>
        ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E ∧
          ∃ S : Finset (Fin n), 1 ≤ S.card ∧ S.card ≤ P.κ E ∧
            P.Δ * S.card + P.B E ≤ onesInRows c σ (topRows m P.g1) S).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ E ∈ Finset.Ico 2 (3 * P.jmax n), Real.exp (-10 * (E : ℝ)) *
          Fintype.card (Scramble m n) :=
        Finset.sum_le_sum fun E hE =>
          R1b_event_card_le P hc hb hf hnum hn (Finset.mem_Ico.mp hE).1
    _ = (∑ E ∈ Finset.Ico 2 (3 * P.jmax n), Real.exp (-10 * (E : ℝ))) *
          Fintype.card (Scramble m n) := by rw [Finset.sum_mul]
    _ ≤ (1 / 20000) * Fintype.card (Scramble m n) :=
        mul_le_mul_of_nonneg_right (sum_exp_Ico_le _) hScr

open Classical in
/-- Assembly, given the numeric hypotheses. -/
theorem F2R1_fail_of_num (P : F2Params) (hc : P.c = 1 / 3) (hb : P.b = 17000)
    (hf : 131040 ≤ P.f) (ha : R1aNum P) (hbn : R1bNum P) {m n : ℕ} (hn : 16 ≤ n) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ F2R1 P σ).card : ℝ) ≤
      (1 / 10000) * Fintype.card (Scramble m n) := by
  classical
  have hsub : (Finset.univ.filter fun σ : Scramble m n => ¬ F2R1 P σ) ⊆
      (Finset.univ.filter fun σ : Scramble m n => ¬ F2R1a P σ) ∪
        (Finset.univ.filter fun σ : Scramble m n => ¬ F2R1b P σ) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, F2R1] at hσ ⊢
    by_contra h
    push_neg at h
    exact hσ ⟨h.1, h.2⟩
  have h1 := F2R1a_fail P hc hf ha (m := m) hn
  have h2 := F2R1b_fail P hc hb hf hbn (m := m) hn
  have h3 : (((Finset.univ.filter fun σ : Scramble m n => ¬ F2R1 P σ)).card : ℝ) ≤
      ((Finset.univ.filter fun σ : Scramble m n => ¬ F2R1a P σ).card : ℝ) +
        ((Finset.univ.filter fun σ : Scramble m n => ¬ F2R1b P σ).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  linarith

/-! ## Part 5: the numerics at `f = 131040` -/

lemma log_ge_pow {y q : ℝ} {k : ℕ} (hq : 0 < q) (h : q ^ k ≤ y) :
    (k : ℝ) * (1 - q⁻¹) ≤ Real.log y := by
  have hpos : 0 < q ^ k := by positivity
  calc (k : ℝ) * (1 - q⁻¹) ≤ k * Real.log q :=
        mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hq) (Nat.cast_nonneg _)
    _ = Real.log (q ^ k) := by rw [Real.log_pow]
    _ ≤ Real.log y := Real.log_le_log hpos h

lemma log_le_pow {y q : ℝ} {k : ℕ} (hq : 0 < q) (hy : 0 < y) (h : y ≤ q ^ k) :
    Real.log y ≤ k * (q - 1) := by
  calc Real.log y ≤ Real.log (q ^ k) := Real.log_le_log hy h
    _ = k * Real.log q := by rw [Real.log_pow]
    _ ≤ k * (q - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hq) (Nat.cast_nonneg _)

lemma log_two_pow (k : ℕ) : Real.log ((2 : ℝ) ^ k) = k * Real.log 2 := by rw [Real.log_pow]

lemma log_52416_ge : (10.85 : ℝ) ≤ Real.log 52416 := by
  have h := log_ge_pow (y := (52416 : ℝ)) (q := 1.0604) (k := 8) (by norm_num) (by norm_num)
  have h2 : Real.log ((2 : ℝ) ^ 15 * 1.0604 ^ 8) ≤ Real.log 52416 :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_mul (by positivity) (by positivity), log_two_pow, Real.log_pow] at h2
  have h3 := Real.log_two_gt_d9
  have h4 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1.0604 by norm_num)
  have h5 : (8 : ℝ) * (1 - (1.0604 : ℝ)⁻¹) ≤ 8 * Real.log 1.0604 :=
    mul_le_mul_of_nonneg_left h4 (by norm_num)
  push_cast at h2
  norm_num at h5 h2
  linarith

lemma log_52417_le : Real.log 52417 ≤ 10.89 := by
  have h2 : Real.log 52417 ≤ Real.log ((2 : ℝ) ^ 15 * 1.0605 ^ 8) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_mul (by positivity) (by positivity), log_two_pow, Real.log_pow] at h2
  have h3 := Real.log_two_lt_d9
  have h4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.0605 by norm_num)
  have h5 : (8 : ℝ) * Real.log 1.0605 ≤ 8 * (1.0605 - 1) :=
    mul_le_mul_of_nonneg_left h4 (by norm_num)
  push_cast at h2
  norm_num at h5 h2
  linarith

lemma log_52417_ge : (10.85 : ℝ) ≤ Real.log 52417 :=
  log_52416_ge.trans (Real.log_le_log (by norm_num) (by norm_num))

lemma log_4096 : Real.log 4096 = 12 * Real.log 2 := by
  rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]; norm_num

lemma log_258e6_le : Real.log 258000000 ≤ 19.41 := by
  have h2 : Real.log 258000000 ≤ Real.log ((2 : ℝ) ^ 28) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [log_two_pow] at h2
  have h3 := Real.log_two_lt_d9
  push_cast at h2
  linarith

lemma log_86e6_le : Real.log 86000000 ≤ 18.72 := by
  have h2 : Real.log 86000000 ≤ Real.log ((2 : ℝ) ^ 27) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [log_two_pow] at h2
  have h3 := Real.log_two_lt_d9
  push_cast at h2
  linarith

theorem R1aNum_std (P : F2Params) (hf : P.f = 131040) (hg1 : P.g1 = 52416)
    (hg2 : P.g2 = 104832) (hJ : P.J = 86000000) (hc : P.c = 1 / 3) : R1aNum P := by
  have hΔ : P.Δ = 52416 := by unfold F2Params.Δ; omega
  unfold R1aNum
  rw [hΔ, hg1, hf, hJ, hc]
  have h1 := log_52417_ge
  have h2 := log_52417_le
  have h3 := log_258e6_le
  have eD : (128 / 4095 : ℝ) * ((131040 : ℕ) : ℝ) = 4096 := by norm_num
  have eG : ((52416 : ℕ) : ℝ) + 1 = 52417 := by norm_num
  have eJ : ((86000000 : ℕ) : ℝ) / (1 / 3) = 258000000 := by norm_num
  simp only [eD, eG, eJ]
  simp only [Nat.cast_ofNat]
  have h1 := log_52417_ge
  have h2 := log_52417_le
  have h3 := log_258e6_le
  have h4 := log_4096
  have h5 := Real.log_two_lt_d9
  have h6 := Real.log_two_gt_d9
  refine ⟨by norm_num, ?_, ?_⟩
  · linarith
  · linarith
theorem R1bNum_std (P : F2Params) (hf : P.f = 131040) (hg1 : P.g1 = 52416)
    (hg2 : P.g2 = 104832) (hJ : P.J = 86000000) (hb : P.b = 17000) : R1bNum P := by
  have hΔ : P.Δ = 52416 := by unfold F2Params.Δ; omega
  unfold R1bNum
  rw [hΔ, hg1, hf, hJ, hb]
  have eD : (128 / 4095 : ℝ) * ((131040 : ℕ) : ℝ) = 4096 := by norm_num
  have eG : ((52416 : ℕ) : ℝ) + 1 = 52417 := by norm_num
  simp only [eD, eG]
  simp only [Nat.cast_ofNat]
  have h0 := log_52416_ge
  have h2 := log_52417_le
  have h3 := log_86e6_le
  have h4 := log_4096
  have h5 := Real.log_two_lt_d9
  have h6 := Real.log_two_gt_d9
  refine ⟨by norm_num, ?_, ?_⟩
  · linarith
  · linarith


/-! ## Part 6: the numerics for every `f ≥ 131040` -/

lemma log_5_2_le : Real.log 5.2 ≤ 1.7 := by
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.7 by norm_num)
  have h3 : Real.exp 1.7 = Real.exp 1 * Real.exp 0.7 := by rw [← Real.exp_add]; norm_num
  rw [Real.log_le_iff_le_exp (by norm_num), h3]
  nlinarith

lemma log_131040_le : Real.log 131040 ≤ 11.785 := by
  have h2 : Real.log 131040 ≤ Real.log ((2 : ℝ) ^ 17) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [log_two_pow] at h2
  have h3 := Real.log_two_lt_d9
  push_cast at h2
  linarith

lemma log_1279_ge : (2.534 : ℝ) ≤ Real.log 12.79 := by
  have h2 : Real.log ((2 : ℝ) ^ 3 * 1.0603 ^ 8) ≤ Real.log 12.79 :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_mul (by positivity) (by positivity), log_two_pow, Real.log_pow] at h2
  have h3 := Real.log_two_gt_d9
  have h4 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1.0603 by norm_num)
  have h5 : (8 : ℝ) * (1 - (1.0603 : ℝ)⁻¹) ≤ 8 * Real.log 1.0603 :=
    mul_le_mul_of_nonneg_left h4 (by norm_num)
  push_cast at h2
  norm_num at h5 h2
  linarith

lemma alpha_A_le (f G : ℝ) (hf : 131040 ≤ f) (hG1 : 2 * f / 5 < G) (hG2 : G ≤ 2 * f / 5 + 1) :
    (86000000 : ℝ) / G * (2 + 2 * Real.log G - Real.log (128 / 4095 * f)) ≤ 25410 := by
  have hf0 : 0 < f := by linarith
  have hG0 : 0 < G := by linarith
  have hD0 : 0 < 128 / 4095 * f := by positivity
  have hGD : G ^ 2 / (128 / 4095 * f) ≤ 5.2 * f := by
    rw [div_le_iff₀ hD0]
    nlinarith [mul_pos hf0 hf0]
  have hA : 2 + 2 * Real.log G - Real.log (128 / 4095 * f) ≤ 14.485 + f / 131040 := by
    have h1 : 2 * Real.log G - Real.log (128 / 4095 * f) =
        Real.log (G ^ 2 / (128 / 4095 * f)) := by
      rw [Real.log_div (by positivity) hD0.ne', Real.log_pow]; push_cast; ring
    have h2 : Real.log (G ^ 2 / (128 / 4095 * f)) ≤ Real.log (5.2 * f) :=
      Real.log_le_log (by positivity) hGD
    have h3 : Real.log (5.2 * f) = Real.log 5.2 + Real.log f :=
      Real.log_mul (by norm_num) hf0.ne'
    have h4 : Real.log f ≤ Real.log 131040 + (f / 131040 - 1) := by
      have := Real.log_le_sub_one_of_pos (show 0 < f / 131040 by positivity)
      rw [Real.log_div hf0.ne' (by norm_num)] at this
      linarith
    linarith [log_5_2_le, log_131040_le]
  have hα : (86000000 : ℝ) / G ≤ 215000000 / f := by
    rw [div_le_div_iff₀ hG0 hf0]; nlinarith
  have hα0 : (0 : ℝ) ≤ 86000000 / G := by positivity
  calc (86000000 : ℝ) / G * (2 + 2 * Real.log G - Real.log (128 / 4095 * f))
      ≤ 86000000 / G * (14.485 + f / 131040) := mul_le_mul_of_nonneg_left hA hα0
    _ ≤ 215000000 / f * (14.485 + f / 131040) :=
        mul_le_mul_of_nonneg_right hα (by positivity)
    _ = 215000000 * 14.485 / f + 215000000 / 131040 := by field_simp
    _ ≤ 215000000 * 14.485 / 131040 + 215000000 / 131040 := by
        gcongr
    _ ≤ 25410 := by norm_num

lemma ratio_ge (f Dl : ℝ) (hf : 131040 ≤ f) (hDl : 2 * f / 5 - 1 < Dl) :
    (2.534 : ℝ) ≤ Real.log Dl - Real.log (128 / 4095 * f) := by
  have hD0 : 0 < 128 / 4095 * f := by positivity
  have hDl0 : 0 < Dl := by linarith
  rw [← Real.log_div hDl0.ne' hD0.ne']
  have : (12.79 : ℝ) ≤ Dl / (128 / 4095 * f) := by
    rw [le_div_iff₀ hD0]; nlinarith
  exact log_1279_ge.trans (Real.log_le_log (by norm_num) this)

theorem numeric_core (f G Dl : ℝ) (hf : 131040 ≤ f) (hG1 : 2 * f / 5 < G)
    (hG2 : G ≤ 2 * f / 5 + 1) (hDl : 2 * f / 5 - 1 < Dl) :
    (86000000 : ℝ) / G ≤ 1641 ∧
    0 ≤ (Dl + 1) * (Real.log (Dl + 1) - 1) - 1 - Real.log (86000000 / (1 / 3)) -
      Dl * Real.log (128 / 4095 * f) ∧
    86000000 / G * (2 + 2 * Real.log G - Real.log (128 / 4095 * f)) -
      1 / 3 * ((Dl + 1) * (Real.log (Dl + 1) - 1) - 1 - Real.log (86000000 / (1 / 3)) -
        Dl * Real.log (128 / 4095 * f)) ≤ -15 ∧
    1 + Real.log 86000000 + Dl * (1 - Real.log Dl) +
      (1 - Dl) * (-Real.log (128 / 4095 * f)) ≤ 0 ∧
    86000000 / G * (2 + 2 * Real.log G - Real.log (128 / 4095 * f)) +
      17000 * (1 + Real.log (128 / 4095 * f) - Real.log Dl) ≤ -22 := by
  have hf0 : 0 < f := by linarith
  have hG0 : 0 < G := by linarith
  have hD0 : 0 < 128 / 4095 * f := by positivity
  have hDl0 : 0 < Dl := by linarith
  have hlD : 0 ≤ Real.log (128 / 4095 * f) :=
    Real.log_nonneg (by nlinarith)
  have hr := ratio_ge f Dl hf hDl
  have hαA := alpha_A_le f G hf hG1 hG2
  have hu : Real.log Dl ≤ Real.log (Dl + 1) := Real.log_le_log hDl0 (by linarith)
  have hJ : Real.log (86000000 / (1 / 3) : ℝ) ≤ 19.41 := by
    have e : (86000000 : ℝ) / (1 / 3) = 258000000 := by norm_num
    rw [e]; exact log_258e6_le
  have hJ2 := log_86e6_le
  have hprod : (Dl + 1) * (Real.log (128 / 4095 * f) + 1.534) ≤
      (Dl + 1) * (Real.log (Dl + 1) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hQ : 0.6136 * f - 20.5 ≤ (Dl + 1) * (Real.log (Dl + 1) - 1) - 1 -
      Real.log (86000000 / (1 / 3)) - Dl * Real.log (128 / 4095 * f) := by
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hG0]; nlinarith
  · linarith
  · linarith
  · have h1 : Dl * (1 - Real.log Dl + Real.log (128 / 4095 * f)) ≤ Dl * (1 - 2.534) :=
      mul_le_mul_of_nonneg_left (by linarith) hDl0.le
    nlinarith
  · linarith


/-! ## Part 7: the main theorem -/

theorem R1num_of_params (P : F2Params) (hf : 131040 ≤ P.f) (hg1 : P.g1 = 2 * P.f / 5)
    (hg2 : P.g2 = 4 * P.f / 5) (hc : P.c = 1 / 3) (hb : P.b = 17000) (hJ : P.J = 86000000) :
    R1aNum P ∧ R1bNum P := by
  have n1 : 5 * P.g1 ≤ 2 * P.f ∧ 2 * P.f < 5 * P.g1 + 5 := by omega
  have n3 : 2 * P.f < 5 * P.Δ + 5 := by
    unfold F2Params.Δ; have := P.hg12; omega
  have r1 : (5 : ℝ) * P.g1 ≤ 2 * P.f := by exact_mod_cast n1.1
  have r2 : (2 : ℝ) * P.f < 5 * P.g1 + 5 := by exact_mod_cast n1.2
  have r3 : (2 : ℝ) * P.f < 5 * P.Δ + 5 := by exact_mod_cast n3
  have hf' : (131040 : ℝ) ≤ P.f := by exact_mod_cast hf
  obtain ⟨c1, c2, c3, c4, c5⟩ := numeric_core (P.f : ℝ) ((P.g1 : ℝ) + 1) (P.Δ : ℝ) hf'
    (by linarith) (by linarith) (by linarith)
  refine ⟨?_, ?_⟩
  · unfold R1aNum
    simp only [hJ, hc, Nat.cast_ofNat]
    exact ⟨c1, c2, c3⟩
  · unfold R1bNum
    simp only [hJ, hb, Nat.cast_ofNat]
    exact ⟨c1, c4, c5⟩

open Classical in
/-- **Failure probability of `F2R1`.**  For every `P` with `131040 ≤ P.f`, `g1 = 2f/5`,
`g2 = 4f/5`, `c = 1/3`, `b = 17000`, `J = 86·10⁶`, every `n ≥ 16` and `m ≥ f`, at most a
`1/10000` fraction of scrambles violate `F2R1`. -/
theorem F2R1_fail (P : F2Params) (hf : 131040 ≤ P.f) (hg1 : P.g1 = 2 * P.f / 5)
    (hg2 : P.g2 = 4 * P.f / 5) (hc : P.c = 1 / 3) (hb : P.b = 17000) (hJ : P.J = 86000000)
    {m n : ℕ} (hn : 16 ≤ n) (hm : P.f ≤ m) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ F2R1 P σ).card : ℝ) ≤
      (1 / 10000) * Fintype.card (Scramble m n) := by
  obtain ⟨ha, hbn⟩ := R1num_of_params P hf hg1 hg2 hc hb hJ
  exact F2R1_fail_of_num P hc hb hf ha hbn hn

open Classical in
/-- The `f = 131040` instance. -/
theorem F2R1_fail_std {m n : ℕ} (hn : 16 ≤ n) (hm : 131040 ≤ m) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ F2R1 F2Params.std σ).card : ℝ) ≤
      (1 / 10000) * Fintype.card (Scramble m n) :=
  F2R1_fail F2Params.std (by norm_num [F2Params.std]) (by norm_num [F2Params.std])
    (by norm_num [F2Params.std]) (by norm_num [F2Params.std]) (by norm_num [F2Params.std])
    (by norm_num [F2Params.std]) hn hm

-- Separate statements for R1(a) and R1(b) at `f = 131040`.
open Classical in
theorem F2R1a_fail_std {m n : ℕ} (hn : 16 ≤ n) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ F2R1a F2Params.std σ).card : ℝ) ≤
      (1 / 20000) * Fintype.card (Scramble m n) :=
  F2R1a_fail F2Params.std (by norm_num [F2Params.std]) (by norm_num [F2Params.std])
    (R1aNum_std F2Params.std rfl rfl rfl rfl rfl) hn

open Classical in
theorem F2R1b_fail_std {m n : ℕ} (hn : 16 ≤ n) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ F2R1b F2Params.std σ).card : ℝ) ≤
      (1 / 20000) * Fintype.card (Scramble m n) :=
  F2R1b_fail F2Params.std (by norm_num [F2Params.std]) (by norm_num [F2Params.std])
    (by norm_num [F2Params.std]) (R1bNum_std F2Params.std rfl rfl rfl rfl rfl) hn

end Chvatal
