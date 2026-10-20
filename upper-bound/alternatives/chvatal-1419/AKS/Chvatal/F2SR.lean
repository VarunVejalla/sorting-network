module

public import AKS.Chvatal.F2Defs
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Small-rank failure bound for the two-round contract (`F2ROUND.md` §4-5)

`F2SR_fail_card_le`: for `131040 ≤ f`, `g1 = 2f/5`, `J = 86·10⁶`, `16 ≤ n`, the scrambles
violating `F2SmallRank` have density at most `1/10000`.

Proof: union over the tops of matrices of total at most `j0 = min J Jmax` and over single columns of
the tail event `T0 ≤ onesInRows` (`scramble_tail_fixed_set`), `T0 = f - g1 + 1`.  The tops are
counted crudely by `(K+1) (n j0)^K`, `K = j0/(g1+1) ≤ 1641`.  The tail base `b = e j0/(n T0)` is
at most `e J/(n T0)` (used `K+1` times, cancelling the `n`-dependence of the tops count) and at most
`1/7` (used for the remaining `T0 - K - 1 ≥ 70000` factors).  Uniform in `n ≥ 16` and `f`. -/

@[expose] public section

namespace Chvatal

open Finset

/-- Crude count of tops: `(K+1) (n j)^K` with `K = j/(g+1)`. -/
theorem tops_card_le_crude (g n j : ℕ) (hn : 0 < n) (hj : 0 < j) :
    (tops g n j).card ≤ (j / (g + 1) + 1) * (n * j) ^ (j / (g + 1)) := by
  refine (tops_card_le g n j).trans ?_
  unfold topClosed
  set K := j / (g + 1) with hK
  have hnj : 1 ≤ n * j := Nat.mul_pos hn hj
  have hterm : ∀ k ∈ Finset.range (n + 1),
      Nat.choose n k * Nat.choose (j - g * k) k ≤ if k ≤ K then (n * j) ^ K else 0 := by
    intro k _
    split_ifs with hk
    · calc Nat.choose n k * Nat.choose (j - g * k) k ≤ n ^ k * j ^ k :=
            Nat.mul_le_mul (Nat.choose_le_pow _ _)
              ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _))
        _ = (n * j) ^ k := (mul_pow _ _ _).symm
        _ ≤ (n * j) ^ K := Nat.pow_le_pow_right hnj hk
    · have hlt : j < k * (g + 1) := (Nat.div_lt_iff_lt_mul (by omega)).mp (not_le.mp hk)
      have hkk : k * (g + 1) = g * k + k := by ring
      have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hk (Nat.zero_le _))
      have : j - g * k < k := by
        generalize g * k = x at hkk
        omega
      rw [Nat.choose_eq_zero_of_lt this]; simp
  calc _ ≤ ∑ k ∈ Finset.range (n + 1), if k ≤ K then (n * j) ^ K else 0 :=
        Finset.sum_le_sum hterm
    _ = ((Finset.range (n + 1)).filter (· ≤ K)).card * (n * j) ^ K := by
        rw [← Finset.sum_filter]; simp
    _ ≤ (K + 1) * (n * j) ^ K := by
        gcongr
        calc ((Finset.range (n + 1)).filter (· ≤ K)).card ≤ (Finset.range (K + 1)).card :=
              Finset.card_le_card (fun k hk => by
                simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; omega)
          _ = K + 1 := Finset.card_range _

/-- Union bound over tops and single columns. -/
theorem F2SR_union_bound {m n : ℕ} (g j0 T : ℕ) (hn : 0 < n) (hj0 : 0 < j0)
    (hT : (j0 : ℝ) / n ≤ (T : ℝ)) (bad : Finset (Scramble m n))
    (hbad : ∀ σ ∈ bad, ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j0 ∧
      ∃ S : Finset (Fin n), S.card = 1 ∧ T ≤ onesInRows c σ (topRows m g) S) :
    (bad.card : ℝ) ≤ ((tops g n j0).card : ℝ) *
      ((n : ℝ) * (Real.exp 1 * j0 / (n * (T : ℝ))) ^ (T : ℝ)) *
        (Fintype.card (Scramble m n) : ℝ) := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have htot : (0 : ℝ) < Fintype.card (Scramble m n) := by exact_mod_cast Fintype.card_pos
  let P : (Fin n → ℕ) → Prop := fun t =>
    ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j0 ∧ topOf g c = t
  let rep : (Fin n → ℕ) → MonotoneColumnSums m n := fun t =>
    if h : P t then Classical.choose h else fun _ => 0
  have hrep : ∀ t, P t → totalColumnOnes (rep t) ≤ j0 ∧ topOf g (rep t) = t := fun t ht => by
    simp only [rep, dif_pos ht]
    exact Classical.choose_spec ht
  let I : Finset (Fin n → ℕ) := (tops g n j0).filter P
  let U : (Fin n → ℕ) → Fin n → Finset (Scramble m n) := fun t col =>
    Finset.univ.filter fun σ => (T : ℝ) ≤ (onesInRows (rep t) σ (topRows m g) {col} : ℝ)
  have hsub : bad ⊆ I.biUnion fun t => (Finset.univ : Finset (Fin n)).biUnion (U t) := by
    intro σ hσ
    obtain ⟨c, hc, S, hS, hX⟩ := hbad σ hσ
    obtain ⟨col, rfl⟩ := Finset.card_eq_one.mp hS
    have hPt : P (topOf g c) := ⟨c, hc, rfl⟩
    obtain ⟨-, hrt⟩ := hrep _ hPt
    have h' : T ≤ onesInRows (rep (topOf g c)) σ (topRows m g) {col} := by
      rwa [onesInRows_topRows_depends_only_on_top (rep (topOf g c)) c
        (fun col => by simpa [topOf] using congrFun hrt col) σ {col}]
    refine Finset.mem_biUnion.mpr ⟨topOf g c, Finset.mem_filter.mpr
      ⟨topOf_mem_tops g j0 c hc, hPt⟩, Finset.mem_biUnion.mpr ⟨col, Finset.mem_univ _, ?_⟩⟩
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    exact_mod_cast h'
  have hper : ∀ t ∈ I, ∀ col : Fin n, ((U t col).card : ℝ) ≤
      (Real.exp 1 * j0 / (n * (T : ℝ))) ^ (T : ℝ) * Fintype.card (Scramble m n) := by
    intro t ht col
    obtain ⟨hct, -⟩ := hrep t (Finset.mem_filter.mp ht).2
    have hR : (∑ r ∈ topRows m g, ((monotoneRowOnes (rep t) r).card : ℝ)) ≤ (j0 : ℝ) := by
      have : (totalColumnOnes (rep t) : ℝ) =
          ∑ r : Fin m, ((monotoneRowOnes (rep t) r).card : ℝ) := by
        exact_mod_cast totalColumnOnes_eq_sum_rowOnes (rep t)
      calc _ ≤ ∑ r : Fin m, ((monotoneRowOnes (rep t) r).card : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun _ _ _ => Nat.cast_nonneg _
        _ = (totalColumnOnes (rep t) : ℝ) := this.symm
        _ ≤ j0 := by exact_mod_cast hct
    have := scramble_tail_fixed_set hn (rep t) (topRows m g) {col} (j0 : ℝ) (T : ℝ)
      (by exact_mod_cast hj0) (by simp) hR (by simpa using hT) (U t col)
      fun σ hσ => (Finset.mem_filter.mp hσ).2
    rw [Finset.card_singleton, Nat.cast_one, mul_one] at this
    exact (div_le_iff₀ htot).mp this
  calc (bad.card : ℝ) ≤ ∑ t ∈ I, ∑ col : Fin n, ((U t col).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans
          ((Finset.card_biUnion_le).trans (Finset.sum_le_sum fun t _ => Finset.card_biUnion_le))
    _ ≤ ∑ t ∈ I, ∑ col : Fin n,
          (Real.exp 1 * j0 / (n * (T : ℝ))) ^ (T : ℝ) * Fintype.card (Scramble m n) :=
        Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun col _ => hper t ht col
    _ = (I.card : ℝ) * ((n : ℝ) * ((Real.exp 1 * j0 / (n * (T : ℝ))) ^ (T : ℝ) *
          Fintype.card (Scramble m n))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ((tops g n j0).card : ℝ) * ((n : ℝ) * ((Real.exp 1 * j0 / (n * (T : ℝ))) ^ (T : ℝ) *
          Fintype.card (Scramble m n))) := by
        refine mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) ?_
        positivity
    _ = _ := by ring

theorem natnum_SR : 10000 * (1642 * 86000000 ^ 1641 * 3300 ^ 1642) ≤ 7 ^ 70000 := by
  decide +kernel

/-- Numerical core: the product of the tops count, the union over columns, and the tail. -/
theorem F2SR_numeric (n K T j0 : ℕ) (hn : 16 ≤ n) (hK : K ≤ 1641) (hT : 71642 ≤ T)
    (b X : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 1 / 7) (hbX : b ≤ X / n) (hX0 : 0 ≤ X) (hX : X ≤ 3300)
    (hj0 : j0 ≤ 86000000) :
    ((K + 1 : ℕ) : ℝ) * ((n : ℝ) * j0) ^ K * ((n : ℝ) * b ^ T) ≤ 1 / 10000 := by
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℝ) < 16 := by norm_num
    exact lt_of_lt_of_le this (by exact_mod_cast hn)
  have hj0r : (j0 : ℝ) ≤ 86000000 := by exact_mod_cast hj0
  have hj00 : (0 : ℝ) ≤ j0 := Nat.cast_nonneg _
  have hT' : b ^ T = b ^ (K + 1) * b ^ (T - (K + 1)) := by
    rw [← pow_add]; congr 1; omega
  have step1 : ((n : ℝ) * j0) ^ K * ((n : ℝ) * b ^ T) ≤
      (86000000 : ℝ) ^ K * X ^ (K + 1) * b ^ (T - (K + 1)) := by
    rw [hT']
    have hbn : b ^ (K + 1) ≤ (X / n) ^ (K + 1) := pow_le_pow_left₀ hb0 hbX _
    have hb2 : 0 ≤ b ^ (T - (K + 1)) := pow_nonneg hb0 _
    have e1 : ((n : ℝ) * j0) ^ K ≤ ((n : ℝ) * 86000000) ^ K :=
      pow_le_pow_left₀ (by positivity) (by gcongr) _
    calc ((n : ℝ) * j0) ^ K * ((n : ℝ) * (b ^ (K + 1) * b ^ (T - (K + 1))))
        ≤ ((n : ℝ) * 86000000) ^ K * ((n : ℝ) * ((X / n) ^ (K + 1) * b ^ (T - (K + 1)))) := by
          gcongr
      _ = _ := by
          rw [mul_pow, div_pow]
          field_simp
          ring
  have h2 : b ^ (T - (K + 1)) ≤ (1 / 7 : ℝ) ^ 70000 :=
    (pow_le_pow_left₀ hb0 hb _).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  have h3 : X ^ (K + 1) ≤ (3300 : ℝ) ^ 1642 :=
    (pow_le_pow_left₀ hX0 hX _).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have h4 : (86000000 : ℝ) ^ K ≤ 86000000 ^ 1641 := pow_le_pow_right₀ (by norm_num) hK
  have h5 : ((K + 1 : ℕ) : ℝ) ≤ 1642 := by exact_mod_cast (by omega : K + 1 ≤ 1642)
  have hnat : (10000 : ℝ) * (1642 * 86000000 ^ 1641 * 3300 ^ 1642) ≤ 7 ^ 70000 := by
    exact_mod_cast natnum_SR
  have h7 : (0 : ℝ) < 7 ^ 70000 := by positivity
  have hX1 : 0 ≤ X ^ (K + 1) := pow_nonneg hX0 _
  calc ((K + 1 : ℕ) : ℝ) * ((n : ℝ) * j0) ^ K * ((n : ℝ) * b ^ T)
      = ((K + 1 : ℕ) : ℝ) * (((n : ℝ) * j0) ^ K * ((n : ℝ) * b ^ T)) := by ring
    _ ≤ 1642 * ((86000000 : ℝ) ^ 1641 * 3300 ^ 1642 * (1 / 7 : ℝ) ^ 70000) := by
        refine mul_le_mul h5 (step1.trans ?_) (by positivity) (by norm_num)
        gcongr
    _ ≤ 1 / 10000 := by
        rw [one_div, inv_pow]
        have : (1642 : ℝ) * (86000000 ^ 1641 * 3300 ^ 1642 * ((7 ^ 70000 : ℝ))⁻¹) =
            (1642 * 86000000 ^ 1641 * 3300 ^ 1642) / 7 ^ 70000 := by
          field_simp
        rw [this, div_le_iff₀ h7]
        generalize (7 : ℝ) ^ 70000 = Z at hnat ⊢
        generalize (86000000 : ℝ) ^ 1641 = A at hnat ⊢
        generalize (3300 : ℝ) ^ 1642 = B at hnat ⊢
        linarith

open scoped Classical in
/-- **Small-rank failure bound** (uniform in `n ≥ 16` and `f ≥ 131040`). -/
theorem F2SR_fail_card_le (P : F2Params) (hf : 131040 ≤ P.f) (hg1 : P.g1 = 2 * P.f / 5)
    (hJ : P.J = 86000000) {m n : ℕ} (hn : 16 ≤ n) (hm : P.f ≤ m) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ F2SmallRank P σ).card : ℝ) ≤
      (1 / 10000) * Fintype.card (Scramble m n) := by
  classical
  have hn0' : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn0'
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hfR : (131040 : ℝ) ≤ P.f := by exact_mod_cast hf
  set j0 : ℕ := min P.J (P.jmax n) with hj0def
  set T : ℕ := P.f - P.g1 + 1 with hTdef
  have hjmaxR : (P.jmax n : ℝ) ≤ (128 / 4095 : ℝ) * (P.f * n) := by
    unfold F2Params.jmax
    exact Nat.floor_le (by positivity)
  have hj0R : (j0 : ℝ) ≤ (128 / 4095 : ℝ) * (P.f * n) :=
    (by exact_mod_cast min_le_right _ _ : (j0 : ℝ) ≤ P.jmax n).trans hjmaxR
  have hj0pos : 0 < j0 := by
    refine lt_min (by rw [hJ]; norm_num) ?_
    unfold F2Params.jmax
    refine Nat.floor_pos.mpr ?_
    have : (131040 : ℝ) * 16 ≤ P.f * n := mul_le_mul hfR hn16 (by norm_num) (by positivity)
    linarith
  have hj0J : j0 ≤ 86000000 := hJ ▸ min_le_left _ _
  have hTR : (T : ℝ) = ((P.f - P.g1 : ℕ) : ℝ) + 1 := by rw [hTdef]; push_cast; ring
  have hT3 : (3 / 5 : ℝ) * P.f ≤ T := by
    have : 3 * P.f ≤ 5 * (P.f - P.g1) := by omega
    have h' : (3 : ℝ) * P.f ≤ 5 * ((P.f - P.g1 : ℕ) : ℝ) := by exact_mod_cast this
    rw [hTR]; linarith
  have hT78 : 78624 ≤ T := by omega
  have hT78R : (78624 : ℝ) ≤ T := by exact_mod_cast hT78
  have hTpos : (0 : ℝ) < T := by linarith
  have hTj : (j0 : ℝ) / n ≤ (T : ℝ) := by
    rw [div_le_iff₀ hn0, hTR]
    have h2 := mul_le_mul_of_nonneg_right P.hD2 hn0.le
    calc (j0 : ℝ) ≤ (128 / 4095 : ℝ) * (P.f * n) := hj0R
      _ = (128 / 4095 : ℝ) * P.f * n := by ring
      _ ≤ _ := h2
  have hbad : ∀ σ ∈ (Finset.univ.filter fun σ : Scramble m n => ¬ F2SmallRank P σ),
      ∃ c : MonotoneColumnSums m n, totalColumnOnes c ≤ j0 ∧
        ∃ S : Finset (Fin n), S.card = 1 ∧ T ≤ onesInRows c σ (topRows m P.g1) S := by
    intro σ hσ
    have h := (Finset.mem_filter.mp hσ).2
    unfold F2SmallRank at h
    push_neg at h
    obtain ⟨c, hc, S, hS, hle⟩ := h
    exact ⟨c, hc, S, hS, hle⟩
  have hmain := F2SR_union_bound P.g1 j0 T hn0' hj0pos hTj _ hbad
  have htops := tops_card_le_crude P.g1 n j0 hn0' hj0pos
  have hKle : j0 / (P.g1 + 1) ≤ 1641 := by
    have : j0 / (P.g1 + 1) ≤ 86000000 / 52417 :=
      Nat.div_le_div hj0J (by omega) (by omega)
    omega
  set K := j0 / (P.g1 + 1) with hKdef
  set b : ℝ := Real.exp 1 * j0 / (n * (T : ℝ)) with hbdef
  set X : ℝ := Real.exp 1 * 86000000 / T with hXdef
  have he1 := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hb0 : 0 ≤ b := by positivity
  have hbX : b ≤ X / n := by
    rw [hbdef, hXdef, div_div, mul_comm (T : ℝ) (n : ℝ)]
    gcongr
    exact_mod_cast hj0J
  have hX0 : 0 ≤ X := by positivity
  have hX : X ≤ 3300 := by
    rw [hXdef, div_le_iff₀ hTpos]
    linarith
  have hb7 : b ≤ 1 / 7 := by
    rw [hbdef, div_le_iff₀ (by positivity)]
    have h1 : Real.exp 1 * j0 ≤ Real.exp 1 * ((128 / 4095 : ℝ) * (P.f * n)) :=
      mul_le_mul_of_nonneg_left hj0R he0.le
    have h2 : (T : ℝ) * n ≥ (3 / 5 : ℝ) * P.f * n := by gcongr
    have h3 : Real.exp 1 * ((128 / 4095 : ℝ) * (P.f * n)) ≤
        (2.7182818286 : ℝ) * ((128 / 4095 : ℝ) * (P.f * n)) :=
      mul_le_mul_of_nonneg_right he1.le (by positivity)
    have hfn : (0 : ℝ) ≤ P.f * n := by positivity
    linarith
  have hnum := F2SR_numeric n K T j0 hn hKle (by omega) b X hb0 hb7 hbX hX0 hX hj0J
  have hcard : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  rw [Real.rpow_natCast] at hmain
  refine hmain.trans ?_
  have htopsR : ((tops P.g1 n j0).card : ℝ) ≤ ((K + 1 : ℕ) : ℝ) * ((n : ℝ) * j0) ^ K := by
    exact_mod_cast htops
  calc ((tops P.g1 n j0).card : ℝ) * ((n : ℝ) * b ^ T) * (Fintype.card (Scramble m n) : ℝ)
      ≤ (((K + 1 : ℕ) : ℝ) * ((n : ℝ) * j0) ^ K) * ((n : ℝ) * b ^ T) *
          (Fintype.card (Scramble m n) : ℝ) := by
        gcongr
    _ ≤ (1 / 10000) * (Fintype.card (Scramble m n) : ℝ) := by
        exact mul_le_mul_of_nonneg_right hnum hcard

open scoped Classical in
/-- Non-vacuity: the hypotheses hold for `F2Params.std`. -/
theorem F2SR_fail_card_le_std {m n : ℕ} (hn : 16 ≤ n) (hm : F2Params.std.f ≤ m) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ F2SmallRank F2Params.std σ).card : ℝ) ≤
      (1 / 10000) * Fintype.card (Scramble m n) :=
  F2SR_fail_card_le F2Params.std (by simp [F2Params.std]) (by simp [F2Params.std])
    (by simp [F2Params.std]) hn hm

end Chvatal
