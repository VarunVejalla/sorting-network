module

public import AKS.Chvatal.F2Defs
public import AKS.Chvatal.F2R2Count
public import AKS.Chvatal.F2R2Num
public import Mathlib.Algebra.Order.Field.GeomSum

/-! # Failure probability of the R2 predicate (`F2ROUND.md` §3-§5)

`F2R2n P σ` is `F2R2 P σ` restricted to the ranks `E` that the deterministic reduction uses,
namely `(E - 1) * J ≤ jmax n` (`F2Det.F2_of_SR_R1_R2` applies R2 at `q = ⌈j/J⌉`, so
`(q - 1) J < j ≤ jmax n`).  Without this restriction the statement is false for small `n`
(`F2ROUND.md` §4 tacitly assumes `n ≥ (E-1) J / D`).

Pipeline: union over `E`, over the tops `y` (`ycap`, support ≤ κ, mass < B), over `s = |S|`;
Chernoff for each `(y, s)` (`scramble_tail_fixed_set` with `J := B`); numerics. -/

@[expose] public section

namespace Chvatal

open Finset

/-- Ones in the rows above the bottom `g` are at most the total excess `Σ (c col - g)₊`. -/
theorem top_ones_le {m n : ℕ} (g : ℕ) (c : MonotoneColumnSums m n) :
    ∑ r ∈ topRows m g, (monotoneRowOnes c r).card ≤ ∑ col, ((c col).val - g) := by
  classical
  simp only [monotoneRowOnes, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun col _ => ?_
  rw [← Finset.card_filter]
  have hc := (c col).isLt
  calc _ ≤ (Finset.Ico (m - (c col).val) (m - g)).card := by
        refine Finset.card_le_card_of_injOn (fun r : Fin m => r.val) ?_ ?_
        · intro r hr
          simp only [Finset.coe_filter, topRows, Finset.mem_filter, Finset.mem_univ, true_and,
            Set.mem_setOf_eq, Finset.coe_Ico, Set.mem_Ico] at hr ⊢
          omega
        · intro a _ b _ hab
          exact Fin.ext hab
    _ = (m - g) - (m - (c col).val) := Nat.card_Ico _ _
    _ ≤ _ := by omega

/-- **S2 (general rows)**: union bound over the `C(n,s)` column sets, with the ones of the rows `R`
bounded by `J` (not the total of `c`). -/
theorem tail_union_top_gen {m n : ℕ} (hn : 0 < n) (c : MonotoneColumnSums m n) (h s : ℕ)
    (J T : ℝ) (hJ : 0 < J) (hs : 0 < s)
    (hR : (∑ r ∈ topRows m h, ((monotoneRowOnes c r).card : ℝ)) ≤ J)
    (hT : J * s / n ≤ T) :
    ((tailBadSet c (topRows m h) s T).card : ℝ) / Fintype.card (Scramble m n) ≤
      (n.choose s : ℝ) * (Real.exp 1 * J * s / (n * T)) ^ T := by
  classical
  have htot : (0 : ℝ) < Fintype.card (Scramble m n) := by exact_mod_cast Fintype.card_pos
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
    exact (div_le_iff₀ htot).mp this
  rw [div_le_iff₀ htot]
  calc ((tailBadSet c (topRows m h) s T).card : ℝ) ≤ ∑ S ∈ P, ((B S).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ S ∈ P, (Real.exp 1 * J * s / (n * T)) ^ T *
          Fintype.card (Scramble m n) := Finset.sum_le_sum hper
    _ = _ := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring

/-- Per-`(y, s)` Chernoff bound: with `R = e B / (n Φ) ≤ 1`. -/
theorem pair_bound {m n : ℕ} (hn : 0 < n) (c : MonotoneColumnSums m n) (g Φ E B s : ℕ) (R : ℝ)
    (hRdef : R = Real.exp 1 * B / (n * Φ)) (hR1 : R ≤ 1) (hΦ : 20 ≤ Φ) (hB : 0 < B)
    (hs : 1 ≤ s)
    (hc : (∑ r ∈ topRows m g, ((monotoneRowOnes c r).card : ℝ)) ≤ B) :
    ((tailBadSet c (topRows m g) s ((Φ * s + E : ℕ) : ℝ)).card : ℝ) /
        Fintype.card (Scramble m n) ≤ (n.choose s : ℝ) * R ^ (20 * s + E) := by
  have hΦ0 : (0 : ℝ) < Φ := by exact_mod_cast (by omega : 0 < Φ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hBn : (B : ℝ) ≤ n * Φ := by
    have h1 : Real.exp 1 * B ≤ n * Φ := by
      rw [hRdef, div_le_one (by positivity)] at hR1; exact hR1
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hTpos : (0 : ℝ) < ((Φ * s + E : ℕ) : ℝ) := by
    have : 0 < Φ * s + E := by positivity
    exact_mod_cast this
  have hT : (B : ℝ) * s / n ≤ ((Φ * s + E : ℕ) : ℝ) := by
    rw [div_le_iff₀ hn0]
    push_cast
    have hE : (0 : ℝ) ≤ E := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hBn hs0.le, mul_nonneg hE hn0.le]
  have key := tail_union_top_gen hn c g s (B : ℝ) _ hB0 hs hc hT
  refine key.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  rw [Real.rpow_natCast]
  have hbase : Real.exp 1 * B * s / (n * ((Φ * s + E : ℕ) : ℝ)) ≤ R := by
    rw [hRdef, div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    have : (0 : ℝ) ≤ Real.exp 1 * B * n := by positivity
    have hE : (0 : ℝ) ≤ E := Nat.cast_nonneg _
    nlinarith [mul_nonneg this hE, mul_nonneg this hs0.le, mul_nonneg (mul_nonneg this hE) hΦ0.le]
  calc _ ≤ R ^ (Φ * s + E) := pow_le_pow_left₀ (by positivity) hbase _
    _ ≤ R ^ (20 * s + E) := pow_le_pow_of_le_one hRpos.le hR1 (by nlinarith)

/-- Sum over `s` of the per-column-set bounds. -/
theorem sum_s_le {n : ℕ} (R : ℝ) (hR : 0 ≤ R) (E : ℕ) :
    ∑ s ∈ Finset.Icc 1 n, (n.choose s : ℝ) * R ^ (20 * s + E) ≤
      R ^ E * (Real.exp (n * R ^ 20) - 1) := by
  set x : ℝ := n * R ^ 20 with hx
  have hx0 : 0 ≤ x := by positivity
  have hterm : ∀ s ∈ Finset.Icc 1 n, (n.choose s : ℝ) * R ^ (20 * s + E) ≤
      R ^ E * (x ^ s / (s.factorial : ℝ)) := by
    intro s _
    have h1 := Nat.choose_le_pow_div (α := ℝ) s n
    have h2 : (n.choose s : ℝ) * R ^ (20 * s + E) ≤ ((n : ℝ) ^ s / s.factorial) * R ^ (20 * s + E) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    refine h2.trans (le_of_eq ?_)
    rw [hx, mul_pow, ← pow_mul, pow_add]
    ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hIcc : Finset.Icc 1 n = (Finset.range (n + 1)).erase 0 := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]; omega
  have h := Real.sum_le_exp_of_nonneg hx0 (n + 1)
  rw [← Finset.add_sum_erase (Finset.range (n + 1)) _ (Finset.mem_range.mpr (Nat.succ_pos n))] at h
  rw [hIcc]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  linarith

/-- The bad set for a fixed `E`. -/
noncomputable def badE {m n : ℕ} (g Φ E κ B : ℕ) : Finset (Scramble m n) := by
  classical
  exact Finset.univ.filter fun σ => ∃ c : MonotoneColumnSums m n,
    (Finset.univ.filter fun col => g < (c col).val).card ≤ κ ∧
    ∑ col, ((c col).val - g) < B ∧
    ∃ S : Finset (Fin n), S.Nonempty ∧ Φ * S.card + E ≤ onesInRows c σ (topRows m g) S

theorem suppC_topOf {m n : ℕ} (g : ℕ) (c : MonotoneColumnSums m n) :
    suppC (topOf g c) = (Finset.univ.filter fun col => g < (c col).val).card := by
  classical
  unfold suppC topOf
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : g < (c i).val
  · simp [h]; omega
  · simp [h]; omega

theorem badE_card_le {m n : ℕ} (hn : 0 < n) (g Φ E κ B : ℕ) (R : ℝ)
    (hRdef : R = Real.exp 1 * B / (n * Φ)) (hR1 : R ≤ 1) (hΦ : 20 ≤ Φ) (hB : 0 < B) :
    ((badE (m := m) (n := n) g Φ E κ B).card : ℝ) ≤
      ((ycap n κ (B - 1)).card : ℝ) * (R ^ E * (Real.exp (n * R ^ 20) - 1)) *
        Fintype.card (Scramble m n) := by
  classical
  have htot : (0 : ℝ) < Fintype.card (Scramble m n) := by exact_mod_cast Fintype.card_pos
  have hRpos : 0 < R := by
    rw [hRdef]
    have : (0 : ℝ) < Φ := by exact_mod_cast (by omega : 0 < Φ)
    have : (0 : ℝ) < n := by exact_mod_cast hn
    have : (0 : ℝ) < B := by exact_mod_cast hB
    positivity
  let Cs : Finset (MonotoneColumnSums m n) := Finset.univ.filter fun c =>
    (Finset.univ.filter fun col => g < (c col).val).card ≤ κ ∧ ∑ col, ((c col).val - g) < B
  let Y : Finset (Fin n → ℕ) := Cs.image (topOf g)
  have hYsub : Y ⊆ ycap n κ (B - 1) := by
    intro t ht
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ht
    have hc' := (Finset.mem_filter.mp hc).2
    refine mem_ycap.mpr ⟨by rw [suppC_topOf]; exact hc'.1, ?_⟩
    have : ∑ i, topOf g c i = ∑ col, ((c col).val - g) := rfl
    omega
  let rep : (Fin n → ℕ) → MonotoneColumnSums m n := fun t =>
    if h : ∃ c ∈ Cs, topOf g c = t then Classical.choose h else fun _ => 0
  have hrep : ∀ t ∈ Y, rep t ∈ Cs ∧ topOf g (rep t) = t := fun t ht => by
    have hex : ∃ c ∈ Cs, topOf g c = t := by
      obtain ⟨c, hc, h⟩ := Finset.mem_image.mp ht
      exact ⟨c, hc, h⟩
    simp only [rep, dif_pos hex]
    exact Classical.choose_spec hex
  let U : (Fin n → ℕ) → ℕ → Finset (Scramble m n) := fun t s =>
    tailBadSet (rep t) (topRows m g) s ((Φ * s + E : ℕ) : ℝ)
  have hsub : badE (m := m) (n := n) g Φ E κ B ⊆
      Y.biUnion fun t => (Finset.Icc 1 n).biUnion (U t) := by
    intro σ hσ
    simp only [badE, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨c, hc1, hc2, S, hne, hge⟩ := hσ
    have hcCs : c ∈ Cs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1, hc2⟩
    have hY : topOf g c ∈ Y := Finset.mem_image.mpr ⟨c, hcCs, rfl⟩
    obtain ⟨-, hrt⟩ := hrep _ hY
    have hones : onesInRows (rep (topOf g c)) σ (topRows m g) S =
        onesInRows c σ (topRows m g) S :=
      onesInRows_topRows_depends_only_on_top _ _
        (fun col => by simpa [topOf] using (congrFun hrt col)) σ S
    refine Finset.mem_biUnion.mpr ⟨topOf g c, hY, Finset.mem_biUnion.mpr ⟨S.card, ?_, ?_⟩⟩
    · rw [Finset.mem_Icc]
      exact ⟨hne.card_pos, by simpa using Finset.card_le_univ S⟩
    · simp only [U, tailBadSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩, ?_⟩
      rw [hones]
      exact_mod_cast hge
  have hUb : ∀ t ∈ Y, ∀ s ∈ Finset.Icc 1 n, ((U t s).card : ℝ) ≤
      ((n.choose s : ℝ) * R ^ (20 * s + E)) * Fintype.card (Scramble m n) := by
    intro t ht s hs
    obtain ⟨hcs, -⟩ := hrep t ht
    have hc' := (Finset.mem_filter.mp hcs).2
    have hcB : (∑ r ∈ topRows m g, ((monotoneRowOnes (rep t) r).card : ℝ)) ≤ B := by
      have h1 := top_ones_le g (rep t)
      have h2 : ∑ r ∈ topRows m g, (monotoneRowOnes (rep t) r).card ≤ B := by omega
      exact_mod_cast h2
    have := pair_bound hn (rep t) g Φ E B s R hRdef hR1 hΦ hB (Finset.mem_Icc.mp hs).1 hcB
    exact (div_le_iff₀ htot).mp this
  have h2 : ((badE (m := m) (n := n) g Φ E κ B).card : ℝ) ≤
      ∑ t ∈ Y, ∑ s ∈ Finset.Icc 1 n, ((U t s).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans
      ((Finset.card_biUnion_le).trans (Finset.sum_le_sum fun t _ => Finset.card_biUnion_le))
  have hN : (0 : ℝ) ≤ R ^ E * (Real.exp (n * R ^ 20) - 1) * Fintype.card (Scramble m n) := by
    have : 1 ≤ Real.exp (n * R ^ 20) := Real.one_le_exp (by positivity)
    have : (0 : ℝ) ≤ R ^ E * (Real.exp (n * R ^ 20) - 1) :=
      mul_nonneg (by positivity) (by linarith)
    positivity
  calc ((badE (m := m) (n := n) g Φ E κ B).card : ℝ)
      ≤ ∑ t ∈ Y, (R ^ E * (Real.exp (n * R ^ 20) - 1)) * Fintype.card (Scramble m n) := by
        refine h2.trans (Finset.sum_le_sum fun t ht => ?_)
        calc ∑ s ∈ Finset.Icc 1 n, ((U t s).card : ℝ)
            ≤ ∑ s ∈ Finset.Icc 1 n, ((n.choose s : ℝ) * R ^ (20 * s + E)) *
                Fintype.card (Scramble m n) := Finset.sum_le_sum (hUb t ht)
          _ = (∑ s ∈ Finset.Icc 1 n, (n.choose s : ℝ) * R ^ (20 * s + E)) *
                Fintype.card (Scramble m n) := by rw [Finset.sum_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right (sum_s_le R hRpos.le E) htot.le
    _ = (Y.card : ℝ) * ((R ^ E * (Real.exp (n * R ^ 20) - 1)) * Fintype.card (Scramble m n)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((ycap n κ (B - 1)).card : ℝ) * ((R ^ E * (Real.exp (n * R ^ 20) - 1)) *
          Fintype.card (Scramble m n)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hYsub) hN
    _ = _ := by ring

/-! ## The restricted predicate and the main bound -/

theorem F2R2_imp_F2R2n {m n : ℕ} (P : F2Params) {σ2 : Scramble m n} (h : F2R2 P σ2) :
    F2R2n P σ2 := fun E hE _ => h E hE

open scoped Classical in
theorem not_F2R2n_subset {m n : ℕ} (P : F2Params) :
    (Finset.univ.filter fun σ : Scramble m n => ¬ F2R2n P σ) ⊆
      (Finset.Icc 2 (1 + P.jmax n / P.J)).biUnion
        fun E => badE (m := m) (n := n) P.g2 P.Φ E (P.κ E) (P.B E) := by
  classical
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, F2R2n] at hσ
  push_neg at hσ
  obtain ⟨E, hE, hEn, c, hc1, hc2, S, hne, hge⟩ := hσ
  refine Finset.mem_biUnion.mpr ⟨E, Finset.mem_Icc.mpr ⟨hE, ?_⟩, ?_⟩
  · have := (Nat.le_div_iff_mul_le P.hJ).mpr hEn
    omega
  · simp only [badE, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨c, hc1, hc2, S, hne, hge⟩

theorem sum_geom_le (N : ℕ) : ∑ E ∈ Finset.Icc 2 N, (17 / 20 : ℝ) ^ E ≤ 5 := by
  have h : ∑ E ∈ Finset.Ico 2 (N + 1), (17 / 20 : ℝ) ^ E ≤ (17 / 20) ^ 2 / (1 - 17 / 20) :=
    geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
  have e : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e]
  refine h.trans ?_
  norm_num

/-- Per-`E` bound under the parameter hypotheses. -/
theorem badE_le_params {m n : ℕ} (P : F2Params) (hf : 131040 ≤ P.f)
    (hfmax : P.f < 8500000000) (hg2 : P.g2 = 4 * P.f / 5) (hc : P.c = 1 / 3) (hb : P.b = 17000)
    (hJ : P.J = 86000000) (hn : 16 ≤ n) {E : ℕ} (hE : 2 ≤ E) (hEn : (E - 1) * P.J ≤ P.jmax n) :
    ((badE (m := m) (n := n) P.g2 P.Φ E (P.κ E) (P.B E)).card : ℝ) ≤
      ((10 ^ 9 / 5000 ^ 19) * (17 / 20 : ℝ) ^ E) * Fintype.card (Scramble m n) := by
  have hn0 : 0 < n := by omega
  have hΦ5 : P.f ≤ 5 * P.Φ := by
    have := P.hg2f
    unfold F2Params.Φ; omega
  have hΦ : 26208 ≤ P.Φ := by omega
  -- κ and B
  have hκ1 : E ≤ 3 * P.κ E := by
    have h1 : (E : ℝ) * (1 / 3) ≤ (P.κ E : ℝ) := by
      have := Nat.le_ceil (P.c * E)
      rw [hc] at this
      unfold F2Params.κ; rw [hc]; linarith
    have : (E : ℝ) ≤ 3 * (P.κ E : ℝ) := by linarith
    exact_mod_cast this
  have hκ2 : 3 * P.κ E ≤ E + 2 := by
    have h1 : (P.κ E : ℝ) < (1 / 3) * E + 1 := by
      have := Nat.ceil_lt_add_one (show 0 ≤ P.c * (E : ℝ) by rw [hc]; positivity)
      unfold F2Params.κ; rw [hc] at this ⊢; linarith
    have : (3 * P.κ E : ℝ) < E + 3 := by linarith
    have : 3 * P.κ E < E + 3 := by exact_mod_cast this
    omega
  have hB : P.B E = 17000 * E := by
    unfold F2Params.B
    rw [hb, show (17000 : ℝ) * E = ((17000 * E : ℕ) : ℝ) by push_cast; ring]
    exact Nat.ceil_natCast _
  -- the real form of the rank hypothesis
  have hjm : ((E : ℝ) - 1) * 86000000 ≤ (128 / 4095 : ℝ) * (P.f * n) := by
    have h1 : (((E - 1) * P.J : ℕ) : ℝ) ≤ (P.jmax n : ℝ) := by exact_mod_cast hEn
    have h2 : (P.jmax n : ℝ) ≤ (128 / 4095 : ℝ) * (P.f * n) :=
      Nat.floor_le (by positivity)
    have h3 : (((E - 1 : ℕ) : ℝ)) = (E : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    push_cast at h1
    rw [h3, hJ] at h1
    simp only [Nat.cast_ofNat] at h1
    linarith
  have hE2 : (2 : ℝ) ≤ E := by exact_mod_cast hE
  have hfn : (1375000000 : ℝ) * E ≤ (P.f : ℝ) * n := by nlinarith
  have hΦ5R : (P.f : ℝ) ≤ 5 * P.Φ := by exact_mod_cast hΦ5
  have hnR0 : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnΦ : (275000000 : ℝ) * E ≤ n * P.Φ := by nlinarith
  have hfmaxR : (P.f : ℝ) ≤ 8500000000 := by
    have : (P.f : ℝ) < 8500000000 := by exact_mod_cast hfmax
    linarith
  have hEn16 : 5 * E ≤ 16 * n := by
    have h1 : (P.f : ℝ) * n ≤ 8500000000 * n := mul_le_mul_of_nonneg_right hfmaxR hnR0.le
    have h16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
    have : (5 : ℝ) * E ≤ 16 * n := by linarith
    exact_mod_cast this
  have hBR : (P.B E : ℝ) = 17000 * E := by rw [hB]; push_cast; ring
  have hΦR : (0 : ℝ) < P.Φ := by exact_mod_cast (by omega : 0 < P.Φ)
  set R : ℝ := Real.exp 1 * (P.B E : ℝ) / (n * P.Φ) with hRdef
  have hR : R ≤ 1 / 5900 := by
    rw [hRdef, div_le_div_iff₀ (by positivity) (by norm_num), hBR]
    have he := Real.exp_one_lt_d9
    nlinarith [mul_le_mul_of_nonneg_right he.le (show (0 : ℝ) ≤ 17000 * E by positivity)]
  have hbad := badE_card_le (m := m) hn0 P.g2 P.Φ E (P.κ E) (P.B E) R hRdef
    (hR.trans (by norm_num)) (by omega) (by rw [hB]; omega)
  have hnum := perE_all n E (P.κ E) (P.B E) P.Φ R hE hκ1 hκ2 hB hΦ hn hEn16 hRdef hR
  refine hbad.trans ?_
  have htot : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right hnum htot

open scoped Classical in
/-- **Main theorem.** -/
theorem F2R2n_fail {m n : ℕ} (P : F2Params) (hf : 131040 ≤ P.f)
    (hfmax : P.f < 8500000000) (hg2 : P.g2 = 4 * P.f / 5) (hc : P.c = 1 / 3) (hb : P.b = 17000)
    (hJ : P.J = 86000000) (hn : 16 ≤ n) (hm : P.f ≤ m) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ F2R2n P σ).card : ℝ) ≤
      (1 / 10000) * Fintype.card (Scramble m n) := by
  classical
  have hsub := not_F2R2n_subset (m := m) (n := n) P
  have h1 : ((Finset.univ.filter fun σ : Scramble m n => ¬ F2R2n P σ).card : ℝ) ≤
      ∑ E ∈ Finset.Icc 2 (1 + P.jmax n / P.J),
        ((badE (m := m) (n := n) P.g2 P.Φ E (P.κ E) (P.B E)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∑ E ∈ Finset.Icc 2 (1 + P.jmax n / P.J),
        ((badE (m := m) (n := n) P.g2 P.Φ E (P.κ E) (P.B E)).card : ℝ) ≤
      ∑ E ∈ Finset.Icc 2 (1 + P.jmax n / P.J),
        ((10 ^ 9 / 5000 ^ 19) * (17 / 20 : ℝ) ^ E) * Fintype.card (Scramble m n) := by
    refine Finset.sum_le_sum fun E hE => ?_
    obtain ⟨hE1, hE2⟩ := Finset.mem_Icc.mp hE
    have hEn : (E - 1) * P.J ≤ P.jmax n := by
      have : E - 1 ≤ P.jmax n / P.J := by omega
      exact (Nat.le_div_iff_mul_le P.hJ).mp this
    exact badE_le_params P hf hfmax hg2 hc hb hJ hn hE1 hEn
  refine h1.trans (h2.trans ?_)
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have h3 := sum_geom_le (1 + P.jmax n / P.J)
  have htot : (0 : ℝ) ≤ Fintype.card (Scramble m n) := Nat.cast_nonneg _
  have h4 : (10 ^ 9 / 5000 ^ 19 : ℝ) * ∑ E ∈ Finset.Icc 2 (1 + P.jmax n / P.J), (17 / 20 : ℝ) ^ E ≤
      1 / 10000 := by
    calc _ ≤ (10 ^ 9 / 5000 ^ 19 : ℝ) * 5 := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ ≤ 1 / 10000 := by norm_num
  exact mul_le_mul_of_nonneg_right h4 htot

open scoped Classical in
/-- The concrete instance `f = 131040` (stage 1). -/
theorem F2R2n_fail_std {m n : ℕ} (hn : 16 ≤ n) (hm : 131040 ≤ m) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ F2R2n F2Params.std σ).card : ℝ) ≤
      (1 / 10000) * Fintype.card (Scramble m n) :=
  F2R2n_fail F2Params.std (by decide) (by decide) (by decide) (by simp [F2Params.std])
    (by simp [F2Params.std]) (by simp [F2Params.std]) hn hm

/-- Non-vacuity of the rank hypothesis: for `n = 21000` the rank `E = 2` is admissible. -/
example : (2 - 1) * F2Params.std.J ≤ F2Params.std.jmax 21000 := by
  unfold F2Params.jmax
  refine Nat.le_floor ?_
  simp [F2Params.std]
  norm_num

end Chvatal

