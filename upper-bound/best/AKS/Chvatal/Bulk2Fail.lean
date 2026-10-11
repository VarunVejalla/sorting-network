module

/- Two-round bulk lemma (B2): the union bound over `(c, S)` and the certified numerics for the
window `m ≥ 2^42`, `n ≥ 16` with `E1 = 371/10^8`, `d = 1/59000000`, `λ = 1/437`. -/

public import AKS.Chvatal.Bulk2Count
public import AKS.Chvatal.GeneralParams

@[expose] public section

open Finset

namespace Chvatal

open Classical in
/-- Union bound for round 2 over all `(c, S)`. -/
theorem failBoundB2 {m n : Nat} (E1 d lam : ℝ) (hm : 0 < m) (hn : 0 < n)
    (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    ((Finset.univ.filter fun σ : Scramble m n => ¬ HasCombinatorialPropertyB2 σ E1 d).card : ℝ) ≤
      (2 * ((m : ℝ) + 1)) ^ n *
        Real.exp (-((n : ℝ) * m * (lam * d / 2 - lam ^ 2 * (1 / 2 + 2 * lam / 9) * E1))) *
        (Fintype.card (Scramble m n) : ℝ) := by
  classical
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set N : ℝ := (Fintype.card (Scramble m n) : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  set cl : ℝ := lam ^ 2 * (1 / 2 + 2 * lam / 9) with hcl
  have hcl0 : 0 ≤ cl := by rw [hcl]; positivity
  set T : ℝ := d / 2 * (m * n) with hT
  let i₀ : MonotoneColumnSums m n → Nat := fun c => totalColumnOnes c / n
  let Adm : MonotoneColumnSums m n → Prop := fun c =>
    n * i₀ c = totalColumnOnes c ∧ 1 ≤ i₀ c ∧ i₀ c ≤ m ∧
      (excessAbove c (i₀ c) : ℝ) < (E1 / 2) * (m * n)
  let V : MonotoneColumnSums m n × Finset (Fin n) → Finset (Scramble m n) := fun p =>
    Finset.univ.filter fun σ => Adm p.1 ∧ (i₀ p.1 : ℝ) * p.2.card + T ≤ (onesInColumns p.1 σ p.2 : ℝ)
  suffices H : ∀ bad : Finset (Scramble m n), (∀ σ ∈ bad, ¬ HasCombinatorialPropertyB2 σ E1 d) →
      (bad.card : ℝ) ≤ (2 * ((m : ℝ) + 1)) ^ n *
        Real.exp (-((n : ℝ) * m * (lam * d / 2 - cl * E1))) * N from
    H _ fun σ hσ => (Finset.mem_filter.1 hσ).2
  intro bad hbad
  have hcover : bad ⊆ Finset.univ.biUnion V := by
    intro σ hσ
    have hnot := hbad σ hσ
    simp only [HasCombinatorialPropertyB2, not_forall, not_lt] at hnot
    obtain ⟨c, i, hc, hi1, him, hexc, hge⟩ := hnot
    have hi0 : i₀ c = i := by
      show totalColumnOnes c / n = i
      rw [hc]; exact Nat.mul_div_cancel_left i hn
    have hex := lemma61_excess_columns d c σ i hge
    refine Finset.mem_biUnion.2 ⟨(c, excessColumnSet c σ i), Finset.mem_univ _,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨?_, ?_, ?_, ?_⟩, ?_⟩⟩
    · rw [hi0, hc]
    · rw [hi0]; exact hi1
    · rw [hi0]; exact him
    · rw [hi0]; exact hexc
    · show (i₀ c : ℝ) * _ + T ≤ _
      rw [hi0]; exact hex
  have hV : ∀ p, ((V p).card : ℝ) ≤
      Real.exp (-((n : ℝ) * m * (lam * d / 2 - cl * E1))) * N := by
    intro p
    by_cases hA : Adm p.1
    · obtain ⟨hA1, hA2, hA3, hA4⟩ := hA
      have hmass : totalColumnOnes p.1 = n * i₀ p.1 := hA1.symm
      have h := lemma63BernsteinBound hn p.1 (i₀ p.1) hmass p.2 lam T hl0 hl1 (V p)
        fun σ hσ => (Finset.mem_filter.1 hσ).2.2
      rw [← hcl] at h
      refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hN)
      have hvar := variance_le_of_excess hn p.1 (i₀ p.1) hmass
      have hV0 : 0 ≤ ∑ r : Fin m, (((monotoneRowOnes p.1 r).card : ℝ) / n) *
          (1 - ((monotoneRowOnes p.1 r).card : ℝ) / n) :=
        Finset.sum_nonneg fun r _ => mul_nonneg (div_nonneg (Nat.cast_nonneg _) hn0.le) (by
          have := row_density_le_one hn p.1 r; linarith)
      have hVE : ∑ r : Fin m, (((monotoneRowOnes p.1 r).card : ℝ) / n) *
          (1 - ((monotoneRowOnes p.1 r).card : ℝ) / n) ≤ E1 * m := by
        refine hvar.trans ?_
        rw [div_le_iff₀ hn0]; nlinarith
      have hs : (p.2.card : ℝ) ≤ n := by exact_mod_cast (by simpa using Finset.card_le_univ p.2 : p.2.card ≤ n)
      have hs0 : (0 : ℝ) ≤ p.2.card := Nat.cast_nonneg _
      set Vv := ∑ r : Fin m, (((monotoneRowOnes p.1 r).card : ℝ) / n) *
          (1 - ((monotoneRowOnes p.1 r).card : ℝ) / n)
      have h1 : (p.2.card : ℝ) * cl * Vv ≤ n * cl * (E1 * m) := by
        calc (p.2.card : ℝ) * cl * Vv ≤ n * cl * Vv := by
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hcl0) hV0
          _ ≤ _ := mul_le_mul_of_nonneg_left hVE (mul_nonneg hn0.le hcl0)
      have : -lam * T + n * cl * (E1 * m) = -((n : ℝ) * m * (lam * d / 2 - cl * E1)) := by
        rw [hT]; ring
      linarith
    · have : V p = ∅ := Finset.filter_false_of_mem fun σ _ h => hA h.1
      rw [this, Finset.card_empty, Nat.cast_zero]; exact mul_nonneg (Real.exp_nonneg _) hN
  calc (bad.card : ℝ) ≤ ((Finset.univ.biUnion V).card : ℝ) := by exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ p, ((V p).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ p : MonotoneColumnSums m n × Finset (Fin n),
          Real.exp (-((n : ℝ) * m * (lam * d / 2 - cl * E1))) * N :=
      Finset.sum_le_sum fun p _ => hV p
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_finset]
      simp only [nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin]
      push_cast
      rw [mul_pow]; ring

end Chvatal

namespace Chvatal

theorem failFactorB2_le {m n : Nat} (hm : 2 ^ 42 ≤ m) (hn : 16 ≤ n) :
    (2 * ((m : ℝ) + 1)) ^ n *
      Real.exp (-((n : ℝ) * m * ((1 / 437 : ℝ) * (1 / 59000000) / 2 -
        (1 / 437 : ℝ) ^ 2 * (1 / 2 + 2 * (1 / 437 : ℝ) / 9) * (371 / 10 ^ 8)))) ≤ 1 / 1000 := by
  have hmR : (2 : ℝ) ^ 42 ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hmR
  set K : ℝ := (1 / 437 : ℝ) * (1 / 59000000) / 2 -
        (1 / 437 : ℝ) ^ 2 * (1 / 2 + 2 * (1 / 437 : ℝ) / 9) * (371 / 10 ^ 8) with hK
  have hK9 : (9 / 10 ^ 12 : ℝ) ≤ K := by rw [hK]; norm_num
  have hl2 := Real.log_two_lt_d9
  have hlogm : Real.log m ≤ 42 * Real.log 2 + (m / 2 ^ 42 - 1) := by
    have := Real.log_le_sub_one_of_pos (div_pos hm0 (by positivity : (0 : ℝ) < 2 ^ 42))
    rw [Real.log_div hm0.ne' (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
  have hlog2m : Real.log (2 * ((m : ℝ) + 1)) ≤ 2 * Real.log 2 + Real.log m := by
    have h4 : (2 : ℝ) * ((m : ℝ) + 1) ≤ 4 * m := by nlinarith [(by norm_num : (1 : ℝ) ≤ 2 ^ 42)]
    calc _ ≤ Real.log (4 * m) := Real.log_le_log (by positivity) h4
      _ = 2 * Real.log 2 + Real.log m := by
        rw [Real.log_mul (by norm_num) hm0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast; ring
  have hkey : Real.log (2 * ((m : ℝ) + 1)) ≤ m * K - 1 := by
    have h1 : (m : ℝ) / 2 ^ 42 ≤ m / 2 ^ 42 := le_rfl
    have h2 : (m : ℝ) * (9 / 10 ^ 12) ≤ m * K := mul_le_mul_of_nonneg_left hK9 hm0.le
    have h3 : (m : ℝ) / 2 ^ 42 = m * (1 / 2 ^ 42) := by ring
    have h4 : (2 : ℝ) ^ 42 * (9 / 10 ^ 12 - 1 / 2 ^ 42) ≤ m * (9 / 10 ^ 12 - 1 / 2 ^ 42) :=
      mul_le_mul_of_nonneg_right hmR (by norm_num)
    norm_num at h4 h3 ⊢
    linarith
  have hq : 2 * ((m : ℝ) + 1) * Real.exp (-((m : ℝ) * K)) ≤ Real.exp (-1) := by
    have : 2 * ((m : ℝ) + 1) ≤ Real.exp (m * K - 1) := by
      calc 2 * ((m : ℝ) + 1) = Real.exp (Real.log (2 * ((m : ℝ) + 1))) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ _ := Real.exp_le_exp.2 hkey
    calc _ ≤ Real.exp (m * K - 1) * Real.exp (-((m : ℝ) * K)) := by gcongr
      _ = _ := by rw [← Real.exp_add]; ring_nf
  have hrew : Real.exp (-((n : ℝ) * m * K)) = Real.exp (-((m : ℝ) * K)) ^ n := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hrew, ← mul_pow]
  calc _ ≤ (Real.exp (-1)) ^ n := pow_le_pow_left₀ (by positivity) hq n
    _ = Real.exp (-(n : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-16) := by
        have : (16 : ℝ) ≤ n := by exact_mod_cast hn
        exact Real.exp_le_exp.2 (by linarith)
    _ ≤ 1 / 1000 := by
        rw [Real.exp_neg, inv_eq_one_div]
        apply one_div_le_one_div_of_le (by norm_num)
        have h1 : (2.7 : ℝ) ^ 16 ≤ Real.exp 1 ^ 16 :=
          pow_le_pow_left₀ (by norm_num) (by have := Real.exp_one_gt_d9; linarith) 16
        rw [← Real.exp_nat_mul] at h1
        norm_num at h1 ⊢
        linarith

end Chvatal

namespace Chvatal

theorem epsB1_le {m : ℕ} (hm : 2 ^ 42 ≤ m) :
    Real.sqrt (2 * (1 + Real.log m) / m) ≤ 371 / 10 ^ 8 := by
  have hmR : (2 : ℝ) ^ 42 ≤ m := by exact_mod_cast hm
  have hmono := chernoff_mono (M := (2 : ℝ) ^ 42) (m := m) (one_le_pow₀ (by norm_num)) hmR
  rw [Real.log_pow] at hmono
  have hl2 := Real.log_two_lt_d9
  rw [Real.sqrt_le_left (by norm_num)]
  refine hmono.trans ?_
  push_cast
  rw [div_le_iff₀ (by positivity)]
  norm_num at hl2 ⊢
  nlinarith

end Chvatal

namespace Chvatal

open Classical in
/-- **T1 (counting bound).** For `m ≥ 2^42`, `n ≥ 16`, at most a `1/1000` fraction of second-round
scrambles violate `HasCombinatorialPropertyB2` at `E1 = 371/10^8`, `d = 1/59000000`. -/
theorem bulk2_fail_fraction_le {m n : ℕ} (hm : 2 ^ 42 ≤ m) (hn : 16 ≤ n) :
    ((Finset.univ.filter fun σ : Scramble m n =>
        ¬ HasCombinatorialPropertyB2 σ (371 / 10 ^ 8) (1 / 59000000)).card : ℝ) ≤
      1 / 1000 * (Fintype.card (Scramble m n) : ℝ) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have h := failBoundB2 (m := m) (n := n) (371 / 10 ^ 8) (1 / 59000000) (1 / 437) hm0
    (by omega) (by norm_num) (by norm_num)
  exact h.trans (mul_le_mul_of_nonneg_right (failFactorB2_le hm hn) (Nat.cast_nonneg _))

end Chvatal
