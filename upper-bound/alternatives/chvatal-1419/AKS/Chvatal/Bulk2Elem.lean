module

/- Two-round bulk lemma (B2), elementary pieces: a Bernstein-type bound on the Bernoulli MGF
and the exact-mass variance identity `∑ᵣ aᵣ (n - aᵣ) ≤ 2 n ∑ⱼ (cⱼ - i)₊`. -/

public import AKS.Chvatal.Lemma63

@[expose] public section

open Finset

namespace Chvatal

theorem bernoulli_cubic_aux (x : ℝ) (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + (2 / 9) * |x| ^ 3 := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  have h2 := (abs_le.1 h).2
  simp [Finset.sum_range_succ, Nat.factorial] at h2
  norm_num at h2
  nlinarith

theorem bernoulli_mgf_bernstein {p lam : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) :
    1 - p + p * Real.exp lam ≤
      Real.exp (p * lam + lam ^ 2 * (1 / 2 + 2 * lam / 9) * (p * (1 - p))) := by
  have hq0 : 0 ≤ 1 - p := by linarith
  have hx1 : |lam * (1 - p)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  have hx2 : |-(lam * p)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]; nlinarith
  have e1 := bernoulli_cubic_aux _ hx1
  have e2 := bernoulli_cubic_aux _ hx2
  rw [abs_of_nonneg (by positivity : 0 ≤ lam * (1 - p))] at e1
  rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ lam * p)] at e2
  have c1 : (1 - p) ^ 3 ≤ (1 - p) ^ 2 := by
    have := pow_le_pow_of_le_one hq0 (by linarith : 1 - p ≤ 1) (by norm_num : 2 ≤ 3)
    exact this
  have c2 : p ^ 3 ≤ p ^ 2 := pow_le_pow_of_le_one h0 h1 (by norm_num : 2 ≤ 3)
  have l3 : 0 ≤ lam ^ 3 := by positivity
  have key : p * Real.exp (lam * (1 - p)) + (1 - p) * Real.exp (-(lam * p)) ≤
      1 + lam ^ 2 * (1 / 2 + 2 * lam / 9) * (p * (1 - p)) := by
    have a1 := mul_le_mul_of_nonneg_left e1 h0
    have a2 := mul_le_mul_of_nonneg_left e2 hq0
    have b1 : p * ((lam * (1 - p)) ^ 3) ≤ p * (lam ^ 3 * (1 - p) ^ 2) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left c1 l3) h0
    have b2 : (1 - p) * ((lam * p) ^ 3) ≤ (1 - p) * (lam ^ 3 * p ^ 2) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left c2 l3) hq0
    nlinarith
  have hfac : 1 - p + p * Real.exp lam =
      Real.exp (p * lam) * (p * Real.exp (lam * (1 - p)) + (1 - p) * Real.exp (-(lam * p))) := by
    have r1 : Real.exp (p * lam) * Real.exp (lam * (1 - p)) = Real.exp lam := by
      rw [← Real.exp_add]; congr 1; ring
    have r2 : Real.exp (p * lam) * Real.exp (-(lam * p)) = 1 := by
      rw [← Real.exp_add]; rw [show p * lam + -(lam * p) = 0 by ring]; simp
    calc 1 - p + p * Real.exp lam = (1 - p) * (Real.exp (p * lam) * Real.exp (-(lam * p))) +
          p * (Real.exp (p * lam) * Real.exp (lam * (1 - p))) := by rw [r1, r2]; ring
      _ = _ := by ring
  rw [hfac, Real.exp_add]
  gcongr
  calc _ ≤ 1 + lam ^ 2 * (1 / 2 + 2 * lam / 9) * (p * (1 - p)) := key
    _ ≤ _ := by linarith [Real.add_one_le_exp (lam ^ 2 * (1 / 2 + 2 * lam / 9) * (p * (1 - p)))]

def excessAbove {m n : Nat} (c : MonotoneColumnSums m n) (i : Nat) : Nat :=
  ∑ j : Fin n, ((c j).val - i)

theorem card_rows_between {m : Nat} (x y : Nat) :
    (univ.filter fun r : Fin m => x < m - r.val ∧ m - r.val ≤ y).card ≤ y - x := by
  calc _ ≤ (Finset.Ioc x y).card := by
        refine Finset.card_le_card_of_injOn (fun r : Fin m => m - r.val) ?_ ?_
        · intro r hr
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hr
          simp [hr.1, hr.2]
        · intro a _ b _ h
          have := a.isLt; have := b.isLt
          apply Fin.ext
          simp only at h
          omega
    _ = y - x := Nat.card_Ioc x y

theorem sum_rowOnes_mul_compl_le {m n : Nat} (c : MonotoneColumnSums m n) (i : Nat)
    (hc : totalColumnOnes c = n * i) :
    ∑ r : Fin m, (monotoneRowOnes c r).card * (n - (monotoneRowOnes c r).card) ≤
      2 * n * excessAbove c i := by
  classical
  have h1 : ∀ r : Fin m, (monotoneRowOnes c r).card * (n - (monotoneRowOnes c r).card) =
      ∑ j : Fin n, ∑ l : Fin n,
        if (m - r.val ≤ (c j).val ∧ ¬ m - r.val ≤ (c l).val) then 1 else 0 := by
    intro r
    have hA : (monotoneRowOnes c r).card = ∑ j : Fin n, if m - r.val ≤ (c j).val then 1 else 0 := by
      rw [monotoneRowOnes, card_filter]
    have hB : n - (monotoneRowOnes c r).card = ∑ l : Fin n, if ¬ m - r.val ≤ (c l).val then 1 else 0 := by
      have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
        (fun j => m - r.val ≤ (c j).val)
      simp only [card_univ, Fintype.card_fin] at this
      rw [← card_filter]
      simp only [monotoneRowOnes]
      omega
    rw [hB, hA, Finset.sum_mul_sum]
    refine sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
    split_ifs <;> simp_all
  have h2 : ∀ j l : Fin n, (∑ r : Fin m, if (m - r.val ≤ (c j).val ∧ ¬ m - r.val ≤ (c l).val) then 1 else 0)
      ≤ ((c j).val - i) + (i - (c l).val) := by
    intro j l
    rw [← card_filter]
    refine (le_trans (le_of_eq ?_) (card_rows_between (m := m) (c l).val (c j).val)).trans ?_
    · congr 1; ext r; simp only [mem_filter, mem_univ, true_and]; omega
    · omega
  calc _ = ∑ r : Fin m, ∑ j : Fin n, ∑ l : Fin n,
        (if (m - r.val ≤ (c j).val ∧ ¬ m - r.val ≤ (c l).val) then 1 else 0) := sum_congr rfl fun r _ => h1 r
    _ = ∑ j : Fin n, ∑ l : Fin n, ∑ r : Fin m,
        (if (m - r.val ≤ (c j).val ∧ ¬ m - r.val ≤ (c l).val) then 1 else 0) := by
        rw [Finset.sum_comm]
        refine sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ j : Fin n, ∑ l : Fin n, (((c j).val - i) + (i - (c l).val)) :=
        sum_le_sum fun j _ => sum_le_sum fun l _ => h2 j l
    _ = n * excessAbove c i + n * ∑ l : Fin n, (i - (c l).val) := by
        simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, excessAbove, ← Finset.mul_sum]
    _ ≤ _ := by
        have e : ∑ l : Fin n, (i - (c l).val) = excessAbove c i := by
          have p : ∀ l : Fin n, ((c l).val - i) + i = (c l).val + (i - (c l).val) := fun l => by omega
          have := sum_congr (rfl : (univ : Finset (Fin n)) = univ) (fun l _ => p l)
          rw [sum_add_distrib, sum_add_distrib] at this
          have h3 : ∑ l : Fin n, (c l).val = n * i := hc
          simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at this
          unfold excessAbove
          nlinarith
        rw [e]; nlinarith

end Chvatal
