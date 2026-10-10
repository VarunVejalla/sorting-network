import AKS.Chvatal.Lemma63
open Finset

namespace Chvatal

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
