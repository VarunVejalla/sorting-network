import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # One row of the walk: a uniform `k`-subset seen from one column

`#{T : #T = k, j ∈ T} = C(n-1, k-1)`, hence for any `f`
`Σ_{#T = k} f [j ∈ T] = C(n,k) ((1 - k/n) f false + (k/n) f true)`. -/

open Finset BigOperators

namespace RowMgf

theorem card_mem (n k : ℕ) (j : Fin n) :
    ((Finset.univ : Finset (Fin n)).powersetCard (k + 1) |>.filter (fun T => j ∈ T)).card =
      (n - 1).choose k := by
  classical
  have h : ((Finset.univ : Finset (Fin n)).powersetCard (k + 1) |>.filter (fun T => j ∈ T)).card =
      ((Finset.univ.erase j).powersetCard k).card := by
    refine Finset.card_bij' (fun T _ => T.erase j) (fun T _ => insert j T) ?_ ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.erase_subset_erase j hT.1.1, ?_⟩
      rw [Finset.card_erase_of_mem hT.2, hT.1.2]; rfl
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      have hjT : j ∉ T := fun h => by simpa using hT.1 h
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.mem_insert_self j T⟩
      rw [Finset.card_insert_of_notMem hjT, hT.2]
    · intro T hT
      rw [Finset.mem_filter] at hT
      exact Finset.insert_erase hT.2
    · intro T hT
      rw [Finset.mem_powersetCard] at hT
      have hjT : j ∉ T := fun h => by simpa using hT.1 h
      exact Finset.erase_insert hjT
  rw [h, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ, Fintype.card_fin]

/-- The column's bit under a uniform `k`-subset: `#{j ∈ T} · n = k · C(n,k)`. -/
theorem card_mem_mul (n k : ℕ) (j : Fin n) :
    (((Finset.univ : Finset (Fin n)).powersetCard k |>.filter (fun T => j ∈ T)).card : ℝ) * n =
      k * (n.choose k : ℝ) := by
  classical
  cases k with
  | zero =>
    have : ((Finset.univ : Finset (Fin n)).powersetCard 0 |>.filter (fun T => j ∈ T)) = ∅ := by
      ext T; simp
      intro h; simp [h]
    rw [this]; simp
  | succ k =>
    rw [card_mem]
    have hn : 0 < n := Fin.pos j
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have := Nat.add_one_mul_choose_eq n' k
    have h' : ((n' + 1 : ℕ) : ℝ) * (n'.choose k : ℝ) = ((n' + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at h' ⊢
    linarith

/-- **Row identity.** -/
theorem sum_bit (n k : ℕ) (j : Fin n) (hn : 0 < n) (f : Bool → ℝ) :
    ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, f (decide (j ∈ T)) =
      (n.choose k : ℝ) * ((1 - (k : ℝ) / n) * f false + (k : ℝ) / n * f true) := by
  classical
  set P := (Finset.univ : Finset (Fin n)).powersetCard k
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun T => j ∈ T)
    (fun T => f (decide (j ∈ T)))
  have h1 : ∑ T ∈ P.filter (fun T => j ∈ T), f (decide (j ∈ T)) =
      (P.filter (fun T => j ∈ T)).card * f true := by
    rw [Finset.sum_congr rfl fun T hT => by rw [decide_eq_true (Finset.mem_filter.1 hT).2],
      Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ T ∈ P.filter (fun T => j ∉ T), f (decide (j ∈ T)) =
      (P.filter (fun T => j ∉ T)).card * f false := by
    rw [Finset.sum_congr rfl fun T hT => by rw [decide_eq_false (Finset.mem_filter.1 hT).2],
      Finset.sum_const, nsmul_eq_mul]
  have hc := Finset.card_filter_add_card_filter_not (s := P) (fun T => j ∈ T)
  have hcR : ((P.filter (fun T => j ∈ T)).card : ℝ) + ((P.filter (fun T => j ∉ T)).card : ℝ) =
      (n.choose k : ℝ) := by
    rw [← Nat.cast_add, hc, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hm := card_mem_mul n k j
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hin : ((P.filter (fun T => j ∈ T)).card : ℝ) = k * (n.choose k : ℝ) / n := by
    field_simp; linarith
  rw [← hsplit, h1, h2]
  have hout : ((P.filter (fun T => j ∉ T)).card : ℝ) = (n.choose k : ℝ) - k * (n.choose k : ℝ) / n := by
    linarith
  rw [hin, hout]
  field_simp
  ring

end RowMgf
