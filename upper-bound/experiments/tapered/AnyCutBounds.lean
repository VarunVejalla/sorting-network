import VariableSeparator
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- Moving a high crossing cut upward costs only the intervening output cells.
No assumption about the output permutation is needed for this step. -/
theorem high_crossing_move_cut {a : Nat} (y : Fin a → Fin a)
    (s r : Nat) (hsr : s ≤ r) :
    (Finset.univ.filter fun c : Fin a => r ≤ (y c).val ∧ c.val < r).card ≤
      (Finset.univ.filter fun c : Fin a => s ≤ (y c).val ∧ c.val < s).card + (r - s) := by
  let A := Finset.univ.filter fun c : Fin a => s ≤ (y c).val ∧ c.val < s
  let B := Finset.univ.filter fun c : Fin a => s ≤ c.val ∧ c.val < r
  have hsub : (Finset.univ.filter fun c : Fin a => r ≤ (y c).val ∧ c.val < r) ⊆ A ∪ B := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : c.val < s
    · exact Or.inl ⟨hsr.trans hc.1, h⟩
    · exact Or.inr ⟨by omega, hc.2⟩
  have hB : B.card ≤ r - s := by
    have h := Finset.card_le_card_of_injOn Fin.val
      (s := B) (t := Finset.Ico s r)
      (by
        intro c hc
        change c ∈ B at hc
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        exact Finset.mem_Ico.mpr hc)
      (by intro c hc c' hc' heq; exact Fin.ext heq)
    simpa only [Nat.card_Ico] using h
  change _ ≤ A.card + (r - s)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le A B).trans (Nat.add_le_add_left hB A.card))

/-- Moving a low crossing cut downward has the dual one-row cost. -/
theorem low_crossing_move_cut {a : Nat} (y : Fin a → Fin a)
    (r s : Nat) (hrs : r ≤ s) :
    (Finset.univ.filter fun c : Fin a => (y c).val < r ∧ r ≤ c.val).card ≤
      (Finset.univ.filter fun c : Fin a => (y c).val < s ∧ s ≤ c.val).card + (s - r) := by
  let A := Finset.univ.filter fun c : Fin a => (y c).val < s ∧ s ≤ c.val
  let B := Finset.univ.filter fun c : Fin a => r ≤ c.val ∧ c.val < s
  have hsub : (Finset.univ.filter fun c : Fin a => (y c).val < r ∧ r ≤ c.val) ⊆ A ∪ B := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : s ≤ c.val
    · exact Or.inl ⟨hc.1.trans_le hrs, h⟩
    · exact Or.inr ⟨hc.2, by omega⟩
  have hB : B.card ≤ s - r := by
    have h := Finset.card_le_card_of_injOn Fin.val
      (s := B) (t := Finset.Ico r s)
      (by
        intro c hc
        change c ∈ B at hc
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        exact Finset.mem_Ico.mpr hc)
      (by intro c hc c' hc' heq; exact Fin.ext heq)
    simpa only [Nat.card_Ico] using h
  change _ ≤ A.card + (s - r)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le A B).trans (Nat.add_le_add_left hB A.card))

/-- Row-cut guarantees extend to every wire cut with less than one row of
additional error on each side. This permits wire-rounded ragged flows. -/
theorem arbitrary_cut_of_row_bounds {m n : Nat} (hn : 0 < n)
    (y : Fin (m * n) → Fin (m * n)) (E : Real)
    (hhigh : ∀ i, i ≤ m →
      ((Finset.univ.filter fun c : Fin (m * n) => i * n ≤ (y c).val ∧ c.val < i * n).card : Real) ≤ E)
    (hlow : ∀ i, i ≤ m →
      ((Finset.univ.filter fun c : Fin (m * n) => (y c).val < i * n ∧ i * n ≤ c.val).card : Real) ≤ E)
    (r : Nat) (hr : r ≤ m * n) :
    ((Finset.univ.filter fun c : Fin (m * n) => r ≤ (y c).val ∧ c.val < r).card : Real) ≤ E + n ∧
    ((Finset.univ.filter fun c : Fin (m * n) => (y c).val < r ∧ r ≤ c.val).card : Real) ≤ E + n := by
  let down := r / n
  let up := if r % n = 0 then down else down + 1
  have hdown : down * n ≤ r := Nat.div_mul_le_self r n
  have hmod := Nat.mod_lt r hn
  have hdecomp : r % n + down * n = r := by
    simpa only [down, Nat.mul_comm] using Nat.mod_add_div r n
  have hdownm : down ≤ m := (Nat.div_le_div_right hr).trans (by simp [hn.ne'])
  have hupmul : up * n = if r % n = 0 then down * n else down * n + n := by
    dsimp [up]
    split_ifs <;> simp only [Nat.add_mul, Nat.one_mul]
  have hup : r ≤ up * n := by rw [hupmul]; split_ifs <;> omega
  have hupm : up ≤ m := by
    dsimp [up]
    split_ifs with h
    · exact hdownm
    · by_contra hle
      have heq : down = m := by omega
      have hprod : down * n = m * n := by rw [heq]
      omega
  have hgapdown : r - down * n < n := by omega
  have hgapup : up * n - r < n := by rw [hupmul]; split_ifs <;> omega
  have hH := high_crossing_move_cut y (down * n) r hdown
  have hL := low_crossing_move_cut y r (up * n) hup
  have hHR : ((Finset.univ.filter fun c : Fin (m * n) => r ≤ (y c).val ∧ c.val < r).card : Real) ≤
      ((Finset.univ.filter fun c : Fin (m * n) => down * n ≤ (y c).val ∧ c.val < down * n).card : Real) + (r - down * n : Nat) := by exact_mod_cast hH
  have hLR : ((Finset.univ.filter fun c : Fin (m * n) => (y c).val < r ∧ r ≤ c.val).card : Real) ≤
      ((Finset.univ.filter fun c : Fin (m * n) => (y c).val < up * n ∧ up * n ≤ c.val).card : Real) + (up * n - r : Nat) := by exact_mod_cast hL
  have hgH : ((r - down * n : Nat) : Real) ≤ n := by exact_mod_cast hgapdown.le
  have hgL : ((up * n - r : Nat) : Real) ≤ n := by exact_mod_cast hgapup.le
  constructor
  · exact hHR.trans (add_le_add (hhigh down hdownm) hgH)
  · exact hLR.trans (add_le_add (hlow up hupm) hgL)

/-- The actual two-round pack controls arbitrary wire cuts, including cuts
not divisible by the column count. The additional charge is one row per side. -/
theorem pack2_arbitrary_cut_bounds {m n : Nat} (hn : 0 < n)
    (σ₁ σ₂ : Scramble m n) {eps : Real}
    (hhigh : HasPackSemanticPropertyB2 hn σ₁ σ₂ eps)
    (hlow : HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) eps)
    (hE : 0 ≤ (eps / 2) * (m * n))
    (x : Equiv.Perm (Fin (m * n))) (r : Nat) (hr : r ≤ m * n) :
    let y := (physicalPack2Net m n hn σ₁ σ₂).exec
      (x : Fin (m * n) → Fin (m * n))
    ((Finset.univ.filter fun c : Fin (m * n) => r ≤ (y c).val ∧ c.val < r).card : Real) ≤
      (eps / 2) * (m * n) + n ∧
    ((Finset.univ.filter fun c : Fin (m * n) => (y c).val < r ∧ r ≤ c.val).card : Real) ≤
      (eps / 2) * (m * n) + n := by
  intro y
  apply arbitrary_cut_of_row_bounds hn y ((eps / 2) * (m * n)) _ _ r hr
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      simpa only [Nat.zero_mul, Nat.not_lt_zero, and_false, Finset.filter_false,
        Finset.card_empty, Nat.cast_zero] using hE
    · have h := pack2_ragged_boundary_high hn σ₁ σ₂ hhigh x (fun _ => 0) 0 i (by omega) hi
      simpa only [raggedPrefixRows, Finset.sum_range_zero, Nat.add_zero] using h
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      simpa only [Nat.zero_mul, Nat.not_lt_zero, false_and, Finset.filter_false,
        Finset.card_empty, Nat.cast_zero] using hE
    · have h := pack2_ragged_boundary_low hn σ₁ σ₂ hlow x (fun _ => 0) 0 i (by omega) hi
      simpa only [raggedPrefixRows, Finset.sum_range_zero, Nat.add_zero] using h

end Tapered945
