import AKS.Chvatal.PackNodeSpec2
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- Two-round bulk control at any row-aligned output cut. -/
theorem pack2_cut_high {m n : Nat} (hn : 0 < n) (σ₁ σ₂ : Scramble m n)
    {epsB : ℝ} (hB : HasPackSemanticPropertyB2 hn σ₁ σ₂ epsB)
    (x : Equiv.Perm (Fin (m * n))) (i : Nat) (hi₁ : 1 ≤ i) (hiₘ : i ≤ m) :
    ((Finset.univ.filter fun c : Fin (m * n) =>
      m * n - i * n ≤ ((physicalPack2Net m n hn σ₁ σ₂).exec
        (x : Fin (m * n) → Fin (m * n)) c).val ∧ c.val < m * n - i * n).card : ℝ) ≤
      (epsB / 2) * (m * n) := by
  have h := hB x i hi₁ hiₘ
  simp only [largestKeyThresholdJ01] at h
  rw [← physical_threshold_count_eq_semantic2 hn σ₁ σ₂ x (i * n) i] at h
  exact h.le

/-- The low-side version follows by reversing values and cells. -/
theorem pack2_cut_low {m n : Nat} (hn : 0 < n) (σ₁ σ₂ : Scramble m n)
    {epsB : ℝ}
    (hB : HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) epsB)
    (x : Equiv.Perm (Fin (m * n))) (i : Nat) (hi₁ : 1 ≤ i) (hiₘ : i ≤ m) :
    ((Finset.univ.filter fun c : Fin (m * n) =>
      ((physicalPack2Net m n hn σ₁ σ₂).exec
        (x : Fin (m * n) → Fin (m * n)) c).val < i * n ∧ i * n ≤ c.val).card : ℝ) ≤
      (epsB / 2) * (m * n) := by
  let y := (physicalPack2Net m n hn σ₁ σ₂).exec (x : Fin (m * n) → Fin (m * n))
  let yf := (physicalPack2Net m n hn (flipScramble σ₁) (flipScramble σ₂)).exec
    (flipPerm x : Fin (m * n) → Fin (m * n))
  have hy : ∀ c, yf c = Fin.rev (y (Fin.rev c)) := by
    intro c
    change (physicalPack2Net m n hn (flipScramble σ₁) (flipScramble σ₂)).exec
      (fun w => Fin.rev (x (Fin.rev w))) c = _
    exact congrFun (physicalPack2Net_flip hn σ₁ σ₂ (x : Fin (m * n) → Fin (m * n))) c
  have hrev := card_low_eq_high y yf hy (i * n) (i * n)
  have hhi := pack2_cut_high hn (flipScramble σ₁) (flipScramble σ₂) hB
    (flipPerm x) i hi₁ hiₘ
  rw [hrev]
  simpa [y, yf] using hhi

/-- Prefix row counts specify genuinely variable child widths. Every cumulative
boundary still receives the two-sided B guarantee because it is row aligned. -/
def raggedPrefixRows (widthRows : Nat → Nat) (j : Nat) : Nat :=
  ∑ i ∈ Finset.range j, widthRows i

theorem pack2_ragged_boundary_high {m n : Nat} (hn : 0 < n) (σ₁ σ₂ : Scramble m n)
    {epsB : ℝ} (hB : HasPackSemanticPropertyB2 hn σ₁ σ₂ epsB)
    (x : Equiv.Perm (Fin (m * n))) (widthRows : Nat → Nat) (j f : Nat)
    (_hcut₁ : 1 ≤ f + raggedPrefixRows widthRows j)
    (hcutₘ : f + raggedPrefixRows widthRows j ≤ m) :
    ((Finset.univ.filter fun c : Fin (m * n) =>
      (f + raggedPrefixRows widthRows j) * n ≤
          ((physicalPack2Net m n hn σ₁ σ₂).exec
            (x : Fin (m * n) → Fin (m * n)) c).val ∧
        c.val < (f + raggedPrefixRows widthRows j) * n).card : ℝ) ≤
      (epsB / 2) * (m * n) := by
  by_cases hfull : f + raggedPrefixRows widthRows j = m
  · rw [hfull]
    have hempty : (Finset.univ.filter fun c : Fin (m * n) =>
        m * n ≤ ((physicalPack2Net m n hn σ₁ σ₂).exec
          (x : Fin (m * n) → Fin (m * n)) c).val ∧ c.val < m * n) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro c hc
      simp only [Finset.mem_univ] at hc
      have hv := ((physicalPack2Net m n hn σ₁ σ₂).exec
        (x : Fin (m * n) → Fin (m * n)) c).isLt
      omega
    rw [hempty]
    have heps : 0 ≤ epsB := by
      have h := hB x 1 (by norm_num) (by omega)
      simp only [one_mul] at h
      have hcount : (0 : ℝ) ≤
          (matrixOnesCountInRegion hn
            (semanticExec2 hn σ₁ σ₂
              (fun w => largestKeyThresholdJ01 (m := m) (n := n) n (x w))) 1 : ℝ) :=
        Nat.cast_nonneg _
      have hm : 0 < m := by omega
      have hmn : (0 : ℝ) < ((m * n : Nat) : ℝ) := by
        exact_mod_cast Nat.mul_pos hm hn
      have h' : (matrixOnesCountInRegion hn
          (semanticExec2 hn σ₁ σ₂
            (fun w => largestKeyThresholdJ01 (m := m) (n := n) n (x w))) 1 : ℝ) <
          epsB / 2 * ((m * n : Nat) : ℝ) := by
        simpa only [Nat.cast_mul] using h
      have hrhs : 0 < epsB / 2 * ((m * n : Nat) : ℝ) := lt_of_le_of_lt hcount h'
      have hhalf : 0 < epsB / 2 := by
        by_contra hh
        have hle : epsB / 2 * ((m * n : Nat) : ℝ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) hmn.le
        exact (not_lt_of_ge hle) hrhs
      linarith
    simp only [Finset.card_empty, Nat.cast_zero]
    apply mul_nonneg
    · exact div_nonneg heps (by norm_num)
    · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have htail : 1 ≤ m - (f + raggedPrefixRows widthRows j) := by omega
    have h := pack2_cut_high hn σ₁ σ₂ hB x (m - (f + raggedPrefixRows widthRows j))
      htail (by omega)
    have hprod : (m - (f + raggedPrefixRows widthRows j)) * n =
        m * n - (f + raggedPrefixRows widthRows j) * n := by
      rw [Nat.sub_mul]
    have hprefixLe : (f + raggedPrefixRows widthRows j) * n ≤ m * n :=
      Nat.mul_le_mul_right n hcutₘ
    have hcut : m * n - (m - (f + raggedPrefixRows widthRows j)) * n =
        (f + raggedPrefixRows widthRows j) * n := by rw [hprod]; omega
    simpa [hcut] using h

theorem pack2_ragged_boundary_low {m n : Nat} (hn : 0 < n) (σ₁ σ₂ : Scramble m n)
    {epsB : ℝ}
    (hB : HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) epsB)
    (x : Equiv.Perm (Fin (m * n))) (widthRows : Nat → Nat) (j f : Nat)
    (hcut₁ : 1 ≤ f + raggedPrefixRows widthRows j)
    (hcutₘ : f + raggedPrefixRows widthRows j ≤ m) :
    ((Finset.univ.filter fun c : Fin (m * n) =>
      ((physicalPack2Net m n hn σ₁ σ₂).exec
        (x : Fin (m * n) → Fin (m * n)) c).val <
          (f + raggedPrefixRows widthRows j) * n ∧
        (f + raggedPrefixRows widthRows j) * n ≤ c.val).card : ℝ) ≤
      (epsB / 2) * (m * n) := by
  exact pack2_cut_low hn σ₁ σ₂ hB x
    (f + raggedPrefixRows widthRows j) hcut₁ hcutₘ

/-- A variable-width child block leaks at most the sum of its lower- and
upper-boundary B errors. This is the rank-window input needed by the
unequal-width analysis. -/
theorem ragged_block_intruders_le {a : Nat} (net : ComparatorNetwork a)
    (x : Equiv.Perm (Fin a)) (lo hi : Nat) (EB : ℝ) (_hlo : lo ≤ hi)
    (hLow : ((Finset.univ.filter fun c : Fin a =>
      (net.exec (x : Fin a → Fin a) c).val < lo ∧ lo ≤ c.val).card : ℝ) ≤ EB)
    (hHigh : ((Finset.univ.filter fun c : Fin a =>
      hi ≤ (net.exec (x : Fin a → Fin a) c).val ∧ c.val < hi).card : ℝ) ≤ EB) :
    ((Finset.univ.filter fun c : Fin a =>
      lo ≤ c.val ∧ c.val < hi ∧
        ¬ (lo ≤ (net.exec (x : Fin a → Fin a) c).val ∧
          (net.exec (x : Fin a → Fin a) c).val < hi)).card : ℝ) ≤ 2 * EB := by
  let bad := Finset.univ.filter fun c : Fin a =>
    lo ≤ c.val ∧ c.val < hi ∧
      ¬ (lo ≤ (net.exec (x : Fin a → Fin a) c).val ∧
        (net.exec (x : Fin a → Fin a) c).val < hi)
  let low := Finset.univ.filter fun c : Fin a =>
    (net.exec (x : Fin a → Fin a) c).val < lo ∧ lo ≤ c.val
  let high := Finset.univ.filter fun c : Fin a =>
    hi ≤ (net.exec (x : Fin a → Fin a) c).val ∧ c.val < hi
  have hsub : bad ⊆ low ∪ high := by
    intro c hc
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp only [low, high, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hc with ⟨hcellL, hcellR, hnot⟩
    by_cases hvalL : (net.exec (x : Fin a → Fin a) c).val < lo
    · exact Or.inl ⟨hvalL, hcellL⟩
    · right
      have hvalLo : lo ≤ (net.exec (x : Fin a → Fin a) c).val := by omega
      have hvalHi : hi ≤ (net.exec (x : Fin a → Fin a) c).val := by
        by_contra h
        exact hnot ⟨hvalLo, Nat.lt_of_not_ge h⟩
      exact ⟨hvalHi, hcellR⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le low high)
  have hnat : bad.card ≤ low.card + high.card := hcard
  have hreal : (bad.card : ℝ) ≤ low.card + high.card := by exact_mod_cast hnat
  dsimp [bad, low, high] at hreal ⊢
  linarith

/-- Physical two-round pack instance of the variable-block intruder estimate.
The row widths may vary independently; only the cumulative boundaries must be
row aligned. -/
theorem pack2_ragged_block_intruders {m n : Nat} (hn : 0 < n) (σ₁ σ₂ : Scramble m n)
    {epsB : ℝ}
    (hBhigh : HasPackSemanticPropertyB2 hn σ₁ σ₂ epsB)
    (hBlow : HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) epsB)
    (x : Equiv.Perm (Fin (m * n))) (widthRows : Nat → Nat) (j f : Nat)
    (hlo₁ : 1 ≤ f + raggedPrefixRows widthRows j)
    (hloM : f + raggedPrefixRows widthRows j ≤ m)
    (hhi₁ : 1 ≤ f + raggedPrefixRows widthRows (j + 1))
    (hhiM : f + raggedPrefixRows widthRows (j + 1) ≤ m) :
    ((Finset.univ.filter fun c : Fin (m * n) =>
      (f + raggedPrefixRows widthRows j) * n ≤ c.val ∧
        c.val < (f + raggedPrefixRows widthRows (j + 1)) * n ∧
        ¬ ((f + raggedPrefixRows widthRows j) * n ≤
            ((physicalPack2Net m n hn σ₁ σ₂).exec
              (x : Fin (m * n) → Fin (m * n)) c).val ∧
          ((physicalPack2Net m n hn σ₁ σ₂).exec
              (x : Fin (m * n) → Fin (m * n)) c).val <
            (f + raggedPrefixRows widthRows (j + 1)) * n)).card : ℝ) ≤ 2 * (epsB / 2 * (m * n)) := by
  apply ragged_block_intruders_le (physicalPack2Net m n hn σ₁ σ₂) x
  · have hprefix : raggedPrefixRows widthRows (j + 1) =
        raggedPrefixRows widthRows j + widthRows j := by
      simp [raggedPrefixRows, Finset.sum_range_succ]
    rw [hprefix]
    exact Nat.mul_le_mul_right n
      (Nat.add_le_add_left (Nat.le_add_right _ _) f)
  · have hl := pack2_ragged_boundary_low hn σ₁ σ₂ hBlow x widthRows j f hlo₁ hloM
    simpa using hl
  · have hh := pack2_ragged_boundary_high hn σ₁ σ₂ hBhigh x widthRows (j + 1) f hhi₁ hhiM
    simpa using hh

end Tapered945
