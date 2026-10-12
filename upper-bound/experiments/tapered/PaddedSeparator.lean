import PrefixPadding
import AnyCutBounds
import RectanglePadding
import Mathlib.Tactic

namespace Tapered945

open Chvatal

/-- A rectangular pack restricted to the actual live register size. This
does not alter the integer flow: every requested live rank cut is retained. -/
def paddedPack2Net {m n a : Nat} (hn : 0 < n) (ha : a ≤ m * n)
    (σ₁ σ₂ : Scramble m n) : ComparatorNetwork a :=
  (physicalPack2Net m n hn σ₁ σ₂).restrictWires a ha

theorem paddedPack2Net_depth_le {m n a : Nat} (hn : 0 < n) (ha : a ≤ m * n)
    (σ₁ σ₂ : Scramble m n) :
    (paddedPack2Net hn ha σ₁ σ₂).depth ≤ (physicalPack2Net m n hn σ₁ σ₂).depth :=
  restrictWires_depth_le _ _ _

/-- Both crossing directions at every actual live cut. The error is charged
at padded rectangle size, plus one row for arbitrary-cut interpolation. -/
theorem paddedPack2Net_all_cut_bounds {m n a : Nat}
    (hn : 0 < n) (ha : a ≤ m * n) (σ₁ σ₂ : Scramble m n) (eps : Real)
    (heps : 0 ≤ eps)
    (hhigh : HasPackSemanticPropertyB2 hn σ₁ σ₂ eps)
    (hlow : HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) eps)
    (p : Equiv.Perm (Fin a)) (r : Nat) (hr : r ≤ a) :
    ((Finset.univ.filter fun c : Fin a =>
      r ≤ ((paddedPack2Net hn ha σ₁ σ₂).exec p c).val ∧ c.val < r).card : Real) ≤
      (eps / 2) * (m * n) + n ∧
    ((Finset.univ.filter fun c : Fin a =>
      ((paddedPack2Net hn ha σ₁ σ₂).exec p c).val < r ∧ r ≤ c.val).card : Real) ≤
      (eps / 2) * (m * n) + n := by
  have hE : 0 ≤ (eps / 2) * ((m : Real) * n) := by positivity
  have h := pack2_arbitrary_cut_bounds hn σ₁ σ₂ hhigh hlow hE
    (padRankPerm ha p) r (hr.trans ha)
  have hH := padding_boundary_high_card ha (physicalPack2Net m n hn σ₁ σ₂) p r
  have hL := padding_boundary_low_card ha (physicalPack2Net m n hn σ₁ σ₂) p r
  dsimp only at h
  dsimp only [paddedPack2Net]
  rw [hH, hL] at h
  exact h

/-- Conditional existence interface. All geometry and the restricted
comparator network are actual; existence of semantic B2 scramble witnesses
is still explicitly supplied by the caller. -/
structure PaddedSeparatorWitness (a : Nat) (eps : Real) where
  rows : Nat
  columns : Nat
  columns_pow : ∃ e : Nat, columns = 2 ^ e
  columns_ge : 16 ≤ columns
  rows_lo : 2 ^ 34 ≤ rows
  rows_hi : rows ≤ 2 ^ 35
  live_le : a ≤ rows * columns
  padding_lt : rows * columns - a < columns
  column_pos : 0 < columns
  scramble₁ : Scramble rows columns
  scramble₂ : Scramble rows columns
  network : ComparatorNetwork a
  network_eq : network = paddedPack2Net column_pos live_le scramble₁ scramble₂
  depth_le : network.depth ≤
    (physicalPack2Net rows columns column_pos scramble₁ scramble₂).depth
  crossing : ∀ (p : Equiv.Perm (Fin a)) r, r ≤ a →
    ((Finset.univ.filter fun c : Fin a =>
      r ≤ (network.exec p c).val ∧ c.val < r).card : Real) ≤
      (eps / 2) * (rows * columns) + columns ∧
    ((Finset.univ.filter fun c : Fin a =>
      (network.exec p c).val < r ∧ r ≤ c.val).card : Real) ≤
      (eps / 2) * (rows * columns) + columns

theorem large_padded_separator_nonempty (a : Nat) (ha : 2 ^ 38 ≤ a)
    (eps : Real) (heps : 0 ≤ eps)
    (provider : ∀ m n : Nat, (∃ e : Nat, n = 2 ^ e) → 16 ≤ n →
      2 ^ 34 ≤ m → m ≤ 2 ^ 35 → ∀ hn : 0 < n,
      ∃ σ₁ σ₂ : Scramble m n,
        HasPackSemanticPropertyB2 hn σ₁ σ₂ eps ∧
        HasPackSemanticPropertyB2 hn (flipScramble σ₁) (flipScramble σ₂) eps) :
    Nonempty (PaddedSeparatorWitness a eps) := by
  obtain ⟨m, n, hnPow, hnGe, hmLo, hmHi, hrect, hpad⟩ := nearby_rectangle a ha
  have hn : 0 < n := by omega
  obtain ⟨σ₁, σ₂, hhigh, hlow⟩ := provider m n hnPow hnGe hmLo hmHi hn
  exact ⟨{
    rows := m
    columns := n
    columns_pow := hnPow
    columns_ge := hnGe
    rows_lo := hmLo
    rows_hi := hmHi
    live_le := hrect
    padding_lt := hpad
    column_pos := hn
    scramble₁ := σ₁
    scramble₂ := σ₂
    network := paddedPack2Net hn hrect σ₁ σ₂
    network_eq := rfl
    depth_le := paddedPack2Net_depth_le hn hrect σ₁ σ₂
    crossing := paddedPack2Net_all_cut_bounds hn hrect σ₁ σ₂ eps heps hhigh hlow
  }⟩

/-- The geometry surcharge is tiny and is measured against the actual live
occupancy, not an independently rounded flow target. -/
theorem padded_separator_error_le_live {a : Nat} {eps : Real}
    (w : PaddedSeparatorWitness a eps) (heps : 0 ≤ eps) :
    (eps / 2) * (w.rows * w.columns) + w.columns ≤
      (eps / 2 + (eps / 2 + 1) / ((2 : Real) ^ 34 - 1)) * a := by
  have hrow := Nat.mul_le_mul_right w.columns w.rows_lo
  have hpad : w.rows * w.columns < a + w.columns := by
    have := w.live_le
    have := w.padding_lt
    omega
  have hscale : 17179869183 * w.columns ≤ a := by
    norm_num at hrow
    omega
  have hscaleR : (17179869183 : Real) * w.columns ≤ a := by exact_mod_cast hscale
  have hpadR : (w.rows : Real) * w.columns ≤ (a : Real) + w.columns := by
    exact_mod_cast hpad.le
  have hmain := mul_le_mul_of_nonneg_left hpadR (show 0 ≤ eps / 2 by positivity)
  have hcost := mul_le_mul_of_nonneg_left hscaleR (show 0 ≤ eps / 2 + 1 by positivity)
  norm_num [div_eq_mul_inv] at hmain hcost ⊢
  nlinarith

theorem padded_separator_crossing_le_live {a : Nat} {eps : Real}
    (w : PaddedSeparatorWitness a eps) (heps : 0 ≤ eps)
    (p : Equiv.Perm (Fin a)) (r : Nat) (hr : r ≤ a) :
    ((Finset.univ.filter fun c : Fin a =>
      r ≤ (w.network.exec p c).val ∧ c.val < r).card : Real) ≤
      (eps / 2 + (eps / 2 + 1) / ((2 : Real) ^ 34 - 1)) * a ∧
    ((Finset.univ.filter fun c : Fin a =>
      (w.network.exec p c).val < r ∧ r ≤ c.val).card : Real) ≤
      (eps / 2 + (eps / 2 + 1) / ((2 : Real) ^ 34 - 1)) * a := by
  have h := w.crossing p r hr
  have he := padded_separator_error_le_live w heps
  exact ⟨h.1.trans he, h.2.trans he⟩

end Tapered945
