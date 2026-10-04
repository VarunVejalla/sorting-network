module

public import AKS.Paterson.RootRebuildNumerics
public import Mathlib.Algebra.Field.GeomSum

/-! # Global deep contamination of coarse native partitions

The union counts each deep wire according to its owning bag's coarse native
interval. Active even levels start at level six at a root-splitting stage.
-/

@[expose] public section

namespace Paterson.Bags

open Finset BigOperators

def levelStrangers {k : ℕ} (pl : StoredPlacement k) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (L l : ℕ) (hl : l ≤ k) : Finset (Fin (2 ^ k)) :=
  univ.biUnion fun x : Fin (2 ^ l) ↦
    (pl.regs ⟨l, x.val, hl, x.isLt⟩).filter
      (fun i ↦ (⟨l, x.val, hl, x.isLt⟩ : Bag k).Strange (l - L + 1) i w)

theorem levelStrangers_bound {root : ℚ} {k t : ℕ}
    (pl : StoredPlacement k) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w)
    (L l : ℕ) (hl : l ≤ k) :
    ((levelStrangers pl w L l hl).card : ℚ) ≤
      (2 : ℚ) ^ l * (fastParams.mu * fastParams.delta ^ (l - L) * capacity fastParams root t l) := by
  have hcard : (univ.biUnion (fun x : Fin (2 ^ l) ↦
      (pl.regs ⟨l, x.val, hl, x.isLt⟩).filter
        (fun i ↦ (⟨l, x.val, hl, x.isLt⟩ : Bag k).Strange (l - L + 1) i w))).card ≤
      ∑ x : Fin (2 ^ l), (⟨l, x.val, hl, x.isLt⟩ : Bag k).strangers (l - L + 1) w
        (pl.regs ⟨l, x.val, hl, x.isLt⟩) := card_biUnion_le
  have hQ : ((levelStrangers pl w L l hl).card : ℚ) ≤
      ∑ x : Fin (2 ^ l), ((⟨l, x.val, hl, x.isLt⟩ : Bag k).strangers (l - L + 1) w
        (pl.regs ⟨l, x.val, hl, x.isLt⟩) : ℚ) := by exact_mod_cast hcard
  apply hQ.trans
  calc (∑ x : Fin (2 ^ l), ((⟨l, x.val, hl, x.isLt⟩ : Bag k).strangers (l - L + 1) w
        (pl.regs ⟨l, x.val, hl, x.isLt⟩) : ℚ)) ≤
      ∑ _ : Fin (2 ^ l), (fastParams.mu * fastParams.delta ^ (l - L) * capacity fastParams root t l) := by
        apply sum_le_sum
        intro x _
        simpa only [Nat.add_sub_cancel] using hi ⟨l, x.val, hl, x.isLt⟩ (l - L + 1) (by omega)
    _ = _ := by simp

def deepErrors {k : ℕ} (pl : StoredPlacement k) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (L : ℕ) : Finset (Fin (2 ^ k)) :=
  (range (k + 1)).biUnion fun q ↦
    if h : 6 + 2 * q ≤ k then levelStrangers pl w L (6 + 2 * q) h else ∅

theorem finite_geometric_upper {r : ℚ} (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∑ q ∈ range n, r ^ q) ≤ 1 / (1 - r) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - r)).mpr
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg hr n]

theorem deep_level_factor {root : ℚ} {t L : ℕ} (hL : L ≤ 6) (q : ℕ) :
    (2 : ℚ) ^ (6 + 2 * q) *
      (fastParams.mu * fastParams.delta ^ (6 + 2 * q - L) * capacity fastParams root t (6 + 2 * q)) =
    (64 * fastParams.mu * fastParams.delta ^ (6 - L) * capacity fastParams root t 6) *
      (4 * fastParams.delta ^ 2 * fastParams.A ^ 2) ^ q := by
  rw [show 6 + 2 * q - L = (6 - L) + 2 * q by omega]
  simp only [capacity, pow_add, pow_mul, mul_pow]
  norm_num
  ring

theorem deepErrors_bound {root : ℚ} (hr : 0 ≤ root) {k t L : ℕ} (hL : L ≤ 6)
    (pl : StoredPlacement k) (w : Fin (2 ^ k) → Fin (2 ^ k))
    (hi : Invariant fastParams (fun c ↦ capacity fastParams root t c.l) pl.regs w) :
    ((deepErrors pl w L).card : ℚ) ≤
      64 * fastParams.mu * fastParams.delta ^ (6 - L) * capacity fastParams root t 6 /
        (1 - 4 * fastParams.delta ^ 2 * fastParams.A ^ 2) := by
  let B := 64 * fastParams.mu * fastParams.delta ^ (6 - L) * capacity fastParams root t 6
  let r := 4 * fastParams.delta ^ 2 * fastParams.A ^ 2
  have hB : 0 ≤ B :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) fastParams.mu_pos.le)
      (pow_nonneg fastParams.delta_pos.le _))
      (capacity_nonneg fastParams hr _ _)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; norm_num [fastParams]
  have hcard : (deepErrors pl w L).card ≤
      ∑ q ∈ range (k + 1), (if h : 6 + 2 * q ≤ k then
        levelStrangers pl w L (6 + 2 * q) h else ∅).card := card_biUnion_le
  have hQ : ((deepErrors pl w L).card : ℚ) ≤
      ∑ q ∈ range (k + 1), ((if h : 6 + 2 * q ≤ k then
        levelStrangers pl w L (6 + 2 * q) h else ∅).card : ℚ) := by exact_mod_cast hcard
  apply hQ.trans
  calc (∑ q ∈ range (k + 1), ((if h : 6 + 2 * q ≤ k then
        levelStrangers pl w L (6 + 2 * q) h else ∅).card : ℚ)) ≤
      ∑ q ∈ range (k + 1), B * r ^ q := by
        apply sum_le_sum
        intro q _
        split_ifs with hq
        · have hlevel := levelStrangers_bound pl w hi L (6 + 2 * q) hq
          rw [deep_level_factor hL q] at hlevel
          exact hlevel
        · simp only [card_empty, Nat.cast_zero]
          exact mul_nonneg hB (pow_nonneg hr0 _)
    _ = B * ∑ q ∈ range (k + 1), r ^ q := by rw [mul_sum]
    _ ≤ B * (1 / (1 - r)) := mul_le_mul_of_nonneg_left (finite_geometric_upper hr0 hr1 _) hB
    _ = _ := by dsimp [B, r]; ring

end Paterson.Bags
