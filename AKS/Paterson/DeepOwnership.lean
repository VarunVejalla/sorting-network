module

public import AKS.Paterson.UpperRegionCounts
public import AKS.Paterson.PrefixDiscrepancy

/-! # Actual deep owners and their coarse error set -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem mem_levelRegisters {k : ℕ} (pl : StoredPlacement k) (b : Bag k) {i : Fin (2 ^ k)}
    (hi : i ∈ pl.regs b) : i ∈ levelRegisters pl b.l b.hl := by
  exact mem_biUnion.mpr ⟨⟨b.x, b.hx⟩, mem_univ _, hi⟩

theorem active_owner_level {root : ℚ} {k t : ℕ} (pl : StoredPlacement k)
    (ha : AllocationInvariant root t pl) (b : Bag k) {i : Fin (2 ^ k)}
    (hi : i ∈ pl.regs b) : (t + b.l) % 2 = 0 := by
  by_contra hp
  rw [allocated_inactive_empty pl ha b hp] at hi
  exact notMem_empty i hi

theorem mem_upperRegisters_of_low {root : ℚ} {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (b : Bag k) (hl : b.l < 6) {i : Fin (2 ^ k)} (hi : i ∈ pl.regs b) :
    i ∈ upperRegisters pl hk := by
  have hactive := active_owner_level pl ha b hi
  have hcases : b.l = 0 ∨ b.l = 2 ∨ b.l = 4 := by omega
  rcases hcases with h0 | h2 | h4
  · have heq : b = Bag.root k := by
      apply Bag.ext h0
      have hx := b.hx
      simp only [h0, pow_zero] at hx
      change b.x = 0
      omega
    exact mem_union_left _ (mem_union_left _ (mem_union_right _ (heq ▸ hi)))
  · apply mem_union_left
    apply mem_union_right
    simpa only [h2] using mem_levelRegisters pl b hi
  · apply mem_union_right
    simpa only [h4] using mem_levelRegisters pl b hi

theorem outside_upper_has_deep_owner {root : ℚ} {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    {i : Fin (2 ^ k)} (hi : i ∉ upperRegisters pl hk) :
    ∃ b : Bag k, 6 ≤ b.l ∧ i ∈ pl.regs b := by
  rcases pl.complete i with hc | ⟨b, hb⟩
  · exact False.elim (hi (mem_union_left _ (mem_union_left _ (mem_union_left _ hc))))
  · refine ⟨b, ?_, hb⟩
    by_contra hl
    exact hi (mem_upperRegisters_of_low hk pl ha hp b (by omega) hb)

theorem deepErrors_contains {root : ℚ} {k t L : ℕ} (hL : L ≤ 6)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (w : Fin (2 ^ k) → Fin (2 ^ k)) (b : Bag k) (hb : 6 ≤ b.l)
    {i : Fin (2 ^ k)} (hi : i ∈ pl.regs b)
    (hwrong : nativeBagIdx k L (w i).val ≠ (b.ancestor (b.l - L)).x) :
    i ∈ deepErrors pl w L := by
  have hactive := active_owner_level pl ha b hi
  let q := (b.l - 6) / 2
  have hlevel : b.l = 6 + 2 * q := by dsimp [q]; omega
  have hq : q < k + 1 := by have := b.hl; dsimp [q]; omega
  have hql : 6 + 2 * q ≤ k := by rw [← hlevel]; exact b.hl
  have hs : b.Strange (b.l - L + 1) i w := by
    simp only [Bag.Strange, show b.l - L + 1 ≠ 0 by omega, false_or, Nat.add_sub_cancel]
    unfold Bag.Native
    have hal : (b.ancestor (b.l - L)).l = L := by change b.l - (b.l - L) = L; omega
    simpa only [hal] using hwrong
  apply mem_biUnion.mpr
  refine ⟨q, mem_range.mpr hq, ?_⟩
  rw [dif_pos hql]
  unfold levelStrangers
  let x : Fin (2 ^ (6 + 2 * q)) := ⟨b.x, by rw [← hlevel]; exact b.hx⟩
  refine mem_biUnion.mpr ⟨x, mem_univ _, ?_⟩
  have heq : (⟨6 + 2 * q, x.val, hql, x.isLt⟩ : Bag k) = b := Bag.ext hlevel.symm rfl
  rw [heq, ← hlevel]
  exact mem_filter.mpr ⟨hi, hs⟩

end Paterson.Bags
