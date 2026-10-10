module

public import AKS.Paterson.RootRebuildAllocation
public import AKS.Paterson.RootBinNesting

/-! # Rebuilt upper bags lie in their fixed native positional bins -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem rebuildUpper_four_bin {root : ℚ} {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (n2 n4 : ℕ) (hw : 0 < (upperRegisters pl hk).card / 16)
    (hd : 16 ∣ (upperRegisters pl hk).card)
    (hn : n4 ≤ (upperRegisters pl hk).card / 16) (b : Bag k) (hb : b.l = 4) :
    (rebuildUpper pl hk n2 n4).regs b ⊆ positionalBin (upperRegisters pl hk) 4 b.x := by
  rw [rebuildUpper_four_filter hk pl ha hp n2 n4 hw hd hn b hb]
  intro i hi
  obtain ⟨hu, hlo, hhi⟩ := mem_filter.mp hi
  have hin : i ∈ Set.range ((upperRegisters pl hk).orderEmbOfFin rfl) := by
    rw [range_orderEmbOfFin]; exact hu
  obtain ⟨j, rfl⟩ := hin
  rw [registerOrdinal_enum] at hlo hhi
  apply mem_image.mpr
  refine ⟨j, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
  norm_num only [show (2 : ℕ) ^ 4 = 16 by norm_num]
  rw [Nat.add_mul, Nat.one_mul]
  exact ⟨hlo, hhi.trans_le (Nat.add_le_add_left hn _)⟩

theorem rebuildUpper_two_bin {root : ℚ} {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (n2 n4 : ℕ) (hw : 0 < (upperRegisters pl hk).card / 16)
    (hd : 16 ∣ (upperRegisters pl hk).card) (b : Bag k) (hb : b.l = 2) :
    (rebuildUpper pl hk n2 n4).regs b ⊆ positionalBin (upperRegisters pl hk) 2 b.x := by
  rw [rebuildUpper_two_filter hk pl ha hp n2 n4 hw hd b hb]
  intro i hi
  obtain ⟨hu, htag, _, _⟩ := mem_filter.mp hi
  have hin : i ∈ Set.range ((upperRegisters pl hk).orderEmbOfFin rfl) := by
    rw [range_orderEmbOfFin]; exact hu
  obtain ⟨j, rfl⟩ := hin
  rw [registerOrdinal_enum] at htag
  have hwidth := bin_width_ancestor (upperRegisters pl hk) (l := 4) (L := 2) (by omega) hd
  norm_num at hwidth
  have htag' : j.val / (4 * ((upperRegisters pl hk).card / 16)) = b.x := by
    rw [mul_comm, ← Nat.div_div_eq_div_mul]
    exact htag
  apply mem_image.mpr
  refine ⟨j, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
  norm_num only [show (2 : ℕ) ^ 2 = 4 by norm_num]
  rw [hwidth]
  constructor
  · rw [← htag']
    exact Nat.div_mul_le_self _ _
  · rw [← htag', Nat.add_mul, Nat.one_mul]
    exact Nat.lt_div_mul_add (by positivity)

theorem allocatedRebuild_upper_bin {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (b : Bag k) (hb : b.l = 2 ∨ b.l = 4) :
    (allocatedRebuild root t pl (by omega)).regs b ⊆
      positionalBin (upperRegisters pl (by omega)) b.l b.x := by
  have hd : 16 ∣ (upperRegisters pl (by omega)).card :=
    dvd_trans (by norm_num) (upperRegisters_dvd64 hr hk hc pl ha hp)
  by_cases hw : 0 < (upperRegisters pl (by omega)).card / 16
  · rcases hb with hb2 | hb4
    · rw [hb2]
      exact rebuildUpper_two_bin (by omega) pl ha hp _ _ hw hd b hb2
    · rw [hb4]
      exact rebuildUpper_four_bin (by omega) pl ha hp _ _ hw hd
        (by have := allocated_rebuild_fit (by omega : 5 ≤ k) pl ha; omega) b hb4
  · have hzero : (upperRegisters pl (by omega)).card = 0 := by
      have := Nat.mul_div_cancel' hd
      omega
    have hs := rebuildUpper_low_regs_subset (by omega : 5 ≤ k) pl ha hp
      (bagTarget root k t 2) (bagTarget root k t 4) b (by omega)
    rw [card_eq_zero.mp hzero] at hs
    exact hs.trans (empty_subset _)

end Paterson.Bags
