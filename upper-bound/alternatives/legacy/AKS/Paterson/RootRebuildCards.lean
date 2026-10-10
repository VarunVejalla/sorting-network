module

public import AKS.Paterson.RootRebuildPlacement
public import AKS.Paterson.RootSortedBins

/-! # Cardinalities of the positional root rebuild -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem div_mod_segment {a width x n : ℕ} (hw : 0 < width) (hn : n ≤ width) :
    a / width = x ∧ a % width < n ↔ x * width ≤ a ∧ a < x * width + n := by
  have hmod := Nat.mod_lt a hw
  have hdecomp : a / width * width + a % width = a := by
    simpa only [mul_comm] using Nat.div_add_mod a width
  constructor
  · rintro ⟨hx, hm⟩
    rw [hx] at hdecomp
    omega
  · rintro ⟨hlo, hhi⟩
    have hdivlo : x ≤ a / width := (Nat.le_div_iff_mul_le hw).mpr hlo
    have hdivhi : a / width < x + 1 := (Nat.div_lt_iff_lt_mul hw).mpr (by
      rw [Nat.add_mul, Nat.one_mul]
      omega)
    have hx : a / width = x := by omega
    rw [hx] at hdecomp
    exact ⟨hx, by omega⟩

theorem rebuildUpper_low_regs_subset {root : ℚ} {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (n2 n4 : ℕ) (b : Bag k) (hb : b.l < 6) :
    (rebuildUpper pl hk n2 n4).regs b ⊆ upperRegisters pl hk := by
  intro i hi
  by_contra hout
  rw [StoredPlacement.mem_regs, rebuildUpper_owner_outside pl hk n2 n4 hout,
    ← StoredPlacement.mem_regs] at hi
  exact hout (mem_upperRegisters_of_low hk pl ha hp b hb hi)

theorem rebuildUpper_other_low_empty {root : ℚ} {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (n2 n4 : ℕ) (b : Bag k) (hb : b.l < 6) (hb2 : b.l ≠ 2) (hb4 : b.l ≠ 4) :
    (rebuildUpper pl hk n2 n4).regs b = ∅ := by
  apply subset_empty.mp
  intro i hi
  have hu := rebuildUpper_low_regs_subset hk pl ha hp n2 n4 b hb hi
  have ho := (StoredPlacement.mem_regs _ b i).mp hi
  rcases rebuildUpper_owner_inside pl hk n2 n4 hu with he | ⟨c, he, hc⟩
  · rw [he] at ho; cases ho
  · have hcb := Option.some.inj (he.symm.trans ho)
    subst c
    omega

theorem rebuildUpper_four_filter {root : ℚ} {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (n2 n4 : ℕ) (hw : 0 < (upperRegisters pl hk).card / 16)
    (hdiv : 16 ∣ (upperRegisters pl hk).card)
    (hn : n4 ≤ (upperRegisters pl hk).card / 16) (b : Bag k) (hb : b.l = 4) :
    (rebuildUpper pl hk n2 n4).regs b =
      (upperRegisters pl hk).filter (fun i ↦
        b.x * ((upperRegisters pl hk).card / 16) ≤ registerOrdinal (upperRegisters pl hk) i ∧
        registerOrdinal (upperRegisters pl hk) i < b.x * ((upperRegisters pl hk).card / 16) + n4) := by
  ext i
  by_cases hu : i ∈ upperRegisters pl hk
  · have ha := registerOrdinal_lt (upperRegisters pl hk) hu
    have hsize := Nat.mul_div_cancel' hdiv
    have hx : registerOrdinal (upperRegisters pl hk) i /
        ((upperRegisters pl hk).card / 16) < 16 :=
      (Nat.div_lt_iff_lt_mul hw).mpr (by simpa only [hsize] using ha)
    simp only [StoredPlacement.mem_regs, rebuildUpper,
      mem_filter, hu, true_and, if_true, dif_pos hx]
    rw [← div_mod_segment hw hn]
    split_ifs with h4 h2
    · simp only [Option.some.injEq, h4, and_true]
      constructor
      · intro he; exact congrArg Bag.x he
      · intro he; exact Bag.ext hb.symm he
    · constructor
      · intro he
        have hl := congrArg Bag.l (Option.some.inj he)
        change 2 = b.l at hl
        omega
      · rintro ⟨_, he⟩; exact False.elim (h4 he)
    · constructor
      · intro he; cases he
      · rintro ⟨_, he⟩; exact False.elim (h4 he)
  · have hnmem : i ∉ (rebuildUpper pl hk n2 n4).regs b :=
      fun hi ↦ hu (rebuildUpper_low_regs_subset hk pl ha hp n2 n4 b (by omega) hi)
    simp only [hnmem, mem_filter, hu, false_and]

theorem rebuildUpper_four_card {root : ℚ} {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (n2 n4 : ℕ) (hw : 0 < (upperRegisters pl hk).card / 16)
    (hdiv : 16 ∣ (upperRegisters pl hk).card)
    (hn : n4 ≤ (upperRegisters pl hk).card / 16) (b : Bag k) (hb : b.l = 4) :
    ((rebuildUpper pl hk n2 n4).regs b).card = n4 := by
  rw [rebuildUpper_four_filter hk pl ha hp n2 n4 hw hdiv hn b hb, filter_regs_card]
  simp only [registerOrdinal_enum]
  have hx : b.x + 1 ≤ 16 := by have := b.hx; rw [hb] at this; omega
  have hsize := Nat.mul_div_cancel' hdiv
  have hbnd : b.x * ((upperRegisters pl hk).card / 16) + n4 ≤
      (upperRegisters pl hk).card := by
    have h := Nat.mul_le_mul_right ((upperRegisters pl hk).card / 16) hx
    rw [Nat.add_mul, Nat.one_mul, hsize] at h
    omega
  rw [positional_interval_card _ _ _ hbnd, Nat.add_sub_cancel_left]

theorem rebuildUpper_two_filter {root : ℚ} {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (n2 n4 : ℕ) (hw : 0 < (upperRegisters pl hk).card / 16)
    (hdiv : 16 ∣ (upperRegisters pl hk).card) (b : Bag k) (hb : b.l = 2) :
    (rebuildUpper pl hk n2 n4).regs b =
      (upperRegisters pl hk).filter (fun i ↦
        registerOrdinal (upperRegisters pl hk) i / ((upperRegisters pl hk).card / 16) / 4 = b.x ∧
        n4 ≤ registerOrdinal (upperRegisters pl hk) i % ((upperRegisters pl hk).card / 16) ∧
        registerOrdinal (upperRegisters pl hk) i % ((upperRegisters pl hk).card / 16) < n4 + n2 / 4) := by
  ext i
  by_cases hu : i ∈ upperRegisters pl hk
  · have hai := registerOrdinal_lt (upperRegisters pl hk) hu
    have hsize := Nat.mul_div_cancel' hdiv
    have hx : registerOrdinal (upperRegisters pl hk) i /
        ((upperRegisters pl hk).card / 16) < 16 :=
      (Nat.div_lt_iff_lt_mul hw).mpr (by simpa only [hsize] using hai)
    simp only [StoredPlacement.mem_regs, rebuildUpper,
      mem_filter, hu, true_and, if_true, dif_pos hx]
    split_ifs with h4 h2
    · constructor
      · intro he
        have hl := congrArg Bag.l (Option.some.inj he)
        change 4 = b.l at hl
        omega
      · rintro ⟨_, he, _⟩; omega
    · simp only [Option.some.injEq]
      constructor
      · intro he; exact ⟨congrArg Bag.x he, by omega, h2⟩
      · rintro ⟨he, _, _⟩; exact Bag.ext hb.symm he
    · constructor
      · intro he; cases he
      · rintro ⟨_, _, he⟩; exact False.elim (h2 he)
  · have hnmem : i ∉ (rebuildUpper pl hk n2 n4).regs b :=
      fun hi ↦ hu (rebuildUpper_low_regs_subset hk pl ha hp n2 n4 b (by omega) hi)
    simp only [hnmem, mem_filter, hu, false_and]

end Paterson.Bags
