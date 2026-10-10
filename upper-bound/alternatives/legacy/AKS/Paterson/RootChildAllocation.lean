module

public import AKS.Paterson.RootChildRegions

/-! # Child-region sizes from allocation alone

These counts do not depend on the rank input or the stranger invariant.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem positionalBin_card {k L : ℕ} (U : Finset (Fin (2 ^ k)))
    (hd : 2 ^ L ∣ U.card) (q : ℕ) (hq : q < 2 ^ L) :
    (positionalBin U L q).card = U.card / 2 ^ L := by
  unfold positionalBin
  rw [card_image_of_injective _ (U.orderEmbOfFin rfl).injective]
  have hb : (q + 1) * (U.card / 2 ^ L) ≤ U.card := by
    exact (Nat.mul_le_mul_right _ hq).trans_eq (Nat.mul_div_cancel' hd)
  rw [positional_interval_card _ _ _ hb, Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]

theorem assignedHalf_deep_card {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (s : Fin 2) :
    ((deepRegisters pl hk).filter (assignedHalf pl s)).card = 32 * subtreeTotal root k t 6 := by
  have hsub : (deepRegisters pl hk).filter (assignedPrefix pl 1 s.val) ⊆
      (deepRegisters pl hk).filter (assignedPrefix pl 1 (s.val + 1)) := by
    intro i hi
    obtain ⟨hiD, hiP⟩ := mem_filter.mp hi
    apply mem_filter.mpr
    refine ⟨hiD, ?_⟩
    cases ho : pl.owner i with
    | none => simp only [assignedPrefix, ho] at hiP
    | some b => simp only [assignedPrefix, ho] at hiP ⊢; omega
  have heq : (deepRegisters pl hk).filter (assignedHalf pl s) =
      (deepRegisters pl hk).filter (assignedPrefix pl 1 (s.val + 1)) \
        (deepRegisters pl hk).filter (assignedPrefix pl 1 s.val) := by
    ext i
    simp only [assignedHalf, mem_filter, mem_sdiff]
    tauto
  rw [heq, card_sdiff_of_subset hsub,
    assigned_deep_prefix_card hr hk hc pl ha hp (by omega : 1 ≤ 6) (s.val + 1)
      (by have := s.isLt; norm_num <;> omega),
    assigned_deep_prefix_card hr hk hc pl ha hp (by omega : 1 ≤ 6) s.val
      (by have := s.isLt; norm_num <;> omega)]
  norm_num only [show (2 : ℕ) ^ (6 - 1) = 32 by norm_num]
  rw [Nat.add_mul, Nat.one_mul, Nat.add_mul, Nat.add_sub_cancel_left]

theorem childRegisters_card_allocation {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (s : Fin 2) : (childRegisters pl hk s).card = 2 ^ (k - 1) := by
  have hd : 2 ∣ (upperRegisters pl (by omega)).card :=
    dvd_trans (by norm_num) (upperRegisters_dvd64 hr hk hc pl ha hp)
  have hdis : Disjoint (positionalBin (upperRegisters pl (by omega)) 1 s.val)
      ((deepRegisters pl hk).filter (assignedHalf pl s)) :=
    (deepRegisters_disjoint_upper hk pl ha hp).symm.mono
      (positionalBin_subset _ _ _) (filter_subset _ _)
  unfold childRegisters
  rw [card_union_of_disjoint hdis, positionalBin_card _ hd s.val (by simpa using s.isLt),
    assignedHalf_deep_card hr hk hc pl ha hp s]
  have hcount : (upperRegisters pl (by omega)).card + 64 * subtreeTotal root k t 6 = 2 ^ k := by
    rw [← deepRegisters_card hr hk hc pl ha hp,
      ← card_union_of_disjoint (deepRegisters_disjoint_upper hk pl ha hp).symm,
      upper_deep_complete hk pl ha hp]
    simp
  have hU := Nat.mul_div_cancel' hd
  have hN : 2 * 2 ^ (k - 1) = 2 ^ k := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
  omega

theorem positionalBin_halves_disjoint {k : ℕ} (U : Finset (Fin (2 ^ k))) :
    Disjoint (positionalBin U 1 0) (positionalBin U 1 1) := by
  rw [disjoint_left]
  intro i hi0 hi1
  obtain ⟨a, ha, hea⟩ := mem_image.mp hi0
  obtain ⟨b, hb, heb⟩ := mem_image.mp hi1
  have hab := (U.orderEmbOfFin rfl).injective (hea.trans heb.symm)
  subst b
  have h0 := (mem_filter.mp ha).2
  have h1 := (mem_filter.mp hb).2
  norm_num at h0 h1
  omega

theorem childRegisters_disjoint {root : ℚ} {k t : ℕ} (hk : 6 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0) :
    Disjoint (childRegisters pl hk 0) (childRegisters pl hk 1) := by
  rw [disjoint_left]
  intro i hi0 hi1
  rcases mem_union.mp hi0 with hU0 | hD0 <;> rcases mem_union.mp hi1 with hU1 | hD1
  · exact disjoint_left.mp (positionalBin_halves_disjoint _) hU0 hU1
  · exact disjoint_left.mp (deepRegisters_disjoint_upper hk pl ha hp)
      (mem_filter.mp hD1).1 (positionalBin_subset _ _ _ hU0)
  · exact disjoint_left.mp (deepRegisters_disjoint_upper hk pl ha hp)
      (mem_filter.mp hD0).1 (positionalBin_subset _ _ _ hU1)
  · have h0 := (mem_filter.mp hD0).2.1
    have h1 := (mem_filter.mp hD1).2.2
    exact h1 h0

end Paterson.Bags
