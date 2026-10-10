module

public import AKS.Paterson.RootChildAllocation
public import AKS.Paterson.ChildLabels

/-! # Rebuilt bag ownership respects the two fixed child regions -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem rebuilt_regs_subset_child {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (b : Bag k) (hb : 1 ≤ b.l) (s : Fin 2)
    (hs : b.x / 2 ^ (b.l - 1) = s.val) :
    (allocatedRebuild root t pl (by omega)).regs b ⊆ childRegisters pl hk s := by
  intro i hi
  by_cases hb6 : 6 ≤ b.l
  · have hiOld : i ∈ pl.regs b := by
      change i ∈ (rebuildUpper pl (by omega) _ _).regs b at hi
      rw [rebuildUpper_deep_regs hk pl ha hp _ _ b hb6] at hi
      exact hi
    apply mem_union_right
    refine mem_filter.mpr ⟨mem_deepRegisters_of_owner pl hk b hb6 hiOld, ?_⟩
    simp only [assignedHalf, assignedPrefix, (pl.mem_regs b i).mp hiOld]
    change b.x / 2 ^ (b.l - 1) < s.val + 1 ∧ ¬ b.x / 2 ^ (b.l - 1) < s.val
    rw [hs]
    omega
  · by_cases hb24 : b.l = 2 ∨ b.l = 4
    · have hd : 2 ^ b.l ∣ (upperRegisters pl (by omega)).card :=
        dvd_trans (Nat.pow_dvd_pow 2 (by omega : b.l ≤ 6))
          (upperRegisters_dvd64 hr hk hc pl ha hp)
      have hsub := (allocatedRebuild_upper_bin hr hk hc pl ha hp b hb24).trans
        (positionalBin_ancestor (upperRegisters pl (by omega)) hb hd b.x)
      rw [hs] at hsub
      exact mem_union_left _ (hsub hi)
    · have hempty := rebuildUpper_other_low_empty (by omega : 5 ≤ k) pl ha hp
        (bagTarget root k t 2) (bagTarget root k t 4) b (by omega) (by omega) (by omega)
      change i ∈ (rebuildUpper pl (by omega) _ _).regs b at hi
      rw [hempty] at hi
      exact False.elim (notMem_empty i hi)

theorem childRegisters_pair_disjoint {root : ℚ} {k t : ℕ} (hk : 6 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (s r : Fin 2) (hsr : s ≠ r) : Disjoint (childRegisters pl hk s) (childRegisters pl hk r) := by
  fin_cases s <;> fin_cases r
  · exact False.elim (hsr rfl)
  · exact childRegisters_disjoint hk pl ha hp
  · exact (childRegisters_disjoint hk pl ha hp).symm
  · exact False.elim (hsr rfl)

theorem rebuilt_child_owner_half {root : ℚ} (hr : 0 ≤ root) {k t : ℕ} (hk : 6 ≤ k)
    (hc : fastParams.minCapacity ≤ capacity fastParams root t 0)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (s : Fin 2) {i : Fin (2 ^ k)} (hiS : i ∈ childRegisters pl hk s)
    (b : Bag k) (hiB : i ∈ (allocatedRebuild root t pl (by omega)).regs b) :
    1 ≤ b.l ∧ b.x / 2 ^ (b.l - 1) = s.val := by
  have hb : 1 ≤ b.l := by
    by_contra h
    have he := rebuildUpper_other_low_empty (by omega : 5 ≤ k) pl ha hp
      (bagTarget root k t 2) (bagTarget root k t 4) b (by omega) (by omega) (by omega)
    change i ∈ (rebuildUpper pl (by omega) _ _).regs b at hiB
    rw [he] at hiB
    exact notMem_empty i hiB
  have hq : b.x / 2 ^ (b.l - 1) < 2 := by
    have h := (b.ancestor (b.l - 1)).hx
    change b.x / 2 ^ (b.l - 1) < 2 ^ (b.l - (b.l - 1)) at h
    simpa only [show b.l - (b.l - 1) = 1 by omega, pow_one] using h
  let q : Fin 2 := ⟨b.x / 2 ^ (b.l - 1), hq⟩
  have hiQ := rebuilt_regs_subset_child hr hk hc pl ha hp b hb q rfl hiB
  have hqs : q = s := by
    by_contra hne
    exact disjoint_left.mp (childRegisters_pair_disjoint hk pl ha hp q s hne) hiQ hiS
  exact ⟨hb, congrArg Fin.val hqs⟩

end Paterson.Bags
