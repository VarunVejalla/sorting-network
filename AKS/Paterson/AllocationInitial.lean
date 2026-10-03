module

public import AKS.Paterson.AllocationPreservation

/-! # Initial rounded allocation and its stage iteration

Paterson's initial root capacity is `(1 - 1/(4*A^2))*N`. For the checked
growth parameter this is `357*N/361`. Active deeper levels start empty.
-/

@[expose] public section

namespace Paterson.Bags

open Finset

def initialCapacity (k : ℕ) : ℚ := (2 : ℚ) ^ k * (357 / 361)

theorem initialCapacity_nonneg (k : ℕ) : 0 ≤ initialCapacity k := by
  unfold initialCapacity
  positivity

theorem ancestorReserve_scale (p : Params) (s cap : ℚ) :
    ancestorReserve p (s * cap) = s * ancestorReserve p cap := by
  unfold ancestorReserve
  ring

theorem initial_deep_reserve (k l : ℕ) (hl : 2 ≤ l) :
    nativeWidth k l ≤ ancestorReserve fastParams (capacity fastParams (initialCapacity k) 0 l) := by
  induction l, hl using Nat.le_induction with
  | base =>
    norm_num [nativeWidth, ancestorReserve, capacity, initialCapacity, fastParams]
    ring_nf
    exact le_rfl
  | succ l hl ih =>
    rw [nativeWidth_succ, capacity_level_succ, ancestorReserve_scale]
    have hn : 0 ≤ ancestorReserve fastParams (capacity fastParams (initialCapacity k) 0 l) :=
      div_nonneg (capacity_nonneg _ (initialCapacity_nonneg k) _ _) (reserve_denominator_pos _).le
    have hw : 0 ≤ nativeWidth k l := by unfold nativeWidth; positivity
    have hg := mul_le_mul_of_nonneg_right fastParams.A_gt_one.le hn
    linarith

theorem initial_deep_total_zero (k l : ℕ) (hl : 2 ≤ l) :
    subtreeTotal (initialCapacity k) k 0 l = 0 := by
  have harg := sub_nonpos.mpr (initial_deep_reserve k l hl)
  simp only [subtreeTotal, scheduledSubtree, idealSubtree, max_eq_left harg,
    ceil32_of_nonpos (le_refl 0)]

def scheduledInitial (k : ℕ) : StoredPlacement k :=
  StoredPlacement.centeredInitial k (subtreeTotal (initialCapacity k) k 0 0)

theorem centeredInitial_other_regs (k count : ℕ) (b : Bag k) (hb : b ≠ Bag.root k) :
    (StoredPlacement.centeredInitial k count).regs b = ∅ := by
  ext i
  simp [StoredPlacement.mem_regs, StoredPlacement.centeredInitial, Ne.symm hb]

theorem centeredInitial_cold_card (k count : ℕ) (hk : 1 ≤ k) (hc : 2 ∣ count)
    (hle : count ≤ 2 ^ k) : (StoredPlacement.centeredInitial k count).cold.card = 2 ^ k - count := by
  have hs : 2 ∣ (univ : Finset (Fin (2 ^ k))).card := by
    simp only [card_univ, Fintype.card_fin]
    exact dvd_pow_self 2 (by omega)
  have hm := centralFeed_card (univ : Finset (Fin (2 ^ k))) count hs hc
    (by simpa only [card_univ, Fintype.card_fin] using hle)
  have heq : (StoredPlacement.centeredInitial k count).cold =
      univ \ centralFeed (univ : Finset (Fin (2 ^ k))) count := by
    ext i
    simp [StoredPlacement.mem_cold, StoredPlacement.centeredInitial]
  rw [heq, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, hm]

theorem scheduledInitial_allocation (k : ℕ) (hk : 5 ≤ k) :
    AllocationInvariant (initialCapacity k) 0 (scheduledInitial k) := by
  have hroot := root_total_le (initialCapacity_nonneg k) k 0 hk
  have heven := dvd_trans (by norm_num : 2 ∣ 32) (subtreeTotal_dvd (initialCapacity k) k 0 0)
  refine ⟨?_, ?_⟩
  · intro b
    by_cases hb : b.l = 0
    · have heq : b = Bag.root k := by
        apply Bag.ext hb
        have hx := b.hx
        simp only [hb, pow_zero] at hx
        change b.x = 0
        omega
      subst b
      rw [scheduledInitial, StoredPlacement.centeredInitial_root_card _ _ (by omega) heven hroot]
      simp only [bagTarget, Bag.root, Nat.zero_add, Nat.zero_mod, ite_true,
        initial_deep_total_zero k 2 (le_refl 2), Nat.mul_zero, Nat.sub_zero]
    · have hne : b ≠ Bag.root k := by intro h; exact hb (congrArg Bag.l h)
      rw [scheduledInitial, centeredInitial_other_regs _ _ b hne, card_empty]
      unfold bagTarget
      by_cases hp : (0 + b.l) % 2 = 0
      · rw [if_pos hp, initial_deep_total_zero k b.l (by omega), Nat.zero_sub]
      · rw [if_neg hp]
  · rw [scheduledInitial, centeredInitial_cold_card _ _ (by omega) heven hroot]
    rfl

def allocationRun (k : ℕ) : ℕ → StoredPlacement k
  | 0 => scheduledInitial k
  | t + 1 => allocationStep (initialCapacity k) t (allocationRun k t)

/-- The concrete iterative allocation has all prescribed cardinalities while
the root stays above the rounding threshold. Comparisons and the rank
invariant remain separate from this purely positional result. -/
theorem allocationRun_invariant (k t : ℕ) (hk : 5 ≤ k)
    (hc : ∀ s, s < t → fastParams.minCapacity ≤ capacity fastParams (initialCapacity k) s 0) :
    AllocationInvariant (initialCapacity k) t (allocationRun k t) := by
  induction t with
  | zero => exact scheduledInitial_allocation k hk
  | succ t ih =>
    apply allocationStep_preserves (initialCapacity_nonneg k) hk (hc t (by omega))
    exact ih (fun s hs ↦ hc s (by omega))

end Paterson.Bags
