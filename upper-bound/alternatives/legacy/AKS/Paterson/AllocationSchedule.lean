module

public import AKS.Paterson.ClippedRouting
public import AKS.Paterson.StoredSizes

/-! # A positional rounded allocation schedule for one tree

Capacities and allocation targets depend only on size and stage, never on
input ranks. Root splitting and forest iteration are separate operations.
-/

@[expose] public section

namespace Paterson.Bags

def nativeWidth (k l : ℕ) : ℚ := (2 : ℚ) ^ k / (2 : ℚ) ^ l

theorem nativeWidth_succ (k l : ℕ) : nativeWidth k (l + 1) = nativeWidth k l / 2 := by
  simp only [nativeWidth, pow_succ]
  field_simp

def subtreeTotal (root : ℚ) (k t l : ℕ) : ℕ :=
  scheduledSubtree fastParams (nativeWidth k l) (capacity fastParams root t l)

def bagTarget (root : ℚ) (k t l : ℕ) : ℕ :=
  if (t + l) % 2 = 0 then subtreeTotal root k t l - 4 * subtreeTotal root k t (l + 2) else 0

def fringeTarget (root : ℚ) (k t l : ℕ) : ℕ :=
  if (t + l) % 2 = 0 then subtreeTotal root k t l / 2 - subtreeTotal root k (t + 1) (l + 1) else 0

def coldTarget (root : ℚ) (k t : ℕ) : ℕ :=
  2 ^ k - if t % 2 = 0 then subtreeTotal root k t 0 else 2 * subtreeTotal root k t 1

def feedTarget (root : ℚ) (k t : ℕ) : ℕ :=
  if t % 2 = 0 then 0 else subtreeTotal root k (t + 1) 0 - 2 * subtreeTotal root k t 1

def AllocationInvariant {k : ℕ} (root : ℚ) (t : ℕ) (pl : StoredPlacement k) : Prop :=
  (∀ b, (pl.regs b).card = bagTarget root k t b.l) ∧ pl.cold.card = coldTarget root k t

def allocationStep {k : ℕ} (root : ℚ) (t : ℕ) (pl : StoredPlacement k) : StoredPlacement k :=
  pl.centralFeedRoute (fun b ↦ fringeTarget root k t b.l) (feedTarget root k t)

theorem subtreeTotal_dvd (root : ℚ) (k t l : ℕ) : 32 ∣ subtreeTotal root k t l :=
  ceil32_dvd _

theorem bagTarget_dvd (root : ℚ) (k t l : ℕ) : 32 ∣ bagTarget root k t l := by
  unfold bagTarget
  split_ifs
  · exact Nat.dvd_sub (subtreeTotal_dvd _ _ _ _) (dvd_mul_of_dvd_right (subtreeTotal_dvd _ _ _ _) 4)
  · exact dvd_zero _

theorem root_capacity_le_level {root : ℚ} (hr : 0 ≤ root) (t l : ℕ) :
    capacity fastParams root t 0 ≤ capacity fastParams root t l := by
  have hpow : (1 : ℚ) ≤ fastParams.A ^ l := one_le_pow₀ fastParams.A_gt_one.le
  simp only [capacity, pow_zero, mul_one]
  exact le_mul_of_one_le_right (mul_nonneg hr (pow_nonneg fastParams.nu_pos.le _)) hpow

theorem subtreeTotal_nesting {root : ℚ} {k t l : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t l) :
    2 * subtreeTotal root k t (l + 2) ≤ subtreeTotal root k (t + 1) (l + 1) ∧
      2 * subtreeTotal root k (t + 1) (l + 1) ≤ subtreeTotal root k t l := by
  have hwidth : nativeWidth k (l + 2) = nativeWidth k l / 4 := by
    rw [show l + 2 = (l + 1) + 1 by omega, nativeWidth_succ, nativeWidth_succ]
    ring
  have hcap : capacity fastParams root t (l + 2) =
      fastParams.A ^ 2 * capacity fastParams root t l := by
    rw [show l + 2 = (l + 1) + 1 by omega, capacity_level_succ, capacity_level_succ]
    ring
  have hnext : capacity fastParams root (t + 1) (l + 1) =
      fastParams.nu * fastParams.A * capacity fastParams root t l := by
    rw [capacity_stage_succ, capacity_level_succ]
    ring
  unfold subtreeTotal
  rw [hwidth, hcap, nativeWidth_succ, hnext]
  exact fast_clipped_nesting (width := nativeWidth k l) hc

theorem lattice_source_cards (a g next : ℕ) (heven : 2 ∣ a)
    (hsmall : 2 * g ≤ next) (hlarge : 2 * next ≤ a) :
    splitChildCard (a - 4 * g) (a / 2 - next) = next - 2 * g ∧
      splitParentCard (a - 4 * g) (a / 2 - next) = a - 2 * next := by
  have hhalf := Nat.mul_div_cancel' heven
  unfold splitChildCard splitParentCard
  omega

theorem target_source_cards {root : ℚ} {k t l : ℕ}
    (hc : fastParams.minCapacity ≤ capacity fastParams root t l)
    (hp : (t + l) % 2 = 0) :
    splitChildCard (bagTarget root k t l) (fringeTarget root k t l) =
      subtreeTotal root k (t + 1) (l + 1) - 2 * subtreeTotal root k t (l + 2) ∧
    splitParentCard (bagTarget root k t l) (fringeTarget root k t l) =
      subtreeTotal root k t l - 2 * subtreeTotal root k (t + 1) (l + 1) := by
  obtain ⟨hsmall, hlarge⟩ := subtreeTotal_nesting (k := k) hc
  simpa only [bagTarget, fringeTarget, if_pos hp] using
    lattice_source_cards _ _ _ (dvd_trans (by norm_num) (subtreeTotal_dvd root k t l)) hsmall hlarge

theorem ceil32_nat_of_dvd (n : ℕ) (hn : 32 ∣ n) : ceil32 (n : ℚ) = n := by
  obtain ⟨m, rfl⟩ := hn
  simp [ceil32]

theorem root_total_le {root : ℚ} (hr : 0 ≤ root) (k t : ℕ) (hk : 5 ≤ k) :
    subtreeTotal root k t 0 ≤ 2 ^ k := by
  have hcap := capacity_nonneg fastParams hr t 0
  have hreserve : 0 ≤ ancestorReserve fastParams (capacity fastParams root t 0) :=
    div_nonneg hcap (reserve_denominator_pos fastParams).le
  have hn : (0 : ℚ) ≤ (2 : ℚ) ^ k := by positivity
  have hideal : idealSubtree fastParams (nativeWidth k 0) (capacity fastParams root t 0) ≤ (2 : ℚ) ^ k := by
    apply max_le hn
    simp only [nativeWidth, pow_zero, div_one]
    linarith
  have hd : 32 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk
  have h := ceil32_mono hideal
  have heq : (2 : ℚ) ^ k = ((2 ^ k : ℕ) : ℚ) := by norm_cast
  rw [heq, ceil32_nat_of_dvd _ hd] at h
  exact h

theorem subtreeTotal_zero_of_deep {root : ℚ} {k t l : ℕ}
    (hl : k ≤ l) (hc : fastParams.minCapacity ≤ capacity fastParams root t l) :
    subtreeTotal root k t l = 0 := by
  have hp : (2 : ℚ) ^ k ≤ (2 : ℚ) ^ l := pow_le_pow_right₀ (by norm_num) hl
  have hw : nativeWidth k l ≤ 1 := by
    exact (div_le_one₀ (by positivity)).mpr hp
  have harg : nativeWidth k l - ancestorReserve fastParams (capacity fastParams root t l) ≤ 0 := by
    norm_num [fastParams, ancestorReserve] at hc ⊢
    linarith
  simp only [subtreeTotal, scheduledSubtree, idealSubtree, max_eq_left harg,
    ceil32_of_nonpos (le_refl 0)]

end Paterson.Bags
