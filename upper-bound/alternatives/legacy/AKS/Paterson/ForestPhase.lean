module

public import AKS.Paterson.ChildInvariant
public import AKS.Paterson.Accounting

/-! # Phase-aware shrinking clock and finite comparison fuel -/

@[expose] public section

namespace Paterson.Bags

def PhaseWindow (root : ℚ) (t : ℕ) : Prop :=
  fastParams.minCapacity ≤ capacity fastParams root t 0 *
    (if t % 2 = 0 then 1 else fastParams.nu)

theorem PhaseWindow.min {root : ℚ} (hr : 0 ≤ root) {t : ℕ} (hc : PhaseWindow root t) :
    fastParams.minCapacity ≤ capacity fastParams root t 0 := by
  unfold PhaseWindow at hc
  split_ifs at hc with hp
  · simpa only [mul_one] using hc
  · exact hc.trans (mul_le_of_le_one_right (capacity_nonneg fastParams hr _ _)
      fastParams.nu_lt_one.le)

theorem PhaseWindow.compare {root : ℚ} (hr : 0 ≤ root) {t : ℕ} (hc : PhaseWindow root t)
    (hskip : ¬ (t % 2 = 0 ∧ capacity fastParams root t 0 ≤ rootCeiling)) :
    PhaseWindow root (t + 1) := by
  unfold PhaseWindow at hc ⊢
  rw [capacity_stage_succ]
  by_cases hp : t % 2 = 0
  · have hnext : (t + 1) % 2 ≠ 0 := by omega
    rw [if_pos hp, mul_one] at hc
    rw [if_neg hnext]
    have hcap : rootCeiling < capacity fastParams root t 0 :=
      lt_of_not_ge (fun h ↦ hskip ⟨hp, h⟩)
    norm_num [rootCeiling, fastParams] at hc hcap ⊢
    linarith
  · have hnext : (t + 1) % 2 = 0 := by omega
    rw [if_neg hp] at hc
    rw [if_pos hnext, mul_one]
    simpa only [mul_comm] using hc

theorem PhaseWindow.child {root : ℚ} (hr : 0 ≤ root) {t : ℕ}
    (hc : PhaseWindow root t) (hp : t % 2 = 0) : PhaseWindow (childRoot root) (t + 1) := by
  unfold PhaseWindow at hc ⊢
  rw [if_pos hp, mul_one] at hc
  rw [child_capacity, if_neg (by omega : (t + 1) % 2 ≠ 0)]
  have hcap : capacity fastParams root t 1 = fastParams.A * capacity fastParams root t 0 := by
    simp only [capacity, pow_one, pow_zero, mul_one]; ring
  rw [hcap]
  norm_num [fastParams] at hc ⊢
  linarith

def FuelCertificate (root : ℚ) (t k fuel : ℕ) : Prop :=
  capacity fastParams root t 0 * fastParams.A ^ k * fastParams.nu ^ fuel < fastParams.minCapacity

theorem FuelCertificate.positive {root : ℚ} (hr : 0 ≤ root) {t k fuel : ℕ}
    (hc : PhaseWindow root t) (hf : FuelCertificate root t k fuel) : 0 < fuel := by
  by_contra hz
  have he : fuel = 0 := by omega
  have hcap := hc.min hr
  have hpow : (1 : ℚ) ≤ fastParams.A ^ k := one_le_pow₀ fastParams.A_gt_one.le
  have hprod := mul_le_mul_of_nonneg_left hpow (capacity_nonneg fastParams hr t 0)
  simp only [he, FuelCertificate, pow_zero, mul_one] at hf
  linarith

theorem FuelCertificate.compare {root : ℚ} {t k fuel : ℕ}
    (hf : FuelCertificate root t k (fuel + 1)) : FuelCertificate root (t + 1) k fuel := by
  unfold FuelCertificate at hf ⊢
  rw [capacity_stage_succ]
  rw [pow_succ] at hf
  convert hf using 1 <;> ring

theorem FuelCertificate.child {root : ℚ} {t k fuel : ℕ} (hk : 1 ≤ k)
    (hf : FuelCertificate root t k fuel) : FuelCertificate (childRoot root) (t + 1) (k - 1) fuel := by
  unfold FuelCertificate at hf ⊢
  rw [child_capacity]
  have hcap : capacity fastParams root t 1 = fastParams.A * capacity fastParams root t 0 := by
    simp only [capacity, pow_one, pow_zero, mul_one]; ring
  rw [hcap]
  have hpow : fastParams.A ^ k = fastParams.A ^ (k - 1) * fastParams.A := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [hpow] at hf
  convert hf using 1 <;> ring

theorem initial_fuel_certificate (k : ℕ) :
    FuelCertificate (initialCapacity k) 0 k (idealStageCount k) := by
  have h := mul_le_mul_of_nonneg_left (idealStageCount_converges k)
    (by norm_num : (0 : ℚ) ≤ 357 / 361)
  have heq : capacity fastParams (initialCapacity k) 0 0 * fastParams.A ^ k *
      fastParams.nu ^ idealStageCount k =
        (357 / 361) * ((2 * fastParams.A) ^ k * fastParams.nu ^ idealStageCount k) := by
    simp only [capacity, initialCapacity, pow_zero, mul_one, mul_pow]
    ring
  unfold FuelCertificate
  rw [heq]
  norm_num [fastParams] at h ⊢
  linarith

end Paterson.Bags
