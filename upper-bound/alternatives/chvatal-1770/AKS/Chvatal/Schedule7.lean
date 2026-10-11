module

public import AKS.Chvatal.Tree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Chvátal §3/§7 capacity, level schedule and allocation (DCS-TR-294 §3 + §7)

Envelopes `α* = (6(t−d)+25)/12`, `ω* = (t+2)/3` at the §7 parameters, realized by integer floors and
parity rounding, with `tf = 3d−20` and meeting level `d−6`. -/

namespace Chvatal

/-- §3 capacity (§7 parameters `br = 64`, `A = 4096`, `ν = 1/64`):
`c(i,t) = N · A^i · ν^t / (A ν br)` with `N = 64^d`. -/
def capacity (d i t : Nat) : Rat :=
  ((64 ^ d : Nat) : Rat) * 4096 ^ i * (1 / 64) ^ t / 4096

theorem capacity_pos (d i t : Nat) : 0 < capacity d i t := by
  unfold capacity; positivity

theorem capacity_nonneg (d i t : Nat) : 0 ≤ capacity d i t := (capacity_pos d i t).le

theorem capacity_succ_level (d i t : Nat) : capacity d (i + 1) t = 4096 * capacity d i t := by
  unfold capacity
  ring

theorem capacity_succ_stage (d i t : Nat) : capacity d i (t + 1) = (1 / 64) * capacity d i t := by
  unfold capacity
  ring

/-- Active-level contribution factor `Q = A² br²`. -/
def capacityRatio : Rat := 4096 ^ 2 * 64 ^ 2

theorem capacityRatio_pos : 0 < capacityRatio := by unfold capacityRatio; norm_num

/-- Weighted capacity along an even step: `br^(2m) * c(i+2m) = Q^m * c(i)`. -/
theorem capacity_weighted_step (d i t m : Nat) :
    (64 : Rat) ^ (2 * m) * capacity d (i + 2 * m) t = capacityRatio ^ m * capacity d i t := by
  induction m with
  | zero => simp [capacityRatio]
  | succ m ih =>
    rw [show i + 2 * (m + 1) = i + 2 * m + 1 + 1 by omega, capacity_succ_level,
      capacity_succ_level]
    unfold capacityRatio at *
    linear_combination (4096 ^ 2 * 64 ^ 2 : Rat) * ih

def tf7 (d : Nat) : Nat := 3 * d - 20
def meetLevel7 (d : Nat) : Nat := d - 6

def ceilParity (m parity : Nat) : Nat :=
  if m % 2 = parity % 2 then m else m + 1

/-- `⌈α*(t)⌉` before parity: `0` on `t ≤ d−5`, else `(t−d+6)/2`. -/
def alphaStarLower (d t : Nat) : Nat :=
  if t + 5 ≤ d then 0 else (t + 6 - d) / 2

/-- `⌈ω*(t)⌉` before parity: `(t+4)/3`. -/
def omegaStarLower (t : Nat) : Nat := (t + 4) / 3

def alpha7 (d t : Nat) : Nat :=
  if t = 0 then 0
  else if t = 1 then 1
  else ceilParity (alphaStarLower d t) t

def omega7 (_d t : Nat) : Nat :=
  if t = 0 then 0
  else if t = 1 then 1
  else ceilParity (omegaStarLower t) t

theorem alpha7_of_ge_two (d t : Nat) (ht : 2 ≤ t) :
    alpha7 d t = ceilParity (alphaStarLower d t) t := by
  simp [alpha7, show t ≠ 0 by omega, show t ≠ 1 by omega]

theorem omega7_of_ge_two (d t : Nat) (ht : 2 ≤ t) :
    omega7 d t = ceilParity (omegaStarLower t) t := by
  simp [omega7, show t ≠ 0 by omega, show t ≠ 1 by omega]

theorem alpha7_parity (d t : Nat) : alpha7 d t % 2 = t % 2 := by
  unfold alpha7 ceilParity; split_ifs <;> omega

theorem omega7_parity (d t : Nat) : omega7 d t % 2 = t % 2 := by
  unfold omega7 ceilParity; split_ifs <;> omega

theorem omega7_le_d (d t : Nat) (hd : 7 ≤ d) (ht : t ≤ tf7 d) : omega7 d t ≤ d := by
  unfold omega7 ceilParity omegaStarLower; unfold tf7 at ht; split_ifs <;> omega

theorem ceilParity_unit_step (m₁ m₂ p : Nat)
    (hm : m₂ ≤ m₁ + 1) (hm' : m₁ ≤ m₂ + 1) :
    ceilParity m₂ (p + 1) ≤ ceilParity m₁ p + 1 ∧
      ceilParity m₁ p ≤ ceilParity m₂ (p + 1) + 1 := by
  unfold ceilParity; split_ifs <;> omega

theorem nat_div2_succ_le (k : Nat) : (k + 1) / 2 ≤ k / 2 + 1 := by
  have h : k / 2 + 1 = (k + 2) / 2 := by
    rw [show k + 2 = k + 1 * 2 by omega, Nat.add_mul_div_right k 1 (by omega : 0 < 2)]
  rw [h]
  exact Nat.div_le_div_right (by omega : k + 1 ≤ k + 2)

theorem nat_div2_le_succ (k : Nat) : k / 2 ≤ (k + 1) / 2 + 1 :=
  (Nat.div_le_div_right (by omega : k ≤ k + 1)).trans (Nat.le_add_right _ _)

theorem alphaStarLower_step (d t : Nat) :
    alphaStarLower d (t + 1) ≤ alphaStarLower d t + 1 ∧
      alphaStarLower d t ≤ alphaStarLower d (t + 1) + 1 := by
  constructor
  · unfold alphaStarLower
    by_cases h1 : t + 1 + 5 ≤ d <;> by_cases h2 : t + 5 ≤ d
    · simp [h1, h2]
    · omega
    · have hnum : t + 1 + 6 - d = 2 := by omega
      simp [h1, h2, hnum]
    ·
      have hge : d ≤ t + 6 := by omega
      have hk : t + 1 + 6 - d = (t + 6 - d) + 1 := by omega
      rw [show (if t + 1 + 5 ≤ d then 0 else (t + 1 + 6 - d) / 2) =
            (t + 1 + 6 - d) / 2 from if_neg h1,
          show (if t + 5 ≤ d then 0 else (t + 6 - d) / 2) =
            (t + 6 - d) / 2 from if_neg h2, hk]
      exact nat_div2_succ_le _
  · unfold alphaStarLower
    by_cases h1 : t + 1 + 5 ≤ d <;> by_cases h2 : t + 5 ≤ d
    · simp [h1, h2]
    · omega
    · simp [h1, h2]
    ·
      have hge : d ≤ t + 6 := by omega
      have hk : t + 1 + 6 - d = (t + 6 - d) + 1 := by omega
      rw [show (if t + 1 + 5 ≤ d then 0 else (t + 1 + 6 - d) / 2) =
            (t + 1 + 6 - d) / 2 from if_neg h1,
          show (if t + 5 ≤ d then 0 else (t + 6 - d) / 2) =
            (t + 6 - d) / 2 from if_neg h2, hk]
      exact nat_div2_le_succ _

theorem omegaStarLower_step (t : Nat) :
    omegaStarLower (t + 1) ≤ omegaStarLower t + 1 ∧
      omegaStarLower t ≤ omegaStarLower (t + 1) + 1 := by
  unfold omegaStarLower; omega

theorem alpha7_step (d t : Nat) (hd : 7 ≤ d) (_ht : t + 1 ≤ tf7 d) :
    alpha7 d (t + 1) ≤ alpha7 d t + 1 ∧
      alpha7 d t ≤ alpha7 d (t + 1) + 1 := by
  by_cases h0 : t = 0
  · subst h0; simp [alpha7]
  · by_cases h1 : t = 1
    · subst h1
      have hwin : 2 + 5 ≤ d := by omega
      simp [alpha7, alphaStarLower, hwin, ceilParity]
    ·
      have ht2 : 2 ≤ t := by omega
      have ht3 : 2 ≤ t + 1 := by omega
      rw [alpha7_of_ge_two d t ht2, alpha7_of_ge_two d (t + 1) ht3]
      have hs := alphaStarLower_step d t
      simpa using ceilParity_unit_step (alphaStarLower d t)
        (alphaStarLower d (t + 1)) t hs.1 hs.2

theorem omega7_step (d t : Nat) (_hd : 7 ≤ d) (_ht : t + 1 ≤ tf7 d) :
    omega7 d (t + 1) ≤ omega7 d t + 1 ∧
      omega7 d t ≤ omega7 d (t + 1) + 1 := by
  by_cases h0 : t = 0
  · subst h0; simp [omega7]
  · by_cases h1 : t = 1
    · subst h1; simp [omega7, omegaStarLower, ceilParity]
    ·
      have ht2 : 2 ≤ t := by omega
      have ht3 : 2 ≤ t + 1 := by omega
      rw [omega7_of_ge_two d t ht2, omega7_of_ge_two d (t + 1) ht3]
      have hs := omegaStarLower_step t
      simpa using ceilParity_unit_step (omegaStarLower t)
        (omegaStarLower (t + 1)) t hs.1 hs.2

theorem alpha7_tf (d : Nat) (hd : 7 ≤ d) : alpha7 d (tf7 d) = meetLevel7 d := by
  unfold alpha7 ceilParity alphaStarLower tf7 meetLevel7; split_ifs <;> omega

theorem omega7_tf (d : Nat) (hd : 7 ≤ d) : omega7 d (tf7 d) = meetLevel7 d := by
  unfold omega7 ceilParity omegaStarLower tf7 meetLevel7; split_ifs <;> omega

/-- Node `i` is active at time `t`. -/
abbrev Active (d i t : Nat) : Prop :=
  t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2

/-- §3 allocation `a(i,t)`. -/
def allocation (d i t : Nat) : Rat :=
  if Active d i t then
    if i = alpha7 d t then
      capacity d i t
    else if i = omega7 d t then
      ((64 ^ d : Nat) : Rat) / (64 : Rat) ^ i - capacity d i t / capacityRatio
    else
      (1 - 1 / capacityRatio) * capacity d i t
  else
    0

theorem allocation_inactive (d i t : Nat) (h : ¬Active d i t) : allocation d i t = 0 := by
  simp only [allocation, if_neg h]

section Alloc

variable (d : Nat)

theorem alloc_top {i t : Nat} (h : Active d i t) (hα : i = alpha7 d t) :
    allocation d i t = capacity d i t := by
  unfold allocation; rw [if_pos h, if_pos hα]

theorem alloc_bot {i t : Nat} (h : Active d i t)
    (hα : i ≠ alpha7 d t) (hω : i = omega7 d t) :
    allocation d i t =
      ((64 ^ d : Nat) : Rat) / (64 : Rat) ^ i - capacity d i t / capacityRatio := by
  unfold allocation; rw [if_pos h, if_neg hα, if_pos hω]

theorem alloc_mid {i t : Nat} (h : Active d i t)
    (hα : i ≠ alpha7 d t) (hω : i ≠ omega7 d t) :
    allocation d i t = (1 - 1 / capacityRatio) * capacity d i t := by
  unfold allocation; rw [if_pos h, if_neg hα, if_neg hω]

end Alloc

/-- Capacity at the §7 parameters: `c(i,t) = 64^e` when `d + 2i = t + 2 + e`. -/
theorem capacity_eq_pow (d i t e : ℕ) (h : d + 2 * i = t + 2 + e) :
    capacity d i t = ((64 ^ e : ℕ) : ℚ) := by
  have h1 : capacity d i t = (64 : ℚ) ^ (d + 2 * i) / 64 ^ (t + 2) := by
    unfold capacity
    push_cast
    rw [pow_add, pow_add, pow_mul, one_div, inv_pow]
    field_simp
    norm_num
    ring
  rw [h1, h, pow_add]
  push_cast
  field_simp

theorem capacity_meet7 (d : Nat) (hd : 7 ≤ d) :
    capacity d (meetLevel7 d) (tf7 d) = (64 : Rat) ^ 6 := by
  rw [capacity_eq_pow d _ _ 6 (by unfold meetLevel7 tf7; omega)]
  norm_num

/-- Paper's claim that top and bottom are apart before `t_f`. -/
theorem alpha7_lt_omega7 (d : Nat) (hd : 7 ≤ d) (s : Nat) (hs : 2 ≤ s)
    (hlt : s < tf7 d) : alpha7 d s < omega7 d s := by
  rw [alpha7_of_ge_two d s hs, omega7_of_ge_two d s hs]
  have htf : s + 20 < 3 * d := by unfold tf7 at hlt; omega
  unfold ceilParity alphaStarLower omegaStarLower
  split_ifs <;> omega

theorem alpha7_tf_eq_omega7_tf (d : Nat) (hd : 7 ≤ d) :
    alpha7 d (tf7 d) = omega7 d (tf7 d) := by
  have h1 := alpha7_tf d hd
  have h2 := omega7_tf d hd
  rw [h1, h2]

/-- Meeting identity `capacity = N / br^(meet level)` at the §7 parameters. -/
theorem capacity_meet7_div (d : Nat) (hd : 7 ≤ d) :
    capacity d (meetLevel7 d) (tf7 d) =
      (((64 : Nat) ^ d : Nat) : Rat) / (64 : Rat) ^ (meetLevel7 d) := by
  rw [capacity_meet7 d hd]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 7 := ⟨d - 7, by omega⟩
  have hm : meetLevel7 (e + 7) = e + 1 := by unfold meetLevel7; omega
  rw [hm]
  push_cast
  rw [show e + 7 = (e + 1) + 6 by omega, pow_add]
  have : (64 : Rat) ^ (e + 1) ≠ 0 := by positivity
  field_simp

/-- Lemma 3.2 at the §7 schedule: on ascent, `α = 0` or `c ≤ A k²/ν = 2^30`. -/
theorem lemma32_schedule7 (d : Nat) (hd : 7 ≤ d) (t : Nat) (hasc : alpha7 d t < alpha7 d (t + 1)) :
    alpha7 d t = 0 ∨ capacity d (alpha7 d t) t ≤ 1073741824 := by
  by_cases hroot : alpha7 d t = 0
  · exact Or.inl hroot
  · right
    obtain ⟨e, he, he5⟩ : ∃ e, d + 2 * alpha7 d t = t + 2 + e ∧ e ≤ 5 := by
      refine ⟨d + 2 * alpha7 d t - (t + 2), ?_, ?_⟩ <;>
        · unfold alpha7 ceilParity alphaStarLower at hasc hroot ⊢
          split_ifs at * <;> omega
    rw [capacity_eq_pow d _ t e he]
    have : ((64 ^ e : ℕ) : ℚ) ≤ ((64 ^ 5 : ℕ) : ℚ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num) he5
    refine this.trans (le_of_eq ?_)
    norm_num

/-! ### Lemma 3.1 (DCS-TR-294 §3): algebraic core under the global mass identity -/

section

open Finset

/-- `α`-ladder: the mass below the active level `α + 2m + 2` telescopes. -/
private theorem ladder (d : Nat) (t : Nat)
    (ht : t ≤ tf7 d) (m : Nat) (hm : alpha7 d t + 2 * m + 2 ≤ omega7 d t) :
    ∑ j ∈ range (alpha7 d t + 2 * m + 2), (64 : Rat) ^ j * allocation d j t =
      (64 : Rat) ^ alpha7 d t * capacity d (alpha7 d t) t * capacityRatio ^ m := by
  have hpar := alpha7_parity d t
  have hbelow : ∑ j ∈ range (alpha7 d t), (64 : Rat) ^ j * allocation d j t = 0 :=
    sum_eq_zero fun j hj => by
      rw [allocation_inactive _ _ _ (by unfold Active; simp at hj; omega), mul_zero]
  induction m with
  | zero =>
    rw [sum_range_succ, sum_range_succ, hbelow, allocation_inactive d (alpha7 d t + 1) t
      (by unfold Active; omega), alloc_top d (i := alpha7 d t) (by unfold Active; omega) rfl]
    simp
  | succ m ih =>
    have := capacity_weighted_step d (alpha7 d t) t (m + 1)
    rw [show alpha7 d t + 2 * (m + 1) + 2 = alpha7 d t + 2 * m + 2 + 1 + 1 by omega,
      sum_range_succ, sum_range_succ, ih (by omega),
      allocation_inactive d (alpha7 d t + 2 * m + 2 + 1) t (by unfold Active; omega),
      alloc_mid d (i := alpha7 d t + 2 * m + 2) (by unfold Active; omega) (by omega)
        (by omega)]
    rw [show alpha7 d t + 2 * m + 2 = alpha7 d t + 2 * (m + 1) by omega] at *
    have hQ1 : (1 - 1 / capacityRatio) * capacityRatio = capacityRatio - 1 := by
      field_simp [capacityRatio_pos.ne']
    linear_combination (64 : Rat) ^ alpha7 d t * (1 - 1 / capacityRatio) * this +
      ((64 : Rat) ^ alpha7 d t * capacity d (alpha7 d t) t * capacityRatio ^ m) * hQ1

/-- §3 Lemma 3.1 under the global mass identity `sum_j br^j a(j,t) = N`. -/
theorem lemma31_of_total (d : Nat) (hd : 7 ≤ d) (t : Nat) (ht : t ≤ tf7 d)
    (htotal : (∑ j ∈ Finset.range (d + 1),
        (64 : Rat) ^ j * allocation d j t) = (64 ^ d : Nat))
    (i : Nat) (hα : alpha7 d t ≤ i) (hω : i ≤ omega7 d t)
    (hpar : i % 2 = t % 2) :
    (∑ j ∈ Finset.Icc i d,
        (64 : Rat) ^ (j - i) * allocation d j t) =
      if i = alpha7 d t then
        ((64 ^ d : Nat) : Rat) / (64 : Rat) ^ i
      else
        ((64 ^ d : Nat) : Rat) / (64 : Rat) ^ i -
          capacity d i t / capacityRatio := by
  have hid : i ≤ d := le_trans hω (omega7_le_d d t hd ht)
  have hbr : (64 : Rat) ^ i ≠ 0 := pow_ne_zero _ (by norm_num)
  -- mass of levels `≥ i`, rescaled by `br^i`, is `N` minus the mass below `i`
  have hsum : (∑ j ∈ Icc i d, (64 : Rat) ^ (j - i) * allocation d j t) =
      (((64 ^ d : Nat) : Rat) - ∑ j ∈ range i, (64 : Rat) ^ j * allocation d j t) /
        (64 : Rat) ^ i := by
    have hlo : (range (d + 1)).filter (· < i) = range i := by
      ext j; simp only [mem_filter, mem_range]; omega
    have hhi : (range (d + 1)).filter (fun j ↦ i ≤ j) = Icc i d := by
      ext j; simp only [mem_filter, mem_range, mem_Icc]; omega
    have h := sum_filter_add_sum_filter_not (range (d + 1)) (fun j : Nat ↦ j < i)
      (fun j ↦ (64 : Rat) ^ j * allocation d j t)
    simp only [not_lt, hlo, hhi] at h
    rw [eq_div_iff hbr, sum_mul]
    have : ((64 ^ d : Nat) : Rat) - ∑ j ∈ range i, (64 : Rat) ^ j * allocation d j t =
        ∑ j ∈ Icc i d, (64 : Rat) ^ j * allocation d j t := by linarith
    rw [this]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_Icc] at hj
    rw [mul_assoc, mul_comm (allocation _ _ _), ← mul_assoc, ← pow_add, Nat.sub_add_cancel hj.1]
  have hpa := alpha7_parity d t
  split_ifs with htop
  · have : ∑ j ∈ range i, (64 : Rat) ^ j * allocation d j t = 0 :=
      sum_eq_zero fun j hj => by
        rw [allocation_inactive _ _ _ (by unfold Active; simp at hj; omega), mul_zero]
    rw [hsum, this, sub_zero]
  · obtain ⟨m, hm⟩ : ∃ m, i = alpha7 d t + 2 * m + 2 := ⟨(i - alpha7 d t) / 2 - 1, by omega⟩
    have hw := capacity_weighted_step d (alpha7 d t) t (m + 1)
    rw [hsum, hm, ladder d t ht m (by omega), sub_div,
      show alpha7 d t + 2 * m + 2 = alpha7 d t + 2 * (m + 1) by omega]
    congr 1
    rw [div_eq_div_iff (pow_ne_zero _ (by norm_num)) capacityRatio_pos.ne']
    linear_combination (-(64 : Rat) ^ alpha7 d t) * hw

end

end Chvatal
