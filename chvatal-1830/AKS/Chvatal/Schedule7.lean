module
/-
  # Chvátal §7 concrete level schedule

  Source: V. Chvátal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §3 + §7.

  Status: paper envelopes `α* = (6(t−d)+25)/12` and `ω* = (t+2)/3` at
  `params7`, realized by integer floors + parity rounding, with `tf = 3d−20`
  and meeting level `d−6`. Meeting capacity, purity envelope, and Lemma 3.2
  (from the envelope, no external snap hyp) are kernel-checked.
-/

public import AKS.Chvatal.Params
public import AKS.Chvatal.SchedulerLemmas
public import AKS.Chvatal.DepthSkeleton
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Chvatal

/-! **§7 endpoints** -/

def tf7 (d : Nat) : Nat := 3 * d - 20
def meetLevel7 (d : Nat) : Nat := d - 6





/-! **Parity rounding** -/

def ceilParity (m parity : Nat) : Nat :=
  if m % 2 = parity % 2 then m else m + 1

theorem ceilParity_parity (m parity : Nat) :
    ceilParity m parity % 2 = parity % 2 := by
  unfold ceilParity; split_ifs with h <;> [exact h; omega]


theorem ceilParity_le_succ (m parity : Nat) : ceilParity m parity ≤ m + 1 := by
  unfold ceilParity; split_ifs <;> omega

theorem ceilParity_le_of_le {m₁ m₂ parity : Nat} (h : m₁ ≤ m₂) :
    ceilParity m₁ parity ≤ ceilParity m₂ parity := by
  unfold ceilParity; split_ifs <;> omega

theorem ceilParity_unit_step (m₁ m₂ p : Nat)
    (hm : m₂ ≤ m₁ + 1) (hm' : m₁ ≤ m₂ + 1) :
    ceilParity m₂ (p + 1) ≤ ceilParity m₁ p + 1 ∧
      ceilParity m₁ p ≤ ceilParity m₂ (p + 1) + 1 := by
  unfold ceilParity; split_ifs <;> omega

/-! **Envelope floors** -/

/-- `⌈α*(t)⌉` before parity: `0` on `t ≤ d−5`, else `(t−d+6)/2`. -/
def alphaStarLower (d t : Nat) : Nat :=
  if t + 5 ≤ d then 0 else (t + 6 - d) / 2

/-- `⌈ω*(t)⌉` before parity: `(t+4)/3`. -/
def omegaStarLower (t : Nat) : Nat := (t + 4) / 3

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

/-- From `3n + 10 ≤ 2m`, conclude `n/2 ≤ m/3`. -/
theorem div2_le_div3_of_slack (n m : Nat) (hm : 5 ≤ m) (h : 3 * n + 10 ≤ 2 * m) :
    n / 2 ≤ m / 3 := by
  have h3 : 3 * (n / 2) ≤ m - 5 := by
    have := Nat.mul_div_le n 2
    omega
  have hle : n / 2 ≤ (m - 5) / 3 := by omega
  exact hle.trans (Nat.div_le_div_right (by omega : m - 5 ≤ m))

theorem alphaStarLower_le_omegaStarLower (d t : Nat) (hd : 7 ≤ d)
    (ht : t ≤ tf7 d) :
    alphaStarLower d t ≤ omegaStarLower t := by
  unfold alphaStarLower omegaStarLower
  split_ifs with h
  · exact Nat.zero_le _
  ·
    set n := t + 6 - d
    set m := t + 4
    have hge : d ≤ t + 6 := by omega
    have htf : t ≤ 3 * d - 20 := by simpa [tf7] using ht
    have hm5 : 5 ≤ m := by simp only [m]; omega
    have hslack : 3 * n + 10 ≤ 2 * m := by simp only [n, m]; omega
    exact div2_le_div3_of_slack n m hm5 hslack

/-! **Discrete α / ω** -/

def alpha7 (d t : Nat) : Nat :=
  if t = 0 then 0
  else if t = 1 then 1
  else ceilParity (alphaStarLower d t) t

def omega7 (_d t : Nat) : Nat :=
  if t = 0 then 0
  else if t = 1 then 1
  else ceilParity (omegaStarLower t) t

theorem alpha7_zero (d : Nat) : alpha7 d 0 = 0 := rfl
theorem omega7_zero (d : Nat) : omega7 d 0 = 0 := rfl

theorem alpha7_of_ge_two (d t : Nat) (ht : 2 ≤ t) :
    alpha7 d t = ceilParity (alphaStarLower d t) t := by
  simp [alpha7, show t ≠ 0 by omega, show t ≠ 1 by omega]

theorem omega7_of_ge_two (d t : Nat) (ht : 2 ≤ t) :
    omega7 d t = ceilParity (omegaStarLower t) t := by
  simp [omega7, show t ≠ 0 by omega, show t ≠ 1 by omega]

theorem alpha7_parity (d t : Nat) : alpha7 d t % 2 = t % 2 := by
  by_cases h0 : t = 0; · subst h0; rfl
  by_cases h1 : t = 1; · subst h1; rfl
  rw [alpha7_of_ge_two d t (by omega)]; exact ceilParity_parity _ _

theorem omega7_parity (d t : Nat) : omega7 d t % 2 = t % 2 := by
  by_cases h0 : t = 0; · subst h0; rfl
  by_cases h1 : t = 1; · subst h1; rfl
  rw [omega7_of_ge_two d t (by omega)]; exact ceilParity_parity _ _

theorem alpha7_le_d (d t : Nat) (hd : 7 ≤ d) (ht : t ≤ tf7 d) :
    alpha7 d t ≤ d := by
  by_cases h0 : t = 0; · subst h0; simp [alpha7]
  by_cases h1 : t = 1; · subst h1; simp [alpha7]; omega
  rw [alpha7_of_ge_two d t (by omega)]
  have hceil := ceilParity_le_succ (alphaStarLower d t) t
  have htf : t ≤ 3 * d - 20 := by simpa [tf7] using ht
  by_cases hwin : t + 5 ≤ d
  · simp [alphaStarLower, hwin, ceilParity] at hceil ⊢; split_ifs <;> omega
  · have : alphaStarLower d t = (t + 6 - d) / 2 := by simp [alphaStarLower, hwin]
    have : (t + 6 - d) / 2 ≤ d - 6 := by
      have hbound : t + 6 - d ≤ 2 * d - 14 := by omega
      have := Nat.div_le_div_right (c := 2) hbound
      have : (2 * d - 14) / 2 = d - 7 := by omega
      omega
    omega

theorem omega7_le_d (d t : Nat) (hd : 7 ≤ d) (ht : t ≤ tf7 d) :
    omega7 d t ≤ d := by
  by_cases h0 : t = 0; · subst h0; simp [omega7]
  by_cases h1 : t = 1; · subst h1; simp [omega7]; omega
  rw [omega7_of_ge_two d t (by omega)]
  have hceil := ceilParity_le_succ (omegaStarLower t) t
  have htf : t ≤ 3 * d - 20 := by simpa [tf7] using ht
  have hlo : omegaStarLower t ≤ d - 6 := by
    simp only [omegaStarLower]
    have : t + 4 ≤ 3 * d - 16 := by omega
    have hdiv := Nat.div_le_div_right (c := 3) this
    have hval : (3 * d - 16) / 3 = d - 6 := by
      have heq : 3 * d - 16 = 2 + 3 * (d - 6) := by omega
      rw [heq, Nat.add_mul_div_left 2 (d - 6) (by omega : 0 < 3)]
      simp
    omega
  omega

theorem alpha7_le_omega7 (d t : Nat) (hd : 7 ≤ d) (ht : t ≤ tf7 d) :
    alpha7 d t ≤ omega7 d t := by
  by_cases h0 : t = 0; · subst h0; simp [alpha7, omega7]
  by_cases h1 : t = 1; · subst h1; simp [alpha7, omega7]
  rw [alpha7_of_ge_two d t (by omega), omega7_of_ge_two d t (by omega)]
  exact ceilParity_le_of_le (alphaStarLower_le_omegaStarLower d t hd ht)

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

theorem alpha7_tf (d : Nat) (hd : 7 ≤ d) :
    alpha7 d (tf7 d) = meetLevel7 d := by
  unfold tf7 meetLevel7
  by_cases hd7 : d = 7
  · subst hd7; simp [alpha7]
  · have ht : 2 ≤ 3 * d - 20 := by omega
    rw [alpha7_of_ge_two d (3 * d - 20) ht]
    have hwin : ¬((3 * d - 20) + 5 ≤ d) := by omega
    simp [alphaStarLower, hwin]
    have hval : (3 * d - 20 + 6 - d) / 2 = d - 7 := by omega
    rw [hval]
    unfold ceilParity
    have hpar : ¬((d - 7) % 2 = (3 * d - 20) % 2) := by omega
    simp [hpar]; omega

theorem omega7_tf (d : Nat) (hd : 7 ≤ d) :
    omega7 d (tf7 d) = meetLevel7 d := by
  unfold tf7 meetLevel7
  by_cases hd7 : d = 7
  · subst hd7; simp [omega7]
  · have ht : 2 ≤ 3 * d - 20 := by omega
    rw [omega7_of_ge_two d (3 * d - 20) ht]
    have hval : omegaStarLower (3 * d - 20) = d - 6 := by
      change (3 * d - 20 + 4) / 3 = d - 6; omega
    rw [hval]
    unfold ceilParity
    have hpar : (d - 6) % 2 = (3 * d - 20) % 2 := by omega
    simp [hpar]

def levelSchedule7 (d : Nat) (hd : 7 ≤ d) : LevelSchedule params7 d where
  tf := tf7 d
  alpha := alpha7 d
  omega := omega7 d
  alpha_le_d := fun t ht => alpha7_le_d d t hd ht
  omega_le_d := fun t ht => omega7_le_d d t hd ht
  alpha_le_omega := fun t ht => alpha7_le_omega7 d t hd ht
  alpha_parity := fun t _ => alpha7_parity d t
  omega_parity := fun t _ => omega7_parity d t
  alpha0 := alpha7_zero d
  omega0 := omega7_zero d
  alpha_step := fun t ht => alpha7_step d t hd ht
  omega_step := fun t ht => omega7_step d t hd ht

theorem levelSchedule7_alpha_tf (d : Nat) (hd : 7 ≤ d) :
    (levelSchedule7 d hd).alpha ((levelSchedule7 d hd).tf) = meetLevel7 d := by
  simpa [levelSchedule7] using alpha7_tf d hd

theorem levelSchedule7_omega_tf (d : Nat) (hd : 7 ≤ d) :
    (levelSchedule7 d hd).omega ((levelSchedule7 d hd).tf) = meetLevel7 d := by
  simpa [levelSchedule7] using omega7_tf d hd

/-! **Capacity and purity** -/

theorem capacity_factor (p : ScheduleParams) (d i t : Nat) :
    capacity p d i t = capacity p d 0 0 * p.A ^ i * p.nu ^ t := by
  have hlev : ∀ i t, capacity p d i t = capacity p d 0 t * p.A ^ i := by
    intro i t
    induction i with
    | zero => simp
    | succ i ih =>
      calc capacity p d (i + 1) t
          = p.A * capacity p d i t := capacity_succ_level p d i t
        _ = p.A * (capacity p d 0 t * p.A ^ i) := by rw [ih]
        _ = capacity p d 0 t * p.A ^ (i + 1) := by rw [pow_succ]; ring
  have hstg : ∀ t, capacity p d 0 t = capacity p d 0 0 * p.nu ^ t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      calc capacity p d 0 (t + 1)
          = p.nu * capacity p d 0 t := capacity_succ_stage p d 0 t
        _ = p.nu * (capacity p d 0 0 * p.nu ^ t) := by rw [ih]
        _ = capacity p d 0 0 * p.nu ^ (t + 1) := by rw [pow_succ]; ring
  rw [hlev, hstg]; ring

theorem capacity_params7_zero (d : Nat) :
    capacity params7 d 0 0 = (64 : Rat) ^ d / 4096 := by
  unfold capacity
  have hden : params7.A * params7.nu * (params7.br : Rat) = 4096 := by
    simp only [params7]; norm_num
  have hN : (↑(params7.br ^ d) : Rat) = (64 : Rat) ^ d := by
    simp only [params7]; norm_cast
  simp only [hden, hN, pow_zero, mul_one]

theorem capacity_params7_zpow (d i t : Nat) :
    capacity params7 d i t =
      (64 : Rat) ^ (((d : Int) + 2 * (i : Int) - 2 - (t : Int))) := by
  have hne : (64 : Rat) ≠ 0 := by norm_num
  rw [capacity_factor params7 d i t, capacity_params7_zero]
  have hA : params7.A = (64 : Rat) ^ 2 := by simp only [params7]; norm_num
  have hnu : params7.nu = (1 : Rat) / 64 := by simp only [params7]
  rw [hA, hnu, div_pow, one_pow]
  have hpow2 : ((64 : Rat) ^ 2) ^ i = (64 : Rat) ^ (2 * i) :=
    (pow_mul (64 : Rat) 2 i).symm
  rw [hpow2]
  have h4096 : (4096 : Rat) = (64 : Rat) ^ 2 := by norm_num
  rw [h4096]
  have hcalc :
      (64 : Rat) ^ d / (64 : Rat) ^ 2 * (64 : Rat) ^ (2 * i) * (1 / (64 : Rat) ^ t) =
        (64 : Rat) ^ d * (64 : Rat) ^ (2 * i) / ((64 : Rat) ^ 2 * (64 : Rat) ^ t) := by
    field_simp [hne]
  rw [hcalc]
  simp only [← zpow_natCast]
  rw [← zpow_add₀ hne, ← zpow_add₀ hne, ← zpow_sub₀ hne]
  congr 1
  omega

theorem lemma32_rhs_params7 :
    params7.A * (params7.br : Rat) ^ 2 / params7.nu = (64 : Rat) ^ (5 : Int) := by
  simp only [params7]; norm_num

theorem capacity_params7_exp_le_five (d i t : Nat)
    (h : ((d : Int) + 2 * (i : Int) - 2 - (t : Int)) ≤ 5) :
    capacity params7 d i t ≤
      params7.A * (params7.br : Rat) ^ 2 / params7.nu := by
  rw [capacity_params7_zpow, lemma32_rhs_params7]
  exact zpow_le_zpow_right₀ (by norm_num : (1 : Rat) ≤ 64) h

theorem capacity_meet7 (d : Nat) (hd : 7 ≤ d) :
    capacity params7 d (meetLevel7 d) (tf7 d) = (64 : Rat) ^ 6 := by
  rw [meetLevel7, tf7, capacity_params7_zpow]
  have hexp :
      ((d : Int) + 2 * ((d - 6 : Nat) : Int) - 2 - ((3 * d - 20 : Nat) : Int)) = 6 := by
    omega
  rw [hexp]
  norm_cast




/-! **Lemma 3.2 from the envelope** -/

theorem ceilParity_le_of_mem (m p n : Nat) (hge : m ≤ n) (hpar : n % 2 = p % 2) :
    ceilParity m p ≤ n := by
  unfold ceilParity
  split_ifs with h
  · exact hge
  · omega

/-- On ascent, `α(t) ≤ α*floor(t+1)`, else `α−1` would be eligible at `t+1`. -/
theorem ascent_le_next_lower (d t : Nat) (_ht : 2 ≤ t)
    (hasc : ceilParity (alphaStarLower d t) t <
      ceilParity (alphaStarLower d (t + 1)) (t + 1))
    (hpos : 0 < ceilParity (alphaStarLower d t) t) :
    ceilParity (alphaStarLower d t) t ≤ alphaStarLower d (t + 1) := by
  set α := ceilParity (alphaStarLower d t) t
  set α' := ceilParity (alphaStarLower d (t + 1)) (t + 1)
  have hs := alphaStarLower_step d t
  have hunit :=
    ceilParity_unit_step (alphaStarLower d t) (alphaStarLower d (t + 1)) t hs.1 hs.2
  have hα'le : α' ≤ α + 1 := by simpa [α, α'] using hunit.1
  have _hαeq : α' = α + 1 := by omega
  by_contra hgt
  push_neg at hgt
  have hge : alphaStarLower d (t + 1) ≤ α - 1 := by omega
  have hparα : α % 2 = t % 2 := by
    simpa [α] using ceilParity_parity (alphaStarLower d t) t
  have hpar : (α - 1) % 2 = (t + 1) % 2 := by omega
  have hceil : α' ≤ α - 1 := by
    simpa [α'] using ceilParity_le_of_mem (alphaStarLower d (t + 1)) (t + 1) (α - 1) hge hpar
  omega

/-- On ascent with positive α, capacity exponent `≤ 5`. -/
theorem ascent_exp_le_five (d t : Nat) (hd : 7 ≤ d)
    (hasc : alpha7 d t < alpha7 d (t + 1)) (hpos : 0 < alpha7 d t) :
    ((d : Int) + 2 * (alpha7 d t : Int) - 2 - (t : Int)) ≤ 5 := by
  by_cases h0 : t = 0
  · subst h0; simp [alpha7] at hpos
  · by_cases h1 : t = 1
    · subst h1
      have hwin : 2 + 5 ≤ d := by omega
      simp [alpha7, alphaStarLower, hwin, ceilParity] at hasc
    ·
      have ht2 : 2 ≤ t := by omega
      have ht3 : 2 ≤ t + 1 := by omega
      rw [alpha7_of_ge_two d t ht2] at hasc hpos ⊢
      rw [alpha7_of_ge_two d (t + 1) ht3] at hasc
      by_cases hwin : t + 5 ≤ d
      · have hz : alphaStarLower d t = 0 := by simp [alphaStarLower, hwin]
        simp only [hz] at hasc hpos ⊢
        have hα1 : ceilParity 0 t = 1 := by
          unfold ceilParity at hpos ⊢
          split_ifs at hpos ⊢ with _hp
          · omega
          · rfl
        rw [hα1] at hasc hpos ⊢
        have hleave : ¬(t + 1 + 5 ≤ d) := by
          by_contra hwin'
          have hz' : alphaStarLower d (t + 1) = 0 := by simp [alphaStarLower, hwin']
          rw [hz'] at hasc
          unfold ceilParity at hasc
          split_ifs at hasc <;> omega
        have ht5 : t + 5 = d := by omega
        subst ht5
        norm_num
      ·
        set α := ceilParity (alphaStarLower d t) t with hαdef
        have hle : α ≤ alphaStarLower d (t + 1) :=
          ascent_le_next_lower d t ht2 hasc hpos
        have hwin1 : ¬(t + 1 + 5 ≤ d) := by omega
        have hlower' : alphaStarLower d (t + 1) = (t + 7 - d) / 2 := by
          have : t + 1 + 6 - d = t + 7 - d := by omega
          simp only [alphaStarLower, if_neg hwin1, this]
        have hαle : α ≤ (t + 7 - d) / 2 := hlower' ▸ hle
        have h2 : 2 * α ≤ t + 7 - d :=
          calc 2 * α ≤ 2 * ((t + 7 - d) / 2) := Nat.mul_le_mul_left 2 hαle
            _ ≤ t + 7 - d := Nat.mul_div_le (t + 7 - d) 2
        have hnat : d + 2 * α ≤ t + 7 := by
          have : d ≤ t + 7 := by omega
          exact Nat.add_le_of_le_sub' (by omega) h2
        have : ((d : Int) + 2 * (α : Int) - 2 - (t : Int)) ≤ 5 := by
          have hcast : (d : Int) + 2 * (α : Int) ≤ (t : Int) + 7 := by exact_mod_cast hnat
          linarith
        simpa [← hαdef] using this

/-- Lemma 3.2 at `levelSchedule7`: on ascent, `α=0` or `c ≤ Ak²/ν`. -/
theorem lemma32_levelSchedule7 (d : Nat) (hd : 7 ≤ d) (t : Nat)
    (hasc : (levelSchedule7 d hd).alpha t <
      (levelSchedule7 d hd).alpha (t + 1)) :
    (levelSchedule7 d hd).alpha t = 0 ∨
      capacity params7 d ((levelSchedule7 d hd).alpha t) t ≤
        params7.A * (params7.br : Rat) ^ 2 / params7.nu := by
  simp only [levelSchedule7] at hasc ⊢
  by_cases hroot : alpha7 d t = 0
  · exact Or.inl hroot
  · right
    have hpos : 0 < alpha7 d t := Nat.pos_of_ne_zero hroot
    exact capacity_params7_exp_le_five d (alpha7 d t) t
      (ascent_exp_le_five d t hd hasc hpos)

end Chvatal
