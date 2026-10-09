module

public import AKS.Chvatal.Params
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Chvátal §7 concrete level schedule (DCS-TR-294 §3 + §7)

Envelopes `α* = (6(t−d)+25)/12`, `ω* = (t+2)/3` at `params7`, realized by integer floors and
parity rounding, with `tf = 3d−20` and meeting level `d−6`. -/

namespace Chvatal

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

def levelSchedule7 (d : Nat) (hd : 7 ≤ d) : LevelSchedule params7 d where
  tf := tf7 d
  alpha := alpha7 d
  omega := omega7 d
  omega_le_d := fun t ht => omega7_le_d d t hd ht
  alpha_parity := fun t _ => alpha7_parity d t
  omega_parity := fun t _ => omega7_parity d t
  alpha_step := fun t ht => alpha7_step d t hd ht
  omega_step := fun t ht => omega7_step d t hd ht

theorem levelSchedule7_alpha_tf (d : Nat) (hd : 7 ≤ d) :
    (levelSchedule7 d hd).alpha ((levelSchedule7 d hd).tf) = meetLevel7 d := alpha7_tf d hd

theorem levelSchedule7_omega_tf (d : Nat) (hd : 7 ≤ d) :
    (levelSchedule7 d hd).omega ((levelSchedule7 d hd).tf) = meetLevel7 d := omega7_tf d hd

/-- Capacity at `params7`: `c(i,t) = 64^e` when `d + 2i = t + 2 + e`. -/
theorem capacity_params7 (d i t e : ℕ) (h : d + 2 * i = t + 2 + e) :
    capacity params7 d i t = ((64 ^ e : ℕ) : ℚ) := by
  have h1 : capacity params7 d i t = (64 : ℚ) ^ (d + 2 * i) / 64 ^ (t + 2) := by
    unfold capacity params7
    simp only [Nat.cast_pow]
    push_cast
    rw [pow_add, pow_mul]
    field_simp
    rw [one_div, inv_pow, pow_add]
    field_simp
    ring
  rw [h1, h, pow_add]
  push_cast
  field_simp

theorem capacity_meet7 (d : Nat) (hd : 7 ≤ d) :
    capacity params7 d (meetLevel7 d) (tf7 d) = (64 : Rat) ^ 6 := by
  rw [capacity_params7 d _ _ 6 (by unfold meetLevel7 tf7; omega)]
  norm_num

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
    obtain ⟨e, he, he5⟩ : ∃ e, d + 2 * alpha7 d t = t + 2 + e ∧ e ≤ 5 := by
      refine ⟨d + 2 * alpha7 d t - (t + 2), ?_, ?_⟩ <;>
        · unfold alpha7 ceilParity alphaStarLower at hasc hroot ⊢
          split_ifs at * <;> omega
    rw [capacity_params7 d _ t e he]
    have : ((64 ^ e : ℕ) : ℚ) ≤ ((64 ^ 5 : ℕ) : ℚ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num) he5
    refine this.trans (le_of_eq ?_)
    simp only [params7]; norm_num

end Chvatal
