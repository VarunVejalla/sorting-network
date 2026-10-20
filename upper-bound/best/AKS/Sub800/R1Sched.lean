import Mathlib

/-! # Schedule of the R1 point (LEAN-PLAN W1, step 1)

Chvátal's §3 schedule (DCS-TR-294 pp. 6–9) at `(k, A, ν) = (2^4, 2^5, 2^-3)`, `N = 16^d`.

* capacity `c(i,t) = N A^i ν^t / (A ν k) = 2^e`, `e(i,t) = 4d + 5i − 3t − 6`;
* top envelope `α*(t) = ⌈(3t − 4d + 15)/5⌉` (so `c(α,t) ≥ 2k² = 2^9`), bottom `ω*(t) = ⌈(t+2)/3⌉`,
  each raised to the parity of `t`; `α(0) = ω(0) = 0`, `α(1) = ω(1) = 1`;
* `t_f = 3d − 14`, meeting level `d − 4` (R1-PROOF §5).

Everything is stated for `d ≥ 10` (the R1 point is used for `d` large). -/

namespace R1T

/-- Exponent of the capacity: `c(i,t) = 2^(4d + 5i − 3t − 6)` (as an integer). -/
def ecap (d i t : ℕ) : ℤ := 4 * d + 5 * i - 3 * t - 6

/-- Capacity `c(i,t)` in `ℚ`. -/
noncomputable def cap (d i t : ℕ) : ℚ := (2 : ℚ) ^ (ecap d i t)

theorem cap_pos (d i t : ℕ) : 0 < cap d i t := by unfold cap; positivity

theorem cap_succ_level (d i t : ℕ) : cap d (i + 1) t = 32 * cap d i t := by
  unfold cap ecap
  rw [show (4 * (d : ℤ) + 5 * ((i + 1 : ℕ) : ℤ) - 3 * t - 6) = (4 * d + 5 * i - 3 * t - 6) + 5 by
    push_cast; ring, zpow_add₀ (by norm_num)]
  norm_num; ring

theorem cap_succ_stage (d i t : ℕ) : cap d i (t + 1) = cap d i t / 8 := by
  unfold cap ecap
  rw [show (4 * (d : ℤ) + 5 * i - 3 * ((t + 1 : ℕ) : ℤ) - 6) = (4 * d + 5 * i - 3 * t - 6) - 3 by
    push_cast; ring, zpow_sub₀ (by norm_num)]
  norm_num

/-- Capacity as a natural number when the exponent is nonnegative. -/
theorem cap_eq_pow (d i t e : ℕ) (h : (4 * d + 5 * i : ℤ) = 3 * t + 6 + e) :
    cap d i t = ((2 ^ e : ℕ) : ℚ) := by
  unfold cap ecap
  rw [show (4 * (d : ℤ) + 5 * i - 3 * t - 6) = (e : ℤ) by linarith]
  push_cast
  rw [zpow_natCast]

/-- Round up to the parity of `t`. -/
def ceilParity (m t : ℕ) : ℕ := if m % 2 = t % 2 then m else m + 1

/-- `⌈α*(t)⌉` before parity: `max(0, ⌈(3t − 4d + 15)/5⌉)`. -/
def alphaLo (d t : ℕ) : ℕ := if 3 * t + 15 ≤ 4 * d then 0 else (3 * t + 15 - 4 * d + 4) / 5

/-- `⌈ω*(t)⌉` before parity: `⌈(t + 2)/3⌉ = (t + 4)/3`. -/
def omegaLo (t : ℕ) : ℕ := (t + 4) / 3

/-- Top level `α(t)`. -/
def alpha (d t : ℕ) : ℕ :=
  if t = 0 then 0 else if t = 1 then 1 else ceilParity (alphaLo d t) t

/-- Bottom level `ω(t)`. -/
def omega (t : ℕ) : ℕ :=
  if t = 0 then 0 else if t = 1 then 1 else ceilParity (omegaLo t) t

/-- Final stage `t_f = 3d − 14`. -/
def tf (d : ℕ) : ℕ := 3 * d - 14

/-- Meeting level `d − 4`. -/
def meet (d : ℕ) : ℕ := d - 4

theorem alpha_of_ge_two (d t : ℕ) (ht : 2 ≤ t) : alpha d t = ceilParity (alphaLo d t) t := by
  simp [alpha, show t ≠ 0 by omega, show t ≠ 1 by omega]

theorem omega_of_ge_two (t : ℕ) (ht : 2 ≤ t) : omega t = ceilParity (omegaLo t) t := by
  simp [omega, show t ≠ 0 by omega, show t ≠ 1 by omega]

theorem alpha_parity (d t : ℕ) : alpha d t % 2 = t % 2 := by
  unfold alpha ceilParity; split_ifs <;> omega

theorem omega_parity (t : ℕ) : omega t % 2 = t % 2 := by
  unfold omega ceilParity; split_ifs <;> omega

/-- Unfold the schedule into linear arithmetic. -/
macro "sched" : tactic =>
  `(tactic| (simp only [alpha, omega, ceilParity, alphaLo, omegaLo, tf, meet] at *; split_ifs at * <;> omega))

theorem alpha_step (d t : ℕ) (hd : 10 ≤ d) :
    alpha d (t + 1) ≤ alpha d t + 1 ∧ alpha d t ≤ alpha d (t + 1) + 1 := by
  rcases Nat.lt_or_ge t 2 with h | h
  · interval_cases t <;> simp [alpha, ceilParity, alphaLo] <;> split_ifs <;> omega
  · rw [alpha_of_ge_two d t h, alpha_of_ge_two d (t + 1) (by omega)]
    have h1 : alphaLo d (t + 1) ≤ alphaLo d t + 1 ∧ alphaLo d t ≤ alphaLo d (t + 1) + 1 := by
      unfold alphaLo; constructor <;> split_ifs <;> omega
    have key : ∀ m₁ m₂ p : ℕ, m₂ ≤ m₁ + 1 → m₁ ≤ m₂ + 1 →
        ceilParity m₂ (p + 1) ≤ ceilParity m₁ p + 1 ∧ ceilParity m₁ p ≤ ceilParity m₂ (p + 1) + 1 := by
      intro m₁ m₂ p hm hm'; unfold ceilParity; constructor <;> split_ifs <;> omega
    exact key _ _ t h1.1 h1.2

theorem omega_step (t : ℕ) : omega (t + 1) ≤ omega t + 1 ∧ omega t ≤ omega (t + 1) + 1 := by
  constructor <;> sched

theorem alpha_tf (d : ℕ) (hd : 10 ≤ d) : alpha d (tf d) = meet d := by sched

theorem omega_tf (d : ℕ) (hd : 10 ≤ d) : omega (tf d) = meet d := by sched

/-- Top strictly above bottom at every stage `2 ≤ t < t_f`. -/
theorem alpha_lt_omega (d t : ℕ) (hd : 10 ≤ d) (h2 : 2 ≤ t) (ht : t < tf d) :
    alpha d t < omega t := by sched

theorem omega_le (d t : ℕ) (hd : 10 ≤ d) (ht : t ≤ tf d) : omega t + 3 ≤ d := by sched

theorem meet_le (d : ℕ) : meet d ≤ d := by unfold meet; omega

/-- `c(α(t),t) ≥ 2k² = 2^9` (the definition of `α*`). -/
theorem exp_top (d t : ℕ) (h2 : 2 ≤ t) : 3 * t + 15 ≤ 4 * d + 5 * alpha d t := by sched

/-- Rising top: `c(α(t),t) ≥ 2^17`. -/
theorem exp_top_rise (d t : ℕ) (hd : 10 ≤ d) (h2 : 2 ≤ t) (hs : alpha d (t + 1) < alpha d t) :
    3 * t + 23 ≤ 4 * d + 5 * alpha d t := by sched

/-- Non-top active nodes: `c(i,t) ≥ 2^19`. -/
theorem exp_nontop (d t i : ℕ) (h2 : 2 ≤ t) (hi : alpha d t + 2 ≤ i) :
    3 * t + 25 ≤ 4 * d + 5 * i := by
  have := exp_top d t h2
  omega

/-- Lemma 3.2: a descending top below the root has `c ≤ A k² / ν = 2^16`. -/
theorem exp_top_desc (d t : ℕ) (hd : 10 ≤ d) (h2 : 2 ≤ t) (hs : alpha d t < alpha d (t + 1))
    (h0 : alpha d t ≠ 0) : 4 * d + 5 * alpha d t ≤ 3 * t + 22 := by sched

/-- `c(α(t_f), t_f) = 2^16` (Lemma 4.5). -/
theorem exp_meet (d : ℕ) (hd : 10 ≤ d) : 4 * d + 5 * meet d = 3 * tf d + 6 + 16 := by
  unfold meet tf; omega

/-- Node `i` is active at stage `t`. -/
abbrev Active (d i t : ℕ) : Prop := t ≤ tf d ∧ alpha d t ≤ i ∧ i ≤ omega t ∧ i % 2 = t % 2


end R1T
