module

public import AKS.Chvatal.Tree
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Chvátal §3 scheduler: capacity and allocation (DCS-TR-294 §3); Lemmas 3.1/3.2 in `SchedulerLemmas`. -/

namespace Chvatal

/-- Scalar parameters of the §3 bag schedule (§7: `br = 64`, `A = br^2`, `nu = 1/br`). -/
structure ScheduleParams where
  br : Nat
  A : Rat
  nu : Rat
  hbr : 2 ≤ br
  hA : 1 < A
  hnu_pos : 0 < nu
  hnu_lt : nu < 1
  hAnu : 1 < A * nu

namespace ScheduleParams

variable (p : ScheduleParams)

theorem br_pos : 0 < p.br := by have := p.hbr; omega

theorem A_pos : (0 : Rat) < p.A := by linarith [p.hA]

theorem br_cast_pos : (0 : Rat) < (p.br : Rat) := by exact_mod_cast p.br_pos

end ScheduleParams

/-- §3 capacity: `c(i,t) = N * A^i * nu^t / (A * nu * br)` with `N = br^d`. -/
def capacity (p : ScheduleParams) (d i t : Nat) : Rat :=
  (↑(p.br ^ d) : Rat) * p.A ^ i * p.nu ^ t / (p.A * p.nu * (p.br : Rat))

theorem capacity_pos (p : ScheduleParams) (d i t : Nat) : 0 < capacity p d i t := by
  unfold capacity
  have hN : (0 : Rat) < ↑(p.br ^ d) := by exact_mod_cast Nat.pow_pos p.br_pos
  have hA := p.A_pos
  have hnu := p.hnu_pos
  have hbr := p.br_cast_pos
  have hAi : (0 : Rat) < p.A ^ i := pow_pos hA _
  have hnui : (0 : Rat) < p.nu ^ t := pow_pos hnu _
  positivity

theorem capacity_succ_level (p : ScheduleParams) (d i t : Nat) :
    capacity p d (i + 1) t = p.A * capacity p d i t := by
  unfold capacity
  field_simp
  ring

theorem capacity_succ_stage (p : ScheduleParams) (d i t : Nat) :
    capacity p d i (t + 1) = p.nu * capacity p d i t := by
  unfold capacity
  field_simp
  ring

/-- Active-level contribution factor `Q = A^2 * br^2`. -/
def capacityRatio (p : ScheduleParams) : Rat := p.A ^ 2 * (p.br : Rat) ^ 2

theorem capacityRatio_pos (p : ScheduleParams) : 0 < capacityRatio p := by
  unfold capacityRatio
  exact mul_pos (sq_pos_of_pos p.A_pos) (sq_pos_of_pos p.br_cast_pos)

/-- Weighted capacity along an even step: `br^(2m) * c(i+2m) = Q^m * c(i)`. -/
theorem capacity_weighted_step (p : ScheduleParams) (d i t m : Nat) :
    (p.br : Rat) ^ (2 * m) * capacity p d (i + 2 * m) t =
      capacityRatio p ^ m * capacity p d i t := by
  induction m with
  | zero => simp [capacityRatio]
  | succ m ih =>
    rw [show i + 2 * (m + 1) = i + 2 * m + 1 + 1 by omega, capacity_succ_level,
      capacity_succ_level]
    unfold capacityRatio at *
    linear_combination (p.A ^ 2 * (p.br : Rat) ^ 2) * ih

/-- Discrete top/bottom schedule for stages `0 … tf`. -/
structure LevelSchedule (p : ScheduleParams) (d : Nat) where
  tf : Nat
  alpha : Nat → Nat
  omega : Nat → Nat
  omega_le_d : ∀ t ≤ tf, omega t ≤ d
  alpha_parity : ∀ t ≤ tf, alpha t % 2 = t % 2
  omega_parity : ∀ t ≤ tf, omega t % 2 = t % 2
  alpha_step : ∀ t, t + 1 ≤ tf →
    alpha (t + 1) ≤ alpha t + 1 ∧ alpha t ≤ alpha (t + 1) + 1
  omega_step : ∀ t, t + 1 ≤ tf →
    omega (t + 1) ≤ omega t + 1 ∧ omega t ≤ omega (t + 1) + 1

/-- Node `i` is active at time `t`. -/
abbrev Active {p : ScheduleParams} {d : Nat} (sched : LevelSchedule p d) (i t : Nat) : Prop :=
  t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2

/-- §3 allocation `a(i,t)`. -/
def allocation (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d)
    (i t : Nat) : Rat :=
  if Active sched i t then
    if i = sched.alpha t then
      capacity p d i t
    else if i = sched.omega t then
      (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ i -
        capacity p d i t / capacityRatio p
    else
      (1 - 1 / capacityRatio p) * capacity p d i t
  else
    0

theorem allocation_inactive (p : ScheduleParams) (d : Nat)
    (sched : LevelSchedule p d) (i t : Nat) (h : ¬Active sched i t) :
    allocation p d sched i t = 0 := by
  simp only [allocation, if_neg h]

section Alloc

variable (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d)

theorem alloc_top {i t : Nat} (h : Active sched i t) (hα : i = sched.alpha t) :
    allocation p d sched i t = capacity p d i t := by
  unfold allocation; rw [if_pos h, if_pos hα]

theorem alloc_bot {i t : Nat} (h : Active sched i t)
    (hα : i ≠ sched.alpha t) (hω : i = sched.omega t) :
    allocation p d sched i t =
      (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ i - capacity p d i t / capacityRatio p := by
  unfold allocation; rw [if_pos h, if_neg hα, if_pos hω]

theorem alloc_mid {i t : Nat} (h : Active sched i t)
    (hα : i ≠ sched.alpha t) (hω : i ≠ sched.omega t) :
    allocation p d sched i t = (1 - 1 / capacityRatio p) * capacity p d i t := by
  unfold allocation; rw [if_pos h, if_neg hα, if_neg hω]

end Alloc

end Chvatal
