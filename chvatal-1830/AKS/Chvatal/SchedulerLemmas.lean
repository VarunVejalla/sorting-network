module

public import AKS.Chvatal.Scheduler
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Chvátal §3 Lemma 3.1 (DCS-TR-294 §3): algebraic core under the global mass identity. -/

namespace Chvatal

open Finset

/-- `α`-ladder: the mass below the active level `α + 2m + 2` telescopes. -/
private theorem ladder (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (ht : t ≤ sched.tf) (m : Nat) (hm : sched.alpha t + 2 * m + 2 ≤ sched.omega t) :
    ∑ j ∈ range (sched.alpha t + 2 * m + 2), (p.br : Rat) ^ j * allocation p d sched j t =
      (p.br : Rat) ^ sched.alpha t * capacity p d (sched.alpha t) t * capacityRatio p ^ m := by
  have hpar := sched.alpha_parity t ht
  have hbelow : ∑ j ∈ range (sched.alpha t), (p.br : Rat) ^ j * allocation p d sched j t = 0 :=
    sum_eq_zero fun j hj => by
      rw [allocation_inactive _ _ _ _ _ (by unfold Active; simp at hj; omega), mul_zero]
  induction m with
  | zero =>
    rw [sum_range_succ, sum_range_succ, hbelow, allocation_inactive p d sched (sched.alpha t + 1) t
      (by unfold Active; omega), alloc_top p d sched (i := sched.alpha t) (by unfold Active; omega) rfl]
    simp
  | succ m ih =>
    have := capacity_weighted_step p d (sched.alpha t) t (m + 1)
    rw [show sched.alpha t + 2 * (m + 1) + 2 = sched.alpha t + 2 * m + 2 + 1 + 1 by omega,
      sum_range_succ, sum_range_succ, ih (by omega),
      allocation_inactive p d sched (sched.alpha t + 2 * m + 2 + 1) t (by unfold Active; omega),
      alloc_mid p d sched (i := sched.alpha t + 2 * m + 2) (by unfold Active; omega) (by omega)
        (by omega)]
    rw [show sched.alpha t + 2 * m + 2 = sched.alpha t + 2 * (m + 1) by omega] at *
    have hQ1 : (1 - 1 / capacityRatio p) * capacityRatio p = capacityRatio p - 1 := by
      field_simp [(capacityRatio_pos p).ne']
    linear_combination (p.br : Rat) ^ sched.alpha t * (1 - 1 / capacityRatio p) * this +
      ((p.br : Rat) ^ sched.alpha t * capacity p d (sched.alpha t) t * capacityRatio p ^ m) * hQ1

/-- §3 Lemma 3.1 under the global mass identity `sum_j br^j a(j,t) = N`. -/
theorem lemma31_of_total (p : ScheduleParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat) (ht : t ≤ sched.tf)
    (htotal : (∑ j ∈ Finset.range (d + 1),
        (p.br : Rat) ^ j * allocation p d sched j t) = (p.br ^ d : Nat))
    (i : Nat) (hα : sched.alpha t ≤ i) (hω : i ≤ sched.omega t)
    (hpar : i % 2 = t % 2) :
    (∑ j ∈ Finset.Icc i d,
        (p.br : Rat) ^ (j - i) * allocation p d sched j t) =
      if i = sched.alpha t then
        (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ i
      else
        (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ i -
          capacity p d i t / capacityRatio p := by
  have hid : i ≤ d := le_trans hω (sched.omega_le_d t ht)
  have hbr : (p.br : Rat) ^ i ≠ 0 := pow_ne_zero _ p.br_cast_pos.ne'
  -- mass of levels `≥ i`, rescaled by `br^i`, is `N` minus the mass below `i`
  have hsum : (∑ j ∈ Icc i d, (p.br : Rat) ^ (j - i) * allocation p d sched j t) =
      ((↑(p.br ^ d) : Rat) - ∑ j ∈ range i, (p.br : Rat) ^ j * allocation p d sched j t) /
        (p.br : Rat) ^ i := by
    have hlo : (range (d + 1)).filter (· < i) = range i := by
      ext j; simp only [mem_filter, mem_range]; omega
    have hhi : (range (d + 1)).filter (fun j ↦ i ≤ j) = Icc i d := by
      ext j; simp only [mem_filter, mem_range, mem_Icc]; omega
    have h := sum_filter_add_sum_filter_not (range (d + 1)) (fun j : Nat ↦ j < i)
      (fun j ↦ (p.br : Rat) ^ j * allocation p d sched j t)
    simp only [not_lt, hlo, hhi] at h
    rw [eq_div_iff hbr, sum_mul]
    have : (↑(p.br ^ d) : Rat) - ∑ j ∈ range i, (p.br : Rat) ^ j * allocation p d sched j t =
        ∑ j ∈ Icc i d, (p.br : Rat) ^ j * allocation p d sched j t := by linarith
    rw [this]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_Icc] at hj
    rw [mul_assoc, mul_comm (allocation _ _ _ _ _), ← mul_assoc, ← pow_add, Nat.sub_add_cancel hj.1]
  have hpa := sched.alpha_parity t ht
  split_ifs with htop
  · have : ∑ j ∈ range i, (p.br : Rat) ^ j * allocation p d sched j t = 0 :=
      sum_eq_zero fun j hj => by
        rw [allocation_inactive _ _ _ _ _ (by unfold Active; simp at hj; omega), mul_zero]
    rw [hsum, this, sub_zero]
  · obtain ⟨m, hm⟩ : ∃ m, i = sched.alpha t + 2 * m + 2 := ⟨(i - sched.alpha t) / 2 - 1, by omega⟩
    have hw := capacity_weighted_step p d (sched.alpha t) t (m + 1)
    rw [hsum, hm, ladder p d sched t ht m (by omega), sub_div,
      show sched.alpha t + 2 * m + 2 = sched.alpha t + 2 * (m + 1) by omega]
    congr 1
    rw [div_eq_div_iff (pow_ne_zero _ p.br_cast_pos.ne') (capacityRatio_pos p).ne']
    linear_combination (-(p.br : Rat) ^ sched.alpha t) * hw

end Chvatal
