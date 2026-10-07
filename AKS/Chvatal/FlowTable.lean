module

/-
  # Chvátal §3 integer flow table (DCS-TR-294 pp. 7–9)

  Between times `t` and `t+1` each node on level `i` sends `flowUp` wires to its parent
  (the fringe blocks `F₁ ∪ F₂`) and `flowDown` wires to each of its `br` children
  (a block `B_j`). Formulas (`c = capacity`, `Q = A²·br²`, `k = br`), for `2 ≤ t < tf`:
  * `i = α t`, top descends (`α t < α (t+1)`): `π = 0`, `τ = c/k`;
  * `i = α t`, top rises: `π = ν c/(A k)`, `τ = (A k − ν) c/(A k²)`;
  * `α t < i < ω t`: `π = (A ν k − 1) c/Q`, `τ = (A k − ν) c/(A k²)`;
  * `i = ω t`, bottom descends: `π = (A ν k − 1) c/Q`, `τ = a(ω t + 1, t + 1)`;
  * `i = ω t`, bottom rises: `π = a(ω t, t)`, `τ = 0`.
  These identities were verified with exact rational arithmetic for `d = 14, 15, 20, 30`.
-/

public import AKS.Chvatal.Scheduler

@[expose] public section

namespace Chvatal

/-- Wires a node on level `i` sends to its parent between times `t` and `t+1`. -/
def flowUp (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d) (i t : Nat) : Rat :=
  if allocation p d sched i t = 0 then 0
  else if i = sched.alpha t then
    (if sched.alpha t < sched.alpha (t + 1) then 0
     else p.nu * capacity p d i t / (p.A * (p.br : Rat)))
  else if i = sched.omega t then
    (if sched.omega t < sched.omega (t + 1) then
      (p.A * p.nu * (p.br : Rat) - 1) * capacity p d i t / capacityRatio p
     else allocation p d sched i t)
  else (p.A * p.nu * (p.br : Rat) - 1) * capacity p d i t / capacityRatio p

/-- Wires a node on level `i` sends to each of its `br` children between `t` and `t+1`. -/
def flowDown (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d) (i t : Nat) : Rat :=
  if allocation p d sched i t = 0 then 0
  else if i = sched.alpha t then
    (if sched.alpha t < sched.alpha (t + 1) then capacity p d i t / (p.br : Rat)
     else (p.A * (p.br : Rat) - p.nu) * capacity p d i t / (p.A * (p.br : Rat) ^ 2))
  else if i = sched.omega t then
    (if sched.omega t < sched.omega (t + 1) then
      allocation p d sched (sched.omega t + 1) (t + 1)
     else 0)
  else (p.A * (p.br : Rat) - p.nu) * capacity p d i t / (p.A * (p.br : Rat) ^ 2)

/-- **B1 (send identity).** Every node sends out exactly its wires:
    `a(i,t) = π(i,t) + br · τ(i,t)` for `2 ≤ t`, `t + 1 < tf`, given `α s < ω s` for
    `2 ≤ s < tf`. -/
theorem allocation_eq_flowUp_add_flowDown (p : ScheduleParams) (d : Nat)
    (sched : LevelSchedule p d)
    (hlt : ∀ s, 2 ≤ s → s < sched.tf → sched.alpha s < sched.omega s)
    (t : Nat) (ht2 : 2 ≤ t) (ht : t + 1 < sched.tf) (i : Nat) :
    allocation p d sched i t =
      flowUp p d sched i t + (p.br : Rat) * flowDown p d sched i t := by
  by_cases h_alloc : allocation p d sched i t = 0
  · simp [flowUp, flowDown, h_alloc]
  have hactive : t ≤ sched.tf ∧ sched.alpha t ≤ i ∧ i ≤ sched.omega t ∧ i % 2 = t % 2 := by
    by_contra h_contra; exact h_alloc (allocation_inactive p d sched i t h_contra)
  have hA := p.A_pos
  have hbr := p.br_cast_pos
  have hnu := p.hnu_pos
  have hc := capacity_pos p d i t
  have hQ : capacityRatio p = p.A ^ 2 * (p.br : Rat) ^ 2 := rfl
  by_cases hα : i = sched.alpha t
  · have hal : allocation p d sched i t = capacity p d i t := by
      unfold allocation; rw [if_pos hactive, if_pos hα]
    by_cases hstep : sched.alpha t < sched.alpha (t + 1)
    · simp only [flowUp, flowDown, if_neg h_alloc, if_pos hα, if_pos hstep]
      rw [hal]; field_simp; simp
    · simp only [flowUp, flowDown, if_neg h_alloc, if_pos hα, if_neg hstep]
      rw [hal]; field_simp; ring
  by_cases hω : i = sched.omega t
  · have hal : allocation p d sched i t =
        (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ i - capacity p d i t / capacityRatio p := by
      unfold allocation; rw [if_pos hactive, if_neg hα, if_pos hω]
    by_cases hstep : sched.omega t < sched.omega (t + 1)
    · have hsucc : sched.omega (t + 1) = sched.omega t + 1 := by
        have h1 := sched.omega_step t (by omega)
        have h2 := sched.omega_parity (t + 1) (by omega)
        have h3 := sched.omega_parity t hactive.1
        omega
      have hα1 : sched.alpha (t + 1) < sched.omega t + 1 := by
        have := hlt (t + 1) (by omega) ht
        omega
      have hact1 : t + 1 ≤ sched.tf ∧ sched.alpha (t + 1) ≤ sched.omega t + 1 ∧
          sched.omega t + 1 ≤ sched.omega (t + 1) ∧ (sched.omega t + 1) % 2 = (t + 1) % 2 := by
        have h3 := sched.omega_parity t hactive.1
        refine ⟨by omega, by omega, by omega, by omega⟩
      have hal1 : allocation p d sched (sched.omega t + 1) (t + 1) =
          (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ (sched.omega t + 1) -
            capacity p d (sched.omega t + 1) (t + 1) / capacityRatio p := by
        unfold allocation
        rw [if_pos hact1, if_neg (by omega), if_pos hsucc.symm]
      have hcap1 : capacity p d (sched.omega t + 1) (t + 1) =
          p.nu * (p.A * capacity p d (sched.omega t) t) := by
        rw [capacity_succ_stage, capacity_succ_level]
      simp only [flowUp, flowDown, if_neg h_alloc, if_neg hα, if_pos hω, if_pos hstep]
      rw [hal, hal1, hcap1, hω]
      simp only [Nat.cast_pow] at *
      rw [hQ]
      field_simp
      ring
    · simp only [flowUp, flowDown, if_neg h_alloc, if_neg hα, if_pos hω, if_neg hstep]
      ring
  · have hal : allocation p d sched i t = (1 - 1 / capacityRatio p) * capacity p d i t := by
      unfold allocation; rw [if_pos hactive, if_neg hα, if_neg hω]
    simp only [flowUp, flowDown, if_neg h_alloc, if_neg hα, if_neg hω]
    rw [hal, hQ]
    field_simp
    ring

end Chvatal
