module
/-
  # Chvatal §4 minimal stage kernel

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §4.

  Status: collapses `StageRoutingResidue` by defining sibling mass as the
  Lemma 4.2 coefficient `(k-1)·μ·siblingFactor·c`. The remaining kernel is the
  irreducible combinatorial/schedule interface for one stage: placement cover,
  separator quality, schedule slack, children-send aggregates, Lemma 4.1 counts,
  bad-send and fringe routing, and level-0. Under `SeparatorConds` + `P` +
  `StageKernel`, the outsider bound advances one stage (kernel-checked).
-/

public import AKS.Chvatal.RoutingFromP
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Chvatal

/-! **Sibling mass (Lemma 4.2)** -/

/-- Paper Lemma 4.2 sibling-contamination budget at the parent capacity. -/
def sibMassBound (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (b : KBag p.br d) (_hb : 1 ≤ b.l) : Rat :=
  ((p.br : Rat) - 1) * ip.mu * siblingFactor p ip * capacity p d (b.l - 1) t

theorem sibMassBound_le (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (b : KBag p.br d) (hb : 1 ≤ b.l) :
    sibMassBound p ip d t b hb ≤
      ((p.br : Rat) - 1) * ip.mu * siblingFactor p ip * capacity p d (b.l - 1) t :=
  le_rfl

/-! **Schedule slack** -/

/-- Exact schedule-slack used by Lemma 4.2 / `hSlack0`: `slackCoeff · c`. -/
def slackBound (p : ScheduleParams) (d t : Nat)
    (b : KBag p.br d) (_hb : 1 ≤ b.l) : Rat :=
  slackCoeff p * capacity p d (b.l - 1) t

theorem slackBound_le (p : ScheduleParams) (d t : Nat)
    (b : KBag p.br d) (hb : 1 ≤ b.l) :
    slackBound p d t b hb ≤ slackCoeff p * capacity p d (b.l - 1) t :=
  le_rfl

/-! **Stage kernel** -/

/-- Irreducible hypotheses for one stage after discharging parent-outsider /
    intrusion / fringe algebra from `P` + separator quality, and sibling mass
    from its closed Lemma 4.2 form. -/
structure StageKernel (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (pl' : Placement p.br d)
    (perm' : Fin (p.br ^ d) → Fin (p.br ^ d)) where
  ht : t + 1 ≤ sched.tf
  step : PlacementStep p d pl pl'
  counts : ∀ i, sched.alpha t ≤ i → i < sched.omega t → StageCounts p d i t
  counts_wires : ∀ i (ha : sched.alpha t ≤ i) (ho : i < sched.omega t),
    (counts i ha ho).WiresMassForm p d i t
  counts_bad : ∀ i (ha : sched.alpha t ≤ i) (ho : i < sched.omega t),
    (counts i ha ho).BadBound p ip d i t
  parentSep : ∀ (b : KBag p.br d), 1 ≤ b.l → LocalSeparatorQuality ip
  ha_le_cap : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    (parentSep b hb).a ≤ capacity p d (b.l - 1) t
  slack0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  hSlack0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    slack0 b hb ≤ slackCoeff p * capacity p d (b.l - 1) t
  /-- Order-0 bad keys in the parent-send Finset ≤ parent outsiders + sibling
      budget + intrusion + slack. -/
  hBadSend0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
      parentOutMass p d pl perm b hb +
        sibMassBound p ip d t b hb +
        (parentSep b hb).intrusion + slack0 b hb
  hFringeSend : ∀ (b : KBag p.br d) (r : Nat)
      (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
      (parentSep b hb).fringeSent
        ((b.parent (br_ge_one p)).strangers r perm
          (pl.regs (b.parent (br_ge_one p))) (br_ge_one p) : Rat)
  hFromChildren0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromChildren b hb) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta * (p.br : Rat) * p.A ^ 2 * capacity p d (b.l - 1) t
  hFromChildrenR : ∀ (b : KBag p.br d) (r : Nat)
      (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromChildren b hb) (br_ge_one p) : Rat)) ≤
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) *
          (p.A * p.nu * capacity p d (b.l - 1) t))
  level0 : ∀ (b : KBag p.br d) (r : Nat), b.l = 0 → r ≤ d →
    ((b.strangers (r + 1) perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta ^ r * capacity p d 0 (t + 1)

/-- `StageKernel` fills `StageRoutingResidue` (sibling mass = closed bound). -/
def stageRoutingResidue_of_kernel (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (K : StageKernel p ip d sched t pl perm pl' perm') :
    StageRoutingResidue p ip d sched t pl perm pl' perm' where
  ht := K.ht
  step := K.step
  counts := K.counts
  counts_wires := K.counts_wires
  counts_bad := K.counts_bad
  parentSep := K.parentSep
  ha_le_cap := K.ha_le_cap
  sibMass0 := fun b hb => sibMassBound p ip d t b hb
  slack0 := K.slack0
  hSibMass0 := fun b hb => sibMassBound_le p ip d t b hb
  hSlack0 := K.hSlack0
  hBadSend0 := fun b hb => by
    simpa [parentOutMass, sibMassBound] using K.hBadSend0 b hb
  hFringeSend := K.hFringeSend
  hFromChildren0 := K.hFromChildren0
  hFromChildrenR := K.hFromChildrenR
  level0 := K.level0

/-- One-step preservation under the minimal stage kernel. -/
theorem outsiderBound_step_of_kernel (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hconds : SeparatorConds p ip)
    (hP : OutsiderBoundLe p ip d sched t pl perm)
    (K : StageKernel p ip d sched t pl perm pl' perm') :
    OutsiderBoundLe p ip d sched (t + 1) pl' perm' :=
  outsiderBound_step_of_p p ip d sched t pl pl' perm perm' hconds hP
    (stageRoutingResidue_of_kernel p ip d sched t pl pl' perm perm' K)

/-- Trajectory of kernels yields the final outsider bound. -/
structure KernelTrajectory (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d)
    (pls : Nat → Placement p.br d)
    (perms : Nat → (Fin (p.br ^ d) → Fin (p.br ^ d))) where
  kernels : ∀ t, t + 1 ≤ sched.tf →
    StageKernel p ip d sched t (pls t) (perms t) (pls (t + 1)) (perms (t + 1))

theorem outsiderBound_induction_of_kernel (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d)
    (pls : Nat → Placement p.br d)
    (perms : Nat → (Fin (p.br ^ d) → Fin (p.br ^ d)))
    (hconds : SeparatorConds p ip)
    (traj : KernelTrajectory p ip d sched pls perms)
    (h0 : OutsiderBoundLe p ip d sched 0 (pls 0) (perms 0)) :
    OutsiderBoundLe p ip d sched sched.tf (pls sched.tf) (perms sched.tf) := by
  have step : ∀ t, t ≤ sched.tf →
      OutsiderBoundLe p ip d sched t (pls t) (perms t) := by
    intro t ht
    induction t with
    | zero => exact h0
    | succ t ih =>
      have ht' : t + 1 ≤ sched.tf := ht
      have ht0 : t ≤ sched.tf := by omega
      exact outsiderBound_step_of_kernel p ip d sched t (pls t) (pls (t + 1))
        (perms t) (perms (t + 1)) hconds (ih ht0) (traj.kernels t ht')
  exact step sched.tf le_rfl

end Chvatal
