module
-- Chvátal §4: `StageKernel` is the one-stage combinatorial interface; under `SeparatorConds` and `P`
-- the outsider bound advances one stage.

public import AKS.Chvatal.RoutingFromP

@[expose] public section

namespace Chvatal

/-- Paper Lemma 4.2 sibling-contamination budget at the parent capacity. -/
def sibMassBound (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (b : KBag p.br d) (_hb : 1 ≤ b.l) : Rat :=
  ((p.br : Rat) - 1) * ip.mu * siblingFactor p ip * capacity p d (b.l - 1) t

/-- Schedule slack used by Lemma 4.2: `slackCoeff · c`. -/
def slackBound (p : ScheduleParams) (d t : Nat)
    (b : KBag p.br d) (_hb : 1 ≤ b.l) : Rat :=
  slackCoeff p * capacity p d (b.l - 1) t

structure StageKernel (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat) (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) (pl' : Placement p.br d)
    (perm' : Fin (p.br ^ d) → Fin (p.br ^ d)) where
  ht : t + 1 ≤ sched.tf
  step : PlacementStep p d pl pl'
  /-- Order-0 bad keys in the parent-send Finset ≤ parent outsiders + sibling budget +
      intrusion + slack. -/
  hBadSend0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
      parentOutMass p d pl perm b hb +
        sibMassBound p ip d t b hb + ip.epsB * capacity p d (b.l - 1) t +
        slackBound p d t b hb
  hFringeSend : ∀ (b : KBag p.br d) (r : Nat)
      (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
      ip.epsF *
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

/-- One-step preservation under the stage kernel: `P(t)` + conds + kernel ⇒ `P(t+1)`. -/
theorem outsiderBound_step_of_kernel (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat) (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hconds : SeparatorConds p ip)
    (hP : OutsiderBoundLe p ip d sched t pl perm)
    (K : StageKernel p ip d sched t pl perm pl' perm') :
    OutsiderBoundLe p ip d sched (t + 1) pl' perm' := by
  obtain ⟨_, h42, _, _, h45⟩ := hconds
  intro b r hr
  by_cases hb0 : b.l = 0
  · simpa [hb0] using K.level0 b r hb0 hr
  have hb : 1 ≤ b.l := by omega
  have hbr := br_ge_one p
  have hc := (capacity_pos p d (b.l - 1) t).le
  have hcap : capacity p d b.l (t + 1) = p.A * p.nu * capacity p d (b.l - 1) t := by
    rw [show b.l = (b.l - 1) + 1 by omega, capacity_succ_level, capacity_succ_stage]
    simp only [Nat.add_sub_cancel]
    ring
  rw [hcap]
  have hsplit := K.step.strangers_split_le perm' b hb (r + 1)
  by_cases hr0 : r = 0
  · subst hr0
    have hpar : parentOutMass p d pl perm b hb ≤ ip.mu * capacity p d (b.l - 1) t := by
      simpa [parentOutMass] using hP (b.parent hbr) 0 (Nat.zero_le d)
    have h := cond42_scaled p ip _ hc h42
    have h1 := K.hBadSend0 b hb
    unfold sibMassBound at h1
    unfold slackBound at h1
    simp only [pow_zero, mul_one]
    linarith [K.hFromChildren0 b hb]
  · have hr1 : 1 ≤ r := by omega
    have hsrc := hP (b.parent hbr) (r - 1) (by omega)
    rw [Nat.sub_add_cancel hr1, show (b.parent hbr).l = b.l - 1 from rfl] at hsrc
    have hf := mul_le_mul_of_nonneg_left hsrc ip.hepsF_nonneg
    have h := cond45_scaled p ip _ hc r hr1 h45
    linarith [K.hFringeSend b r hr1 hr hb, K.hFromChildrenR b r hr1 hr hb]

end Chvatal
