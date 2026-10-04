module
/-
  # Chvatal §4 StageRouting from P + separator quality

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §4.

  Status: discharges `StageRouting` parent-outsider / intrusion / fringe bounds
  from `OutsiderBoundLe` and `LocalSeparatorQuality`. Sibling mass is collapsed
  in `StageKernel`; schedule slack, children-send aggregates, Lemma 4.1 counts,
  and level-0 routing stay as kernel hypotheses. Scramble separators (Thm 5.1)
  remain Phase 2.
-/

public import AKS.Chvatal.PlacementStep
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Chvatal

/-! **Residue after P + local separator quality** -/

/-- Hypotheses left after defining parent-outsider and intrusion masses from
    `P` and `LocalSeparatorQuality`, and chaining the fringe filter. -/
structure StageRoutingResidue (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
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
  /-- Local separator at the parent of each non-root child. -/
  parentSep : ∀ (b : KBag p.br d), 1 ≤ b.l → LocalSeparatorQuality ip
  /-- Bag size of the parent separator is at most capacity. -/
  ha_le_cap : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    (parentSep b hb).a ≤ capacity p d (b.l - 1) t
  sibMass0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  slack0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  hSibMass0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    sibMass0 b hb ≤
      ((p.br : Rat) - 1) * ip.mu * siblingFactor p ip * capacity p d (b.l - 1) t
  hSlack0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    slack0 b hb ≤
      (p.A * p.nu * (p.br : Rat) - 2 * p.A * p.nu +
        1 / (2 * p.A ^ 2 * (p.br : Rat) ^ 2)) * capacity p d (b.l - 1) t
  /-- Order-0 bad keys in the parent-send Finset are covered by Lemma 4.2 parts
      (parent outsiders + sibling mass + intrusion + slack). -/
  hBadSend0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
      ((b.parent (br_ge_one p)).strangers 1 perm
          (pl.regs (b.parent (br_ge_one p))) (br_ge_one p) : Rat) +
        sibMass0 b hb + (parentSep b hb).intrusion + slack0 b hb
  /-- Fringe routing: order-`r` outsiders entering from the parent are at most
      the separator's fringe image of the parent's order-`(r-1)` outsiders. -/
  hFringeSend : ∀ (b : KBag p.br d) (r : Nat)
      (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
      (parentSep b hb).fringeSent
        ((b.parent (br_ge_one p)).strangers r perm
          (pl.regs (b.parent (br_ge_one p))) (br_ge_one p) : Rat)
  hFromChildren0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromChildren b hb) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta / (p.br : Rat) * capacity p d (b.l - 1) t
  hFromChildrenR : ∀ (b : KBag p.br d) (r : Nat)
      (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromChildren b hb) (br_ge_one p) : Rat)) ≤
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) *
          (p.A * p.nu * capacity p d (b.l - 1) t))
  level0 : ∀ (b : KBag p.br d) (r : Nat), b.l = 0 → r ≤ d →
    ((b.strangers (r + 1) perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta ^ r * capacity p d 0 (t + 1)

/-! **Masses defined from P / separator** -/

/-- Parent order-0 outsider mass at time `t`. -/
def parentOutMass (p : ScheduleParams) (d : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (b : KBag p.br d) (_hb : 1 ≤ b.l) : Rat :=
  ((b.parent (br_ge_one p)).strangers 1 perm
    (pl.regs (b.parent (br_ge_one p))) (br_ge_one p) : Rat)

/-- Intrusion mass from the parent separator. -/
def StageRoutingResidue.intrusionMass {p : ScheduleParams} {ip : InvariantParams}
    {d : Nat} {sched : LevelSchedule p d} {t : Nat}
    {pl : Placement p.br d}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    {pl' : Placement p.br d}
    {perm' : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (R : StageRoutingResidue p ip d sched t pl perm pl' perm')
    (b : KBag p.br d) (hb : 1 ≤ b.l) : Rat :=
  (R.parentSep b hb).intrusion

theorem parentOutMass_le_of_P (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hP : OutsiderBoundLe p ip d sched t pl perm)
    (b : KBag p.br d) (hb : 1 ≤ b.l) :
    parentOutMass p d pl perm b hb ≤
      ip.mu * capacity p d (b.l - 1) t := by
  have hbr := br_ge_one p
  have hle := hP (b.parent hbr) 0 (Nat.zero_le d)
  -- `hle`: strangers 1 ≤ μ · δ⁰ · c(parent.l, t)
  rw [pow_zero, mul_one, show (b.parent hbr).l = b.l - 1 from rfl] at hle
  simpa [parentOutMass] using hle

theorem StageRoutingResidue.intrusionMass_le {p : ScheduleParams}
    {ip : InvariantParams} {d : Nat} {sched : LevelSchedule p d} {t : Nat}
    {pl : Placement p.br d}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    {pl' : Placement p.br d}
    {perm' : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (R : StageRoutingResidue p ip d sched t pl perm pl' perm')
    (b : KBag p.br d) (hb : 1 ≤ b.l) :
    R.intrusionMass b hb ≤ ip.epsB * capacity p d (b.l - 1) t := by
  have hintr := (R.parentSep b hb).hIntrusion
  have ha := R.ha_le_cap b hb
  have hmul :
      ip.epsB * (R.parentSep b hb).a ≤
        ip.epsB * capacity p d (b.l - 1) t :=
    mul_le_mul_of_nonneg_left ha ip.hepsB_nonneg
  simpa [StageRoutingResidue.intrusionMass] using hintr.trans hmul

theorem fringe_parent_le_of_P (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (pl' : Placement p.br d)
    (perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hP : OutsiderBoundLe p ip d sched t pl perm)
    (R : StageRoutingResidue p ip d sched t pl perm pl' perm')
    (b : KBag p.br d) (r : Nat) (hr1 : 1 ≤ r) (hrd : r ≤ d)
    (hb : 1 ≤ b.l) :
    ((b.strangers (r + 1) perm' (R.step.fromParent b hb) (br_ge_one p) : Rat)) ≤
      ip.epsF * (ip.mu * ip.delta ^ (r - 1) * capacity p d (b.l - 1) t) := by
  have hbr := br_ge_one p
  have hsend := R.hFringeSend b r hr1 hrd hb
  set src : Rat :=
    ((b.parent hbr).strangers r perm (pl.regs (b.parent hbr)) hbr : Rat)
  have hfringe : (R.parentSep b hb).fringeSent src ≤ ip.epsF * src :=
    (R.parentSep b hb).hFringe src
  have hPpar := hP (b.parent hbr) (r - 1) (by omega)
  have hsrc : src ≤
      ip.mu * ip.delta ^ (r - 1) * capacity p d (b.l - 1) t := by
    -- `hPpar`: strangers ((r-1)+1) ≤ μ · δ^{r-1} · c(parent.l, t)
    have hidx : (r - 1) + 1 = r := by omega
    rw [hidx, show (b.parent hbr).l = b.l - 1 from rfl] at hPpar
    simpa [src] using hPpar
  have heps : (R.parentSep b hb).fringeSent src ≤
      ip.epsF * (ip.mu * ip.delta ^ (r - 1) * capacity p d (b.l - 1) t) :=
    hfringe.trans (mul_le_mul_of_nonneg_left hsrc ip.hepsF_nonneg)
  exact hsend.trans heps

/-! **Assemble StageRouting** -/

/-- `OutsiderBoundLe` + separator quality + residue ⇒ `StageRouting`. -/
def stageRouting_of_p (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hP : OutsiderBoundLe p ip d sched t pl perm)
    (R : StageRoutingResidue p ip d sched t pl perm pl' perm') :
    StageRouting p ip d sched t pl perm pl' perm' where
  ht := R.ht
  step := R.step
  counts := R.counts
  counts_wires := R.counts_wires
  counts_bad := R.counts_bad
  parentOut0 := fun b hb => parentOutMass p d pl perm b hb
  sibMass0 := R.sibMass0
  intrusion0 := fun b hb => R.intrusionMass b hb
  slack0 := R.slack0
  hParentOut0 := fun b hb => parentOutMass_le_of_P p ip d sched t pl perm hP b hb
  hSibMass0 := R.hSibMass0
  hIntrusion0 := fun b hb => R.intrusionMass_le b hb
  hSlack0 := R.hSlack0
  hFromParent0 := fun b hb => by
    simpa [parentOutMass, StageRoutingResidue.intrusionMass] using R.hBadSend0 b hb
  hFromChildren0 := R.hFromChildren0
  hFromParentR := fun b r hr1 hrd hb =>
    fringe_parent_le_of_P p ip d sched t pl perm pl' perm' hP R b r hr1 hrd hb
  hFromChildrenR := R.hFromChildrenR
  level0 := R.level0

/-- One-step preservation from `P`, separator residue, and separator conds. -/
theorem outsiderBound_step_of_p (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hconds : SeparatorConds p ip)
    (hP : OutsiderBoundLe p ip d sched t pl perm)
    (R : StageRoutingResidue p ip d sched t pl perm pl' perm') :
    OutsiderBoundLe p ip d sched (t + 1) pl' perm' :=
  outsiderBound_step_of_routing p ip d sched t pl pl' perm perm' hconds
    (stageRouting_of_p p ip d sched t pl pl' perm perm' hP R) hP

end Chvatal
