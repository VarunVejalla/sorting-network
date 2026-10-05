module
/-
  # Chvatal §4 placement transition (source split)

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §4.

  Status: a child bag after one stage is covered by a parent-send Finset and a
  children-send Finset. Kernel-checks the outsider source-split inequalities
  used by `StageDynamics`, and assembles `StageDynamics` when the remaining
  numeric routing bounds are supplied. Comparator networks and separator
  modules that produce those Finsets remain deferred.
-/

public import AKS.Chvatal.StageDynamics
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Chvatal

open Finset

/-! **Placement step** -/

/-- One stage's register routing: each non-root child bag is covered by keys
    sent from its parent and keys sent up from its children. -/
structure PlacementStep (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) where
  fromParent : ∀ (b : KBag p.br d), 1 ≤ b.l → Finset (Fin (p.br ^ d))
  fromChildren : ∀ (b : KBag p.br d), 1 ≤ b.l → Finset (Fin (p.br ^ d))
  hregs : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    pl'.regs b ⊆ fromParent b hb ∪ fromChildren b hb

/-- Outsider count on a covered bag splits across the two send Finsets. -/
theorem PlacementStep.strangers_split_le (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (S : PlacementStep p d pl pl')
    (perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (b : KBag p.br d) (hb : 1 ≤ b.l) (j : Nat) :
    (b.strangers j perm' (pl'.regs b) (br_ge_one p) : Rat) ≤
      (b.strangers j perm' (S.fromParent b hb) (br_ge_one p) : Rat) +
        (b.strangers j perm' (S.fromChildren b hb) (br_ge_one p) : Rat) := by
  have hmono :=
    b.strangers_mono j perm' (S.hregs b hb) (br_ge_one p)
  have hunion :=
    b.strangers_union_le j perm' (S.fromParent b hb) (S.fromChildren b hb)
      (br_ge_one p)
  have hnat :
      b.strangers j perm' (pl'.regs b) (br_ge_one p) ≤
        b.strangers j perm' (S.fromParent b hb) (br_ge_one p) +
          b.strangers j perm' (S.fromChildren b hb) (br_ge_one p) :=
    Nat.le_trans hmono hunion
  exact_mod_cast hnat

/-! **Routing bounds on a placement step** -/

/-- Numeric bounds needed on top of a `PlacementStep` to fill `StageDynamics`.
    The stranger masses are the Finset outsider counts on the send sets. -/
structure StageRouting (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
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
  parentOut0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  sibMass0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  intrusion0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  slack0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  hParentOut0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    parentOut0 b hb ≤ ip.mu * capacity p d (b.l - 1) t
  hSibMass0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    sibMass0 b hb ≤
      ((p.br : Rat) - 1) * ip.mu * siblingFactor p ip * capacity p d (b.l - 1) t
  hIntrusion0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    intrusion0 b hb ≤ ip.epsB * capacity p d (b.l - 1) t
  hSlack0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    slack0 b hb ≤ slackCoeff p * capacity p d (b.l - 1) t
  /-- Order-0 outsiders in the parent-send Finset are covered by Lemma 4.2 parts. -/
  hFromParent0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
      parentOut0 b hb + sibMass0 b hb + intrusion0 b hb + slack0 b hb
  /-- Order-0 outsiders in the children-send Finset. -/
  hFromChildren0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromChildren b hb) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta / (p.br : Rat) * capacity p d (b.l - 1) t
  /-- Order-`r` outsiders in the parent-send Finset (fringe filter). -/
  hFromParentR : ∀ (b : KBag p.br d) (r : Nat)
      (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
      ip.epsF * (ip.mu * ip.delta ^ (r - 1) * capacity p d (b.l - 1) t)
  /-- Order-`r` outsiders in the children-send Finset. -/
  hFromChildrenR : ∀ (b : KBag p.br d) (r : Nat)
      (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromChildren b hb) (br_ge_one p) : Rat)) ≤
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) *
          (p.A * p.nu * capacity p d (b.l - 1) t))
  level0 : ∀ (b : KBag p.br d) (r : Nat), b.l = 0 → r ≤ d →
    ((b.strangers (r + 1) perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta ^ r * capacity p d 0 (t + 1)

/-- Parent-send outsider mass used by `StageDynamics`. -/
def StageRouting.fromParent0Mass {p : ScheduleParams} {ip : InvariantParams}
    {d : Nat} {sched : LevelSchedule p d} {t : Nat}
    {pl : Placement p.br d}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    {pl' : Placement p.br d}
    {perm' : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (R : StageRouting p ip d sched t pl perm pl' perm')
    (b : KBag p.br d) (hb : 1 ≤ b.l) : Rat :=
  (b.strangers 1 perm' (R.step.fromParent b hb) (br_ge_one p) : Rat)

/-- Children-send outsider mass used by `StageDynamics`. -/
def StageRouting.fromChildren0Mass {p : ScheduleParams} {ip : InvariantParams}
    {d : Nat} {sched : LevelSchedule p d} {t : Nat}
    {pl : Placement p.br d}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    {pl' : Placement p.br d}
    {perm' : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (R : StageRouting p ip d sched t pl perm pl' perm')
    (b : KBag p.br d) (hb : 1 ≤ b.l) : Rat :=
  (b.strangers 1 perm' (R.step.fromChildren b hb) (br_ge_one p) : Rat)

/-- Order-`r` parent-send outsider mass. -/
def StageRouting.fromParentRMass {p : ScheduleParams} {ip : InvariantParams}
    {d : Nat} {sched : LevelSchedule p d} {t : Nat}
    {pl : Placement p.br d}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    {pl' : Placement p.br d}
    {perm' : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (R : StageRouting p ip d sched t pl perm pl' perm')
    (b : KBag p.br d) (r : Nat) (_hr1 : 1 ≤ r) (_hrd : r ≤ d)
    (hb : 1 ≤ b.l) : Rat :=
  (b.strangers (r + 1) perm' (R.step.fromParent b hb) (br_ge_one p) : Rat)

/-- Order-`r` children-send outsider mass. -/
def StageRouting.fromChildrenRMass {p : ScheduleParams} {ip : InvariantParams}
    {d : Nat} {sched : LevelSchedule p d} {t : Nat}
    {pl : Placement p.br d}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    {pl' : Placement p.br d}
    {perm' : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (R : StageRouting p ip d sched t pl perm pl' perm')
    (b : KBag p.br d) (r : Nat) (_hr1 : 1 ≤ r) (_hrd : r ≤ d)
    (hb : 1 ≤ b.l) : Rat :=
  (b.strangers (r + 1) perm' (R.step.fromChildren b hb) (br_ge_one p) : Rat)

/-- `PlacementStep` discharges the stranger source-split; remaining fields come
    from `StageRouting` numeric bounds. -/
def stageDynamics_of_routing (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (R : StageRouting p ip d sched t pl perm pl' perm') :
    StageDynamics p ip d sched t pl perm pl' perm' where
  ht := R.ht
  counts := R.counts
  counts_wires := R.counts_wires
  counts_bad := R.counts_bad
  parentOut0 := R.parentOut0
  sibMass0 := R.sibMass0
  intrusion0 := R.intrusion0
  slack0 := R.slack0
  fromParent0 := fun b hb => R.fromParent0Mass b hb
  fromChildren0 := fun b hb => R.fromChildren0Mass b hb
  hParentOut0 := R.hParentOut0
  hSibMass0 := R.hSibMass0
  hIntrusion0 := R.hIntrusion0
  hSlack0 := R.hSlack0
  hFromParent0 := fun b hb => by
    simpa [StageRouting.fromParent0Mass] using R.hFromParent0 b hb
  hFromChildren0 := fun b hb => by
    simpa [StageRouting.fromChildren0Mass] using R.hFromChildren0 b hb
  hStrangers0 := fun b hb => by
    simpa [StageRouting.fromParent0Mass, StageRouting.fromChildren0Mass] using
      PlacementStep.strangers_split_le p d pl pl' R.step perm' b hb 1
  fromParentR := fun b r hr1 hrd hb => R.fromParentRMass b r hr1 hrd hb
  fromChildrenR := fun b r hr1 hrd hb => R.fromChildrenRMass b r hr1 hrd hb
  hFromParentR := fun b r hr1 hrd hb => by
    simpa [StageRouting.fromParentRMass] using R.hFromParentR b r hr1 hrd hb
  hFromChildrenR := fun b r hr1 hrd hb => by
    simpa [StageRouting.fromChildrenRMass] using R.hFromChildrenR b r hr1 hrd hb
  hStrangersR := fun b r hr1 hrd hb => by
    simpa [StageRouting.fromParentRMass, StageRouting.fromChildrenRMass] using
      PlacementStep.strangers_split_le p d pl pl' R.step perm' b hb (r + 1)
  level0 := R.level0

/-- One-step preservation under a placement step + routing bounds. -/
theorem outsiderBound_step_of_routing (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hconds : SeparatorConds p ip)
    (R : StageRouting p ip d sched t pl perm pl' perm')
    (hP : OutsiderBoundLe p ip d sched t pl perm) :
    OutsiderBoundLe p ip d sched (t + 1) pl' perm' :=
  outsiderBound_step_of_dynamics p ip d sched t pl pl' perm perm' hconds
    (stageDynamics_of_routing p ip d sched t pl pl' perm perm' R) hP

end Chvatal
