module
/-
  # Chvatal §4 children-send cover

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §4 (Lemmas 4.3–4.4 children terms).

  Status: covers `fromChildren` by per-child send-ups. The concrete cover is
  `fromChildren ∩ child.regs`. Order-0 size bounds discharge from schedule card
  (`|sendUp| ≤ |regs|/Q`) plus fair density / perm-mono, then `P`. Order-`r`
  with `r+1 ≤ d` discharges from `OutsiderBoundLe` + bridge. The top order
  `r = d` remains a one-line residual. Leaf bags (`l = d`) send nothing.
-/

public import AKS.Chvatal.StageKernel
public import AKS.Chvatal.SendSchedule
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Chvatal

open Finset

/-! **Child send-up cover** -/

/-- `fromChildren` is covered by send-up Finsets from each child; leaf bags
    contribute the empty set. -/
structure ChildSendCover (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl') where
  sendUp : ∀ (b : KBag p.br d) (_hb : 1 ≤ b.l) (_hbd : b.l < d)
      (_j : Fin p.br), Finset (Fin (p.br ^ d))
  hsubset : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    sendUp b hb hbd j ⊆ pl.regs (b.child j.val j.isLt hbd)
  hcover : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d),
    step.fromChildren b hb ⊆
      (univ : Finset (Fin p.br)).biUnion (fun j => sendUp b hb hbd j)
  hempty : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l), b.l = d →
    step.fromChildren b hb = ∅

/-- Placement support for the concrete send-up `fromChildren ∩ child.regs`. -/
structure ChildSendSupport (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl') where
  hsupport : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d),
    step.fromChildren b hb ⊆
      (univ : Finset (Fin p.br)).biUnion
        (fun j => pl.regs (b.child j.val j.isLt hbd))
  hempty : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l), b.l = d →
    step.fromChildren b hb = ∅

/-- Build the child-send cover by intersecting `fromChildren` with each child
    register set. -/
def childSendCover_of_support (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl')
    (sup : ChildSendSupport p d pl pl' step) :
    ChildSendCover p d pl pl' step where
  sendUp := fun b hb hbd j =>
    step.fromChildren b hb ∩ pl.regs (b.child j.val j.isLt hbd)
  hsubset := fun b hb hbd j => inter_subset_right
  hcover := fun b hb hbd => by
    intro x hx
    have hxsup := sup.hsupport b hb hbd hx
    rcases mem_biUnion.mp hxsup with ⟨j, hj, hxj⟩
    exact mem_biUnion.mpr ⟨j, hj, mem_inter.mpr ⟨hx, hxj⟩⟩
  hempty := sup.hempty

/-- Stranger count on a `biUnion` is at most the sum of the counts. -/
theorem strangers_biUnion_le (p : ScheduleParams) (d : Nat)
    (b : KBag p.br d) (j : Nat)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (f : Fin p.br → Finset (Fin (p.br ^ d))) :
    (b.strangers j perm ((univ : Finset (Fin p.br)).biUnion f) (br_ge_one p) :
        Nat) ≤
      ∑ i : Fin p.br, b.strangers j perm (f i) (br_ge_one p) := by
  classical
  simp only [KBag.strangers, filter_biUnion]
  exact card_biUnion_le

/-- On any set, order-`j` outsiders at a parent equal order-`(j+1)` at a child. -/
theorem strangers_child_eq (p : ScheduleParams) (d : Nat)
    (b : KBag p.br d) (hbd : b.l < d) (j : Nat) (hj : 1 ≤ j)
    (childIdx : Fin p.br)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (S : Finset (Fin (p.br ^ d)))
    (hbr : 1 ≤ p.br := br_ge_one p) :
    b.strangers j perm S hbr =
      (b.child childIdx.val childIdx.isLt hbd).strangers (j + 1) perm S hbr := by
  have hcl : 1 ≤ (b.child childIdx.val childIdx.isLt hbd).l := by
    change 1 ≤ b.l + 1
    omega
  have h :=
    KBag.strangers_parent_eq (b.child childIdx.val childIdx.isLt hbd) j hj hcl
      perm S hbr
  rw [KBag.child_parent b childIdx.val childIdx.isLt hbd hbr] at h
  exact h

/-! **Order-0 per-child budget** -/



/-- Send-up size is at most a `1/(k² A²)` fraction of the child bag, and
    outsider density on the send-up is at most that of the full child bag. -/
structure ChildSendSize (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl')
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (cover : ChildSendCover p d pl pl' step) where
  hCardFrac : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    ((cover.sendUp b hb hbd j).card : Rat) ≤
      ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) /
        ((p.br : Rat) ^ 2 * p.A ^ 2)
  /-- `strangers(sendUp) · |regs| ≤ strangers(regs) · |sendUp|` under the
      child order-1 indexing (`Strange 2`). -/
  hDensity : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    (((b.child j.val j.isLt hbd).strangers 2 perm'
        (cover.sendUp b hb hbd j) (br_ge_one p) : Rat)) *
        ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) ≤
      (((b.child j.val j.isLt hbd).strangers 2 perm
          (pl.regs (b.child j.val j.isLt hbd)) (br_ge_one p) : Rat)) *
        ((cover.sendUp b hb hbd j).card : Rat)

/-- Schedule card bound: send-up is at most a `1/Q` fraction of the child bag
    (`Q = capacityRatio = A² k²`). -/
structure ChildSendCard (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl')
    (cover : ChildSendCover p d pl pl' step) where
  hCardFrac : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    ((cover.sendUp b hb hbd j).card : Rat) ≤
      ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) / capacityRatio p

/-- Capacity-normalized send-up budget: `|sendUp| ≤ c/Q` and `c ≤ |regs|`. -/
structure ChildSendCapBudget (p : ScheduleParams) (d : Nat) (t : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl')
    (cover : ChildSendCover p d pl pl' step) where
  hSend : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    ((cover.sendUp b hb hbd j).card : Rat) ≤
      sendUpBudget p d (b.l + 1) t
  hRegs : ∀ (b : KBag p.br d) (_hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    0 < (pl.regs (b.child j.val j.isLt hbd)).card →
      capacity p d (b.l + 1) t ≤
        ((pl.regs (b.child j.val j.isLt hbd)).card : Rat)



/-- Fair send-up density under the pre-stage permutation, plus a one-step
    stranger mono bound from `perm` to `perm'` on the send-up. -/
structure ChildSendFair (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl')
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (cover : ChildSendCover p d pl pl' step) where
  hSame : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    (((b.child j.val j.isLt hbd).strangers 2 perm
        (cover.sendUp b hb hbd j) (br_ge_one p) : Rat)) *
        ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) ≤
      (((b.child j.val j.isLt hbd).strangers 2 perm
          (pl.regs (b.child j.val j.isLt hbd)) (br_ge_one p) : Rat)) *
        ((cover.sendUp b hb hbd j).card : Rat)
  hPermLe : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    (((b.child j.val j.isLt hbd).strangers 2 perm'
        (cover.sendUp b hb hbd j) (br_ge_one p) : Nat)) ≤
      ((b.child j.val j.isLt hbd).strangers 2 perm
        (cover.sendUp b hb hbd j) (br_ge_one p) : Nat)





/-! **Order-`r` from P** -/

/-- Bridge: send-up stranger mass under `perm'` is ≤ the child's `P`-mass under
    `perm` on its full register set. -/
structure ChildSendBridge (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl')
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (cover : ChildSendCover p d pl pl' step) where
  hLe : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br) (ord : Nat),
    (((b.child j.val j.isLt hbd).strangers ord perm'
        (cover.sendUp b hb hbd j) (br_ge_one p) : Rat)) ≤
      (((b.child j.val j.isLt hbd).strangers ord perm
          (pl.regs (b.child j.val j.isLt hbd)) (br_ge_one p) : Rat))



/-- Scale `k · μ · δ^{r+1} · A² · c` into the StageKernel children-send form. -/
theorem childrenR_scale (p : ScheduleParams) (ip : InvariantParams)
    (c : Rat) (r : Nat) (hr1 : 1 ≤ r) :
    (p.br : Rat) * (ip.mu * ip.delta ^ (r + 1) * (p.A * (p.A * c))) =
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) * (p.A * p.nu * c)) := by
  have hnu : p.nu ≠ 0 := ne_of_gt p.hnu_pos
  have hpow : ip.delta ^ (r + 1) = ip.delta ^ 2 * ip.delta ^ (r - 1) := by
    have : r + 1 = 2 + (r - 1) := by omega
    rw [this, pow_add]
  rw [hpow]
  field_simp [hnu]


/-! **Assemble into StageKernel** -/

/-- `StageKernel` with children-send fields replaced by placement support,
    schedule card, fair density, and bridge. The top order `r = d` is still an
    explicit residual. -/
structure StageKernelWithChildren (p : ScheduleParams) (ip : InvariantParams)
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
  parentSep : ∀ (b : KBag p.br d), 1 ≤ b.l → LocalSeparatorQuality ip
  ha_le_cap : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    (parentSep b hb).a ≤ capacity p d (b.l - 1) t
  slack0 : ∀ (b : KBag p.br d), 1 ≤ b.l → Rat
  hSlack0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    slack0 b hb ≤ slackCoeff p * capacity p d (b.l - 1) t
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
  support : ChildSendSupport p d pl pl' step
  card : ChildSendCard p d pl pl' step
    (childSendCover_of_support p d pl pl' step support)
  fair : ChildSendFair p d pl pl' step perm perm'
    (childSendCover_of_support p d pl pl' step support)
  bridge : ChildSendBridge p d pl pl' step perm perm'
    (childSendCover_of_support p d pl pl' step support)
  /-- Residual children-send bound at the maximum order `r = d`. -/
  hFromChildrenR_top : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    ((b.strangers (d + 1) perm' (step.fromChildren b hb) (br_ge_one p) : Rat)) ≤
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (d - 1) *
          (p.A * p.nu * capacity p d (b.l - 1) t))
  level0 : ∀ (b : KBag p.br d) (r : Nat), b.l = 0 → r ≤ d →
    ((b.strangers (r + 1) perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta ^ r * capacity p d 0 (t + 1)



end Chvatal
