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

/-- Allocation budgets for order-0 send-ups (one child contributes at most
    `μδ/k² · c(parent)`). -/
structure ChildSendBudget0 (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (t : Nat) (pl pl' : Placement p.br d)
    (step : PlacementStep p d pl pl')
    (perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (cover : ChildSendCover p d pl pl' step) where
  hPerChild : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    ((b.strangers 1 perm' (cover.sendUp b hb hbd j) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta / (p.br : Rat) ^ 2 * capacity p d (b.l - 1) t

/-- Send-up carries at most a `1/(k² A²)` fraction of the child's order-1
    outsider mass (allocation / send-up size). -/
structure ChildSendAlloc (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl')
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (cover : ChildSendCover p d pl pl' step) where
  hFrac : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    ((b.strangers 1 perm' (cover.sendUp b hb hbd j) (br_ge_one p) : Rat)) ≤
      (1 / ((p.br : Rat) ^ 2 * p.A ^ 2)) *
        (((b.child j.val j.isLt hbd).strangers 2 perm
            (pl.regs (b.child j.val j.isLt hbd)) (br_ge_one p) : Rat))

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

theorem sendUp_empty_of_childRegs_empty {p : ScheduleParams} {d : Nat} {t : Nat}
    {pl pl' : Placement p.br d} {step : PlacementStep p d pl pl'}
    {cover : ChildSendCover p d pl pl' step}
    (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d) (j : Fin p.br)
    (h : (pl.regs (b.child j.val j.isLt hbd)).card = 0) :
    cover.sendUp b hb hbd j = ∅ := by
  have hempty : pl.regs (b.child j.val j.isLt hbd) = ∅ := Finset.card_eq_zero.mp h
  ext x
  constructor
  · intro hx
    have hxR := cover.hsubset b hb hbd j hx
    rw [hempty] at hxR
    exact hxR
  · intro hx; exact False.elim (notMem_empty x hx)

/-- Capacity budget discharges the `|sendUp| ≤ |regs|/Q` card bound. -/
def childSendCard_of_capBudget (p : ScheduleParams) (d : Nat) (t : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl')
    (cover : ChildSendCover p d pl pl' step)
    (bud : ChildSendCapBudget p d t pl pl' step cover) :
    ChildSendCard p d pl pl' step cover where
  hCardFrac := fun b hb hbd j => by
    have hs := bud.hSend b hb hbd j
    have hQ := (capacityRatio_pos p).le
    have hchild : (b.child j.val j.isLt hbd).l = b.l + 1 := rfl
    set child := b.child j.val j.isLt hbd
    by_cases h0 : (pl.regs child).card = 0
    · have hcard :
          ((cover.sendUp b hb hbd j).card : Rat) = 0 := by
        have hempty := sendUp_empty_of_childRegs_empty (t := t) (cover := cover) (b := b)
          (hb := hb) (hbd := hbd) (j := j) h0
        simp [hempty]
      rw [hcard, h0]
      simp
    · have hpos : 0 < (pl.regs child).card := Nat.pos_of_ne_zero h0
      have hr := bud.hRegs b hb hbd j hpos
      have hs' : ((cover.sendUp b hb hbd j).card : Rat) ≤
          capacity p d (b.l + 1) t / capacityRatio p := by
        simpa [sendUpBudget, hchild] using hs
      calc ((cover.sendUp b hb hbd j).card : Rat)
          ≤ capacity p d (b.l + 1) t / capacityRatio p := hs'
        _ ≤ ((pl.regs child).card : Rat) / capacityRatio p :=
            div_le_div_of_nonneg_right hr hQ

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

/-- Card + fair density discharge `ChildSendSize`. -/
def childSendSize_of_card_fair (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl')
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (cover : ChildSendCover p d pl pl' step)
    (card : ChildSendCard p d pl pl' step cover)
    (fair : ChildSendFair p d pl pl' step perm perm' cover) :
    ChildSendSize p d pl pl' step perm perm' cover where
  hCardFrac := fun b hb hbd j => by
    simpa [capacityRatio, mul_comm] using card.hCardFrac b hb hbd j
  hDensity := fun b hb hbd j => by
    have hbr := br_ge_one p
    have hsame := fair.hSame b hb hbd j
    have hperm := fair.hPermLe b hb hbd j
    have hpermR :
        (((b.child j.val j.isLt hbd).strangers 2 perm'
            (cover.sendUp b hb hbd j) hbr : Rat)) ≤
          (((b.child j.val j.isLt hbd).strangers 2 perm
              (cover.sendUp b hb hbd j) hbr : Rat)) := by
      exact_mod_cast hperm
    have hnn : (0 : Rat) ≤
        ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) :=
      Nat.cast_nonneg _
    calc (((b.child j.val j.isLt hbd).strangers 2 perm'
            (cover.sendUp b hb hbd j) hbr : Rat)) *
            ((pl.regs (b.child j.val j.isLt hbd)).card : Rat)
        ≤ (((b.child j.val j.isLt hbd).strangers 2 perm
              (cover.sendUp b hb hbd j) hbr : Rat)) *
            ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) :=
          mul_le_mul_of_nonneg_right hpermR hnn
      _ ≤ (((b.child j.val j.isLt hbd).strangers 2 perm
              (pl.regs (b.child j.val j.isLt hbd)) hbr : Rat)) *
            ((cover.sendUp b hb hbd j).card : Rat) := hsame

/-- `ChildSendSize` discharges the allocation-fraction form of `ChildSendAlloc`. -/
def childSendAlloc_of_size (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl')
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (cover : ChildSendCover p d pl pl' step)
    (sz : ChildSendSize p d pl pl' step perm perm' cover) :
    ChildSendAlloc p d pl pl' step perm perm' cover where
  hFrac := fun b hb hbd j => by
    have hbr := br_ge_one p
    by_cases hR : (pl.regs (b.child j.val j.isLt hbd)).card = 0
    · have hsub := cover.hsubset b hb hbd j
      have hS0 : (cover.sendUp b hb hbd j).card = 0 := by
        have := card_le_card hsub
        omega
      rw [card_eq_zero.mp hS0, KBag.strangers_empty, Nat.cast_zero]
      exact mul_nonneg
        (div_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
        (Nat.cast_nonneg _)
    · have heq :=
        strangers_child_eq p d b hbd 1 (by omega) j perm'
          (cover.sendUp b hb hbd j) hbr
      have hcard := sz.hCardFrac b hb hbd j
      have hden := sz.hDensity b hb hbd j
      set child := b.child j.val j.isLt hbd with hchild
      set S := cover.sendUp b hb hbd j with hS
      set R := pl.regs child with hRset
      have hRpos : (0 : Rat) < (R.card : Rat) := by
        exact_mod_cast (Nat.pos_of_ne_zero (by simpa [hRset, hchild] using hR))
      have hstrS :
          (b.strangers 1 perm' (cover.sendUp b hb hbd j) hbr : Rat) *
              ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) ≤
            (((b.child j.val j.isLt hbd).strangers 2 perm
                (pl.regs (b.child j.val j.isLt hbd)) hbr : Rat)) *
              ((cover.sendUp b hb hbd j).card : Rat) := by
        have hL :
            (b.strangers 1 perm' (cover.sendUp b hb hbd j) hbr : Rat) =
              ((b.child j.val j.isLt hbd).strangers 2 perm'
                  (cover.sendUp b hb hbd j) hbr : Rat) := by
          exact_mod_cast heq
        rw [hL]
        simpa using hden
      have hdiv :
          (b.strangers 1 perm' (cover.sendUp b hb hbd j) hbr : Rat) ≤
            (((b.child j.val j.isLt hbd).strangers 2 perm
                (pl.regs (b.child j.val j.isLt hbd)) hbr : Rat)) *
              ((cover.sendUp b hb hbd j).card : Rat) /
              ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) :=
        (le_div_iff₀ hRpos).mpr (by
          simpa [hS, hRset, hchild] using hstrS)
      have hratio :
          ((cover.sendUp b hb hbd j).card : Rat) /
              ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) ≤
            1 / ((p.br : Rat) ^ 2 * p.A ^ 2) := by
        have hne : ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) ≠ 0 :=
          ne_of_gt hRpos
        calc ((cover.sendUp b hb hbd j).card : Rat) /
                ((pl.regs (b.child j.val j.isLt hbd)).card : Rat)
            ≤ (((pl.regs (b.child j.val j.isLt hbd)).card : Rat) /
                  ((p.br : Rat) ^ 2 * p.A ^ 2)) /
                ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) :=
              div_le_div_of_nonneg_right hcard (le_of_lt hRpos)
          _ = ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) *
                (1 / ((p.br : Rat) ^ 2 * p.A ^ 2)) *
                (1 / ((pl.regs (b.child j.val j.isLt hbd)).card : Rat)) := by
              ring
          _ = 1 / ((p.br : Rat) ^ 2 * p.A ^ 2) := by
              field_simp [hne]
      have hmul :
          (((b.child j.val j.isLt hbd).strangers 2 perm
                (pl.regs (b.child j.val j.isLt hbd)) hbr : Rat)) *
              ((cover.sendUp b hb hbd j).card : Rat) /
              ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) ≤
            (((b.child j.val j.isLt hbd).strangers 2 perm
                (pl.regs (b.child j.val j.isLt hbd)) hbr : Rat)) *
              (1 / ((p.br : Rat) ^ 2 * p.A ^ 2)) := by
        have hnn : (0 : Rat) ≤
            (((b.child j.val j.isLt hbd).strangers 2 perm
                (pl.regs (b.child j.val j.isLt hbd)) hbr : Rat)) :=
          Nat.cast_nonneg _
        calc _
            = (((b.child j.val j.isLt hbd).strangers 2 perm
                  (pl.regs (b.child j.val j.isLt hbd)) hbr : Rat)) *
                (((cover.sendUp b hb hbd j).card : Rat) /
                  ((pl.regs (b.child j.val j.isLt hbd)).card : Rat)) := by
                ring
          _ ≤ (((b.child j.val j.isLt hbd).strangers 2 perm
                  (pl.regs (b.child j.val j.isLt hbd)) hbr : Rat)) *
                (1 / ((p.br : Rat) ^ 2 * p.A ^ 2)) :=
              mul_le_mul_of_nonneg_left hratio hnn
      exact (hdiv.trans hmul).trans (le_of_eq (mul_comm _ _))

/-- `ChildSendAlloc` + `P` discharges the order-0 per-child budget. -/
def childSendBudget0_of_alloc (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (step : PlacementStep p d pl pl')
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hP : OutsiderBoundLe p ip d sched t pl perm)
    (cover : ChildSendCover p d pl pl' step)
    (alloc : ChildSendAlloc p d pl pl' step perm perm' cover) :
    ChildSendBudget0 p ip d t pl pl' step perm' cover where
  hPerChild := fun b hb hbd j => by
    have hbr := br_ge_one p
    have hfrac := alloc.hFrac b hb hbd j
    have hPch := hP (b.child j.val j.isLt hbd) 1 (by omega)
    have hcl : (b.child j.val j.isLt hbd).l = b.l + 1 := rfl
    have hPch' :
        (((b.child j.val j.isLt hbd).strangers 2 perm
            (pl.regs (b.child j.val j.isLt hbd)) hbr : Rat)) ≤
          ip.mu * ip.delta * capacity p d (b.l + 1) t := by
      simpa [hcl, pow_one] using hPch
    have hcap1 : capacity p d (b.l + 1) t = p.A * capacity p d b.l t :=
      capacity_succ_level p d b.l t
    have hcap0 : capacity p d b.l t = p.A * capacity p d (b.l - 1) t := by
      rw [show b.l = (b.l - 1) + 1 by omega]
      exact capacity_succ_level p d (b.l - 1) t
    have hden : (0 : Rat) ≤ 1 / ((p.br : Rat) ^ 2 * p.A ^ 2) :=
      div_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hscale :
        (1 / ((p.br : Rat) ^ 2 * p.A ^ 2)) *
            (ip.mu * ip.delta * capacity p d (b.l + 1) t) =
          ip.mu * ip.delta / (p.br : Rat) ^ 2 * capacity p d (b.l - 1) t := by
      have hk : (p.br : Rat) ≠ 0 := ne_of_gt p.br_cast_pos
      have hA : p.A ≠ 0 := ne_of_gt p.A_pos
      rw [hcap1, hcap0]
      field_simp [hk, hA, pow_two]
    calc ((b.strangers 1 perm' (cover.sendUp b hb hbd j) hbr : Rat))
        ≤ (1 / ((p.br : Rat) ^ 2 * p.A ^ 2)) *
            (((b.child j.val j.isLt hbd).strangers 2 perm
                (pl.regs (b.child j.val j.isLt hbd)) hbr : Rat)) := hfrac
      _ ≤ (1 / ((p.br : Rat) ^ 2 * p.A ^ 2)) *
            (ip.mu * ip.delta * capacity p d (b.l + 1) t) :=
          mul_le_mul_of_nonneg_left hPch' hden
      _ = ip.mu * ip.delta / (p.br : Rat) ^ 2 * capacity p d (b.l - 1) t :=
          hscale

theorem fromChildren0_of_cover (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (t : Nat) (pl pl' : Placement p.br d)
    (step : PlacementStep p d pl pl')
    (perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (cover : ChildSendCover p d pl pl' step)
    (bud : ChildSendBudget0 p ip d t pl pl' step perm' cover)
    (b : KBag p.br d) (hb : 1 ≤ b.l) :
    ((b.strangers 1 perm' (step.fromChildren b hb) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta / (p.br : Rat) * capacity p d (b.l - 1) t := by
  have hbr := br_ge_one p
  by_cases hbd : b.l < d
  · have hmono :=
      b.strangers_mono 1 perm' (cover.hcover b hb hbd) hbr
    have hunion :=
      strangers_biUnion_le p d b 1 perm'
        (fun j => cover.sendUp b hb hbd j)
    have hnat :
        b.strangers 1 perm' (step.fromChildren b hb) hbr ≤
          ∑ j : Fin p.br,
            b.strangers 1 perm' (cover.sendUp b hb hbd j) hbr :=
      Nat.le_trans hmono hunion
    have hsum :
        (∑ j : Fin p.br,
            (b.strangers 1 perm' (cover.sendUp b hb hbd j) hbr : Rat)) ≤
          ∑ _j : Fin p.br,
            ip.mu * ip.delta / (p.br : Rat) ^ 2 *
              capacity p d (b.l - 1) t := by
      refine sum_le_sum ?_
      intro j _
      exact bud.hPerChild b hb hbd j
    have hcard :
        (∑ _j : Fin p.br,
            ip.mu * ip.delta / (p.br : Rat) ^ 2 *
              capacity p d (b.l - 1) t) =
          (p.br : Rat) *
            (ip.mu * ip.delta / (p.br : Rat) ^ 2 *
              capacity p d (b.l - 1) t) := by
      simp [sum_const]
    have hscale :
        (p.br : Rat) *
            (ip.mu * ip.delta / (p.br : Rat) ^ 2 *
              capacity p d (b.l - 1) t) =
          ip.mu * ip.delta / (p.br : Rat) * capacity p d (b.l - 1) t := by
      have hk : (p.br : Rat) ≠ 0 := ne_of_gt p.br_cast_pos
      field_simp [hk, pow_two]
    have hcast :
        (b.strangers 1 perm' (step.fromChildren b hb) hbr : Rat) ≤
          ∑ j : Fin p.br,
            (b.strangers 1 perm' (cover.sendUp b hb hbd j) hbr : Rat) := by
      exact_mod_cast hnat
    calc (b.strangers 1 perm' (step.fromChildren b hb) hbr : Rat)
        ≤ ∑ j : Fin p.br,
            (b.strangers 1 perm' (cover.sendUp b hb hbd j) hbr : Rat) := hcast
      _ ≤ ∑ _j : Fin p.br,
            ip.mu * ip.delta / (p.br : Rat) ^ 2 *
              capacity p d (b.l - 1) t := hsum
      _ = (p.br : Rat) *
            (ip.mu * ip.delta / (p.br : Rat) ^ 2 *
              capacity p d (b.l - 1) t) := hcard
      _ = ip.mu * ip.delta / (p.br : Rat) * capacity p d (b.l - 1) t := hscale
  · have hleaf : b.l = d := Nat.le_antisymm b.hl (Nat.not_lt.mp hbd)
    have hemp := cover.hempty b hb hleaf
    rw [hemp, KBag.strangers_empty, Nat.cast_zero]
    exact mul_nonneg
      (div_nonneg (mul_nonneg ip.mu_nonneg ip.delta_nonneg) p.br_cast_pos.le)
      (capacity_pos p d (b.l - 1) t).le

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

/-- Same-permutation send-up: bridge collapses to `strangers_mono` on the
    subset `sendUp ⊆ child.regs`. -/
def childSendBridge_of_same_perm (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl')
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (cover : ChildSendCover p d pl pl' step) :
    ChildSendBridge p d pl pl' step perm perm cover where
  hLe := fun b hb hbd j ord => by
    have hbr := br_ge_one p
    have hsub := cover.hsubset b hb hbd j
    exact_mod_cast
      ((b.child j.val j.isLt hbd).strangers_mono ord perm hsub hbr)

/-- Same-permutation fair package: density remains an obligation; perm-mono is
    reflexive. -/
def childSendFair_of_same_perm (p : ScheduleParams) (d : Nat)
    (pl pl' : Placement p.br d) (step : PlacementStep p d pl pl')
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (cover : ChildSendCover p d pl pl' step)
    (hSame : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
        (j : Fin p.br),
      (((b.child j.val j.isLt hbd).strangers 2 perm
          (cover.sendUp b hb hbd j) (br_ge_one p) : Rat)) *
          ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) ≤
        (((b.child j.val j.isLt hbd).strangers 2 perm
            (pl.regs (b.child j.val j.isLt hbd)) (br_ge_one p) : Rat)) *
          ((cover.sendUp b hb hbd j).card : Rat)) :
    ChildSendFair p d pl pl' step perm perm cover where
  hSame := hSame
  hPermLe := fun _b _hb _hbd _j => le_rfl

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

theorem fromChildrenR_of_cover (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (step : PlacementStep p d pl pl')
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hP : OutsiderBoundLe p ip d sched t pl perm)
    (cover : ChildSendCover p d pl pl' step)
    (bridge : ChildSendBridge p d pl pl' step perm perm' cover)
    (b : KBag p.br d) (hb : 1 ≤ b.l)
    (r : Nat) (hr1 : 1 ≤ r) (hrd : r + 1 ≤ d) :
    ((b.strangers (r + 1) perm' (step.fromChildren b hb) (br_ge_one p) : Rat)) ≤
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (r - 1) *
          (p.A * p.nu * capacity p d (b.l - 1) t)) := by
  have hbr := br_ge_one p
  by_cases hbd : b.l < d
  · have hj : 1 ≤ r + 1 := by omega
    have hmono :=
      b.strangers_mono (r + 1) perm' (cover.hcover b hb hbd) hbr
    have hunion :=
      strangers_biUnion_le p d b (r + 1) perm'
        (fun j => cover.sendUp b hb hbd j)
    have hnat :
        b.strangers (r + 1) perm' (step.fromChildren b hb) hbr ≤
          ∑ j : Fin p.br,
            b.strangers (r + 1) perm' (cover.sendUp b hb hbd j) hbr :=
      Nat.le_trans hmono hunion
    have hterm : ∀ (j : Fin p.br),
        (b.strangers (r + 1) perm' (cover.sendUp b hb hbd j) hbr : Rat) ≤
          ip.mu * ip.delta ^ (r + 1) *
            capacity p d (b.l + 1) t := by
      intro j
      have heq :=
        strangers_child_eq p d b hbd (r + 1) hj j perm'
          (cover.sendUp b hb hbd j) hbr
      have hbridge := bridge.hLe b hb hbd j (r + 2)
      have hPch := hP (b.child j.val j.isLt hbd) (r + 1) hrd
      have hcl : (b.child j.val j.isLt hbd).l = b.l + 1 := rfl
      have hPch' :
          (((b.child j.val j.isLt hbd).strangers (r + 2) perm
              (pl.regs (b.child j.val j.isLt hbd)) hbr : Rat)) ≤
            ip.mu * ip.delta ^ (r + 1) * capacity p d (b.l + 1) t := by
        simpa [hcl] using hPch
      calc (b.strangers (r + 1) perm' (cover.sendUp b hb hbd j) hbr : Rat)
          = ((b.child j.val j.isLt hbd).strangers (r + 2) perm'
              (cover.sendUp b hb hbd j) hbr : Rat) := by
                exact_mod_cast heq
        _ ≤ ((b.child j.val j.isLt hbd).strangers (r + 2) perm
              (pl.regs (b.child j.val j.isLt hbd)) hbr : Rat) := hbridge
        _ ≤ ip.mu * ip.delta ^ (r + 1) * capacity p d (b.l + 1) t := hPch'
    have hsum :
        (∑ j : Fin p.br,
            (b.strangers (r + 1) perm' (cover.sendUp b hb hbd j) hbr : Rat)) ≤
          ∑ _j : Fin p.br,
            ip.mu * ip.delta ^ (r + 1) * capacity p d (b.l + 1) t := by
      refine sum_le_sum ?_
      intro j _
      exact hterm j
    have hcard :
        (∑ _j : Fin p.br,
            ip.mu * ip.delta ^ (r + 1) * capacity p d (b.l + 1) t) =
          (p.br : Rat) *
            (ip.mu * ip.delta ^ (r + 1) * capacity p d (b.l + 1) t) := by
      simp [sum_const]
    have hcap1 : capacity p d (b.l + 1) t = p.A * capacity p d b.l t :=
      capacity_succ_level p d b.l t
    have hcap0 : capacity p d b.l t = p.A * capacity p d (b.l - 1) t := by
      rw [show b.l = (b.l - 1) + 1 by omega]
      exact capacity_succ_level p d (b.l - 1) t
    have hcast :
        (b.strangers (r + 1) perm' (step.fromChildren b hb) hbr : Rat) ≤
          ∑ j : Fin p.br,
            (b.strangers (r + 1) perm' (cover.sendUp b hb hbd j) hbr : Rat) := by
      exact_mod_cast hnat
    calc (b.strangers (r + 1) perm' (step.fromChildren b hb) hbr : Rat)
        ≤ ∑ j : Fin p.br,
            (b.strangers (r + 1) perm' (cover.sendUp b hb hbd j) hbr : Rat) :=
          hcast
      _ ≤ ∑ _j : Fin p.br,
            ip.mu * ip.delta ^ (r + 1) * capacity p d (b.l + 1) t := hsum
      _ = (p.br : Rat) *
            (ip.mu * ip.delta ^ (r + 1) * capacity p d (b.l + 1) t) := hcard
      _ = (p.br : Rat) *
            (ip.mu * ip.delta ^ (r + 1) *
              (p.A * (p.A * capacity p d (b.l - 1) t))) := by
            rw [hcap1, hcap0]
      _ = ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
            (ip.mu * ip.delta ^ (r - 1) *
              (p.A * p.nu * capacity p d (b.l - 1) t)) :=
            childrenR_scale p ip (capacity p d (b.l - 1) t) r hr1
  · have hleaf : b.l = d := Nat.le_antisymm b.hl (Nat.not_lt.mp hbd)
    have hemp := cover.hempty b hb hleaf
    rw [hemp, KBag.strangers_empty, Nat.cast_zero]
    refine mul_nonneg ?_ ?_
    · exact div_nonneg
        (mul_nonneg (mul_nonneg (pow_nonneg ip.delta_nonneg 2) p.A_pos.le)
          p.br_cast_pos.le)
        p.hnu_pos.le
    · exact mul_nonneg
        (mul_nonneg ip.mu_nonneg (pow_nonneg ip.delta_nonneg _))
        (mul_nonneg (mul_nonneg p.A_pos.le p.hnu_pos.le)
          (capacity_pos p d (b.l - 1) t).le)

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

/-- Fill `StageKernel` children-send fields from support + card + fair density. -/
def StageKernel.ofChildSend (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hP : OutsiderBoundLe p ip d sched t pl perm)
    (K : StageKernelWithChildren p ip d sched t pl perm pl' perm') :
    StageKernel p ip d sched t pl perm pl' perm' :=
  let cover := childSendCover_of_support p d pl pl' K.step K.support
  let size :=
    childSendSize_of_card_fair p d pl pl' K.step perm perm' cover K.card K.fair
  let alloc := childSendAlloc_of_size p d pl pl' K.step perm perm' cover size
  let bud :=
    childSendBudget0_of_alloc p ip d sched t pl pl' K.step perm perm' hP
      cover alloc
  { ht := K.ht
    step := K.step
    counts := K.counts
    counts_wires := K.counts_wires
    counts_bad := K.counts_bad
    parentSep := K.parentSep
    ha_le_cap := K.ha_le_cap
    slack0 := K.slack0
    hSlack0 := K.hSlack0
    hBadSend0 := K.hBadSend0
    hFringeSend := K.hFringeSend
    hFromChildren0 := fun b hb =>
      fromChildren0_of_cover p ip d t pl pl' K.step perm' cover bud b hb
    hFromChildrenR := fun b r hr1 hrd hb => by
      by_cases h : r + 1 ≤ d
      · exact fromChildrenR_of_cover p ip d sched t pl pl' K.step perm perm' hP
          cover K.bridge b hb r hr1 h
      · have hr : r = d := by omega
        subst hr
        exact K.hFromChildrenR_top b hb
    level0 := K.level0 }

theorem outsiderBound_step_of_childSend (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hconds : SeparatorConds p ip)
    (hP : OutsiderBoundLe p ip d sched t pl perm)
    (K : StageKernelWithChildren p ip d sched t pl perm pl' perm') :
    OutsiderBoundLe p ip d sched (t + 1) pl' perm' :=
  outsiderBound_step_of_kernel p ip d sched t pl pl' perm perm' hconds hP
    (StageKernel.ofChildSend p ip d sched t pl pl' perm perm' hP K)

end Chvatal
