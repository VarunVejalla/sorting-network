module
/-
  # Chvatal abstract schedule-sized child send-ups

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §3–4.

  Status: thin placement layer. Packages schedule-sized per-child send-ups
  (`|sendUp| ≤ ⌊c/Q⌋₊`, `|regs| ≥ c`) with fair stranger density, and
  discharges `ChildSendSupport`, `ChildSendCapBudget`, same-perm
  `ChildSendFair`, and `ChildSendBridge`. Builds a real `PlacementStep` with
  `preferNon` `fromChildren`, equates the support cover to the abstract cover,
  and assembles `StageKernelWithChildren` children fields (level-0 / top-order
  discharged on root init). Parent-send residue is
  `AbstractParentResidue` / `AbstractParentResidueRouting` (Thm 5.1).
-/

public import AKS.Chvatal.ChildSend
public import AKS.Chvatal.StageCountsFill
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace Chvatal

open Finset

/-! **Density for goods-first subsets** -/

/-- If `S ⊆ R` either avoids `P` or contains every non-`P` element of `R`, then
    `|S ∩ P| · |R| ≤ |R ∩ P| · |S|`. -/
theorem density_of_goods_first {α : Type*} [DecidableEq α]
    (R S : Finset α) (P : α → Prop) [DecidablePred P]
    (hsub : S ⊆ R)
    (hfirst :
      (S.filter P).card = 0 ∨
        R.filter (fun x => ¬ P x) ⊆ S) :
    ((S.filter P).card : Rat) * (R.card : Rat) ≤
      ((R.filter P).card : Rat) * (S.card : Rat) := by
  classical
  set G := R.filter (fun x => ¬ P x)
  set B := R.filter P
  cases hfirst with
  | inl h0 =>
    simp [h0]
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  | inr hGsub =>
    have hSleR : S.card ≤ R.card := card_le_card hsub
    have hGleS : G.card ≤ S.card := card_le_card hGsub
    have hGB : G.card + B.card = R.card := by
      simpa [G, B, add_comm] using
        (Finset.card_filter_add_card_filter_not (s := R) (p := P))
    have hunion : S = G ∪ (S.filter P) := by
      ext x
      constructor
      · intro hx
        by_cases hP : P x
        · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hx, hP⟩))
        · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hsub hx, hP⟩))
      · intro hx
        exact (mem_union.mp hx).elim (fun hxG => hGsub hxG) (fun hxP =>
          (mem_filter.mp hxP).1)
    have hdis : Disjoint G (S.filter P) :=
      disjoint_left.mpr fun x hxG hxS =>
        (mem_filter.mp hxG).2 (mem_filter.mp hxS).2
    have hSfilter : (S.filter P).card = S.card - G.card := by
      have hcu := card_union_of_disjoint hdis
      rw [← hunion] at hcu
      omega
    -- (|S| - |G|) * |R| ≤ |B| * |S|  ⇔  |S| * |G| ≤ |G| * |R|
    -- since |G| = |R| - |B|.
    have hKey :
        ((S.card : Rat) - (G.card : Rat)) * (R.card : Rat) ≤
          (B.card : Rat) * (S.card : Rat) := by
      have hGeq : (G.card : Rat) = (R.card : Rat) - (B.card : Rat) := by
        have hsum : (G.card : Rat) + (B.card : Rat) = (R.card : Rat) := by
          exact_mod_cast hGB
        linarith
      have hSR : (S.card : Rat) ≤ (R.card : Rat) := by exact_mod_cast hSleR
      have hGnn : (0 : Rat) ≤ (G.card : Rat) := Nat.cast_nonneg _
      -- |S|*(|R|-|B|) ≤ |G|*|R|  because |R|-|B| = |G| and |S| ≤ |R|
      have hmul :
          (S.card : Rat) * (G.card : Rat) ≤ (G.card : Rat) * (R.card : Rat) := by
        simpa [mul_comm (G.card : Rat) (S.card : Rat)] using
          mul_le_mul_of_nonneg_left hSR hGnn
      have hrew :
          (S.card : Rat) * (R.card : Rat) - (B.card : Rat) * (S.card : Rat) ≤
            (G.card : Rat) * (R.card : Rat) := by
        have :
            (S.card : Rat) * ((R.card : Rat) - (B.card : Rat)) ≤
              (G.card : Rat) * (R.card : Rat) := by
          simpa [hGeq] using hmul
        convert this using 1
        ring
      linarith
    have hSf : ((S.filter P).card : Rat) = (S.card : Rat) - (G.card : Rat) := by
      exact_mod_cast hSfilter
    simpa [hSf] using hKey
/-! **Greedy non-stranger prefix** -/

/-- Take up to `n` elements of `R`, preferring those that fail `P`. -/
def preferNon {N : Nat} (R : Finset (Fin N)) (P : Fin N → Prop)
    [DecidablePred P] (n : Nat) : Finset (Fin N) :=
  let m := min n R.card
  let goods := (R.filter (fun x => ¬ P x)).sort (· ≤ ·)
  let bads := (R.filter P).sort (· ≤ ·)
  ((goods ++ bads).take m).toFinset

theorem preferNon_subset {N : Nat} (R : Finset (Fin N)) (P : Fin N → Prop)
    [DecidablePred P] (n : Nat) :
    preferNon R P n ⊆ R := by
  classical
  intro x hx
  simp only [preferNon, List.mem_toFinset] at hx
  have hx' : x ∈ (R.filter (fun y => ¬ P y)).sort (· ≤ ·) ++
      (R.filter P).sort (· ≤ ·) := List.mem_of_mem_take hx
  rw [List.mem_append] at hx'
  cases hx' with
  | inl hxg => exact (mem_filter.mp ((mem_sort (· ≤ ·)).1 hxg)).1
  | inr hxb => exact (mem_filter.mp ((mem_sort (· ≤ ·)).1 hxb)).1

theorem preferNon_card_le {N : Nat} (R : Finset (Fin N)) (P : Fin N → Prop)
    [DecidablePred P] (n : Nat) :
    (preferNon R P n).card ≤ n := by
  classical
  simp only [preferNon]
  set L := (R.filter (fun x => ¬ P x)).sort (· ≤ ·) ++
    (R.filter P).sort (· ≤ ·)
  set m := min n R.card
  have hcard : (L.take m).toFinset.card ≤ (L.take m).length :=
    List.toFinset_card_le (L.take m)
  have hlen : (L.take m).length ≤ m := List.length_take_le m L
  have hm : m ≤ n := Nat.min_le_left _ _
  omega

/-- Goods-first property of `preferNon`, proved by case split on the take. -/
theorem preferNon_goods_first {N : Nat} (R : Finset (Fin N)) (P : Fin N → Prop)
    [DecidablePred P] (n : Nat) :
    ((preferNon R P n).filter P).card = 0 ∨
      R.filter (fun x => ¬ P x) ⊆ preferNon R P n := by
  classical
  set G := R.filter (fun x => ¬ P x)
  set goods := G.sort (· ≤ ·)
  set bads := (R.filter P).sort (· ≤ ·)
  set m := min n R.card
  have hdef : preferNon R P n = ((goods ++ bads).take m).toFinset := by
    simp only [preferNon, goods, bads, m, G]
  rw [hdef]
  by_cases hmg : m ≤ goods.length
  · left
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxL : x ∈ (goods ++ bads).take m :=
      List.mem_toFinset.mp (mem_filter.mp hx).1
    have hxg : x ∈ goods := by
      rw [List.take_append_of_le_length hmg] at hxL
      exact List.mem_of_mem_take hxL
    have hxG : x ∈ G := (mem_sort (· ≤ ·)).1 (by simpa [goods] using hxg)
    exact (mem_filter.mp hxG).2 (mem_filter.mp hx).2
  · right
    have hlt : goods.length < m := lt_of_not_ge hmg
    intro x hxG
    have hxg : x ∈ goods := (mem_sort (· ≤ ·)).2 (by simpa [G] using hxG)
    have htake :
        (goods ++ bads).take m =
          goods.take m ++ bads.take (m - goods.length) := by
      simp [List.take_append]
    have hgoods : goods.take m = goods := List.take_of_length_le (le_of_lt hlt)
    have hxL : x ∈ (goods ++ bads).take m := by
      rw [htake, hgoods]
      exact List.mem_append.mpr (Or.inl hxg)
    exact List.mem_toFinset.mpr hxL

theorem preferNon_density {N : Nat} (R : Finset (Fin N)) (P : Fin N → Prop)
    [DecidablePred P] (n : Nat) :
    (((preferNon R P n).filter P).card : Rat) * (R.card : Rat) ≤
      ((R.filter P).card : Rat) * ((preferNon R P n).card : Rat) :=
  density_of_goods_first R (preferNon R P n) P
    (preferNon_subset R P n) (preferNon_goods_first R P n)

/-! **Schedule-sized abstract child send** -/

def sendUpNat (p : ScheduleParams) (d i t : Nat) : Nat :=
  ⌊sendUpBudget p d i t⌋₊

theorem sendUpNat_le_budget (p : ScheduleParams) (d i t : Nat) :
    (sendUpNat p d i t : Rat) ≤ sendUpBudget p d i t := by
  simpa [sendUpNat] using
    (Nat.floor_le (sendUpBudget_nonneg p d i t) : (⌊sendUpBudget p d i t⌋₊ : Rat) ≤ _)

structure PlacementCapacityLower (p : ScheduleParams) (d t : Nat)
    (pl : Placement p.br d) where
  hGe : ∀ (b : KBag p.br d),
    capacity p d b.l t ≤ ((pl.regs b).card : Rat)

/-- Child register lower bound used by preferNon send-up (only when the child
    register set is nonempty). Empty child bags impose no capacity obligation. -/
structure ChildRegisterCapacityLower (p : ScheduleParams) (d t : Nat)
    (pl : Placement p.br d) where
  hGe : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d) (j : Fin p.br),
    0 < (pl.regs (b.child j.val j.isLt hbd)).card →
      capacity p d (b.l + 1) t ≤
        ((pl.regs (b.child j.val j.isLt hbd)).card : Rat)



/-- On the scheduler ladder `α(t) ≤ l < ω(t)`, capacity is below native bag size
    once `3 * l + 2 ≤ t` (params7 native-card exponent comparison). -/
structure PlacementCapacityLowerOnLadder (p : ScheduleParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat) (pl : Placement p.br d) where
  hGe : ∀ (b : KBag p.br d),
    sched.alpha t ≤ b.l → b.l < sched.omega t →
      capacity p d b.l t ≤ ((pl.regs b).card : Rat)

/-- Abstract child-send data with schedule size and fair density. -/
structure AbstractChildSend (p : ScheduleParams) (d : Nat) (t : Nat)
    (pl pl' : Placement p.br d)
    (step : PlacementStep p d pl pl')
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) where
  sendUp : ∀ (b : KBag p.br d) (_hb : 1 ≤ b.l) (_hbd : b.l < d)
      (_j : Fin p.br), Finset (Fin (p.br ^ d))
  hsubset : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    sendUp b hb hbd j ⊆ pl.regs (b.child j.val j.isLt hbd)
  hSend : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    ((sendUp b hb hbd j).card : Rat) ≤ sendUpBudget p d (b.l + 1) t
  hRegs : ∀ (b : KBag p.br d) (_hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    0 < (pl.regs (b.child j.val j.isLt hbd)).card →
      capacity p d (b.l + 1) t ≤
        ((pl.regs (b.child j.val j.isLt hbd)).card : Rat)
  hDensity : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d)
      (j : Fin p.br),
    (((b.child j.val j.isLt hbd).strangers 2 perm
        (sendUp b hb hbd j) (br_ge_one p) : Rat)) *
        ((pl.regs (b.child j.val j.isLt hbd)).card : Rat) ≤
      (((b.child j.val j.isLt hbd).strangers 2 perm
          (pl.regs (b.child j.val j.isLt hbd)) (br_ge_one p) : Rat)) *
        ((sendUp b hb hbd j).card : Rat)
  hFrom : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d),
    step.fromChildren b hb =
      (univ : Finset (Fin p.br)).biUnion (fun j => sendUp b hb hbd j)
  hempty : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l), b.l = d →
    step.fromChildren b hb = ∅







/-! **Fillers** -/

def AbstractChildSend.empty (p : ScheduleParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (step : PlacementStep p d pl pl')
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hcap : ChildRegisterCapacityLower p d t pl)
    (hfrom0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l), step.fromChildren b hb = ∅) :
    AbstractChildSend p d t pl pl' step perm where
  sendUp := fun _ _ _ _ => ∅
  hsubset := fun _ _ _ _ => empty_subset _
  hSend := fun b _ _ _ => by
    simp only [card_empty, Nat.cast_zero]
    exact sendUpBudget_nonneg p d (b.l + 1) t
  hRegs := fun b hb hbd j hpos => hcap.hGe b hb hbd j hpos
  hDensity := fun b _hbd hbd j => by
    have hbr := br_ge_one p
    have hs0 :
        ((b.child j.val j.isLt hbd).strangers 2 perm ∅ hbr : Rat) = 0 := by
      simp [KBag.strangers_empty]
    have hc0 : ((∅ : Finset (Fin (p.br ^ d))).card : Rat) = 0 := by simp
    simp only [hs0, hc0, zero_mul, mul_zero, le_rfl]
  hFrom := fun b hb _hbd => by
    have hbi :
        (univ : Finset (Fin p.br)).biUnion
          (fun _ : Fin p.br => (∅ : Finset (Fin (p.br ^ d)))) = ∅ := by
      ext x; simp
    exact (hfrom0 b hb).trans hbi.symm
  hempty := fun b hb _ => hfrom0 b hb

def AbstractChildSend.ofPreferNon (p : ScheduleParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (step : PlacementStep p d pl pl')
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hcap : ChildRegisterCapacityLower p d t pl)
    (hfrom : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      step.fromChildren b hb =
        if hbd : b.l < d then
          (univ : Finset (Fin p.br)).biUnion (fun j =>
            preferNon (pl.regs (b.child j.val j.isLt hbd))
              (fun r => (b.child j.val j.isLt hbd).Strange 2 r perm (br_ge_one p))
              (sendUpNat p d (b.l + 1) t))
        else ∅) :
    AbstractChildSend p d t pl pl' step perm where
  sendUp := fun b _hbd hbd j =>
    preferNon (pl.regs (b.child j.val j.isLt hbd))
      (fun r => (b.child j.val j.isLt hbd).Strange 2 r perm (br_ge_one p))
      (sendUpNat p d (b.l + 1) t)
  hsubset := fun _ _ _ _ => preferNon_subset _ _ _
  hSend := fun b _ hbd j => by
    have hcard := preferNon_card_le (pl.regs (b.child j.val j.isLt hbd))
      (fun r => (b.child j.val j.isLt hbd).Strange 2 r perm (br_ge_one p))
      (sendUpNat p d (b.l + 1) t)
    exact (Nat.cast_le.mpr hcard).trans (sendUpNat_le_budget p d (b.l + 1) t)
  hRegs := fun b hb hbd j hpos => hcap.hGe b hb hbd j hpos
  hDensity := fun b _ hbd j => by
    have hbr := br_ge_one p
    have h := preferNon_density (pl.regs (b.child j.val j.isLt hbd))
      (fun r => (b.child j.val j.isLt hbd).Strange 2 r perm hbr)
      (sendUpNat p d (b.l + 1) t)
    simpa [KBag.strangers] using h
  hFrom := fun b hb hbd => by
    rw [hfrom b hb, dif_pos hbd]
  hempty := fun b hb hleaf => by
    rw [hfrom b hb, dif_neg (by omega : ¬ b.l < d)]

/-! **Wire preferNon into a PlacementStep** -/


/-- Aggregate prefer-non send-ups used as `fromChildren`. -/
def preferNonFromChildren (p : ScheduleParams) (d t : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (b : KBag p.br d) (_hb : 1 ≤ b.l) : Finset (Fin (p.br ^ d)) :=
  if hbd : b.l < d then
    (univ : Finset (Fin p.br)).biUnion (fun j =>
      preferNon (pl.regs (b.child j.val j.isLt hbd))
        (fun r => (b.child j.val j.isLt hbd).Strange 2 r perm (br_ge_one p))
        (sendUpNat p d (b.l + 1) t))
  else
    ∅

/-- `PlacementStep` with `fromChildren := preferNonFromChildren`; parent-send
    and register cover remain hypotheses. -/
def placementStep_of_preferNon (p : ScheduleParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (fromParent : ∀ (b : KBag p.br d), 1 ≤ b.l → Finset (Fin (p.br ^ d)))
    (hregs : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      pl'.regs b ⊆
        fromParent b hb ∪ preferNonFromChildren p d t pl perm b hb) :
    PlacementStep p d pl pl' where
  fromParent := fromParent
  fromChildren := preferNonFromChildren p d t pl perm
  hregs := hregs

theorem preferNonFromChildren_eq (p : ScheduleParams) (d t : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (b : KBag p.br d) (hb : 1 ≤ b.l) :
    preferNonFromChildren p d t pl perm b hb =
      if hbd : b.l < d then
        (univ : Finset (Fin p.br)).biUnion (fun j =>
          preferNon (pl.regs (b.child j.val j.isLt hbd))
            (fun r => (b.child j.val j.isLt hbd).Strange 2 r perm (br_ge_one p))
            (sendUpNat p d (b.l + 1) t))
      else
        ∅ :=
  rfl

/-- Abstract child-send on a preferNon-backed placement step. -/
def AbstractChildSend.ofPreferNonStep (p : ScheduleParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (fromParent : ∀ (b : KBag p.br d), 1 ≤ b.l → Finset (Fin (p.br ^ d)))
    (hregs : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      pl'.regs b ⊆
        fromParent b hb ∪ preferNonFromChildren p d t pl perm b hb)
    (hcap : ChildRegisterCapacityLower p d t pl) :
    let step := placementStep_of_preferNon p d t pl pl' perm fromParent hregs
    AbstractChildSend p d t pl pl' step perm :=
  AbstractChildSend.ofPreferNon p d t pl pl'
    (placementStep_of_preferNon p d t pl pl' perm fromParent hregs) perm hcap
    fun b hb => preferNonFromChildren_eq p d t pl perm b hb

/-! **Support cover equals abstract cover** -/






/-! **Assemble StageKernelWithChildren children fields** -/

/-- Parent-send / separator residual still needed after abstract children-send
    discharge. Top-order `r = d` and level-0 are discharged from root nativeness. -/
structure AbstractParentResidue (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (t : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (pl' : Placement p.br d)
    (perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (step : PlacementStep p d pl pl') where
  parentSep : ∀ (b : KBag p.br d), 1 ≤ b.l → LocalSeparatorQuality ip
  ha_le_cap : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    (parentSep b hb).a ≤ capacity p d (b.l - 1) t
  hBadSend0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
      parentOutMass p d pl perm b hb +
        sibMassBound p ip d t b hb +
        (parentSep b hb).intrusion + slackBound p d t b hb
  hFringeSend : ∀ (b : KBag p.br d) (r : Nat)
      (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
      (parentSep b hb).fringeSent
        ((b.parent (br_ge_one p)).strangers r perm
          (pl.regs (b.parent (br_ge_one p))) (br_ge_one p) : Rat)




/-! **Initial root placement** -/




/-! **Residual per-stage data for a preferNon trajectory** -/

/-- Kernel-checked preferNon children-send inputs: executable parent send-up,
    register cover, and child register lower bounds. -/
structure PreferNonStageChildrenData (p : ScheduleParams) (d : Nat) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) where
  fromParent : ∀ (b : KBag p.br d), 1 ≤ b.l → Finset (Fin (p.br ^ d))
  hregs : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    pl'.regs b ⊆
      fromParent b hb ∪ preferNonFromChildren p d t pl perm b hb
  hcap : ChildRegisterCapacityLower p d t pl

/-- One scheduler stage after abstract children-send discharge: executable
    `fromParent`, register cover, capacity lower bound, and parent-send /
    separator-quality residue (`AbstractParentResidue`). Same-perm stages use
    `AbstractChildSend.ofPreferNonStep`; Thm 5.1 routing fills `parent` once
    scramble B/F and matrix bridge are available. -/
structure PreferNonStageObligation (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) where
  fromParent : ∀ (b : KBag p.br d), 1 ≤ b.l → Finset (Fin (p.br ^ d))
  hregs : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    pl'.regs b ⊆
      fromParent b hb ∪ preferNonFromChildren p d t pl perm b hb
  hcap : ChildRegisterCapacityLower p d t pl
  parent : AbstractParentResidue p ip d t pl perm pl' perm
    (placementStep_of_preferNon p d t pl pl' perm fromParent hregs)

def PreferNonStageObligation.step {p : ScheduleParams} {ip : InvariantParams}
    {d t : Nat} {pl pl' : Placement p.br d}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (O : PreferNonStageObligation p ip d t pl pl' perm) :
    PlacementStep p d pl pl' :=
  placementStep_of_preferNon p d t pl pl' perm O.fromParent O.hregs










end Chvatal


