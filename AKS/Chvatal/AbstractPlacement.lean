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

def PlacementCapacityLower.toChildRegister {p : ScheduleParams} {d t : Nat}
    {pl : Placement p.br d} (h : PlacementCapacityLower p d t pl) :
    ChildRegisterCapacityLower p d t pl where
  hGe := fun b hb hbd j _hpos => h.hGe (b.child j.val j.isLt hbd)

def ChildRegisterCapacityLower.of_emptyChildRegs (p : ScheduleParams) (d t : Nat)
    (pl : Placement p.br d)
    (h : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d) (j : Fin p.br),
      (pl.regs (b.child j.val j.isLt hbd)).card = 0) :
    ChildRegisterCapacityLower p d t pl where
  hGe := fun b hb hbd j hpos =>
    absurd hpos (by rw [h b hb hbd j]; exact Nat.not_lt_zero 0)

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

def AbstractChildSend.toCover {p : ScheduleParams} {d t : Nat}
    {pl pl' : Placement p.br d} {step : PlacementStep p d pl pl'}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (A : AbstractChildSend p d t pl pl' step perm) :
    ChildSendCover p d pl pl' step where
  sendUp := A.sendUp
  hsubset := A.hsubset
  hcover := fun b hb hbd => by rw [A.hFrom b hb hbd]
  hempty := A.hempty

def AbstractChildSend.toSupport {p : ScheduleParams} {d t : Nat}
    {pl pl' : Placement p.br d} {step : PlacementStep p d pl pl'}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (A : AbstractChildSend p d t pl pl' step perm) :
    ChildSendSupport p d pl pl' step where
  hsupport := fun b hb hbd => by
    rw [A.hFrom b hb hbd]
    intro x hx
    rcases mem_biUnion.mp hx with ⟨j, hj, hxj⟩
    exact mem_biUnion.mpr ⟨j, hj, A.hsubset b hb hbd j hxj⟩
  hempty := A.hempty

def AbstractChildSend.toCapBudget {p : ScheduleParams} {d t : Nat}
    {pl pl' : Placement p.br d} {step : PlacementStep p d pl pl'}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (A : AbstractChildSend p d t pl pl' step perm) :
    ChildSendCapBudget p d t pl pl' step A.toCover where
  hSend := A.hSend
  hRegs := A.hRegs

def AbstractChildSend.toFair {p : ScheduleParams} {d t : Nat}
    {pl pl' : Placement p.br d} {step : PlacementStep p d pl pl'}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (A : AbstractChildSend p d t pl pl' step perm) :
    ChildSendFair p d pl pl' step perm perm A.toCover :=
  childSendFair_of_same_perm p d pl pl' step perm A.toCover fun b hb hbd j => by
    simpa [AbstractChildSend.toCover] using A.hDensity b hb hbd j

def AbstractChildSend.toBridge {p : ScheduleParams} {d t : Nat}
    {pl pl' : Placement p.br d} {step : PlacementStep p d pl pl'}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (A : AbstractChildSend p d t pl pl' step perm) :
    ChildSendBridge p d pl pl' step perm perm A.toCover :=
  childSendBridge_of_same_perm p d pl pl' step perm A.toCover

def AbstractChildSend.toCard {p : ScheduleParams} {d t : Nat}
    {pl pl' : Placement p.br d} {step : PlacementStep p d pl pl'}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (A : AbstractChildSend p d t pl pl' step perm) :
    ChildSendCard p d pl pl' step A.toCover :=
  childSendCard_of_capBudget p d t pl pl' step A.toCover A.toCapBudget

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

/-- Distinct child indices yield distinct child bags. -/
theorem KBag.child_ne {br d : Nat} (b : KBag br d) (hbd : b.l < d)
    (j1 j2 : Fin br) (hne : j1 ≠ j2) :
    b.child j1.val j1.isLt hbd ≠ b.child j2.val j2.isLt hbd := by
  intro heq
  have hx : (b.child j1.val j1.isLt hbd).x = (b.child j2.val j2.isLt hbd).x :=
    congrArg KBag.x heq
  simp only [KBag.child] at hx
  exact hne (Fin.ext (by omega))

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

theorem AbstractChildSend.sendUp_eq_inter {p : ScheduleParams} {d t : Nat}
    {pl pl' : Placement p.br d} {step : PlacementStep p d pl pl'}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (A : AbstractChildSend p d t pl pl' step perm)
    (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d) (j : Fin p.br) :
    A.sendUp b hb hbd j =
      step.fromChildren b hb ∩ pl.regs (b.child j.val j.isLt hbd) := by
  ext x
  constructor
  · intro hx
    refine mem_inter.mpr ⟨?_, A.hsubset b hb hbd j hx⟩
    rw [A.hFrom b hb hbd]
    exact mem_biUnion.mpr ⟨j, mem_univ j, hx⟩
  · intro hx
    have hxFC := (mem_inter.mp hx).1
    have hxR := (mem_inter.mp hx).2
    rw [A.hFrom b hb hbd] at hxFC
    rcases mem_biUnion.mp hxFC with ⟨j', _, hxj'⟩
    have hxRj' : x ∈ pl.regs (b.child j'.val j'.isLt hbd) :=
      A.hsubset b hb hbd j' hxj'
    have hj : j' = j := by
      by_contra hne
      have hbags := KBag.child_ne b hbd j' j hne
      exact (disjoint_left.mp (pl.disjoint _ _ hbags)) hxRj' hxR
    subst hj
    exact hxj'

/-- Support-cover send-up equals the abstract send-up. -/
theorem AbstractChildSend.sendUp_eq_supportCover {p : ScheduleParams} {d t : Nat}
    {pl pl' : Placement p.br d} {step : PlacementStep p d pl pl'}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (A : AbstractChildSend p d t pl pl' step perm)
    (b : KBag p.br d) (hb : 1 ≤ b.l) (hbd : b.l < d) (j : Fin p.br) :
    (childSendCover_of_support p d pl pl' step A.toSupport).sendUp b hb hbd j =
      A.sendUp b hb hbd j := by
  simp only [childSendCover_of_support, A.sendUp_eq_inter b hb hbd j]

def AbstractChildSend.toSupportCard {p : ScheduleParams} {d t : Nat}
    {pl pl' : Placement p.br d} {step : PlacementStep p d pl pl'}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (A : AbstractChildSend p d t pl pl' step perm) :
    ChildSendCard p d pl pl' step
      (childSendCover_of_support p d pl pl' step A.toSupport) where
  hCardFrac := fun b hb hbd j => by
    simpa [A.sendUp_eq_supportCover b hb hbd j, AbstractChildSend.toCover] using
      A.toCard.hCardFrac b hb hbd j

def AbstractChildSend.toSupportFair {p : ScheduleParams} {d t : Nat}
    {pl pl' : Placement p.br d} {step : PlacementStep p d pl pl'}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (A : AbstractChildSend p d t pl pl' step perm) :
    ChildSendFair p d pl pl' step perm perm
      (childSendCover_of_support p d pl pl' step A.toSupport) :=
  childSendFair_of_same_perm p d pl pl' step perm
    (childSendCover_of_support p d pl pl' step A.toSupport)
    fun b hb hbd j => by
      simpa [A.sendUp_eq_supportCover b hb hbd j] using A.hDensity b hb hbd j

def AbstractChildSend.toSupportBridge {p : ScheduleParams} {d t : Nat}
    {pl pl' : Placement p.br d} {step : PlacementStep p d pl pl'}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (A : AbstractChildSend p d t pl pl' step perm) :
    ChildSendBridge p d pl pl' step perm perm
      (childSendCover_of_support p d pl pl' step A.toSupport) :=
  childSendBridge_of_same_perm p d pl pl' step perm
    (childSendCover_of_support p d pl pl' step A.toSupport)

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

theorem hFromChildrenR_top_of_root (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (t : Nat) (pl pl' : Placement p.br d)
    (step : PlacementStep p d pl pl')
    (perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (b : KBag p.br d) (hb : 1 ≤ b.l) :
    ((b.strangers (d + 1) perm' (step.fromChildren b hb) (br_ge_one p) : Rat)) ≤
      ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
        (ip.mu * ip.delta ^ (d - 1) *
          (p.A * p.nu * capacity p d (b.l - 1) t)) := by
  have h0 := KBag.strangers_succ_d_eq_zero b perm' (step.fromChildren b hb)
    (br_ge_one p)
  have hRHS :
      (0 : Rat) ≤
        ip.delta ^ 2 * p.A * (p.br : Rat) / p.nu *
          (ip.mu * ip.delta ^ (d - 1) *
            (p.A * p.nu * capacity p d (b.l - 1) t)) := by
    have := p.A_pos
    have := p.hnu_pos
    have := p.br_cast_pos
    have := ip.hmu_pos
    have := ip.hdelta_pos
    have := capacity_pos p d (b.l - 1) t
    positivity
  simpa [h0] using hRHS

theorem level0_of_root (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (t : Nat) (pl' : Placement p.br d)
    (perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (b : KBag p.br d) (r : Nat) (hb0 : b.l = 0) (_hr : r ≤ d) :
    ((b.strangers (r + 1) perm' (pl'.regs b) (br_ge_one p) : Rat)) ≤
      ip.mu * ip.delta ^ r * capacity p d 0 (t + 1) := by
  have hlt : b.l < r + 1 := by
    rw [hb0]; omega
  have h0 := KBag.strangers_eq_zero_of_lt_order b (r + 1) perm' (pl'.regs b)
    (br_ge_one p) (by omega) hlt
  have hRHS :
      (0 : Rat) ≤ ip.mu * ip.delta ^ r * capacity p d 0 (t + 1) := by
    have := ip.hmu_pos
    have := ip.hdelta_pos
    have := capacity_pos p d 0 (t + 1)
    positivity
  simpa [h0] using hRHS

/-- Fill `StageKernelWithChildren` from abstract children-send (same perm) plus
    parent-send residue. Schedule counts, slack, top-order, and level-0 are
    discharged. -/
def StageKernelWithChildren.ofAbstractChildSend
    (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (step : PlacementStep p d pl pl')
    (ht : t + 1 ≤ sched.tf)
    (A : AbstractChildSend p d t pl pl' step perm)
    (R : AbstractParentResidue p ip d t pl perm pl' perm step) :
    StageKernelWithChildren p ip d sched t pl perm pl' perm where
  ht := ht
  step := step
  counts := stageCounts_on_schedule p ip d sched t
  counts_wires := stageCounts_on_schedule_wires p ip d sched t
  counts_bad := stageCounts_on_schedule_bad p ip d sched t
  parentSep := R.parentSep
  ha_le_cap := R.ha_le_cap
  slack0 := fun b hb => slackBound p d t b hb
  hSlack0 := fun b hb => slackBound_le p d t b hb
  hBadSend0 := R.hBadSend0
  hFringeSend := R.hFringeSend
  support := A.toSupport
  card := A.toSupportCard
  fair := A.toSupportFair
  bridge := A.toSupportBridge
  hFromChildrenR_top := fun b hb =>
    hFromChildrenR_top_of_root p ip d t pl pl' step perm b hb
  level0 := fun b r hb0 hr => level0_of_root p ip d t pl' perm b r hb0 hr

/-! **Initial root placement** -/

/-- All wires at the unique root bag. -/
def rootPlacement (br d : Nat) : Placement br d where
  regs b := if b = KBag.root br d then univ else ∅
  disjoint a b hab := by
    by_cases ha : a = KBag.root br d <;> by_cases hb : b = KBag.root br d
    · exact absurd (ha.trans hb.symm) hab
    · simp [ha, hb]
    · simp [ha, hb]
    · simp [ha, hb]
  complete i := ⟨KBag.root br d, by simp⟩

theorem rootPlacement_strangers_eq_zero (br d : Nat) (hbr : 1 ≤ br)
    (perm : Fin (br ^ d) → Fin (br ^ d))
    (b : KBag br d) (r : Nat) (_hr : r ≤ d) :
    b.strangers (r + 1) perm ((rootPlacement br d).regs b) hbr = 0 := by
  by_cases hb : b = KBag.root br d
  · subst hb
    exact KBag.strangers_eq_zero_of_lt_order _ (r + 1) perm _ hbr (by omega)
      (by simp [KBag.root])
  · simp only [rootPlacement, if_neg hb, KBag.strangers_empty]

/-- Initial outsider bound: root placement has no strangers. -/
theorem outsiderBoundLe_rootPlacement (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (sched : LevelSchedule p d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) :
    OutsiderBoundLe p ip d sched 0 (rootPlacement p.br d) perm := by
  intro b r hr
  have h0 := rootPlacement_strangers_eq_zero p.br d (br_ge_one p) perm b r hr
  have hRHS :
      (0 : Rat) ≤ ip.mu * ip.delta ^ r * capacity p d b.l 0 := by
    have := ip.hmu_pos
    have := ip.hdelta_pos
    have := capacity_pos p d b.l 0
    positivity
  simpa [h0] using hRHS

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

def PreferNonStageObligation.childSend {p : ScheduleParams} {ip : InvariantParams}
    {d t : Nat} {pl pl' : Placement p.br d}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (O : PreferNonStageObligation p ip d t pl pl' perm) :
    AbstractChildSend p d t pl pl' O.step perm :=
  AbstractChildSend.ofPreferNonStep p d t pl pl' perm O.fromParent O.hregs O.hcap

def PreferNonStageObligation.of_childrenData {p : ScheduleParams} {ip : InvariantParams}
    {d t : Nat} {pl pl' : Placement p.br d}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (C : PreferNonStageChildrenData p d t pl pl' perm)
    (parent : AbstractParentResidue p ip d t pl perm pl' perm
      (placementStep_of_preferNon p d t pl pl' perm C.fromParent C.hregs)) :
    PreferNonStageObligation p ip d t pl pl' perm where
  fromParent := C.fromParent
  hregs := C.hregs
  hcap := C.hcap
  parent := parent

def PreferNonStageChildrenData.of_obligation {p : ScheduleParams} {ip : InvariantParams}
    {d t : Nat} {pl pl' : Placement p.br d}
    {perm : Fin (p.br ^ d) → Fin (p.br ^ d)}
    (O : PreferNonStageObligation p ip d t pl pl' perm) :
    PreferNonStageChildrenData p d t pl pl' perm where
  fromParent := O.fromParent
  hregs := O.hregs
  hcap := O.hcap

/-- PreferNon children-send with no parent send-up (only `fromChildren`). -/
def PreferNonStageChildrenData.fromParent_empty (p : ScheduleParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hregs : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      pl'.regs b ⊆ preferNonFromChildren p d t pl perm b hb)
    (hcap : ChildRegisterCapacityLower p d t pl) :
    PreferNonStageChildrenData p d t pl pl' perm where
  fromParent := fun _ _ => ∅
  hregs := fun b hb => by
    simpa [empty_union, union_empty] using hregs b hb
  hcap := hcap

theorem preferNonFromChildren_empty_of_childRegs_empty (p : ScheduleParams) (d t : Nat)
    (pl : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (b : KBag p.br d) (hb : 1 ≤ b.l)
    (h : ∀ (hbd : b.l < d) (j : Fin p.br),
      (pl.regs (b.child j.val j.isLt hbd)).card = 0) :
    preferNonFromChildren p d t pl perm b hb = ∅ := by
  by_cases hbd : b.l < d
  · rw [preferNonFromChildren_eq, dif_pos hbd]
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases mem_biUnion.mp hx with ⟨j, _, hxj⟩
    have h0 := h hbd j
    have hxR : x ∈ pl.regs (b.child j.val j.isLt hbd) :=
      preferNon_subset (pl.regs (b.child j.val j.isLt hbd))
        (fun r => (b.child j.val j.isLt hbd).Strange 2 r perm (br_ge_one p))
        (sendUpNat p d (b.l + 1) t) hxj
    have hempty : pl.regs (b.child j.val j.isLt hbd) = ∅ := Finset.card_eq_zero.mp h0
    exact False.elim (notMem_empty x (hempty ▸ hxR))
  · rw [preferNonFromChildren_eq, dif_neg hbd]

theorem rootPlacement_childRegs_empty (br d : Nat) (b : KBag br d) (_hb : 1 ≤ b.l)
    (hbd : b.l < d) (j : Fin br) :
    (rootPlacement br d).regs (b.child j.val j.isLt hbd) = ∅ := by
  simp only [rootPlacement]
  have hne : b.child j.val j.isLt hbd ≠ KBag.root br d := by
    intro heq
    have hl := congrArg KBag.l heq
    simp only [KBag.child, KBag.root] at hl
    omega
  simp [hne]

theorem registerCover_rootPlacement_fromParent_empty (p : ScheduleParams) (d t : Nat)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) :
    ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      (rootPlacement p.br d).regs b ⊆
        preferNonFromChildren p d t (rootPlacement p.br d) perm b hb := by
  intro b hb
  have hregs : (rootPlacement p.br d).regs b = ∅ := by
    simp only [rootPlacement]
    have hne : b ≠ KBag.root p.br d := by
      intro heq
      have hl := congrArg KBag.l heq
      simp only [KBag.root] at hl
      omega
    simp [hne]
  by_cases hbd : b.l < d
  · have hempty := preferNonFromChildren_empty_of_childRegs_empty p d t
      (rootPlacement p.br d) perm b hb (fun hbd' j => by
        rw [rootPlacement_childRegs_empty p.br d b hb hbd' j]
        simp)
    rw [hregs, hempty]
  · have hempty : preferNonFromChildren p d t (rootPlacement p.br d) perm b hb = ∅ := by
      rw [preferNonFromChildren_eq, dif_neg hbd]
    rw [hregs, hempty]

def PreferNonStageChildrenData.rootStage_fromParent_empty (p : ScheduleParams)
    (d t : Nat) (perm : Fin (p.br ^ d) → Fin (p.br ^ d)) :
    PreferNonStageChildrenData p d t (rootPlacement p.br d) (rootPlacement p.br d) perm :=
  PreferNonStageChildrenData.fromParent_empty p d t (rootPlacement p.br d)
    (rootPlacement p.br d) perm
    (registerCover_rootPlacement_fromParent_empty p d t perm)
    (ChildRegisterCapacityLower.of_emptyChildRegs p d t (rootPlacement p.br d)
      (fun b hb hbd j => by
        rw [rootPlacement_childRegs_empty p.br d b hb hbd j]
        simp))

theorem placementStep_of_preferNon_fromParent_empty (p : ScheduleParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (hregs : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      pl'.regs b ⊆ preferNonFromChildren p d t pl perm b hb)
    (hcap : ChildRegisterCapacityLower p d t pl) :
    placementStep_of_preferNon p d t pl pl' perm
      (PreferNonStageChildrenData.fromParent_empty p d t pl pl' perm hregs hcap).fromParent
      (PreferNonStageChildrenData.fromParent_empty p d t pl pl' perm hregs hcap).hregs =
      placementStep_of_preferNon p d t pl pl' perm
        (fun _ _ => ∅) (fun b hb => by
          simpa [empty_union, union_empty] using hregs b hb) := rfl

end Chvatal


