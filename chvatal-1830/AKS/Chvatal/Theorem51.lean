module
/-
  # Chvátal Theorem 5.1 — scramble separators

  Source: V. Chvátal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §5–§6
  (`http://users.encs.concordia.ca/~chvatal/aks.pdf`).

  Status: kernel-checked statement of Thm 5.1 (geometry + matrix Properties B/F),
  §7 parameter side-conditions, the Lemma 6.1 closing numeric bound
  `(2(m+1)/(e m))^n < 1/100`, and the bridge from matrix B/F budgets into the
  bag-level `PropertyB`/`PropertyF` / `LocalSeparatorQuality` used by §4.

  The probabilistic counting proof of Lemmas 6.1–6.2 is partially packaged:
  [Lemma61](Lemma61.lean) has the algebraic/counting core and existence glue
  from a fail-fraction bound; [Lemma63](Lemma63.lean) discharges
  `lemma63ExpBound` (paper Lemma 6.3 + (6.1)). Residual: FailBound union + Lemma
  6.2 / F-side. Existence of a full scramble witness with B and F remains
  `ExistsScrambleSeparator`.
-/

public import AKS.Chvatal.Theorem51Core
public import AKS.Chvatal.PropertyBF
public import AKS.Chvatal.RoutingFromP

@[expose] public section

namespace Chvatal

/-! Witness types (`ScrambleSeparatorWitness`, `ExistsScrambleSeparator`,
    `Theorem51Obligation`) live in `MatrixBridge.lean` after `SortScrambleSortPack`. -/

/-! **§7 fit** -/

/-- §7 uses `δF = 128/4095 ≤ 1/25`. -/
theorem params7_deltaF_theorem51 : (invariant7.deltaF : ℝ) ≤ 1 / 25 := by
  simp only [invariant7]
  norm_num

/-- §7 `εF = 1/8·10⁷` meets `εF ≥ 4e/f` whenever `f ≥ 4 e · 8·10⁷`. -/
theorem params7_epsF_ge_4e {f : Nat}
    (hf : (4 * Real.exp 1) * (8 * 10 ^ 7) ≤ f) :
    (4 * Real.exp 1) / f ≤ (invariant7.epsF : ℝ) := by
  have hfpos : (0 : ℝ) < f :=
    lt_of_lt_of_le (by positivity) hf
  have hinv : (invariant7.epsF : ℝ) = 1 / (8 * 10 ^ 7) := by
    norm_num [invariant7]
  rw [hinv]
  have : (4 * Real.exp 1) / f ≤ (4 * Real.exp 1) / ((4 * Real.exp 1) * (8 * 10 ^ 7)) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hf
  have hsimp :
      (4 * Real.exp 1) / ((4 * Real.exp 1) * (8 * 10 ^ 7)) = 1 / (8 * 10 ^ 7) := by
    field_simp
  linarith

/-- Bag-level B/F witnesses saturating the `εB`/`εF` budgets. -/
def PropertyB.ofEps (ip : InvariantParams) (a : Rat) (ha : 0 < a) :
    PropertyB ip where
  a := a
  ha_pos := ha
  intrusion := ip.epsB * a
  hIntrusion := le_rfl

def PropertyF.ofEps (ip : InvariantParams) : PropertyF ip where
  fringeSent := fun src => ip.epsF * src
  hFringe := fun _ => le_rfl

/-- From Thm 5.1 quality budgets at bag size `a`, build `LocalSeparatorQuality`.
    Matrix→bag intrusion translation is absorbed into the `epsB·a` / `epsF·src`
    budgets already used by §4. -/
def LocalSeparatorQuality.ofTheorem51 (ip : InvariantParams)
    (a : Rat) (ha : 0 < a) : LocalSeparatorQuality ip :=
  LocalSeparatorQuality.ofBF ip (PropertyB.ofEps ip a ha) (PropertyF.ofEps ip)

/-- Residual Thm 5.1 parent-send: bad-send and fringe Finset bounds at the
    paper `εB`/`εF` capacity budgets (positivity of parent capacity is not
    assumed here). -/
structure AbstractParentResidueRouting (p : ScheduleParams) (ip : InvariantParams)
    (d : Nat) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (step : PlacementStep p d pl pl') where
  hBadSend0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
    ((b.strangers 1 perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
      parentOutMass p d pl perm b hb +
        sibMassBound p ip d t b hb +
        ip.epsB * capacity p d (b.l - 1) t + slackBound p d t b hb
  hFringeSend : ∀ (b : KBag p.br d) (r : Nat)
      (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
    ((b.strangers (r + 1) perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
      ip.epsF *
        ((b.parent (br_ge_one p)).strangers r perm
          (pl.regs (b.parent (br_ge_one p))) (br_ge_one p) : Rat)

/-- Parent residue from Thm 5.1 quality per bag plus routing Finset bounds. -/
def AbstractParentResidue.ofTheorem51Routing
    (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (step : PlacementStep p d pl pl')
    (ha : ∀ (b : KBag p.br d), 1 ≤ b.l →
      0 < (capacity p d (b.l - 1) t))
    (hBadSend0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      ((b.strangers 1 perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
        parentOutMass p d pl perm b hb +
          sibMassBound p ip d t b hb +
          ip.epsB * capacity p d (b.l - 1) t + slackBound p d t b hb)
    (hFringeSend : ∀ (b : KBag p.br d) (r : Nat)
        (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
      ((b.strangers (r + 1) perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
        ip.epsF *
          ((b.parent (br_ge_one p)).strangers r perm
            (pl.regs (b.parent (br_ge_one p))) (br_ge_one p) : Rat)) :
    AbstractParentResidue p ip d t pl perm pl' perm' step :=
  AbstractParentResidue.ofQualityRouting p ip d t pl pl' perm perm' step
    (fun b hb => LocalSeparatorQuality.ofTheorem51 ip
      (capacity p d (b.l - 1) t) (ha b hb))
    (fun b hb => by
      change (LocalSeparatorQuality.ofTheorem51 ip
          (capacity p d (b.l - 1) t) (ha b hb)).a ≤ capacity p d (b.l - 1) t
      simp [LocalSeparatorQuality.ofTheorem51, LocalSeparatorQuality.ofBF,
        PropertyB.ofEps])
    (fun b hb => by
      simpa [LocalSeparatorQuality.ofTheorem51, LocalSeparatorQuality.ofBF,
        PropertyB.ofEps] using hBadSend0 b hb)
    (fun b r hr1 hrd hb => by
      simpa [LocalSeparatorQuality.ofTheorem51, LocalSeparatorQuality.ofBF,
        PropertyF.ofEps] using hFringeSend b r hr1 hrd hb)

/-- Discharge `AbstractParentResidue` from Thm 5.1 routing bounds; parent
    capacity is positive via `capacity_pos`. -/
def AbstractParentResidue.ofTheorem51BudgetRouting
    (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (step : PlacementStep p d pl pl')
    (R : AbstractParentResidueRouting p ip d t pl pl' perm perm' step) :
    AbstractParentResidue p ip d t pl perm pl' perm' step :=
  AbstractParentResidue.ofTheorem51Routing p ip d t pl pl' perm perm' step
    (fun b _hb => capacity_pos p d (b.l - 1) t) R.hBadSend0 R.hFringeSend

/-- Same-perm preferNon stage: children data + Thm 5.1 routing ⇒ full stage. -/
def PreferNonStageObligation.of_children_and_routing
    (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (C : PreferNonStageChildrenData p d t pl pl' perm)
    (R : AbstractParentResidueRouting p ip d t pl pl' perm perm
      (placementStep_of_preferNon p d t pl pl' perm C.fromParent C.hregs)) :
    PreferNonStageObligation p ip d t pl pl' perm :=
  PreferNonStageObligation.of_childrenData C
    (AbstractParentResidue.ofTheorem51BudgetRouting p ip d t pl pl' perm perm
      (placementStep_of_preferNon p d t pl pl' perm C.fromParent C.hregs) R)

/-- Same stage from children data + full parent residue (not only routing bounds). -/
def PreferNonStageObligation.of_children_and_residue
    (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (C : PreferNonStageChildrenData p d t pl pl' perm)
    (parent : AbstractParentResidue p ip d t pl perm pl' perm
      (placementStep_of_preferNon p d t pl pl' perm C.fromParent C.hregs)) :
    PreferNonStageObligation p ip d t pl pl' perm :=
  PreferNonStageObligation.of_childrenData C parent

/-! **Residue ↔ routing budgets; §4 residue collapse** -/

/-- `AbstractParentResidue` implies the paper `εB`/`εF` routing interface. -/
def AbstractParentResidueRouting.of_residue
    (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (step : PlacementStep p d pl pl')
    (R : AbstractParentResidue p ip d t pl perm pl' perm' step) :
    AbstractParentResidueRouting p ip d t pl pl' perm perm' step where
  hBadSend0 := fun b hb =>
    (R.hBadSend0 b hb).trans (by
      gcongr
      exact (R.parentSep b hb).hIntrusion.trans
        (mul_le_mul_of_nonneg_left (R.ha_le_cap b hb) ip.hepsB_nonneg))
  hFringeSend := fun b r hr1 hrd hb =>
    (R.hFringeSend b r hr1 hrd hb).trans
      ((R.parentSep b hb).hFringe
        ((b.parent (br_ge_one p)).strangers r perm
          (pl.regs (b.parent (br_ge_one p))) (br_ge_one p)))

theorem AbstractParentResidue.toRouting
    (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (step : PlacementStep p d pl pl')
    (R : AbstractParentResidue p ip d t pl perm pl' perm' step) :
    AbstractParentResidueRouting p ip d t pl pl' perm perm' step :=
  AbstractParentResidueRouting.of_residue p ip d t pl pl' perm perm' step R

/-- Collapse `StageRoutingResidue` sibling/slack budgets to the kernel bounds. -/
def AbstractParentResidue.of_stageRoutingResidue
    (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (R : StageRoutingResidue p ip d sched t pl perm pl' perm') :
    AbstractParentResidue p ip d t pl perm pl' perm' R.step where
  parentSep := R.parentSep
  ha_le_cap := R.ha_le_cap
  hBadSend0 := fun b hb =>
    (R.hBadSend0 b hb).trans
      (add_le_add (add_le_add (add_le_add le_rfl (R.hSibMass0 b hb)) le_rfl)
        (R.hSlack0 b hb))
  hFringeSend := R.hFringeSend

def AbstractParentResidueRouting.of_stageRoutingResidue
    (p : ScheduleParams) (ip : InvariantParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (R : StageRoutingResidue p ip d sched t pl perm pl' perm') :
    AbstractParentResidueRouting p ip d t pl pl' perm perm' R.step :=
  AbstractParentResidueRouting.of_residue p ip d t pl pl' perm perm' R.step
    (AbstractParentResidue.of_stageRoutingResidue p ip d sched t pl pl' perm perm' R)

theorem PreferNonStageObligation.routing_of_residue
    (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm : Fin (p.br ^ d) → Fin (p.br ^ d))
    (O : PreferNonStageObligation p ip d t pl pl' perm) :
    AbstractParentResidueRouting p ip d t pl pl' perm perm O.step :=
  AbstractParentResidue.toRouting p ip d t pl pl' perm perm O.step O.parent

end Chvatal
