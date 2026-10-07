module
/-
  # Chvátal Properties B/F → LocalSeparatorQuality

  Source: V. Chvátal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §5–§6 (Thm 5.1).

  Status: definitional bridge from paper Properties B/F into
  `LocalSeparatorQuality`, and from quality + Finset routing bounds into
  `AbstractParentResidue`. Scramble-separator *existence* (Thm 5.1 / Lemmas
  6.1–6.2) is not constructed here.
-/

public import AKS.Chvatal.AbstractPlacement
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Chvatal

/-! **Properties B and F** -/

/-- Property B: intrusion into one child block is at most `epsB · a`. -/
structure PropertyB (ip : InvariantParams) where
  a : Rat
  ha_pos : 0 < a
  intrusion : Rat
  hIntrusion : intrusion ≤ ip.epsB * a

/-- Property F: fringe image of a source mass is at most `epsF · src`. -/
structure PropertyF (ip : InvariantParams) where
  fringeSent : Rat → Rat
  hFringe : ∀ src, fringeSent src ≤ ip.epsF * src

/-- Combine B/F into the stage-kernel separator quality interface. -/
def LocalSeparatorQuality.ofBF (ip : InvariantParams)
    (B : PropertyB ip) (F : PropertyF ip) : LocalSeparatorQuality ip where
  a := B.a
  ha_pos := B.ha_pos
  ha_le := fun c => B.a ≤ c
  intrusion := B.intrusion
  hIntrusion := B.hIntrusion
  fringeSent := F.fringeSent
  hFringe := F.hFringe

/-- Parent residue from separator quality plus the two Finset routing bounds
    (bad-send / fringe). This is the Thm 5.1 + routing interface. -/
def AbstractParentResidue.ofQualityRouting
    (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (step : PlacementStep p d pl pl')
    (parentSep : ∀ (b : KBag p.br d), 1 ≤ b.l → LocalSeparatorQuality ip)
    (ha_le_cap : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      (parentSep b hb).a ≤ capacity p d (b.l - 1) t)
    (hBadSend0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      ((b.strangers 1 perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
        parentOutMass p d pl perm b hb +
          sibMassBound p ip d t b hb +
          (parentSep b hb).intrusion + slackBound p d t b hb)
    (hFringeSend : ∀ (b : KBag p.br d) (r : Nat)
        (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
      ((b.strangers (r + 1) perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
        (parentSep b hb).fringeSent
          ((b.parent (br_ge_one p)).strangers r perm
            (pl.regs (b.parent (br_ge_one p))) (br_ge_one p) : Rat)) :
    AbstractParentResidue p ip d t pl perm pl' perm' step where
  parentSep := parentSep
  ha_le_cap := ha_le_cap
  hBadSend0 := hBadSend0
  hFringeSend := hFringeSend

/-- Same package with B/F witnesses per bag. -/
def AbstractParentResidue.ofBFRouting
    (p : ScheduleParams) (ip : InvariantParams) (d t : Nat)
    (pl pl' : Placement p.br d)
    (perm perm' : Fin (p.br ^ d) → Fin (p.br ^ d))
    (step : PlacementStep p d pl pl')
    (B : ∀ (b : KBag p.br d), 1 ≤ b.l → PropertyB ip)
    (F : ∀ (b : KBag p.br d), 1 ≤ b.l → PropertyF ip)
    (ha_le_cap : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      (B b hb).a ≤ capacity p d (b.l - 1) t)
    (hBadSend0 : ∀ (b : KBag p.br d) (hb : 1 ≤ b.l),
      ((b.strangers 1 perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
        parentOutMass p d pl perm b hb +
          sibMassBound p ip d t b hb +
          (B b hb).intrusion + slackBound p d t b hb)
    (hFringeSend : ∀ (b : KBag p.br d) (r : Nat)
        (_hr1 : 1 ≤ r) (_hrd : r ≤ d) (hb : 1 ≤ b.l),
      ((b.strangers (r + 1) perm' (step.fromParent b hb) (br_ge_one p) : Rat)) ≤
        (F b hb).fringeSent
          ((b.parent (br_ge_one p)).strangers r perm
            (pl.regs (b.parent (br_ge_one p))) (br_ge_one p) : Rat)) :
    AbstractParentResidue p ip d t pl perm pl' perm' step :=
    AbstractParentResidue.ofQualityRouting p ip d t pl pl' perm perm' step
    (fun b hb => LocalSeparatorQuality.ofBF ip (B b hb) (F b hb))
    ha_le_cap hBadSend0 hFringeSend

end Chvatal
