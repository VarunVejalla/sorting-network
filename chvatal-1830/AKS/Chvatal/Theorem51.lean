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





/-! **Residue ↔ routing budgets; §4 residue collapse** -/






end Chvatal
