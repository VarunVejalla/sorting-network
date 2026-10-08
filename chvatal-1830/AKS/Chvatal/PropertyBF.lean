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




end Chvatal
