module
/-
  # Chvátal Lemma 6.2 — fringe-row product Chernoff

  Clones the scramble MGF and exp bound from Lemma 6.3, restricted to rows in
  `aboveHalfFringeRows`. Status: kernel-checked (`avg_exp_onesAboveHalfFringe_le`,
  `lemma62FringeExpBound`, paper bad-event ⇒ Chernoff threshold under
  `FringeOnesDensityLeHalfWidth`, `lemma62_exp_bound`, `Lemma62FringeCellBound.of_hyp`).
-/

public import AKS.Chvatal.Lemma62
public import AKS.Chvatal.Theorem51
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Chvatal

/-! ## Fringe-row MGF factorization -/






/-! ## Fringe average MGF (clone of `avg_exp_onesInColumns_le`) -/


/-! ## Fringe exp bound (clone of `lemma63ExpBound`) -/

/-- Paper fringe-row Chernoff: threshold `(p+t)·m_F·|S|` on `onesAboveHalfFringe`. -/
structure Lemma62FringeExpBound (m n f : Nat) (hf : Even f) : Prop where
  bound :
    ∀ (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (t : ℝ),
      0 < t →
      ∀ (bad : Finset (Scramble m n)),
        (∀ σ ∈ bad,
          (fringeOnesDensity hf c + t) * (fringeRowCount m f hf : ℝ) * S.card ≤
            (onesAboveHalfFringe hf c σ S : ℝ)) →
          (bad.card : ℝ) ≤
            Real.exp (-(2 * t ^ 2 * (fringeRowCount m f hf : ℝ) * S.card)) *
              (Fintype.card (Scramble m n) : ℝ)


/-! ## Paper bad event ⇒ fringe Chernoff threshold -/











/-! ## `(e m)^{-n}` algebraic bound (clone of `lemma61_exp_bound`) -/





/-! ## Per-cell bound `Lemma62FringeCellBound` -/







end Chvatal
