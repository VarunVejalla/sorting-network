module

public import AKS.Chvatal.Lemma63

/-! # Chvátal Lemma 6.2: fringe-row model (DCS-TR-294, §6) -/

@[expose] public section

namespace Chvatal

/-- Rows strictly above the bottom `f/2` block (paper Lemma 6.2). -/
def aboveHalfFringeRows (m f : Nat) (_hf : Even f) : Finset (Fin m) :=
  Finset.univ.filter fun r => r.val < m - f / 2

def onesAboveHalfFringe {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (S : Finset (Fin n)) : Nat :=
  ∑ r ∈ aboveHalfFringeRows m f hf, rowHit c S r (σ r)

/-- Paper event `E` at `(c,j,S)` for a fixed scramble (Lemma 6.2). -/
def fringeColumnEventBad {m n f : Nat} (hf : Even f) (_deltaF epsF : ℝ)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (j : Nat) (S : Finset (Fin n)) :
    Prop :=
  (f / 2 : ℝ) * S.card + epsF * j ≤ (onesAboveHalfFringe hf c σ S : ℝ)

theorem finset_card (n : Nat) :
    Fintype.card (Finset (Fin n)) = 2 ^ n := by
  simp

end Chvatal
