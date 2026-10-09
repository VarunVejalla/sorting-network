module

public import AKS.Chvatal.Lemma63

/-! # Chvátal Lemma 6.2: fringe-row model (DCS-TR-294, §6) -/

@[expose] public section

namespace Chvatal

/-- The rows strictly above the bottom `h` rows (the "top `m - h` rows"). -/
def topRows (m h : Nat) : Finset (Fin m) :=
  Finset.univ.filter fun r => r.val < m - h

def onesAboveHalfFringe {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (S : Finset (Fin n)) : Nat :=
  ∑ r ∈ topRows m (f / 2), rowHit c S r (σ r)

/-- Paper event `E` at `(c,j,S)` for a fixed scramble (Lemma 6.2). -/
def fringeColumnEventBad {m n f : Nat} (hf : Even f) (_deltaF epsF : ℝ)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (j : Nat) (S : Finset (Fin n)) :
    Prop :=
  (f / 2 : ℝ) * S.card + epsF * j ≤ (onesAboveHalfFringe hf c σ S : ℝ)

theorem cast_half_of_even {f : ℕ} (hf : Even f) : ((f / 2 : ℕ) : ℝ) = (f : ℝ) / 2 := by
  obtain ⟨k, rfl⟩ := hf
  push_cast [show (k + k) / 2 = k by omega]; ring

end Chvatal
