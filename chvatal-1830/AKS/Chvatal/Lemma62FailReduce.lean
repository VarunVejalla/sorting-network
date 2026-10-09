module

public import AKS.Chvatal.Lemma62
public import AKS.Chvatal.Lemma62Tail
public import AKS.Chvatal.Lemma62TopsCount

/-! # Reduction of the Property-F failure set to tail events (Chvátal Lemma 6.2 (ii))

`badSetF hf j` is the set of scrambles on which some `c` with `totalColumnOnes c = j` and some column
set `S` realise `fringeColumnEventBad`.  `badSetF_card_le`: a union bound over the tops of `c`
(the fringe count only depends on the top), each top being represented by one matrix. -/

@[expose] public section

namespace Chvatal

/-- Failure set: some monotone `c` with exactly `j` ones and some `S` realise the fringe event. -/
noncomputable def badSetF {m n f : Nat} (hf : Even f) (deltaF epsF : ℝ) (j : Nat) :
    Finset (Scramble m n) := by
  classical
  exact Finset.univ.filter fun σ =>
    ∃ c : MonotoneColumnSums m n, totalColumnOnes c = j ∧
      ∃ S : Finset (Fin n), fringeColumnEventBad hf deltaF epsF c σ j S

/-- The fringe count depends only on the tops `(c col) - f/2`. -/
theorem event_depends_only_on_top {m n f : Nat} (hf : Even f)
    (c c' : MonotoneColumnSums m n)
    (htop : ∀ col, (c col).val - f / 2 = (c' col).val - f / 2)
    (σ : Scramble m n) (S : Finset (Fin n)) :
    onesAboveHalfFringe hf c σ S = onesAboveHalfFringe hf c' σ S := by
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r.val < m - f / 2 := by simpa [aboveHalfFringeRows] using hr
  have hrow : monotoneRowOnes c r = monotoneRowOnes c' r := by
    ext col
    simp only [monotoneRowOnes, Finset.mem_filter, Finset.mem_univ, true_and]
    have := htop col
    omega
  unfold rowHit
  rw [hrow]

/-- The top of a monotone matrix as a function `Fin n → ℕ`. -/
def topOf {m n : Nat} (h : Nat) (c : MonotoneColumnSums m n) : Fin n → ℕ :=
  fun col => (c col).val - h

/-- `|badSetF| ≤ |tops| · B · |Scramble|`, given the per-matrix tail-sum bound `B` for matrices with
exactly `j` ones (and `0 < epsF`, `0 < j`, `0 ≤ B`). -/
theorem badSetF_card_le {m n f : Nat} (hf : Even f) (deltaF epsF : ℝ) (hε : 0 < epsF)
    (j : Nat) (hj : 0 < j) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ c : MonotoneColumnSums m n, totalColumnOnes c = j →
      ∑ s ∈ Finset.Icc 1 n,
        ((tailBadSet c (topRows m (f / 2)) s ((f / 2 : ℝ) * s + epsF * j)).card : ℝ) ≤
          B * (Fintype.card (Scramble m n) : ℝ)) :
    ((badSetF (m := m) (n := n) hf deltaF epsF j).card : ℝ) ≤
      ((tops (f / 2) n j).card : ℝ) * B * (Fintype.card (Scramble m n) : ℝ) := by
  classical
  let P : (Fin n → ℕ) → Prop := fun t =>
    ∃ c : MonotoneColumnSums m n, totalColumnOnes c = j ∧ topOf (f / 2) c = t
  let rep : (Fin n → ℕ) → MonotoneColumnSums m n := fun t =>
    if h : P t then Classical.choose h else fun _ => 0
  have hrep : ∀ t, P t → totalColumnOnes (rep t) = j ∧ topOf (f / 2) (rep t) = t := fun t ht => by
    simp only [rep, dif_pos ht]
    exact Classical.choose_spec ht
  let I : Finset (Fin n → ℕ) := (tops (f / 2) n j).filter P
  let U : (Fin n → ℕ) → ℕ → Finset (Scramble m n) := fun t s =>
    tailBadSet (rep t) (topRows m (f / 2)) s ((f / 2 : ℝ) * s + epsF * j)
  have hsub : badSetF hf deltaF epsF j ⊆ I.biUnion fun t => (Finset.Icc 1 n).biUnion (U t) := by
    intro σ hσ
    simp only [badSetF, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨c, hc, S, hS⟩ := hσ
    have hPt : P (topOf (f / 2) c) := ⟨c, hc, rfl⟩
    obtain ⟨-, hrt⟩ := hrep _ hPt
    have hS' : fringeColumnEventBad hf deltaF epsF (rep (topOf (f / 2) c)) σ j S := by
      unfold fringeColumnEventBad at hS ⊢
      rwa [event_depends_only_on_top hf _ c
        (fun col => by simpa [topOf] using congrFun hrt col) σ S]
    have h' : (f / 2 : ℝ) * S.card + epsF * j ≤
        (onesInRows (rep (topOf (f / 2) c)) σ (topRows m (f / 2)) S : ℝ) := hS'
    have hne : S.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      have := mul_pos hε (show (0 : ℝ) < j by exact_mod_cast hj)
      simp [onesInRows] at h'
      linarith
    refine Finset.mem_biUnion.mpr ⟨_, Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨fun col => (c col).val, mem_sset.mpr hc.le, rfl⟩, hPt⟩,
      Finset.mem_biUnion.mpr ⟨S.card, ?_, ?_⟩⟩
    · rw [Finset.mem_Icc]
      exact ⟨hne.card_pos, by simpa using Finset.card_le_univ S⟩
    · simp only [U, tailBadSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩, h'⟩
  have h2 : ((badSetF (m := m) (n := n) hf deltaF epsF j).card : ℝ) ≤
      ∑ t ∈ I, ∑ s ∈ Finset.Icc 1 n, ((U t s).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans
      ((Finset.card_biUnion_le).trans (Finset.sum_le_sum fun t _ => Finset.card_biUnion_le))
  have hN : (0 : ℝ) ≤ B * (Fintype.card (Scramble m n) : ℝ) := by positivity
  calc ((badSetF hf deltaF epsF j).card : ℝ)
      ≤ ∑ t ∈ I, B * (Fintype.card (Scramble m n) : ℝ) :=
        h2.trans (Finset.sum_le_sum fun t ht => hB (rep t) (hrep t (Finset.mem_filter.mp ht).2).1)
    _ = (I.card : ℝ) * (B * (Fintype.card (Scramble m n) : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((tops (f / 2) n j).card : ℝ) * (B * (Fintype.card (Scramble m n) : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) hN
    _ = _ := by ring

end Chvatal
