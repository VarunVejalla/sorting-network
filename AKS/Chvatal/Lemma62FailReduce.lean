module

/-
  # Reduction of the Property-F failure set to tail events (Chvátal Lemma 6.2, claim (ii))

  Source: V. Chvátal, DCS-TR-294 (1992), proof of Lemma 6.2.

  The existing `HasCombinatorialPropertyF` quantifies over all monotone `c` with no tie between
  `j` and the number of ones of `c`; we therefore use the corrected event class
  `totalColumnOnes c = j`, and define `badSetF hf j` as the scrambles on which some such `c`
  and column set `S` realise `fringeColumnEventBad`.

  * `event_depends_only_on_top` (R1): the fringe count depends only on the top of `c`.
  * `tail_event_of_fringe_event` (R2): the fringe event implies membership in a `tailBadSet`.
  * `badSetF_card_le` (R3): union bound over the tops, with a representative per top.
-/

public import AKS.Chvatal.Lemma62
public import AKS.Chvatal.Lemma62Tail
public import AKS.Chvatal.Lemma62TopsCount

@[expose] public section

namespace Chvatal

/-- Corrected failure set: some monotone `c` with exactly `j` ones and some `S` realise the
fringe event. -/
noncomputable def badSetF {m n f : Nat} (hf : Even f) (deltaF epsF : ℝ) (j : Nat) :
    Finset (Scramble m n) := by
  classical
  exact Finset.univ.filter fun σ =>
    ∃ c : MonotoneColumnSums m n, totalColumnOnes c = j ∧
      ∃ S : Finset (Fin n), fringeColumnEventBad hf deltaF epsF c σ j S

/-- R1: the fringe count depends only on the tops `(c col) - f/2`. -/
theorem event_depends_only_on_top {m n f : Nat} (hf : Even f)
    (c c' : MonotoneColumnSums m n)
    (htop : ∀ col, (c col).val - f / 2 = (c' col).val - f / 2)
    (σ : Scramble m n) (S : Finset (Fin n)) :
    onesAboveHalfFringe hf c σ S = onesAboveHalfFringe hf c' σ S := by
  unfold onesAboveHalfFringe
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r.val < m - f / 2 := by
    simpa [aboveHalfFringeRows] using hr
  have hrow : monotoneRowOnes c r = monotoneRowOnes c' r := by
    ext col
    simp only [monotoneRowOnes, Finset.mem_filter, Finset.mem_univ, true_and]
    have := htop col
    omega
  unfold rowHit
  rw [hrow]

theorem aboveHalfFringeRows_eq_topRows (m f : Nat) (hf : Even f) :
    aboveHalfFringeRows m f hf = topRows m (f / 2) := rfl

theorem onesAboveHalfFringe_eq_onesInRows {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (S : Finset (Fin n)) :
    onesAboveHalfFringe hf c σ S = onesInRows c σ (topRows m (f / 2)) S := rfl

/-- R2: the fringe event gives a nonempty `S` and membership in the tail set
(`0 < epsF` is needed for nonemptiness). -/
theorem tail_event_of_fringe_event {m n f : Nat} (hf : Even f) (deltaF epsF : ℝ)
    (hε : 0 < epsF) (c : MonotoneColumnSums m n) (σ : Scramble m n) (j : Nat) (hj : 0 < j)
    (S : Finset (Fin n)) (h : fringeColumnEventBad hf deltaF epsF c σ j S) :
    S.Nonempty ∧
      σ ∈ tailBadSet c (topRows m (f / 2)) S.card ((f / 2 : ℝ) * S.card + epsF * j) := by
  classical
  have h' : (f / 2 : ℝ) * S.card + epsF * j ≤
      (onesInRows c σ (topRows m (f / 2)) S : ℝ) := by
    have := h
    unfold fringeColumnEventBad at this
    rwa [onesAboveHalfFringe_eq_onesInRows] at this
  refine ⟨?_, ?_⟩
  · by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    have h0 : onesInRows c σ (topRows m (f / 2)) (∅ : Finset (Fin n)) = 0 := by
      simp [onesInRows]
    rw [h0] at h'
    have : (0 : ℝ) < epsF * j := mul_pos hε (by exact_mod_cast hj)
    simp at h'
    linarith
  · simp only [tailBadSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩, h'⟩

/-- The top of a monotone matrix as a function `Fin n → ℕ`. -/
def topOf {m n : Nat} (h : Nat) (c : MonotoneColumnSums m n) : Fin n → ℕ :=
  fun col => (c col).val - h

theorem topOf_mem_tops {m n : Nat} (h j : Nat) (c : MonotoneColumnSums m n)
    (hc : totalColumnOnes c = j) : topOf h c ∈ tops h n j := by
  unfold tops topOf
  refine Finset.mem_image.mpr ⟨fun col => (c col).val, mem_sset.mpr ?_, rfl⟩
  exact hc.le

/-- R3 (main): `|badSetF| ≤ |tops| · B · |Scramble|`, given the per-matrix tail-sum bound `B`
for matrices with exactly `j` ones.  Extra hypotheses: `0 < j`, `0 < epsF` (for R2) and
`0 ≤ B` (so that tops without a witness matrix cost nothing). -/
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
  have hrep : ∀ t, P t → totalColumnOnes (rep t) = j ∧ topOf (f / 2) (rep t) = t := by
    intro t ht
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
    obtain ⟨hrc, hrt⟩ := hrep _ hPt
    set t := topOf (f / 2) c with ht
    have hS' : fringeColumnEventBad hf deltaF epsF (rep t) σ j S := by
      unfold fringeColumnEventBad at hS ⊢
      rw [event_depends_only_on_top hf (rep t) c
        (fun col => by have := congrFun hrt col; simpa [topOf] using this) σ S]
      exact hS
    obtain ⟨hne, hmem⟩ := tail_event_of_fringe_event hf deltaF epsF hε (rep t) σ j hj S hS'
    refine Finset.mem_biUnion.mpr ⟨t, Finset.mem_filter.mpr
      ⟨topOf_mem_tops _ _ c hc, hPt⟩, Finset.mem_biUnion.mpr ⟨S.card, ?_, hmem⟩⟩
    rw [Finset.mem_Icc]
    exact ⟨hne.card_pos, by simpa using Finset.card_le_univ S⟩
  have h1 : (badSetF hf deltaF epsF j).card ≤
      ∑ t ∈ I, ∑ s ∈ Finset.Icc 1 n, (U t s).card :=
    (Finset.card_le_card hsub).trans
      ((Finset.card_biUnion_le).trans (Finset.sum_le_sum fun t _ => Finset.card_biUnion_le))
  have h2 : ((badSetF (m := m) (n := n) hf deltaF epsF j).card : ℝ) ≤
      ∑ t ∈ I, ∑ s ∈ Finset.Icc 1 n, ((U t s).card : ℝ) := by
    exact_mod_cast h1
  have h3 : ∀ t ∈ I, ∑ s ∈ Finset.Icc 1 n, ((U t s).card : ℝ) ≤
      B * (Fintype.card (Scramble m n) : ℝ) := by
    intro t ht
    exact hB (rep t) (hrep t (Finset.mem_filter.mp ht).2).1
  have hN : (0 : ℝ) ≤ B * (Fintype.card (Scramble m n) : ℝ) := by positivity
  calc ((badSetF hf deltaF epsF j).card : ℝ)
      ≤ ∑ t ∈ I, B * (Fintype.card (Scramble m n) : ℝ) :=
        h2.trans (Finset.sum_le_sum h3)
    _ = (I.card : ℝ) * (B * (Fintype.card (Scramble m n) : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((tops (f / 2) n j).card : ℝ) * (B * (Fintype.card (Scramble m n) : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hN
        exact_mod_cast Finset.card_filter_le _ _
    _ = _ := by ring

end Chvatal
