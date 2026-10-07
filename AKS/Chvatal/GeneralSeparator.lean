module

/-
  # Thm 5.1 separators for every geometry `m ≥ 100`, `n ≥ 16`, `f ≥ 1.7·10^10`

  Combines the pipeline Property B failure bound (`lemma61_failFactor < 1/100`) with the
  corrected paper Property F failure bound (`≤ 0.44`, `Lemma62Round` + `Lemma62FailE`) by
  pigeonhole, and the corrected F-bridge (`Lemma62Bridge`) to the canonical
  sort–scramble–sort pack. This replaces the `δ_F n < 1` shortcut (valid only for `n ≤ 31`).
-/

public import AKS.Chvatal.ModuleABridge
public import AKS.Chvatal.Lemma62FailE
public import AKS.Chvatal.Lemma62Round
public import AKS.Chvatal.Lemma62Bridge

@[expose] public section

namespace Chvatal

open Classical in
/-- The corrected paper Property F fails for at most `44%` of the scrambles. -/
theorem paperF_fail_fraction_final {m n f : ℕ} (hf : Even f) (hfm : f ≤ m)
    (hfbig : 17 * 10 ^ 9 ≤ f) (hn : 16 ≤ n) :
    (((Finset.univ.filter fun σ : Scramble m n =>
        ¬ HasPaperPropertyF hf σ (128 / 4095) eps).card : ℝ) ≤
      44 / 100 * (Fintype.card (Scramble m n) : ℝ)) :=
  paperF_fail_fraction hf hfm hfbig hn
    (fun j E hE1 hE P => fail_prob_at_E hf (128 / 4095) j E hE1 hE P)

/-- Semantic Property F is monotone in `δ_F` (down) and `ε_F` (up). -/
theorem HasPackSemanticPropertyF.mono {m n f : ℕ} (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (hfm : f ≤ m) {δ δ' ε ε' : ℝ}
    (hδ : δ' ≤ δ) (hε : ε ≤ ε') (h : HasPackSemanticPropertyF hn pack f hfm δ ε) :
    HasPackSemanticPropertyF hn pack f hfm δ' ε' := by
  rw [HasPackSemanticPropertyF_iff] at h ⊢
  intro v j hj hjδ
  have hfn : (0 : ℝ) ≤ (f : ℝ) * n := by positivity
  have hjδ0 : (j : ℝ) ≤ δ * (f * n) :=
    le_trans hjδ (mul_le_mul_of_nonneg_right hδ hfn)
  have h1 := h v j hj hjδ0
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  calc _ < ε * j := h1
    _ ≤ ε' * j := mul_le_mul_of_nonneg_right hε hj0

/-- **Thm 5.1 for general geometry.** For every `ScrambleGeometry` (so `m ≥ 100`, `n ≥ 16`)
    with `f ≥ 1.7·10^10` and parameters with `δ_F ≤ 128/4095`, `ε_F ≥ 1/(8·10^7)`, a scramble
    with Property B (pipeline) and Property F exists, giving a semantic separator. -/
theorem ExistsScrambleSeparator_general {g : ScrambleGeometry} {P : Theorem51Params g}
    (hfbig : 17 * 10 ^ 9 ≤ g.f) (hδ : P.deltaF ≤ 128 / 4095) (hε : eps ≤ P.epsF) :
    ExistsScrambleSeparator g P := by
  classical
  have hm := g.hm
  have hn := g.hn
  have hmpos : 0 < g.m := lt_of_lt_of_le (by norm_num) hm
  have hnpos := scrambleGeometry_hn g
  let O := DecodeMatrixClassObligation.standard hmpos hnpos (Nat.succ_le_of_lt hmpos)
    (Nat.succ_le_of_lt hnpos) P.hepsB_lb
  have hBfail := lemma61FailBound_onPipeline_of_decodeClass P.epsB O
  have hfac : lemma61_failFactor g.m g.n < 1 / 100 :=
    lemma61_failFactor_lt_one_hundredth g.m g.n hm hn
  have hfm : g.f ≤ g.m := scrambleGeometry_f_le_m g
  have hFfail := paperF_fail_fraction_final g.hfeven hfm hfbig hn
  have hNpos : (0 : ℝ) < (Fintype.card (Scramble g.m g.n) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble g.m g.n))
  have hex : ∃ σ : Scramble g.m g.n, HasCombinatorialPropertyBOnPipeline σ P.epsB ∧
      HasPaperPropertyF g.hfeven σ (128 / 4095) eps := by
    by_contra hno
    push_neg at hno
    set badB := Finset.univ.filter fun σ : Scramble g.m g.n =>
      ¬ HasCombinatorialPropertyBOnPipeline σ P.epsB with hbadB
    set badF := Finset.univ.filter fun σ : Scramble g.m g.n =>
      ¬ HasPaperPropertyF g.hfeven σ (128 / 4095) eps with hbadF
    have hBle := hBfail.bound badB (fun σ hσ => by
      simpa [hbadB] using hσ)
    have hcover : (Finset.univ : Finset (Scramble g.m g.n)) ⊆ badB ∪ badF := by
      intro σ _
      by_cases hB : HasCombinatorialPropertyBOnPipeline σ P.epsB
      · have := hno σ hB
        exact Finset.mem_union_right _ (by simpa [hbadF] using this)
      · exact Finset.mem_union_left _ (by simpa [hbadB] using hB)
    have hcard : (Fintype.card (Scramble g.m g.n) : ℝ) ≤ (badB.card : ℝ) + (badF.card : ℝ) := by
      have h1 := Finset.card_le_card hcover
      have h2 := Finset.card_union_le badB badF
      simp only [Finset.card_univ] at h1
      exact_mod_cast h1.trans h2
    have hfacN : lemma61_failFactor g.m g.n * (Fintype.card (Scramble g.m g.n) : ℝ) ≤
        1 / 100 * (Fintype.card (Scramble g.m g.n) : ℝ) :=
      mul_le_mul_of_nonneg_right hfac.le hNpos.le
    linarith
  obtain ⟨σ, hBσ, hFσ⟩ := hex
  let pack := canonicalSortScrambleSortPack g.m g.n hnpos σ
  have hBsem : HasPackSemanticPropertyB hnpos pack P.epsB :=
    HasPackSemanticPropertyB_canonical_of_combinatorial_onPipeline hnpos σ hBσ
  have hF0 : HasPackSemanticPropertyF hnpos pack g.f hfm (128 / 4095) eps :=
    HasPackSemanticPropertyF.of_paperF (hf := g.hfeven) hnpos hfm (by norm_num) (by norm_num)
      (IdealColumnSort.all_packs hnpos) (RowScrambleCorrect.all_packs_forall hnpos) pack
      (fun c j hc hj hjδ S => hFσ c j hc hj hjδ S)
  have hFsem : HasPackSemanticPropertyF hnpos pack g.f (scrambleGeometry_f_le_m g)
      P.deltaF P.epsF :=
    HasPackSemanticPropertyF.mono hnpos pack hfm hδ hε hF0
  exact ⟨ScrambleSeparatorWitness.ofSemanticSeparator ⟨σ, pack, hBsem, hFsem⟩⟩

end Chvatal
