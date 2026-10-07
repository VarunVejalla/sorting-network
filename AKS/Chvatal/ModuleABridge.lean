module
/-
  Module A §7 bridge: residual α+β, combinatorial B∧F existence → `ExistsScrambleSeparator`.
  Split from `ModuleA.lean` so Lemma 6.1/6.2 counting proofs keep a separate heartbeat budget.
-/

public import AKS.Chvatal.ModuleA
public import AKS.Chvatal.PaperScrambleNumerics

set_option maxHeartbeats 2000000

@[expose] public section

namespace Chvatal
/-! **Combinatorial B∧F + matrix bridge → Theorem 5.1** -/

/-- Pipeline B uses `lemma61_failFactor` (one matrix per `matrixOnesLevel`); F uses `lemma62_failFactor`. -/
def ModuleACombinedFailFraction_m100 : Prop :=
  lemma61_failFactor 100 16 + lemma62_failFactor (3 / 10 : ℝ) < 1

theorem moduleACombinedFailFraction_m100 :
    ModuleACombinedFailFraction_m100 :=
  moduleA_global_failFraction_add_lt_one_m100

/-- Legacy nested-level pipeline factor `m · lemma61_failFactor` overshoots; crude `α+β` is not `< 1`. -/
theorem not_ModuleACombinedFailFraction_m100_crude :
    ¬ (lemma61_failFactor_pipeline 100 16 + lemma62_failFactor (3 / 10 : ℝ) < 1) := by
  intro h
  have hβ : (43 / 100 : ℝ) < lemma62_failFactor (3 / 10 : ℝ) := by
    rw [show (3 / 10 : ℝ) = Lemma62InnerBound.thirty.x from by simp [Lemma62InnerBound.thirty],
      lemma62_failFactor_thirty_eq]
    norm_num
  have hα := lemma61_failFactor_pipeline_100_16_gt_four_fifths
  have hsum :
      (4 / 5 : ℝ) + (43 / 100 : ℝ) <
        lemma61_failFactor_pipeline 100 16 + lemma62_failFactor (3 / 10 : ℝ) :=
    add_lt_add hα hβ
  have hone : (1 : ℝ) < 4 / 5 + 43 / 100 := by norm_num
  exact lt_irrefl _ (lt_trans hone (lt_trans hsum h))

theorem ModuleACombinatorialObligation.cast_F_inner {m n : Nat} {epsB : ℝ} {f : Nat}
    {hf : Even f} {deltaF epsF : ℝ} (hm : m = 100) (hn : n = 16)
    (O : ModuleACombinatorialObligation m n epsB f hf deltaF epsF) :
    (show ModuleACombinatorialObligation 100 16 epsB f hf deltaF epsF from
        cast (by simp [hm, hn]) O).F.inner = O.F.inner := by
  subst hm hn
  rfl

theorem moduleA_combined_failFraction_of_obligation {f : Nat} {hf : Even f}
    {epsB deltaF epsF : ℝ} (O : ModuleACombinatorialObligation 100 16 epsB f hf deltaF epsF)
    (hinner : O.F.inner = Lemma62InnerBound.thirty) :
    lemma61_failFactor 100 16 + lemma62_failFactor O.F.inner.x < 1 := by
  rw [hinner]
  dsimp [Lemma62InnerBound.thirty]
  exact moduleA_global_failFraction_add_lt_one_m100

private theorem HasCombinatorialPropertyBOnPipeline_cast_scramble {m n m' n' : Nat}
    (hm : m = m') (hn : n = n') {σ : Scramble m n} {epsB : ℝ}
    (h : HasCombinatorialPropertyBOnPipeline σ epsB) :
    HasCombinatorialPropertyBOnPipeline (cast (congrArg₂ Scramble hm hn) σ) epsB := by
  subst hm
  subst hn
  exact h

private theorem HasCombinatorialPropertyF_cast_scramble {m n m' n' f : Nat} (hf : Even f)
    (hm : m = m') (hn : n = n') {σ : Scramble m n} {deltaF epsF : ℝ}
    (h : HasCombinatorialPropertyF hf σ deltaF epsF) :
    HasCombinatorialPropertyF hf (cast (congrArg₂ Scramble hm hn) σ) deltaF epsF := by
  subst hm
  subst hn
  exact h

/-- Residual: some scramble has pipeline-class B and F (needs `α+β < 1` at paper numerics). -/
def ModuleACombinatorialExistence_onPipeline_m100 (f : Nat) (hf : Even f)
    (epsB deltaF epsF : ℝ) : Prop :=
  ExistsCombinatorialScrambleBF_onPipeline 100 16 f hf epsB deltaF epsF

/-- Residual: pipeline combinatorial B∧F + matrix bridge ⇒ `ExistsScrambleSeparator`
    (transport proof not kernel-checked here; see `MatrixBridge`). -/
def ModuleAPipelineBFImpliesScrambleSeparator_m100 (g : ScrambleGeometry) (P : Theorem51Params g) :
    Prop :=
  ExistsScrambleSeparator g P

theorem ExistsCombinatorialScrambleBF_onPipeline_of_ModuleA_m100 {epsB : ℝ} {f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (O : ModuleACombinatorialObligation 100 16 epsB f hf deltaF epsF)
    (hinner : O.F.inner = Lemma62InnerBound.thirty) :
    ExistsCombinatorialScrambleBF_onPipeline 100 16 f hf epsB deltaF epsF := by
  have hB := lemma61FailBound_onPipeline_of_decodeClass epsB O.B
  have hF := lemma62FailBound_of_cellExp O.F
  have hNpos : 0 < Fintype.card (Scramble 100 16) := scramble_card_pos 100 16
  have hαβ' :
      lemma61_failFactor 100 16 + lemma62_failFactor O.F.inner.x < 1 :=
    moduleA_combined_failFraction_of_obligation O hinner
  exact exists_combinatorialScrambleBF_onPipeline_of_failFractions 100 16 f hf epsB deltaF epsF
    O.F.inner.x hB hF hNpos hαβ'

theorem exists_combinatorialScrambleBF_onPipeline_of_ModuleA_m100 {f : Nat} {hf : Even f}
    {epsB deltaF epsF : ℝ} (O : ModuleACombinatorialObligation 100 16 epsB f hf deltaF epsF)
    (hinner : O.F.inner = Lemma62InnerBound.thirty) :
    ExistsCombinatorialScrambleBF_onPipeline 100 16 f hf epsB deltaF epsF :=
  ExistsCombinatorialScrambleBF_onPipeline_of_ModuleA_m100 O hinner

theorem ModuleACombinatorialExistence_onPipeline_of_obligation {f : Nat} {hf : Even f}
    {epsB deltaF epsF : ℝ} (O : ModuleACombinatorialObligation 100 16 epsB f hf deltaF epsF)
    (hinner : O.F.inner = Lemma62InnerBound.thirty) :
    ModuleACombinatorialExistence_onPipeline_m100 f hf epsB deltaF epsF :=
  ExistsCombinatorialScrambleBF_onPipeline_of_ModuleA_m100 O hinner

/-- Kernel-checked: pipeline combinatorial B∧F + matrix bridge ⇒ `ExistsScrambleSeparator`. -/
theorem ModuleAPipelineBFImpliesScrambleSeparator_m100_discharged
    {g : ScrambleGeometry} {P : Theorem51Params g}
    (hm : g.m = 100) (hn : g.n = 16)
    {σ : Scramble 100 16}
    (hB : HasCombinatorialPropertyBOnPipeline σ P.epsB)
    (hF : HasCombinatorialPropertyF g.hfeven σ P.deltaF P.epsF)
    (bridge : CombinatorialToMatrixObligation g.m g.n g.f (scrambleGeometry_hn g) g.hfeven
      (scrambleGeometry_f_le_m g) P.epsB P.deltaF P.epsF) :
    ExistsScrambleSeparator g P := by
  let hnpos := scrambleGeometry_hn g
  let σg : Scramble g.m g.n := cast (congrArg₂ Scramble hm.symm hn.symm) σ
  let pack := canonicalSortScrambleSortPack g.m g.n hnpos σg
  have hBg := HasCombinatorialPropertyBOnPipeline_cast_scramble hm.symm hn.symm hB
  have hFg := HasCombinatorialPropertyF_cast_scramble g.hfeven hm.symm hn.symm hF
  have hBsem :
      HasPackSemanticPropertyB hnpos pack P.epsB :=
    HasPackSemanticPropertyB_canonical_of_combinatorial_onPipeline hnpos σg hBg
  exact ExistsScrambleSeparator_of_combinatorial_onPipeline_and_bridge (pack := pack) hnpos hBsem
    hFg (scrambleGeometry_f_le_m g) bridge

/-- Pipeline combinatorial obligation + matrix bridge ⇒ separator (no residual `hExist` / `hRes` / `hαβ`). -/
theorem ExistsScrambleSeparator_of_moduleACombinatorialObligation_m100
    {g : ScrambleGeometry} {P : Theorem51Params g}
    (hm : g.m = 100) (hn : g.n = 16)
    (O : ModuleACombinatorialObligation 100 16 P.epsB g.f g.hfeven P.deltaF P.epsF)
    (hinner : O.F.inner = Lemma62InnerBound.thirty)
    (bridge : CombinatorialToMatrixObligation g.m g.n g.f (scrambleGeometry_hn g) g.hfeven
      (scrambleGeometry_f_le_m g) P.epsB P.deltaF P.epsF) :
    ExistsScrambleSeparator g P := by
  obtain ⟨σ, hB, hF⟩ := ExistsCombinatorialScrambleBF_onPipeline_of_ModuleA_m100 O hinner
  exact ModuleAPipelineBFImpliesScrambleSeparator_m100_discharged hm hn (σ := σ) hB hF bridge

theorem ExistsScrambleSeparator_of_moduleA_and_bridge_m100
    {g : ScrambleGeometry} {P : Theorem51Params g}
    (_hm : g.m = 100) (_hn : g.n = 16)
    (_O : ModuleACombinatorialObligation 100 16 P.epsB g.f g.hfeven P.deltaF P.epsF)
    (_hαβ : ModuleACombinedFailFraction_m100)
    (_hinner : _O.F.inner = Lemma62InnerBound.thirty)
    (_hExist : ModuleACombinatorialExistence_onPipeline_m100 g.f g.hfeven P.epsB P.deltaF P.epsF)
    (_bridge : CombinatorialToMatrixObligation g.m g.n g.f (scrambleGeometry_hn g) g.hfeven
      (scrambleGeometry_f_le_m g) P.epsB P.deltaF P.epsF)
    (_rowScramble : ∀ σ : Scramble g.m g.n, RowScrambleNetwork g.m g.n σ)
    (hRes : ModuleAPipelineBFImpliesScrambleSeparator_m100 g P) :
    ExistsScrambleSeparator g P :=
  hRes

theorem ExistsScrambleSeparator_of_moduleA_and_bridge
    {g : ScrambleGeometry} {P : Theorem51Params g}
    (hm : g.m = 100) (hn : g.n = 16)
    (O : ModuleACombinatorialObligation g.m g.n P.epsB g.f g.hfeven P.deltaF P.epsF)
    (hαβ : ModuleACombinedFailFraction_m100)
    (hinner : O.F.inner = Lemma62InnerBound.thirty)
    (hExist : ModuleACombinatorialExistence_onPipeline_m100 g.f g.hfeven P.epsB P.deltaF P.epsF)
    (bridge : CombinatorialToMatrixObligation g.m g.n g.f (scrambleGeometry_hn g) g.hfeven
      (scrambleGeometry_f_le_m g) P.epsB P.deltaF P.epsF)
    (_rowScramble : ∀ σ : Scramble g.m g.n, RowScrambleNetwork g.m g.n σ)
    (hRes : ModuleAPipelineBFImpliesScrambleSeparator_m100 g P) :
    ExistsScrambleSeparator g P := by
  have hinner100 :
      (show ModuleACombinatorialObligation 100 16 P.epsB g.f g.hfeven P.deltaF P.epsF from
          cast (by simp [hm, hn]) O).F.inner = Lemma62InnerBound.thirty :=
    (ModuleACombinatorialObligation.cast_F_inner hm hn O).trans hinner
  exact ExistsScrambleSeparator_of_moduleA_and_bridge_m100 hm hn
    (cast (by simp [hm, hn]) O) hαβ hinner100 hExist bridge _rowScramble hRes

theorem Theorem51Obligation.of_moduleA_and_bridge
    {g : ScrambleGeometry} {P : Theorem51Params g}
    (hm : g.m = 100) (hn : g.n = 16)
    (O : ModuleACombinatorialObligation g.m g.n P.epsB g.f g.hfeven P.deltaF P.epsF)
    (hαβ : ModuleACombinedFailFraction_m100)
    (hinner : O.F.inner = Lemma62InnerBound.thirty)
    (hExist : ModuleACombinatorialExistence_onPipeline_m100 g.f g.hfeven P.epsB P.deltaF P.epsF)
    (bridge : CombinatorialToMatrixObligation g.m g.n g.f (scrambleGeometry_hn g) g.hfeven
      (scrambleGeometry_f_le_m g) P.epsB P.deltaF P.epsF)
    (_rowScramble : ∀ σ : Scramble g.m g.n, RowScrambleNetwork g.m g.n σ)
    (hRes : ModuleAPipelineBFImpliesScrambleSeparator_m100 g P) :
    Theorem51Obligation g P :=
  ⟨ExistsScrambleSeparator_of_moduleA_and_bridge hm hn O hαβ hinner hExist bridge _rowScramble
    hRes⟩

def Lemma61FailBoundObligation.of_params7_heps_m100 {epsB : ℝ}
    (heps : Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ epsB)
    (havg : AvgRowOnesLeOne 100 16) :
    Lemma61FailBoundObligation 100 16 epsB :=
  Lemma61FailBoundObligation.of_avgRowOnes_le_one (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) heps havg

def Lemma61FailBoundObligation.of_params7_heps_m100_total {epsB : ℝ}
    (heps : Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ epsB)
    (htotal : TotalColumnOnesLeN 100 16) :
    Lemma61FailBoundObligation 100 16 epsB :=
  Lemma61FailBoundObligation.of_totalColumnOnesLeN (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) heps htotal

noncomputable def ModuleACombinatorialObligation.of_params7_m100_n16 {f : Nat} {hf : Even f}
    {epsB deltaF epsF : ℝ}
    (hepsB : Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ epsB)
    (havg : AvgRowOnesLeOne 100 16)
    (hepsF : 0 < epsF) (hf2 : 2 ≤ f)
    (hmF : 1 ≤ fringeRowCount 100 f hf)
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log 100) * 16 * fringeRowCount 100 f hf * 16 / 2) ≤
        epsF)
    (hdeltaF : 0 ≤ deltaF) (hjMax48 : lemma62_jMax deltaF f 16 ≤ 48) :
    ModuleACombinatorialObligation 100 16 epsB f hf deltaF epsF :=
  ModuleACombinatorialObligation.of_decodeClass_and_cellCounting (by norm_num) (by norm_num)
    (DecodeMatrixClassObligation.standard (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hepsB)
    (Lemma62CellCountingObligation.m100_n16_jMax48 hdeltaF hepsF hf2 havg hmF hepsWorst hjMax48)

theorem ModuleACombinatorialObligation.of_params7_m100_n16_inner {f : Nat} {hf : Even f}
    {epsB deltaF epsF : ℝ}
    (hepsB : Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ epsB)
    (havg : AvgRowOnesLeOne 100 16) (hepsF : 0 < epsF) (hf2 : 2 ≤ f)
    (hmF : 1 ≤ fringeRowCount 100 f hf)
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log 100) * 16 * fringeRowCount 100 f hf * 16 / 2) ≤
        epsF)
    (hdeltaF : 0 ≤ deltaF) (hjMax48 : lemma62_jMax deltaF f 16 ≤ 48) :
    (ModuleACombinatorialObligation.of_params7_m100_n16 hepsB havg hepsF hf2 hmF hepsWorst
        hdeltaF hjMax48).F.inner =
      Lemma62InnerBound.thirty := by
  dsimp [ModuleACombinatorialObligation.of_params7_m100_n16,
    ModuleACombinatorialObligation.of_decodeClass_and_cellCounting,
    Lemma62CellCountingObligation.m100_n16_jMax48]
  rfl

/-- Same as `of_params7_m100_n16` but B-side uses only `hepsB` (decode class discharged). -/
noncomputable def ModuleACombinatorialObligation.of_params7_m100_n16_decode {f : Nat} {hf : Even f}
    {epsB deltaF epsF : ℝ}
    (hepsB : Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ epsB)
    (havg : AvgRowOnesLeOne 100 16)
    (hepsF : 0 < epsF) (hf2 : 2 ≤ f)
    (hmF : 1 ≤ fringeRowCount 100 f hf)
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log 100) * 16 * fringeRowCount 100 f hf * 16 / 2) ≤
        epsF)
    (hdeltaF : 0 ≤ deltaF) (hjMax48 : lemma62_jMax deltaF f 16 ≤ 48) :
    ModuleACombinatorialObligation 100 16 epsB f hf deltaF epsF :=
  of_params7_m100_n16 hepsB havg hepsF hf2 hmF hepsWorst hdeltaF hjMax48

/-- Same as `of_params7_m100_n16` with fringe Chernoff supplied as `Lemma62FringeCellBoundHyp`. -/
noncomputable def ModuleACombinatorialObligation.of_params7_m100_n16_fringe {f : Nat} {hf : Even f}
    {epsB deltaF epsF : ℝ}
    (hepsB : Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ epsB)
    (H : Lemma62FringeCellBoundHyp 100 16 f hf deltaF epsF)
    (hdeltaF : 0 ≤ deltaF) (hjMax48 : lemma62_jMax deltaF f 16 ≤ 48) :
    ModuleACombinatorialObligation 100 16 epsB f hf deltaF epsF :=
  ModuleACombinatorialObligation.of_decodeClass_and_cellCounting (by norm_num) (by norm_num)
    (DecodeMatrixClassObligation.standard (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hepsB)
    (Lemma62CellCountingObligation.m100_n16_jMax48_of_fringeHyp hdeltaF H hjMax48)

/-- Generic §7-style counting bundle at any `ScrambleGeometry` (not only `m = 100`, `n = 16`). -/
noncomputable def Lemma62CellCountingObligation.of_geometry_jMax {g : ScrambleGeometry}
    {deltaF epsF : ℝ} (hdeltaF : 0 ≤ deltaF) (hepsF : 0 < epsF)
    (havg : AvgRowOnesLeOne g.m g.n)
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log g.m) * g.n * fringeRowCount g.m g.f g.hfeven * g.n / 2) ≤
        epsF)
    (hclose :
      lemma62_cellUnionFactor g.m g.n (lemma62_jMax deltaF g.f g.n) ≤
        lemma62_failFactor Lemma62InnerBound.thirty.x) :
    Lemma62CellCountingObligation g.m g.n g.f g.hfeven deltaF epsF := by
  let jMax := lemma62_jMax deltaF g.f g.n
  refine of_avgRowOnes (scrambleGeometry_hn_pos (g := g)) hepsF (scrambleGeometry_hf2 (g := g)) havg
    (scrambleGeometry_hm_pos (g := g)) g.hm g.hn (scrambleGeometry_hm1 (g := g))
    (scrambleGeometry_hn1 (g := g)) (scrambleGeometry_hmF (g := g)) Lemma62InnerBound.thirty jMax
    (fun j hj hjδ => lemma62_jMax_hjMax j hj hjδ)
    (lemma62_jMax_le deltaF g.f g.n (lemma62_jMax_fn_nonneg g.f g.n hdeltaF)) hepsWorst hclose

def Lemma61FailBoundObligation.of_geometry_heps {g : ScrambleGeometry} {epsB : ℝ}
    (hepsB : Real.sqrt (2 * (1 + Real.log g.m) / g.m) ≤ epsB)
    (havg : AvgRowOnesLeOne g.m g.n) :
    Lemma61FailBoundObligation g.m g.n epsB :=
  Lemma61FailBoundObligation.of_avgRowOnes_le_one (scrambleGeometry_hm_pos (g := g))
    (scrambleGeometry_hn_pos (g := g)) (scrambleGeometry_hm1 (g := g)) (scrambleGeometry_hn1 (g := g))
    hepsB havg

def Lemma61FailBoundObligation.of_geometry_heps_total {g : ScrambleGeometry} {epsB : ℝ}
    (hepsB : Real.sqrt (2 * (1 + Real.log g.m) / g.m) ≤ epsB)
    (htotal : TotalColumnOnesLeN g.m g.n) :
    Lemma61FailBoundObligation g.m g.n epsB :=
  Lemma61FailBoundObligation.of_totalColumnOnesLeN (scrambleGeometry_hm_pos (g := g))
    (scrambleGeometry_hn_pos (g := g)) (scrambleGeometry_hm1 (g := g)) (scrambleGeometry_hn1 (g := g))
    hepsB htotal

noncomputable def ModuleACombinatorialObligation.of_scrambleGeometry {g : ScrambleGeometry}
    {epsB deltaF epsF : ℝ}
    (hepsB : Real.sqrt (2 * (1 + Real.log g.m) / g.m) ≤ epsB)
    (havg : AvgRowOnesLeOne g.m g.n)
    (hepsF : 0 < epsF) (hdeltaF : 0 ≤ deltaF)
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log g.m) * g.n * fringeRowCount g.m g.f g.hfeven * g.n / 2) ≤
        epsF)
    (hclose :
      lemma62_cellUnionFactor g.m g.n (lemma62_jMax deltaF g.f g.n) ≤
        lemma62_failFactor Lemma62InnerBound.thirty.x) :
    ModuleACombinatorialObligation g.m g.n epsB g.f g.hfeven deltaF epsF :=
  ModuleACombinatorialObligation.of_decodeClass_and_cellCounting g.hm g.hn
    (DecodeMatrixClassObligation.standard (scrambleGeometry_hm_pos (g := g))
      (scrambleGeometry_hn_pos (g := g)) (scrambleGeometry_hm1 (g := g)) (scrambleGeometry_hn1 (g := g))
      hepsB)
    (Lemma62CellCountingObligation.of_geometry_jMax hdeltaF hepsF havg hepsWorst hclose)

theorem not_TotalColumnOnesLeN_paperOrdinaryM :
    ¬ TotalColumnOnesLeN paperOrdinaryGeometry.m paperOrdinaryGeometry.n := by
  have hm : paperOrdinaryGeometry.m = paperOrdinaryM := rfl
  rw [hm]
  exact not_TotalColumnOnesLeN_of_m_gt_one (by decide) (by norm_num : 0 < 16)

noncomputable def ModuleACombinatorialObligation.of_params7Geometry_m100_n16 {f k b : Nat}
    {hf : Even f} (hf10 : 10 ≤ f) (hshape : 100 = 2 * f + k * b)
    {epsB deltaF epsF : ℝ}
    (hepsB : Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ epsB)
    (havg : AvgRowOnesLeOne 100 16)
    (hepsF : 0 < epsF)
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log 100) * 16 * fringeRowCount 100 f hf * 16 / 2) ≤
        epsF)
    (hdeltaF : 0 ≤ deltaF)
    (hdeltaF_eq : deltaF = invariant7.deltaF) :
    ModuleACombinatorialObligation 100 16 epsB f hf deltaF epsF :=
  ModuleACombinatorialObligation.of_params7_m100_n16 hepsB havg hepsF
    (params7Geometry_hf2 hf10)
    (params7Geometry_hmF hf hf10 hshape)
    hepsWorst hdeltaF
    (params7Geometry_hjMax48 hf hshape hdeltaF_eq)

/-! **§7 `m = 100`, `n = 16`: Module A + matrix bridge ⇒ `ExistsScrambleSeparator`** -/

theorem ExistsScrambleSeparator_params7_m100_n16
    {f k b : Nat} {hf : Even f} (hf10 : 10 ≤ f) (hshape : 100 = 2 * f + k * b)
    {P : Theorem51Params (params7Geometry f k b hf hf10 hshape)}
    (hPeps :
      P.epsB = (invariant7.epsB : ℝ) ∧ P.deltaF = (invariant7.deltaF : ℝ) ∧
        P.epsF = (invariant7.epsF : ℝ))
    (hepsB : Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ P.epsB)
    (havg : AvgRowOnesLeOne 100 16)
    (hf2 : 2 ≤ f) (hmF : 1 ≤ fringeRowCount 100 f hf)
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log 100) * 16 * fringeRowCount 100 f hf * 16 / 2) ≤
        P.epsF)
    (hjMax48 : lemma62_jMax P.deltaF f 16 ≤ 48)
    (hfm : f ≤ 100) (hfpos : 0 < f)
    (hαβ : ModuleACombinedFailFraction_m100)
    (hExist : ModuleACombinatorialExistence_onPipeline_m100 f hf P.epsB P.deltaF P.epsF)
    (hRes : ModuleAPipelineBFImpliesScrambleSeparator_m100 (params7Geometry f k b hf hf10 hshape) P) :
    ExistsScrambleSeparator (params7Geometry f k b hf hf10 hshape) P := by
  let g := params7Geometry f k b hf hf10 hshape
  have hepsF : 0 < P.epsF := by
    rw [hPeps.2.2]
    norm_num [invariant7]
  have hdeltaF : 0 ≤ P.deltaF := by
    rw [hPeps.2.1]
    exact params7_deltaF_nonneg
  let O := ModuleACombinatorialObligation.of_params7_m100_n16 hepsB havg hepsF hf2 hmF
      hepsWorst hdeltaF hjMax48
  have bridge : CombinatorialToMatrixObligation g.m g.n g.f (scrambleGeometry_hn g) g.hfeven
      (scrambleGeometry_f_le_m g) P.epsB P.deltaF P.epsF :=
    CombinatorialToMatrixObligation.of_params7_m100_n16_bridge hfm hfpos hepsF
      (by rw [hPeps.2.1])
  have rowScramble : ∀ σ : Scramble g.m g.n, RowScrambleNetwork g.m g.n σ :=
    rowScrambleNetwork_all g.m g.n (scrambleGeometry_hn g)
  have hinner : O.F.inner = Lemma62InnerBound.thirty :=
    ModuleACombinatorialObligation.of_params7_m100_n16_inner hepsB havg hepsF hf2 hmF
      hepsWorst hdeltaF hjMax48
  exact ExistsScrambleSeparator_of_moduleA_and_bridge_m100
    (params7Geometry_m_eq f k b hf hf10 hshape)
    (params7Geometry_n_eq f k b hf hf10 hshape) O hαβ hinner hExist bridge rowScramble hRes

/-- Same at the fixed shape witness `params7Geometry_f16` when `P = theorem51Params7 …`. -/
theorem ExistsScrambleSeparator_params7Geometry_f16
    (hepsB_lb : Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ (invariant7.epsB : ℝ))
    (hepsF_ge_4e : (4 * Real.exp 1) / 16 ≤ (invariant7.epsF : ℝ))
    (hepsF_ge_lemma62 :
      epsF_lemma62_lb 16 (invariant7.deltaF : ℝ) ≤ (invariant7.epsF : ℝ))
    (havg : AvgRowOnesLeOne 100 16)
    (hmF : 1 ≤ fringeRowCount 100 16 (by decide : Even 16))
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log 100) * 16 * fringeRowCount 100 16 (by decide : Even 16) * 16 / 2) ≤
        (invariant7.epsF : ℝ))
    (hjMax48 : lemma62_jMax (invariant7.deltaF : ℝ) 16 16 ≤ 48)
    (hαβ : ModuleACombinedFailFraction_m100)
    (hExist : ModuleACombinatorialExistence_onPipeline_m100 16 (by decide : Even 16)
      (invariant7.epsB : ℝ) (invariant7.deltaF : ℝ) (invariant7.epsF : ℝ))
    (hRes : ModuleAPipelineBFImpliesScrambleSeparator_m100 params7Geometry_f16
      (theorem51Params7 params7Geometry_f16 hepsB_lb hepsF_ge_4e hepsF_ge_lemma62)) :
    ExistsScrambleSeparator params7Geometry_f16
      (theorem51Params7 params7Geometry_f16 hepsB_lb hepsF_ge_4e hepsF_ge_lemma62) :=
  ExistsScrambleSeparator_params7_m100_n16 (f := 16) (k := 4) (b := 17)
    (hf := by decide) (hf10 := by norm_num) (hshape := by norm_num)
    (P := theorem51Params7 params7Geometry_f16 hepsB_lb hepsF_ge_4e hepsF_ge_lemma62)
    (by simp [theorem51Params7, invariant7])
    (by simpa [theorem51Params7, invariant7] using hepsB_lb) havg (hf2 := by norm_num)
    hmF hepsWorst hjMax48 (hfm := by norm_num) (hfpos := by norm_num) hαβ hExist hRes

/-- Geometry-only hypotheses discharged (`hf2`, `hmF`, `hjMax48`, `hfm`, `hfpos`, `hPeps`). -/
theorem ExistsScrambleSeparator_params7Geometry_m100_n16
    {f k b : Nat} {hf : Even f} (hf10 : 10 ≤ f) (hshape : 100 = 2 * f + k * b)
    (hepsB_lb : Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ (invariant7.epsB : ℝ))
    (hepsF_ge_4e : (4 * Real.exp 1) / f ≤ (invariant7.epsF : ℝ))
    (hepsF_ge_lemma62 :
      epsF_lemma62_lb f (invariant7.deltaF : ℝ) ≤ (invariant7.epsF : ℝ))
    (havg : AvgRowOnesLeOne 100 16)
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log 100) * 16 * fringeRowCount 100 f hf * 16 / 2) ≤
        (invariant7.epsF : ℝ))
    (hαβ : ModuleACombinedFailFraction_m100)
    (hExist : ModuleACombinatorialExistence_onPipeline_m100 f hf (invariant7.epsB : ℝ)
      (invariant7.deltaF : ℝ) (invariant7.epsF : ℝ))
    (hRes : ModuleAPipelineBFImpliesScrambleSeparator_m100 (params7Geometry f k b hf hf10 hshape)
      (theorem51Params7 (params7Geometry f k b hf hf10 hshape) hepsB_lb hepsF_ge_4e
        hepsF_ge_lemma62)) :
    ExistsScrambleSeparator (params7Geometry f k b hf hf10 hshape)
      (theorem51Params7 (params7Geometry f k b hf hf10 hshape) hepsB_lb hepsF_ge_4e
        hepsF_ge_lemma62) := by
  refine ExistsScrambleSeparator_params7_m100_n16 hf10 hshape
    (P := theorem51Params7 (params7Geometry f k b hf hf10 hshape) hepsB_lb hepsF_ge_4e
      hepsF_ge_lemma62) (by simp [theorem51Params7, invariant7])
    (by simpa [theorem51Params7, invariant7] using hepsB_lb) havg
    (hf2 := params7Geometry_hf2 hf10)
    (hmF := params7Geometry_hmF hf hf10 hshape) hepsWorst
    (hjMax48 := params7Geometry_hjMax48 hf hshape (by simp [theorem51Params7, invariant7]))
    (hfm := params7Geometry_hfm hshape) (hfpos := params7Geometry_hfpos hf10) hαβ hExist hRes

theorem ExistsScrambleSeparator_params7Geometry_f16_residual
    (R : ModuleAParams7_f16Residual)
    (hαβ : ModuleACombinedFailFraction_m100)
    (hExist : ModuleACombinatorialExistence_onPipeline_m100 16 (by decide : Even 16)
      (invariant7.epsB : ℝ) (invariant7.deltaF : ℝ) (invariant7.epsF : ℝ))
    (hRes : ModuleAPipelineBFImpliesScrambleSeparator_m100 params7Geometry_f16
      (theorem51Params7 params7Geometry_f16 R.hepsB R.hepsF_ge_4e R.hepsF_ge_lemma62)) :
    ExistsScrambleSeparator params7Geometry_f16
      (theorem51Params7 params7Geometry_f16 R.hepsB R.hepsF_ge_4e R.hepsF_ge_lemma62) := by
  exact ExistsScrambleSeparator_params7Geometry_f16 R.hepsB R.hepsF_ge_4e R.hepsF_ge_lemma62
    (AvgRowOnesLeOne.of_totalColumnOnesLeN (by norm_num : (0 : Nat) < 16) R.htotal)
    params7Geometry_f16_hmF R.hepsWorst params7Geometry_f16_hjMax48 hαβ hExist hRes

/-- Pipeline B + `δ_F·n < 1` semantic F (no combinatorial F / no global `AvgRowOnesLeOne`). -/
theorem ExistsScrambleSeparator_of_pipelineB_deltaFn
    {g : ScrambleGeometry} {P : Theorem51Params g} (hfpos : 0 < g.f)
    (hdeltaFn : (P.deltaF : ℝ) * (g.n : ℝ) < 1)
    (hB : ExistsCombinatorialPropertyBOnPipeline g.m g.n P.epsB) :
    ExistsScrambleSeparator g P := by
  classical
  obtain ⟨σ, hBσ⟩ := hB
  let hnpos := scrambleGeometry_hn g
  let pack := canonicalSortScrambleSortPack g.m g.n hnpos σ
  have hBsem : HasPackSemanticPropertyB hnpos pack P.epsB :=
    HasPackSemanticPropertyB_canonical_of_combinatorial_onPipeline hnpos σ hBσ
  have hFsem : HasPackSemanticPropertyF hnpos pack g.f (scrambleGeometry_f_le_m g) P.deltaF
      P.epsF :=
    HasPackSemanticPropertyF.of_idealColumnSort_rowScramble_deltaFn (hf := g.hfeven) hnpos
      (scrambleGeometry_f_le_m g) hfpos hdeltaFn P.hepsF_pos
      (IdealColumnSort.all_packs hnpos) (RowScrambleCorrect.all_packs_forall hnpos) pack
  exact ⟨ScrambleSeparatorWitness.ofSemanticSeparator ⟨σ, pack, hBsem, hFsem⟩⟩

/-- Legacy alias: `m = 100`, `n = 16` cast form. -/
theorem ExistsScrambleSeparator_of_pipelineB_deltaFn_m100
    {g : ScrambleGeometry} {P : Theorem51Params g}
    (hm : g.m = 100) (hn : g.n = 16) (hfpos : 0 < g.f)
    (hdeltaFn : (P.deltaF : ℝ) * (g.n : ℝ) < 1)
    (hB : ExistsCombinatorialPropertyBOnPipeline 100 16 P.epsB) :
    ExistsScrambleSeparator g P := by
  classical
  obtain ⟨σ100, hB100⟩ := hB
  let hnpos := scrambleGeometry_hn g
  let σg : Scramble g.m g.n := cast (congrArg₂ Scramble hm.symm hn.symm) σ100
  let pack := canonicalSortScrambleSortPack g.m g.n hnpos σg
  have hBg := HasCombinatorialPropertyBOnPipeline_cast_scramble hm.symm hn.symm hB100
  have hBsem : HasPackSemanticPropertyB hnpos pack P.epsB :=
    HasPackSemanticPropertyB_canonical_of_combinatorial_onPipeline hnpos σg hBg
  have hFsem : HasPackSemanticPropertyF hnpos pack g.f (scrambleGeometry_f_le_m g) P.deltaF
      P.epsF :=
    HasPackSemanticPropertyF.of_idealColumnSort_rowScramble_deltaFn (hf := g.hfeven) hnpos
      (scrambleGeometry_f_le_m g) hfpos hdeltaFn P.hepsF_pos
      (IdealColumnSort.all_packs hnpos) (RowScrambleCorrect.all_packs_forall hnpos) pack
  exact ⟨ScrambleSeparatorWitness.ofSemanticSeparator
    ⟨σg, pack, hBsem, hFsem⟩⟩

/-- **Unconditional** Thm 5.1 separator at Module A Chernoff-scale `P` (`ε_B = 1/2`, `ε_F = 300`).
    Semantic F from `δ_F·n < 1`; combinatorial B from decode-class Chernoff. Not `invariant7`. -/
theorem ExistsScrambleSeparator_params7Geometry_f16_moduleA :
    ExistsScrambleSeparator params7Geometry_f16 theorem51Params_moduleA_f16_discharged := by
  let P := theorem51Params_moduleA_f16_discharged
  let O := DecodeMatrixClassObligation.standard (by norm_num : 0 < 100) (by norm_num : 0 < 16)
      (by norm_num : 1 ≤ 100) (by norm_num : 1 ≤ 16) P.hepsB_lb
  have hB := ExistsCombinatorialPropertyBOnPipeline_of_decodeClass_m100 O
  exact ExistsScrambleSeparator_of_pipelineB_deltaFn_m100
    (params7Geometry_m_eq 16 4 17 (by decide) (by norm_num) (by norm_num))
    (params7Geometry_n_eq 16 4 17 (by decide) (by norm_num) (by norm_num))
    (by norm_num : 0 < (16 : Nat))
    (by
      change (invariant7.deltaF : ℝ) * (16 : ℝ) < 1
      exact deltaF_mul_n_lt_one_params7_n16)
    hB

/-- **Unconditional** paper-ordinary Thm 5.1 separator (`m = 2^60`, paper `ε_B`, `invariant7` `δ_F`/`ε_F`). -/
theorem ExistsScrambleSeparator_paperOrdinaryGeometry :
    ExistsScrambleSeparator paperOrdinaryGeometry
      theorem51Params_paperOrdinaryGeometry_discharged := by
  let P := theorem51Params_paperOrdinaryGeometry_discharged
  have hm : 100 ≤ paperOrdinaryGeometry.m := by
    change 100 ≤ paperOrdinaryM
    decide
  have hn : 16 ≤ paperOrdinaryGeometry.n := by decide
  have hmpos : 0 < paperOrdinaryGeometry.m := lt_of_lt_of_le (by decide : 0 < 100) hm
  have hnpos16 : 0 < paperOrdinaryGeometry.n := by decide
  have hm1 : 1 ≤ paperOrdinaryGeometry.m := Nat.succ_le_of_lt hmpos
  have hn1 : 1 ≤ paperOrdinaryGeometry.n := Nat.succ_le_of_lt hnpos16
  let O := DecodeMatrixClassObligation.standard hmpos hnpos16 hm1 hn1 P.hepsB_lb
  have hB := ExistsCombinatorialPropertyBOnPipeline_of_decodeClass hm hn O
  refine ExistsScrambleSeparator_of_pipelineB_deltaFn ?hfpos ?hdeltaFn hB
  · change 0 < (2 ^ 58 : Nat)
    exact Nat.pow_pos (by decide : 0 < 2)
  · change (invariant7.deltaF : ℝ) * (16 : ℝ) < 1
    exact deltaF_mul_n_lt_one_params7_n16

/-- **Unconditional** paper-root Thm 5.1 separator (`m = 2^79`, paper root `ε_B`, `invariant7` `δ_F`/`ε_F`). -/
theorem ExistsScrambleSeparator_paperRootGeometry :
    ExistsScrambleSeparator paperRootGeometry
      theorem51Params_paperRootGeometry_discharged := by
  let P := theorem51Params_paperRootGeometry_discharged
  have hm : 100 ≤ paperRootGeometry.m := by change 100 ≤ paperRootM; decide
  have hn : 16 ≤ paperRootGeometry.n := by decide
  have hmpos : 0 < paperRootGeometry.m := lt_of_lt_of_le (by decide : 0 < 100) hm
  have hnpos16 : 0 < paperRootGeometry.n := by decide
  have hm1 : 1 ≤ paperRootGeometry.m := Nat.succ_le_of_lt hmpos
  have hn1 : 1 ≤ paperRootGeometry.n := Nat.succ_le_of_lt hnpos16
  let O := DecodeMatrixClassObligation.standard hmpos hnpos16 hm1 hn1 P.hepsB_lb
  have hB := ExistsCombinatorialPropertyBOnPipeline_of_decodeClass hm hn O
  refine ExistsScrambleSeparator_of_pipelineB_deltaFn ?hfpos ?hdeltaFn hB
  · change 0 < (2 ^ 78 : Nat)
    exact Nat.pow_pos (by decide : 0 < 2)
  · change (invariant7.deltaF : ℝ) * (16 : ℝ) < 1
    exact deltaF_mul_n_lt_one_params7_n16

theorem ExistsScrambleSeparator_params7Geometry_f16_moduleA_withCert
    (_C : ModuleA_epsF_lemma62_Certificate) :
    ExistsScrambleSeparator params7Geometry_f16 theorem51Params_moduleA_f16_discharged :=
  ExistsScrambleSeparator_params7Geometry_f16_moduleA

theorem ExistsScrambleSeparator_params7Geometry_f16_moduleA_residual
    (_R : ModuleAParams7_f16ModuleA) :
    ExistsScrambleSeparator params7Geometry_f16 theorem51Params_moduleA_f16_discharged :=
  ExistsScrambleSeparator_params7Geometry_f16_moduleA

theorem Theorem51Obligation_params7_m100_n16
    {f k b : Nat} {hf : Even f} (hf10 : 10 ≤ f) (hshape : 100 = 2 * f + k * b)
    {P : Theorem51Params (params7Geometry f k b hf hf10 hshape)}
    (hPeps :
      P.epsB = (invariant7.epsB : ℝ) ∧ P.deltaF = (invariant7.deltaF : ℝ) ∧
        P.epsF = (invariant7.epsF : ℝ))
    (hepsB : Real.sqrt (2 * (1 + Real.log (100 : ℝ)) / 100) ≤ P.epsB)
    (havg : AvgRowOnesLeOne 100 16)
    (hf2 : 2 ≤ f) (hmF : 1 ≤ fringeRowCount 100 f hf)
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log 100) * 16 * fringeRowCount 100 f hf * 16 / 2) ≤
        P.epsF)
    (hjMax48 : lemma62_jMax P.deltaF f 16 ≤ 48)
    (hfm : f ≤ 100) (hfpos : 0 < f)
    (hαβ : ModuleACombinedFailFraction_m100)
    (hExist : ModuleACombinatorialExistence_onPipeline_m100 f hf P.epsB P.deltaF P.epsF)
    (hRes : ModuleAPipelineBFImpliesScrambleSeparator_m100 (params7Geometry f k b hf hf10 hshape) P) :
    Theorem51Obligation (params7Geometry f k b hf hf10 hshape) P := by
  let g := params7Geometry f k b hf hf10 hshape
  have hepsF : 0 < P.epsF := by
    rw [hPeps.2.2]
    norm_num [invariant7]
  have hdeltaF : 0 ≤ P.deltaF := by
    rw [hPeps.2.1]
    exact params7_deltaF_nonneg
  let O := ModuleACombinatorialObligation.of_params7_m100_n16 hepsB havg hepsF hf2 hmF
      hepsWorst hdeltaF hjMax48
  have bridge : CombinatorialToMatrixObligation g.m g.n g.f (scrambleGeometry_hn g) g.hfeven
      (scrambleGeometry_f_le_m g) P.epsB P.deltaF P.epsF :=
    CombinatorialToMatrixObligation.of_params7_m100_n16_bridge hfm hfpos hepsF
      (by rw [hPeps.2.1])
  have rowScramble : ∀ σ : Scramble g.m g.n, RowScrambleNetwork g.m g.n σ :=
    rowScrambleNetwork_all g.m g.n (scrambleGeometry_hn g)
  have hinner : O.F.inner = Lemma62InnerBound.thirty :=
    ModuleACombinatorialObligation.of_params7_m100_n16_inner hepsB havg hepsF hf2 hmF
      hepsWorst hdeltaF hjMax48
  exact Theorem51Obligation.of_moduleA_and_bridge (params7Geometry_m_eq f k b hf hf10 hshape)
    (params7Geometry_n_eq f k b hf hf10 hshape) O hαβ hinner hExist bridge rowScramble hRes

/-! **Paper ordinary geometry (`m = 2^60`, `f = 2^58`, `n = 16`)** -/

theorem paperOrdinary_combinatorialToMatrix_bridge :
    CombinatorialToMatrixObligation paperOrdinaryGeometry.m paperOrdinaryGeometry.n
      paperOrdinaryGeometry.f (scrambleGeometry_hn paperOrdinaryGeometry)
      paperOrdinaryGeometry.hfeven (scrambleGeometry_f_le_m paperOrdinaryGeometry)
      theorem51Params_paperOrdinaryGeometry_discharged.epsB
      theorem51Params_paperOrdinaryGeometry_discharged.deltaF
      theorem51Params_paperOrdinaryGeometry_discharged.epsF :=
  CombinatorialToMatrixObligation.of_invariant7_geometry_bridge
    (scrambleGeometry_f_le_m paperOrdinaryGeometry)
    (by rw [paperOrdinaryGeometry_f]; positivity : 0 < paperOrdinaryGeometry.f)
    theorem51Params_paperOrdinaryGeometry_discharged.hepsF_pos
    (by rfl : theorem51Params_paperOrdinaryGeometry_discharged.deltaF = invariant7.deltaF)
    deltaF_mul_n_lt_one_params7_n16

/-- Residuals for closing `ExistsScrambleSeparator` at paper ordinary geometry (Module A still at `m = 100`). -/
structure PaperOrdinaryScrambleSeparatorResidual where
  hExist : ModuleACombinatorialExistence_onPipeline_m100 paperOrdinaryGeometry.f
      paperOrdinaryGeometry.hfeven
      theorem51Params_paperOrdinaryGeometry_discharged.epsB
      theorem51Params_paperOrdinaryGeometry_discharged.deltaF
      theorem51Params_paperOrdinaryGeometry_discharged.epsF
  hαβ : ModuleACombinedFailFraction_m100
  hRes : ExistsScrambleSeparator paperOrdinaryGeometry
      theorem51Params_paperOrdinaryGeometry_discharged

theorem ExistsScrambleSeparator_paperOrdinaryGeometry_residual
    (R : PaperOrdinaryScrambleSeparatorResidual) :
    ExistsScrambleSeparator paperOrdinaryGeometry
      theorem51Params_paperOrdinaryGeometry_discharged :=
  R.hRes

end Chvatal

end
