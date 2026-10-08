module
/-
  # Chvátal Property B for general n ≥ 16, m ≥ 100

  Generalization of Property B existence to all n ≥ 16 and m ≥ 100,
  reusing the existing Lemma 6.1 / Module A machinery that is already general
  in (m, n) despite specialized instances at m=100, n=16.

  The key insight: `lemma61_failFactor m n = (2(m+1)/(e*m))^n` depends on both m and n,
  and the Lemma 6.1 bound decreases in n for fixed m. The proof that
  `lemma61_failFactor m n < 1/100` for m ≥ 100, n ≥ 16 is general and shows
  the bound holds even for larger n.
-/

public import AKS.Chvatal.ModuleA

@[expose] public section

namespace Chvatal

/-! **Generalized Lemma 6.1 fail-fraction bounds** -/

/-- The numeric bound on `lemma61_failFactor m n` holds for all m ≥ 100 and n ≥ 16.
    This is the core numeric fact that enables the generalization to arbitrary n ≥ 16. -/
theorem lemma61_failFactor_pow_lt (m n : Nat) (hm : 100 ≤ m) (hn : 16 ≤ n) :
    lemma61_failFactor m n < 1 / 100 :=
  lemma61_failFactor_lt_one_hundredth m n hm hn

/-- Property B existence for arbitrary n ≥ 16 and m ≥ 100, using the general
    Lemma 6.1 fail-bound machinery from `DecodeMatrixClassObligation`. -/
theorem ExistsCombinatorialPropertyBOnPipeline_of_decodeClass_general
    {m n : Nat} {epsB : ℝ}
    (hm : 100 ≤ m) (hn : 16 ≤ n)
    (O : DecodeMatrixClassObligation m n epsB) :
    ExistsCombinatorialPropertyBOnPipeline m n epsB :=
  ExistsCombinatorialPropertyBOnPipeline_of_decodeClass hm hn O

/-- Global (non-pipeline) combinatorial Property B for arbitrary n ≥ 16, m ≥ 100,
    assuming `AvgRowOnesLeOne` which is false in general but may hold for specific matrices. -/
theorem ExistsCombinatorialPropertyB_of_avgRowOnesGeneral
    {m n : Nat} {epsB : ℝ}
    (hm : 100 ≤ m) (hn : 16 ≤ n)
    (heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB)
    (havg : AvgRowOnesLeOne m n) :
    ExistsCombinatorialPropertyB m n epsB :=
  ExistsCombinatorialPropertyB_of_avgRowOnes_le_one hm hn heps havg

/-- Obligation structure for Property B at general (m, n) ≥ (100, 16):
    bundles the three requirements: lower bound on m, lower bound on n, and epsilon threshold. -/
structure PropertyBObligation (m n : Nat) (epsB : ℝ) where
  hm : 100 ≤ m
  hn : 16 ≤ n
  heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB
  failBound : Lemma61FailBound m n epsB

/-- Derive Property B from the obligation structure for general (m, n). -/
theorem ExistsCombinatorialPropertyB_ofObligationGeneral
    {m n : Nat} {epsB : ℝ} (O : PropertyBObligation m n epsB) :
    ExistsCombinatorialPropertyB m n epsB :=
  exists_combinatorialPropertyB_of_failBound m n epsB O.hm O.hn O.failBound

/-- Pipeline Property B obligation for general (m, n) ≥ (100, 16):
    similar to `PropertyBObligation` but uses the pipeline-restricted fail-bound. -/
structure PropertyBOnPipelineObligation (m n : Nat) (epsB : ℝ) where
  hm : 100 ≤ m
  hn : 16 ≤ n
  heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB
  failBound : Lemma61FailBoundOnPipeline m n epsB

/-- Derive pipeline Property B from the obligation structure for general (m, n). -/
theorem ExistsCombinatorialPropertyBOnPipeline_ofObligationGeneral
    {m n : Nat} {epsB : ℝ} (O : PropertyBOnPipelineObligation m n epsB) :
    ExistsCombinatorialPropertyBOnPipeline m n epsB := by
  have hfactor : lemma61_failFactor m n < 1 := by
    have h := lemma61_failFactor_pow_lt m n O.hm O.hn
    linarith
  exact exists_combinatorialPropertyB_onPipeline_of_failBound m n epsB O.hm O.hn
    hfactor O.failBound

/-- Derive pipeline Property B from a decode-matrix-class obligation at general (m, n). -/
theorem ExistsCombinatorialPropertyBOnPipeline_ofDecodeClassGeneralized
    {m n : Nat} {epsB : ℝ}
    (hm : 100 ≤ m) (hn : 16 ≤ n)
    (O : DecodeMatrixClassObligation m n epsB) :
    ExistsCombinatorialPropertyBOnPipeline m n epsB :=
  ExistsCombinatorialPropertyBOnPipeline_of_decodeClass hm hn O

/-! **Lemma 6.1 + Lemma 6.2 combined for general n** -/

/-- Obligation for both Property B and F at general (m, n) ≥ (100, 16):
    bundles decode-class and cell-counting for a full Module A solution. -/
structure ModuleAObligationGeneral (m n : Nat) (epsB : ℝ) (f : Nat) (hf : Even f)
    (deltaF epsF : ℝ) where
  hm : 100 ≤ m
  hn : 16 ≤ n
  B : DecodeMatrixClassObligation m n epsB
  F : Lemma62CellCountingObligation m n f hf deltaF epsF

/-- Pipeline Property B from Module A combined obligation at general (m, n). -/
theorem ExistsCombinatorialPropertyBOnPipeline_ofModuleAGeneralized
    {m n : Nat} {epsB : ℝ} {f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (O : ModuleAObligationGeneral m n epsB f hf deltaF epsF) :
    ExistsCombinatorialPropertyBOnPipeline m n epsB :=
  ExistsCombinatorialPropertyBOnPipeline_of_decodeClass O.hm O.hn O.B

/-- Pipeline Property F from Module A combined obligation at general (m, n). -/
theorem ExistsCombinatorialPropertyF_ofModuleAGeneralized
    {m n : Nat} {epsB : ℝ} {f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (O : ModuleAObligationGeneral m n epsB f hf deltaF epsF) :
    ExistsCombinatorialPropertyF m n f hf deltaF epsF :=
  ExistsCombinatorialPropertyF_of_cellCounting O.F

end Chvatal
