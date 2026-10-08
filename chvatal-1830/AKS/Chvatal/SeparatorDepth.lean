module
/-
  # Depth of Chvátal sort–scramble–sort packs

  Column sorts are wire-disjoint bitonic embeddings, so they run in parallel
  (`depth_flatMap_disjoint`). The canonical row scramble has empty comparators,
  so a sort–scramble–sort pack has depth at most twice one column sort.

  At paper ordinary `m = 2^60` this is `2 · 1830 = 3660 = ordinaryStagePaperDepth`.
  At paper root `m = 2^79` this is `2 · 3160 = 6320 = rootSeparatorPaperDepth`.

  Status: pack-depth accounting only. Contiguous / abstract embeddings into
  `64^d` stage nets live in `StagePackEmbed` / `PackEmbed` (depth shells only).
-/

public import AKS.Chvatal.ModuleABridge
public import AKS.Chvatal.RowScramble
public import AKS.Chvatal.DepthSkeleton
public import AKS.Sort.Depth
public import AKS.Bitonic.TightDepth

@[expose] public section

namespace Chvatal

/-! ## Column-sort depth -/

theorem columnSortColumnNet_depth_le (m n : Nat) (hn : 0 < n) (j : Fin n) :
    (columnSortColumnNet m n hn j).depth ≤ (bitonicNetwork m).depth := by
  simpa [columnSortColumnNet] using
    depth_scatterEmbed_le (bitonicNetwork m) (m * n) (columnWireEmbed m n hn j)

private theorem columnSortColumnNets_wire_disjoint {m n : Nat} (hn : 0 < n)
    {a b : Fin n} (hne : a ≠ b)
    (c₁ : Comparator (m * n)) (hc₁ : c₁ ∈ (columnSortColumnNet m n hn a).comparators)
    (c₂ : Comparator (m * n)) (hc₂ : c₂ ∈ (columnSortColumnNet m n hn b).comparators) :
    (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j) := by
  obtain ⟨r₁, k₁, hi₁, hk₁⟩ := columnSortColumnNet_scatter_wire (m := m) (n := n) hn a c₁ hc₁
  obtain ⟨r₂, k₂, hi₂, hk₂⟩ := columnSortColumnNet_scatter_wire (m := m) (n := n) hn b c₂ hc₂
  have ha_i : matrixCol m n hn c₁.i = a := by rw [hi₁, (matrixWire_row_col hn r₁ a).2]
  have ha_j : matrixCol m n hn c₁.j = a := by rw [hk₁, (matrixWire_row_col hn k₁ a).2]
  have hb_i : matrixCol m n hn c₂.i = b := by rw [hi₂, (matrixWire_row_col hn r₂ b).2]
  have hb_j : matrixCol m n hn c₂.j = b := by rw [hk₂, (matrixWire_row_col hn k₂ b).2]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h; exact hne (by rw [← ha_i, h, hb_i])
  · intro h; exact hne (by rw [← ha_i, h, hb_j])
  · intro h; exact hne (by rw [← ha_j, h, hb_i])
  · intro h; exact hne (by rw [← ha_j, h, hb_j])

theorem columnSortNetwork_depth_le (m n : Nat) (hn : 0 < n) :
    (columnSortNetwork m n hn).net.depth ≤ (bitonicNetwork m).depth := by
  dsimp [columnSortNetwork, ColumnSortNetwork.net]
  refine depth_flatMap_disjoint (List.finRange n)
    (fun j => (columnSortColumnNet m n hn j).comparators)
    (bitonicNetwork m).depth ?hchunk ?hdisj
  · intro j _
    simpa using columnSortColumnNet_depth_le m n hn j
  · refine List.Pairwise.imp ?_ ((List.nodup_iff_pairwise_ne).mp (List.nodup_finRange n))
    intro a b hne c₁ hc₁ c₂ hc₂
    exact columnSortColumnNets_wire_disjoint hn hne c₁ hc₁ c₂ hc₂

theorem columnSortNetwork_depth_le_budget (m n : Nat) (hn : 0 < n) :
    (columnSortNetwork m n hn).net.depth ≤ bitonicDepthBudget (Nat.clog 2 m) :=
  (columnSortNetwork_depth_le m n hn).trans (bitonicNetwork_depth_le_budget m)

/-! ## Pack depth (two column sorts; empty scramble comparators) -/

theorem rowScrambleNetwork_depth_eq_zero (m n : Nat) (hn : 0 < n) (σ : Scramble m n) :
    (rowScrambleNetwork m n hn σ).net.depth = 0 := by
  have h := rowScrambleNetwork_comparators_eq_nil m n hn σ
  change (⟨(rowScrambleNetwork m n hn σ).net.comparators⟩ : ComparatorNetwork (m * n)).depth = 0
  rw [h]
  exact depth_nil

theorem sortScrambleSortNetwork_depth_le (m n : Nat) (_hn : 0 < n) (σ : Scramble m n)
    (colSort : ColumnSortNetwork m n) (rowScramble : RowScrambleNetwork m n σ)
    (hrow : rowScramble.net.comparators = []) :
    (sortScrambleSortNetwork m n σ colSort rowScramble).depth ≤
      2 * colSort.net.depth := by
  dsimp [sortScrambleSortNetwork]
  have happend :
      colSort.net.comparators ++ rowScramble.net.comparators ++ colSort.net.comparators =
        colSort.net.comparators ++ colSort.net.comparators := by
    simp [hrow]
  rw [happend]
  have h := depth_append colSort.net colSort.net
  simpa [two_mul] using h

theorem SortScrambleSortPack_net_depth_le (m n : Nat) (hn : 0 < n) (σ : Scramble m n)
    (pack : SortScrambleSortPack m n hn σ)
    (hrow : pack.rowScramble.net.comparators = []) :
    pack.net.depth ≤ 2 * (columnSortNetwork m n hn).net.depth := by
  simpa [SortScrambleSortPack.net_eq, SortScrambleSortPack.colSort] using
    sortScrambleSortNetwork_depth_le m n hn σ pack.colSort pack.rowScramble hrow

/-- Canonical `columnSortNetwork` + empty `rowScrambleNetwork` comparators. -/
theorem sortScrambleSortNetwork_columnSort_depth_le (m n : Nat) (hn : 0 < n)
    (σ : Scramble m n) :
    (sortScrambleSortNetwork m n σ (columnSortNetwork m n hn)
      (rowScrambleNetwork m n hn σ)).depth ≤ 2 * (bitonicNetwork m).depth := by
  have h := sortScrambleSortNetwork_depth_le m n hn σ (columnSortNetwork m n hn)
    (rowScrambleNetwork m n hn σ) (rowScrambleNetwork_comparators_eq_nil m n hn σ)
  exact h.trans (Nat.mul_le_mul_left 2 (columnSortNetwork_depth_le m n hn))

theorem SortScrambleSortPack_canonical_depth_le (m n : Nat) (hn : 0 < n) (σ : Scramble m n) :
    (canonicalSortScrambleSortPack m n hn σ).net.depth ≤
      2 * (bitonicNetwork m).depth := by
  have hpack := SortScrambleSortPack_net_depth_le m n hn σ
    (canonicalSortScrambleSortPack m n hn σ)
    (rowScrambleNetwork_comparators_eq_nil m n hn σ)
  exact hpack.trans (Nat.mul_le_mul_left 2 (columnSortNetwork_depth_le m n hn))

theorem SortScrambleSortPack_canonical_depth_le_budget (m n : Nat) (hn : 0 < n)
    (σ : Scramble m n) :
    (canonicalSortScrambleSortPack m n hn σ).net.depth ≤
      2 * bitonicDepthBudget (Nat.clog 2 m) :=
  (SortScrambleSortPack_canonical_depth_le m n hn σ).trans
    (Nat.mul_le_mul_left 2 (bitonicNetwork_depth_le_budget m))

/-! ## Paper budgets -/

theorem bitonicDepthBudget_60 : bitonicDepthBudget 60 = 1830 := by
  rw [bitonicDepthBudget_eq 60]

theorem bitonicDepthBudget_79 : bitonicDepthBudget 79 = 3160 := by
  rw [bitonicDepthBudget_eq 79]

theorem clog2_paperOrdinaryM : Nat.clog 2 paperOrdinaryM = 60 := by
  unfold paperOrdinaryM
  exact Nat.clog_pow 2 60 (by decide : 1 < 2)

theorem clog2_paperRootM : Nat.clog 2 paperRootM = 79 := by
  unfold paperRootM
  exact Nat.clog_pow 2 79 (by decide : 1 < 2)

theorem SortScrambleSortPack_paperOrdinary_depth_le_ordinaryStage
    (σ : Scramble paperOrdinaryGeometry.m paperOrdinaryGeometry.n) :
    (canonicalSortScrambleSortPack paperOrdinaryGeometry.m paperOrdinaryGeometry.n
      (by decide) σ).net.depth ≤ ordinaryStagePaperDepth := by
  have h := SortScrambleSortPack_canonical_depth_le_budget
    paperOrdinaryGeometry.m paperOrdinaryGeometry.n (by decide) σ
  have hm : paperOrdinaryGeometry.m = paperOrdinaryM := rfl
  have hbud : 2 * bitonicDepthBudget (Nat.clog 2 paperOrdinaryGeometry.m) =
      ordinaryStagePaperDepth := by
    rw [hm, clog2_paperOrdinaryM, bitonicDepthBudget_60]
    unfold ordinaryStagePaperDepth
    decide
  exact h.trans (le_of_eq hbud)

theorem SortScrambleSortPack_paperRoot_depth_le_rootSeparator
    (σ : Scramble paperRootGeometry.m paperRootGeometry.n) :
    (canonicalSortScrambleSortPack paperRootGeometry.m paperRootGeometry.n
      (by decide) σ).net.depth ≤ rootSeparatorPaperDepth := by
  have h := SortScrambleSortPack_canonical_depth_le_budget
    paperRootGeometry.m paperRootGeometry.n (by decide) σ
  have hm : paperRootGeometry.m = paperRootM := rfl
  have hbud : 2 * bitonicDepthBudget (Nat.clog 2 paperRootGeometry.m) =
      rootSeparatorPaperDepth := by
    rw [hm, clog2_paperRootM, bitonicDepthBudget_79]
    unfold rootSeparatorPaperDepth
    decide
  exact h.trans (le_of_eq hbud)

/-- Thm 5.1 witnesses built by the pipeline B + `δ_F·n < 1` route use the canonical pack. -/
theorem ScrambleSeparatorWitness_of_pipelineB_deltaFn_depth_le_budget
    {g : ScrambleGeometry} {P : Theorem51Params g} (hfpos : 0 < g.f)
    (hdeltaFn : (P.deltaF : ℝ) * (g.n : ℝ) < 1)
    (hB : ExistsCombinatorialPropertyBOnPipeline g.m g.n P.epsB) :
    ∃ w : ScrambleSeparatorWitness g P,
      w.net.depth ≤ 2 * bitonicDepthBudget (Nat.clog 2 g.m) := by
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
  refine ⟨ScrambleSeparatorWitness.ofSemanticSeparator ⟨σ, pack, hBsem, hFsem⟩, ?_⟩
  simpa [ScrambleSeparatorWitness.net, SemanticSeparator.net] using
    SortScrambleSortPack_canonical_depth_le_budget g.m g.n hnpos σ

/-- Unconditional paper-ordinary separator with pack depth ≤ `ordinaryStagePaperDepth`. -/
theorem ExistsScrambleSeparator_paperOrdinaryGeometry_depth_le_ordinaryStage :
    ∃ w : ScrambleSeparatorWitness paperOrdinaryGeometry
        theorem51Params_paperOrdinaryGeometry_discharged,
      w.net.depth ≤ ordinaryStagePaperDepth := by
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
  obtain ⟨w, hdepth⟩ := ScrambleSeparatorWitness_of_pipelineB_deltaFn_depth_le_budget
    (g := paperOrdinaryGeometry) (P := P)
    (by change 0 < (2 ^ 58 : Nat); exact Nat.pow_pos (by decide : 0 < 2))
    (by change (invariant7.deltaF : ℝ) * (16 : ℝ) < 1
        exact deltaF_mul_n_lt_one_params7_n16)
    hB
  refine ⟨w, hdepth.trans (le_of_eq ?_)⟩
  have hm' : paperOrdinaryGeometry.m = paperOrdinaryM := rfl
  rw [hm', clog2_paperOrdinaryM, bitonicDepthBudget_60]
  unfold ordinaryStagePaperDepth
  decide

/-- Unconditional paper-root separator with pack depth ≤ `rootSeparatorPaperDepth` (= 6320). -/
theorem ExistsScrambleSeparator_paperRootGeometry_depth_le_rootSeparator :
    ∃ w : ScrambleSeparatorWitness paperRootGeometry
        theorem51Params_paperRootGeometry_discharged,
      w.net.depth ≤ rootSeparatorPaperDepth := by
  let P := theorem51Params_paperRootGeometry_discharged
  have hm : 100 ≤ paperRootGeometry.m := by
    change 100 ≤ paperRootM
    decide
  have hn : 16 ≤ paperRootGeometry.n := by decide
  have hmpos : 0 < paperRootGeometry.m := lt_of_lt_of_le (by decide : 0 < 100) hm
  have hnpos16 : 0 < paperRootGeometry.n := by decide
  have hm1 : 1 ≤ paperRootGeometry.m := Nat.succ_le_of_lt hmpos
  have hn1 : 1 ≤ paperRootGeometry.n := Nat.succ_le_of_lt hnpos16
  let O := DecodeMatrixClassObligation.standard hmpos hnpos16 hm1 hn1 P.hepsB_lb
  have hB := ExistsCombinatorialPropertyBOnPipeline_of_decodeClass hm hn O
  obtain ⟨w, hdepth⟩ := ScrambleSeparatorWitness_of_pipelineB_deltaFn_depth_le_budget
    (g := paperRootGeometry) (P := P)
    (by change 0 < (2 ^ 78 : Nat); exact Nat.pow_pos (by decide : 0 < 2))
    (by change (invariant7.deltaF : ℝ) * (16 : ℝ) < 1
        exact deltaF_mul_n_lt_one_params7_n16)
    hB
  refine ⟨w, hdepth.trans (le_of_eq ?_)⟩
  have hm' : paperRootGeometry.m = paperRootM := rfl
  rw [hm', clog2_paperRootM, bitonicDepthBudget_79]
  unfold rootSeparatorPaperDepth
  decide

end Chvatal
