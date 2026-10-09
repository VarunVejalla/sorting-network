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

public import AKS.Chvatal.RowScramble
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







/-! ## Paper budgets -/










end Chvatal
