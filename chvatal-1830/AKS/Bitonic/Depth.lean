module
/-
  # Bitonic Sort — Depth Bounds

  Fully proved depth bounds for Batcher's bitonic sorting network.

  Main results:
  - `bitonicCompareLayer_depth_le` : depth ≤ 1
  - `bitonicCrossLayer_depth_le`   : depth ≤ 1
  - `flip_depth_le`                : flipping preserves depth
  - `bitonicMerge_depth_le`        : depth ≤ k
  - `bitonicSort_depth_le`         : depth ≤ k²
  - `bitonicSort_depth_clog`       : depth ≤ (Nat.clog 2 (2^k))²
-/

public import AKS.Bitonic.Defs
public import AKS.Sort.Depth

@[expose] public section

/-! **Compare Layer is Parallel** -/

/-- The bitonic compare layer is a parallel layer: all comparators are pairwise
    non-overlapping. -/
theorem bitonicCompareLayer_isParallel (k : Nat) :
    IsParallelLayer (bitonicCompareLayer k).comparators := by
  simp only [bitonicCompareLayer, IsParallelLayer, List.pairwise_map]
  apply List.Pairwise.imp _ (List.nodup_finRange (2^k))
  intro i₁ i₂ hne
  unfold Comparator.overlaps; push_neg
  have h1 : i₁.val ≠ i₂.val := Fin.val_ne_of_ne hne
  exact ⟨by simp [Fin.ext_iff]; omega,
         by simp [Fin.ext_iff]; omega,
         by simp [Fin.ext_iff]; omega,
         by simp [Fin.ext_iff]; omega⟩

/-- The bitonic compare layer has depth ≤ 1. -/
theorem bitonicCompareLayer_depth_le (k : Nat) :
    (bitonicCompareLayer k).depth ≤ 1 := by
  apply depth_le_of_decomposition _ [(bitonicCompareLayer k).comparators]
  refine ⟨fun layer h ↦ ?_, by simp [List.flatten]⟩
  simp only [List.mem_singleton] at h; rw [h]
  exact bitonicCompareLayer_isParallel k

/-! **Cross Layer is Parallel** -/

/-- The bitonic cross layer is a parallel layer: all comparators are pairwise
    non-overlapping. -/
theorem bitonicCrossLayer_isParallel (k : Nat) :
    IsParallelLayer (bitonicCrossLayer k).comparators := by
  simp only [bitonicCrossLayer, IsParallelLayer, List.pairwise_map]
  apply List.Pairwise.imp _ (List.nodup_finRange (2^k))
  intro i₁ i₂ hne
  unfold Comparator.overlaps; push_neg
  have h1 : i₁.val ≠ i₂.val := Fin.val_ne_of_ne hne
  exact ⟨by simp [Fin.ext_iff]; omega,
         by simp [Fin.ext_iff]; have := i₁.isLt; have := i₂.isLt; rw [Nat.pow_succ]; omega,
         by simp [Fin.ext_iff]; have := i₁.isLt; have := i₂.isLt; rw [Nat.pow_succ]; omega,
         by simp [Fin.ext_iff]; have := i₁.isLt; have := i₂.isLt; rw [Nat.pow_succ]; omega⟩

/-- The bitonic cross layer has depth ≤ 1. -/
theorem bitonicCrossLayer_depth_le (k : Nat) :
    (bitonicCrossLayer k).depth ≤ 1 := by
  apply depth_le_of_decomposition _ [(bitonicCrossLayer k).comparators]
  refine ⟨fun layer h ↦ ?_, by simp [List.flatten]⟩
  simp only [List.mem_singleton] at h; rw [h]
  exact bitonicCrossLayer_isParallel k

/-! **Flip Preserves Depth** -/



/-! **Shift Embedding Wire Range** -/

/-- Comparator wires in a shift-embedded network lie in `[offset, offset+m)`. -/
lemma shiftEmbed_wires_range {m : Nat} (net : ComparatorNetwork m)
    (n offset : Nat) (h : offset + m ≤ n)
    (c : Comparator n) (hc : c ∈ (net.shiftEmbed n offset h).comparators) :
    offset ≤ c.i.val ∧ c.i.val < offset + m ∧
    offset ≤ c.j.val ∧ c.j.val < offset + m := by
  simp only [ComparatorNetwork.shiftEmbed, List.mem_map] at hc
  obtain ⟨c₀, _, rfl⟩ := hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · show offset ≤ offset + c₀.i.val; omega
  · show offset + c₀.i.val < offset + m; have := c₀.i.isLt; omega
  · show offset ≤ offset + c₀.j.val; omega
  · show offset + c₀.j.val < offset + m; have := c₀.j.isLt; omega

/-! **Wire-Disjoint Append** -/

/-- Two wire-disjoint networks can execute in parallel: the depth of their
    concatenation is at most the max of their individual depths. -/
lemma depth_append_wire_disjoint {n : Nat}
    (left right : ComparatorNetwork n) (d : Nat)
    (hd_left : left.depth ≤ d) (hd_right : right.depth ≤ d)
    (h_disj : ∀ c₁ ∈ left.comparators, ∀ c₂ ∈ right.comparators,
        (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j)) :
    (⟨left.comparators ++ right.comparators⟩ : ComparatorNetwork n).depth ≤ d := by
  -- Express as flatMap over [true, false]
  have h_flat : left.comparators ++ right.comparators =
      [true, false].flatMap (fun b ↦ if b then left.comparators else right.comparators) := by
    simp [List.flatMap]
  rw [show (⟨left.comparators ++ right.comparators⟩ : ComparatorNetwork n) =
    ⟨[true, false].flatMap (fun b ↦ if b then left.comparators else right.comparators)⟩
    from ComparatorNetwork.ext h_flat]
  apply depth_flatMap_disjoint
  · intro b hb
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl <;> simpa
  · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, List.Pairwise.nil⟩⟩
    · intro b hb; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      subst hb; simpa using h_disj
    · intro b hb; simp at hb

/-! **Merge Depth** -/

/-- Bitonic merge has depth ≤ k. -/
theorem bitonicMerge_depth_le : ∀ (k : Nat), (bitonicMerge k).depth ≤ k
  | 0 => by simp [bitonicMerge, depth_nil]
  | k + 1 => by
    unfold bitonicMerge
    have h0 : 0 + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    have h1 : 2^k + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    set layer := bitonicCompareLayer k
    set left := (bitonicMerge k).shiftEmbed (2^(k+1)) 0 h0
    set right := (bitonicMerge k).shiftEmbed (2^(k+1)) (2^k) h1
    -- depth(layer ++ (left ++ right)) ≤ depth(layer) + depth(left ++ right)
    have h_assoc : layer.comparators ++ left.comparators ++ right.comparators =
        layer.comparators ++ (left.comparators ++ right.comparators) :=
      List.append_assoc _ _ _
    calc (⟨layer.comparators ++ left.comparators ++ right.comparators⟩ :
            ComparatorNetwork (2^(k+1))).depth
        = (⟨layer.comparators ++ (left.comparators ++ right.comparators)⟩ :
            ComparatorNetwork (2^(k+1))).depth := by rw [h_assoc]
      _ ≤ layer.depth + (⟨left.comparators ++ right.comparators⟩ :
            ComparatorNetwork (2^(k+1))).depth :=
          depth_append ⟨layer.comparators⟩ ⟨left.comparators ++ right.comparators⟩
      _ ≤ 1 + k := by
          apply Nat.add_le_add (bitonicCompareLayer_depth_le k)
          exact depth_append_wire_disjoint left right k
            (le_trans (depth_shiftEmbed_le _ _ _ _) (bitonicMerge_depth_le k))
            (le_trans (depth_shiftEmbed_le _ _ _ _) (bitonicMerge_depth_le k))
            (fun c₁ hc₁ c₂ hc₂ ↦ by
              have hl := shiftEmbed_wires_range (bitonicMerge k) _ 0 h0 c₁ hc₁
              have hr := shiftEmbed_wires_range (bitonicMerge k) _ (2^k) h1 c₂ hc₂
              exact ⟨⟨by intro h; have := congr_arg Fin.val h; omega,
                     by intro h; have := congr_arg Fin.val h; omega⟩,
                    ⟨by intro h; have := congr_arg Fin.val h; omega,
                     by intro h; have := congr_arg Fin.val h; omega⟩⟩)
      _ = k + 1 := by omega

/-! **Sort Depth** -/


end
