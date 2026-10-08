module

public import AKS.Bitonic.Shrink

/-! # The triangular bitonic depth budget

The sharper bound is needed to account for bounded exact root sorts in the
Paterson forest, rather than using the inherited square-log upper bound.
-/

@[expose] public section

def bitonicDepthBudget : ℕ → ℕ
  | 0 => 0
  | k + 1 => bitonicDepthBudget k + (k + 1)

theorem bitonicDepthBudget_double (k : ℕ) :
    2 * bitonicDepthBudget k = k * (k + 1) := by
  induction k with
  | zero => simp [bitonicDepthBudget]
  | succ k ih => simp only [bitonicDepthBudget]; nlinarith

/-- Batcher's triangular depth budget: `∑_{i=1}^p i = p(p+1)/2`. -/
theorem bitonicDepthBudget_eq (k : ℕ) :
    bitonicDepthBudget k = k * (k + 1) / 2 := by
  calc bitonicDepthBudget k
      = (2 * bitonicDepthBudget k) / 2 :=
        (Nat.mul_div_cancel_left (bitonicDepthBudget k) (by decide : 0 < 2)).symm
    _ = (k * (k + 1)) / 2 := by rw [bitonicDepthBudget_double k]

/-- §7 final sorter: `42·43/2 = 903` comparator layers for `2^42` wires. -/
theorem bitonicDepthBudget_42 : bitonicDepthBudget 42 = 903 := by
  rw [bitonicDepthBudget_eq 42]

theorem bitonicDepthBudget_mono : Monotone bitonicDepthBudget := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [bitonicDepthBudget]
  omega

theorem bitonicSort_depth_le_budget : ∀ (k : Nat), (bitonicSort k).depth ≤ bitonicDepthBudget k
  | 0 => by simp [bitonicSort, depth_nil]
  | k + 1 => by
    unfold bitonicSort
    have h0 : 0 + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    have h1 : 2^k + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    set sortLeft := (bitonicSort k).shiftEmbed (2^(k+1)) 0 h0
    set sortRight := (bitonicSort k).shiftEmbed (2^(k+1)) (2^k) h1
    set cross := bitonicCrossLayer k
    set mergeLeft := (bitonicMerge k).shiftEmbed (2^(k+1)) 0 h0
    set mergeRight := (bitonicMerge k).shiftEmbed (2^(k+1)) (2^k) h1
    -- Regroup: (S ++ R ++ X ++ ML ++ MR) = (S ++ R) ++ (X ++ (ML ++ MR))
    have h_assoc : sortLeft.comparators ++ sortRight.comparators ++
        cross.comparators ++ mergeLeft.comparators ++ mergeRight.comparators =
        (sortLeft.comparators ++ sortRight.comparators) ++
        (cross.comparators ++ (mergeLeft.comparators ++ mergeRight.comparators)) := by
      simp only [List.append_assoc]
    -- Wire disjointness helper for left/right at offsets 0 and 2^k
    have h_disj_sort : ∀ c₁ ∈ sortLeft.comparators, ∀ c₂ ∈ sortRight.comparators,
        (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j) :=
      fun c₁ hc₁ c₂ hc₂ ↦ by
        have hl := shiftEmbed_wires_range (bitonicSort k) _ 0 h0 c₁ hc₁
        have hr := shiftEmbed_wires_range (bitonicSort k) _ (2^k) h1 c₂ hc₂
        exact ⟨⟨by intro h; have := congr_arg Fin.val h; omega,
               by intro h; have := congr_arg Fin.val h; omega⟩,
              ⟨by intro h; have := congr_arg Fin.val h; omega,
               by intro h; have := congr_arg Fin.val h; omega⟩⟩
    have h_disj_merge : ∀ c₁ ∈ mergeLeft.comparators, ∀ c₂ ∈ mergeRight.comparators,
        (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j) :=
      fun c₁ hc₁ c₂ hc₂ ↦ by
        have hl := shiftEmbed_wires_range (bitonicMerge k) _ 0 h0 c₁ hc₁
        have hr := shiftEmbed_wires_range (bitonicMerge k) _ (2^k) h1 c₂ hc₂
        exact ⟨⟨by intro h; have := congr_arg Fin.val h; omega,
               by intro h; have := congr_arg Fin.val h; omega⟩,
              ⟨by intro h; have := congr_arg Fin.val h; omega,
               by intro h; have := congr_arg Fin.val h; omega⟩⟩
    calc (⟨sortLeft.comparators ++ sortRight.comparators ++
            cross.comparators ++ mergeLeft.comparators ++ mergeRight.comparators⟩ :
            ComparatorNetwork (2^(k+1))).depth
        = (⟨(sortLeft.comparators ++ sortRight.comparators) ++
            (cross.comparators ++ (mergeLeft.comparators ++ mergeRight.comparators))⟩ :
            ComparatorNetwork (2^(k+1))).depth := by rw [h_assoc]
      _ ≤ (⟨sortLeft.comparators ++ sortRight.comparators⟩ :
            ComparatorNetwork (2^(k+1))).depth +
          (⟨cross.comparators ++ (mergeLeft.comparators ++ mergeRight.comparators)⟩ :
            ComparatorNetwork (2^(k+1))).depth :=
          depth_append _ _
      _ ≤ bitonicDepthBudget k + (1 + k) := by
          apply Nat.add_le_add
          · exact depth_append_wire_disjoint sortLeft sortRight (bitonicDepthBudget k)
              (le_trans (depth_shiftEmbed_le _ _ _ _) (bitonicSort_depth_le_budget k))
              (le_trans (depth_shiftEmbed_le _ _ _ _) (bitonicSort_depth_le_budget k))
              h_disj_sort
          · calc (⟨cross.comparators ++ (mergeLeft.comparators ++ mergeRight.comparators)⟩ :
                    ComparatorNetwork (2^(k+1))).depth
                ≤ cross.depth + (⟨mergeLeft.comparators ++ mergeRight.comparators⟩ :
                    ComparatorNetwork (2^(k+1))).depth :=
                  depth_append _ _
              _ ≤ 1 + k := Nat.add_le_add (bitonicCrossLayer_depth_le k)
                  (depth_append_wire_disjoint mergeLeft mergeRight k
                    (le_trans (depth_shiftEmbed_le _ _ _ _) (bitonicMerge_depth_le k))
                    (le_trans (depth_shiftEmbed_le _ _ _ _) (bitonicMerge_depth_le k))
                    h_disj_merge)
      _ ≤ bitonicDepthBudget (k + 1) := by simp only [bitonicDepthBudget]; omega


theorem bitonicNetwork_depth_le_budget (n : ℕ) :
    (bitonicNetwork n).depth ≤ bitonicDepthBudget (Nat.clog 2 n) := by
  unfold bitonicNetwork
  exact (restrictWires_depth_le _ _ _).trans (bitonicSort_depth_le_budget _)




theorem bitonicNetwork_2pow42_depth_le_903 :
    (bitonicNetwork (2 ^ 42)).depth ≤ 903 := by
  calc (bitonicNetwork (2 ^ 42)).depth
      ≤ bitonicDepthBudget (Nat.clog 2 (2 ^ 42)) := bitonicNetwork_depth_le_budget (2 ^ 42)
    _ = 903 := by rw [show Nat.clog 2 (2 ^ 42) = 42 from by decide +kernel, bitonicDepthBudget_42]
