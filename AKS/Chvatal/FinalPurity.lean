module

/-
  # Parallel final sorter correctness under purity (§7)

  When input values are block-separated (each block holds a contiguous rank slice),
  the parallel final sorters (Batcher on each block) complete the sort. This module
  proves the purity-dependent sorting theorems: monotone output and rank identity.
-/

public import AKS.Chvatal.ParallelFinalDepth
public import AKS.Sort.Monotone
public import AKS.Bitonic.Shrink
public import AKS.Sort.Defs

set_option maxRecDepth 4096

@[expose] public section

namespace Chvatal

/-! ## Helper: every network output is a permuted input -/

/-- A single comparator permutes values: output at any wire equals some input. -/
private theorem Comparator.apply_exists_preimage' {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) (k : Fin n) :
    ∃ i : Fin n, c.apply v k = v i := by
  unfold Comparator.apply
  by_cases hki : k = c.i
  · subst hki
    rw [if_pos rfl]
    by_cases hle : v c.i ≤ v c.j
    · refine ⟨c.i, ?_⟩
      simp [min_eq_left hle]
    · refine ⟨c.j, ?_⟩
      simp [min_eq_right (le_of_not_ge hle)]
  · rw [if_neg hki]
    by_cases hkj : k = c.j
    · subst hkj
      rw [if_pos rfl]
      by_cases hle : v c.i ≤ v c.j
      · refine ⟨c.j, ?_⟩
        simp [max_eq_right hle]
      · refine ⟨c.i, ?_⟩
        simp [max_eq_left (le_of_not_ge hle)]
    · rw [if_neg hkj]
      exact ⟨k, rfl⟩

/-- A network permutes values: output at any wire equals some input. -/
private theorem network_exec_exists_preimage {n : ℕ} {α : Type*} [LinearOrder α]
    (net : ComparatorNetwork n) (v : Fin n → α) (k : Fin n) :
    ∃ i : Fin n, net.exec v k = v i := by
  unfold ComparatorNetwork.exec
  induction net.comparators generalizing v with
  | nil => exact ⟨k, rfl⟩
  | cons c cs ih =>
    simp only [List.foldl_cons]
    obtain ⟨j, hj⟩ := ih (c.apply v)
    obtain ⟨i, hi⟩ := Comparator.apply_exists_preimage' c v j
    refine ⟨i, ?_⟩
    rw [hj, hi]

/-! ## Block-local output preservation -/

/-- Every output value on block `b` equals some input value from block `b`.
    Follows from the block Batcher: output at `finalBlockEmbed d hd b i` comes
    from some input at `finalBlockEmbed d hd b j`. -/
theorem parallelFinal_exec_block_range {d : Nat} (hd : 7 ≤ d)
    {α : Type*} [LinearOrder α] (v : Fin (64 ^ d) → α)
    (b : Fin (64 ^ (d - 7))) (i : Fin finalBlockSize) :
    ∃ j : Fin finalBlockSize,
      (chvatalParallelFinalNet d hd).exec v (finalBlockEmbed d hd b i) =
        v (finalBlockEmbed d hd b j) := by
  -- On block b, the parallel final agrees with the Batcher on that block
  rw [chvatalParallelFinalNet_exec_block hd v b i]
  -- The Batcher's output is a permutation of its input values
  obtain ⟨j, hj⟩ := network_exec_exists_preimage (bitonicNetwork finalBlockSize)
    (v ∘ finalBlockEmbed d hd b) i
  exact ⟨j, hj⟩

/-! ## Monotonicity under block separation -/

/-- The parallel final is monotone when the input is block-separated.
    Proof: within each block the output is monotone (Batcher sorts), values
    stay within their block (parallelFinal_exec_block_range), and cross-block
    order is inherited from FinalBlockSeparated. -/
theorem ParallelFinalBlockSeparatedMonotoneResidual_holds (d : Nat) (hd : 7 ≤ d) :
    ParallelFinalBlockSeparatedMonotoneResidual d hd := by
  intro α _ v hv
  intro w₁ w₂ hw
  -- Decode wires as block coordinates
  obtain ⟨b₁, i₁, rfl⟩ := exists_finalBlockCoords d hd w₁
  obtain ⟨b₂, i₂, rfl⟩ := exists_finalBlockCoords d hd w₂
  -- Wire ordering gives block ordering: w₁ ≤ w₂ means (b₁, i₁) ≤ (b₂, i₂)
  have hb : b₁.val * finalBlockSize + i₁.val ≤ b₂.val * finalBlockSize + i₂.val := by
    have : (finalBlockEmbed d hd b₁ i₁).val ≤ (finalBlockEmbed d hd b₂ i₂).val :=
      Fin.le_def.mp hw
    simp only [finalBlockEmbed_val] at this
    exact this
  have hb_blocks : b₁.val ≤ b₂.val := by
    have hw_vals : (finalBlockEmbed d hd b₁ i₁).val ≤ (finalBlockEmbed d hd b₂ i₂).val :=
      Fin.le_def.mp hw
    simp only [finalBlockEmbed_val] at hw_vals
    -- hw_vals: b₁ * finalBlockSize + i₁ ≤ b₂ * finalBlockSize + i₂
    -- Since i₁ < finalBlockSize, we have b₁ * finalBlockSize < (b₁ + 1) * finalBlockSize
    have hi₁ : i₁.val < finalBlockSize := i₁.isLt
    have hi₂ : i₂.val < finalBlockSize := i₂.isLt
    -- From hw_vals: b₁ * finalBlockSize ≤ b₂ * finalBlockSize + finalBlockSize
    have key : b₁.val * finalBlockSize ≤ b₂.val * finalBlockSize + finalBlockSize := by omega
    -- Therefore b₁ ≤ b₂
    by_contra h_neg
    have hb_gt : b₂.val < b₁.val := by omega
    -- From key: b₁ * finalBlockSize ≤ b₂ * finalBlockSize + finalBlockSize
    -- But if b₂ < b₁, then b₂ + 1 ≤ b₁, so b₂ * finalBlockSize + finalBlockSize ≤ b₁ * finalBlockSize
    -- This contradicts key.
    have h_succ : b₂.val + 1 ≤ b₁.val := Nat.succ_le_of_lt hb_gt
    have h_mul_le : (b₂.val + 1) * finalBlockSize ≤ b₁.val * finalBlockSize :=
      Nat.mul_le_mul_right finalBlockSize h_succ
    have h_eq : (b₂.val + 1) * finalBlockSize = b₂.val * finalBlockSize + finalBlockSize := by ring
    rw [h_eq] at h_mul_le
    linarith [key]
  rcases Nat.lt_or_eq_of_le hb_blocks with hb_lt | hb_eq
  · -- b₁ < b₂
    obtain ⟨j₁, hj₁⟩ := parallelFinal_exec_block_range hd v b₁ i₁
    obtain ⟨j₂, hj₂⟩ := parallelFinal_exec_block_range hd v b₂ i₂
    rw [hj₁, hj₂]
    exact hv b₁ b₂ (Fin.lt_def.mpr hb_lt) j₁ j₂
  · -- b₁ = b₂: use Batcher's monotonicity within the block
    have hb_eq_fin : b₁ = b₂ := Fin.ext hb_eq
    subst hb_eq_fin
    have hib : i₁.val ≤ i₂.val := by omega
    have hi : i₁ ≤ i₂ := Fin.le_def.mpr hib
    rw [chvatalParallelFinalNet_exec_block hd v b₁ i₁]
    rw [chvatalParallelFinalNet_exec_block hd v b₁ i₂]
    -- The Batcher sorts on all inputs. We use this for the local view.
    -- Since chvatalParallelFinalNet_exec_block tells us the output on the block
    -- is the Batcher applied to the local view, and Batcher sorts, we get monotonicity.
    exact bitonicNetwork_sorts finalBlockSize α (v ∘ finalBlockEmbed d hd b₁) hi

/-! ## Rank purity corollary -/

/-- Under rank purity (each block contains exactly the ranks of its rank slice),
    block separation holds. -/
lemma FinalBlockSeparated_of_rank_pure (d : Nat) (hd : 7 ≤ d)
    (v : Fin (64 ^ d) → Fin (64 ^ d))
    (hpure : ∀ (b : Fin (64 ^ (d - 7))) (i : Fin finalBlockSize),
      (v (finalBlockEmbed d hd b i)).val / finalBlockSize = b.val) :
    FinalBlockSeparated d hd v := by
  intro b b' hb i j
  -- Values from block b have (v-value) / finalBlockSize = b
  have hvb : (v (finalBlockEmbed d hd b i)).val / finalBlockSize = b.val := hpure b i
  have hvb' : (v (finalBlockEmbed d hd b' j)).val / finalBlockSize = b'.val := hpure b' j
  -- Since b < b', the minimum value in block b' is higher than max in block b
  have hle : b.val < b'.val := Fin.lt_def.mp hb
  -- Using division property: if a / c = d then d * c ≤ a
  have h_lower_b : b.val * finalBlockSize ≤ (v (finalBlockEmbed d hd b i)).val := by
    have := Nat.div_mul_le_self (v (finalBlockEmbed d hd b i)).val finalBlockSize
    rw [hvb] at this
    exact this
  have h_lower_b' : b'.val * finalBlockSize ≤ (v (finalBlockEmbed d hd b' j)).val := by
    have := Nat.div_mul_le_self (v (finalBlockEmbed d hd b' j)).val finalBlockSize
    rw [hvb'] at this
    exact this
  -- Key: (b+1) * finalBlockSize ≤ b' * finalBlockSize when b < b'
  have hblock_bound : (b.val + 1) * finalBlockSize ≤ b'.val * finalBlockSize := by
    have h_succ : b.val + 1 ≤ b'.val := Nat.succ_le_of_lt hle
    exact Nat.mul_le_mul_right finalBlockSize h_succ
  -- v(finalBlockEmbed b i) is strictly less than (b+1) * finalBlockSize
  have hv_upper : (v (finalBlockEmbed d hd b i)).val < (b.val + 1) * finalBlockSize := by
    have h_remainder : (v (finalBlockEmbed d hd b i)).val % finalBlockSize < finalBlockSize :=
      Nat.mod_lt _ (by simp [finalBlockSize])
    -- From division algorithm: a = (a / c) * c + (a % c)
    have h_div_alg := Nat.div_add_mod (v (finalBlockEmbed d hd b i)).val finalBlockSize
    -- h_div_alg: finalBlockSize * ((v ...).val / finalBlockSize) + (v ...).val % finalBlockSize = (v ...).val
    have h_eq : (v (finalBlockEmbed d hd b i)).val / finalBlockSize = b.val := hvb
    rw [h_eq] at h_div_alg
    -- h_div_alg: finalBlockSize * b.val + (v ...).val % finalBlockSize = (v ...).val
    have h_eq' : (v (finalBlockEmbed d hd b i)).val = finalBlockSize * b.val + (v (finalBlockEmbed d hd b i)).val % finalBlockSize :=
      h_div_alg.symm
    have : (v (finalBlockEmbed d hd b i)).val = b.val * finalBlockSize + (v (finalBlockEmbed d hd b i)).val % finalBlockSize := by
      rw [mul_comm] at h_eq'
      exact h_eq'
    linarith
  -- v(finalBlockEmbed b' j) is at least b' * finalBlockSize
  have hv_lower_b' : b'.val * finalBlockSize ≤ (v (finalBlockEmbed d hd b' j)).val := h_lower_b'
  -- Use the chain: v(b,i) < (b+1)*size ≤ b'*size ≤ v(b',j)
  have : (v (finalBlockEmbed d hd b i)).val ≤ (v (finalBlockEmbed d hd b' j)).val := by
    have h1 : (v (finalBlockEmbed d hd b i)).val < (b.val + 1) * finalBlockSize := hv_upper
    have h2 : (b.val + 1) * finalBlockSize ≤ b'.val * finalBlockSize := hblock_bound
    have h3 : b'.val * finalBlockSize ≤ (v (finalBlockEmbed d hd b' j)).val := hv_lower_b'
    linarith
  exact Fin.le_def.mpr this

/-- If the input is a rank-pure permutation, the output is monotone. -/
theorem parallelFinal_monotone_of_rank_pure (d : Nat) (hd : 7 ≤ d)
    (v : Fin (64 ^ d) → Fin (64 ^ d))
    (hpure : ∀ (b : Fin (64 ^ (d - 7))) (i : Fin finalBlockSize),
      (v (finalBlockEmbed d hd b i)).val / finalBlockSize = b.val) :
    Monotone ((chvatalParallelFinalNet d hd).exec v) := by
  have hsep := FinalBlockSeparated_of_rank_pure d hd v hpure
  exact ParallelFinalBlockSeparatedMonotoneResidual_holds d hd v hsep

end Chvatal
