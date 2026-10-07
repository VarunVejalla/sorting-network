module
/-
  # Parallel §7 final sorters (depth only)

  For `d ≥ 7`, tile `64^d` by contiguous `finalBlockSize = 2^42` blocks and
  `scatterEmbed` a Batcher into each. Wire-disjoint flatMap ⇒ depth ≤ 903
  (`finalSorterPaperDepth` / `bitonicDepthBudget 42`).

  **Honest residual:** no `ComparatorNetwork.Sorts` claim; see
  `ParallelFinalPuritySortResidual` (needs purity that each block already holds
  the correct keys). At `d = 7` the full-wire `chvatalFinalBatcherNet` sorts.
-/

public import AKS.Chvatal.DepthSkeleton
public import AKS.Bitonic.TightDepth
public import AKS.Bitonic.Shrink
public import AKS.Sort.Depth
public import AKS.Sort.Monotone
public import AKS.Sort.ParallelScatterFlat
public import Mathlib.Data.List.FinRange

set_option maxRecDepth 4096

@[expose] public section

namespace Chvatal

/-- §7 final block size (`def` so proofs need not unfold `2^42`). -/
def finalBlockSize : Nat := 2 ^ 42

theorem pow64_seven : (64 : Nat) ^ 7 = finalBlockSize := by
  have h64 : (64 : Nat) = 2 ^ 6 := by decide
  unfold finalBlockSize
  calc (64 : Nat) ^ 7
      = (2 ^ 6) ^ 7 := by rw [h64]
    _ = 2 ^ (6 * 7) := by rw [Nat.pow_mul]
    _ = 2 ^ 42 := by norm_num

theorem pow64_eq_finalBlocks (d : Nat) (hd : 7 ≤ d) :
    (64 : Nat) ^ d = 64 ^ (d - 7) * finalBlockSize := by
  have hsplit : d = (d - 7) + 7 := (Nat.sub_add_cancel hd).symm
  calc (64 : Nat) ^ d
      = 64 ^ ((d - 7) + 7) := by rw [← hsplit]
    _ = 64 ^ (d - 7) * 64 ^ 7 := Nat.pow_add _ _ _
    _ = 64 ^ (d - 7) * finalBlockSize := by rw [pow64_seven]

/-- Contiguous `2^42`-blocks tile `64^d` when `7 ≤ d`. -/
theorem finalBlockSize_dvd_pow64 {d : Nat} (hd : 7 ≤ d) :
    finalBlockSize ∣ 64 ^ d := by
  rw [pow64_eq_finalBlocks d hd]
  exact Nat.dvd_mul_left _ _

theorem finalBlock_lt_mul (d : Nat) (b : Fin (64 ^ (d - 7))) (i : Fin finalBlockSize) :
    b.val * finalBlockSize + i.val < 64 ^ (d - 7) * finalBlockSize := by
  have hb := b.isLt
  have hi := i.isLt
  calc b.val * finalBlockSize + i.val
      < b.val * finalBlockSize + finalBlockSize := Nat.add_lt_add_left hi _
    _ = (b.val + 1) * finalBlockSize := (Nat.succ_mul b.val finalBlockSize).symm
    _ ≤ 64 ^ (d - 7) * finalBlockSize :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hb)

theorem finalBlock_wire_lt (d : Nat) (hd : 7 ≤ d)
    (b : Fin (64 ^ (d - 7))) (i : Fin finalBlockSize) :
    b.val * finalBlockSize + i.val < 64 ^ d := by
  rw [pow64_eq_finalBlocks d hd]
  exact finalBlock_lt_mul d b i

theorem finalBlock_offset_gap {b b' : Nat} (hlt : b < b')
    {i : Nat} (hi : i < finalBlockSize) :
    b * finalBlockSize + i < b' * finalBlockSize := by
  have hgap : b + 1 ≤ b' := Nat.succ_le_of_lt hlt
  calc b * finalBlockSize + i
      < b * finalBlockSize + finalBlockSize := Nat.add_lt_add_left hi _
    _ = (b + 1) * finalBlockSize := (Nat.succ_mul b finalBlockSize).symm
    _ ≤ b' * finalBlockSize := Nat.mul_le_mul_right _ hgap

/-! ## Consecutive block embeddings -/

/-- Block `b` occupies wires `[b·finalBlockSize, (b+1)·finalBlockSize)` in `64^d`. -/
def finalBlockEmbed (d : Nat) (hd : 7 ≤ d) (b : Fin (64 ^ (d - 7))) :
    Fin finalBlockSize ↪o Fin (64 ^ d) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨b.val * finalBlockSize + i.val, finalBlock_wire_lt d hd b i⟩)
    (fun {a c} hac => by
      simp only [Fin.lt_def]
      exact Nat.add_lt_add_left hac _)

theorem finalBlockEmbed_val (d : Nat) (hd : 7 ≤ d) (b : Fin (64 ^ (d - 7)))
    (i : Fin finalBlockSize) :
    (finalBlockEmbed d hd b i).val = b.val * finalBlockSize + i.val :=
  rfl

theorem finalBlockEmbed_disjoint (d : Nat) (hd : 7 ≤ d)
    {b b' : Fin (64 ^ (d - 7))} (hne : b ≠ b')
    (i j : Fin finalBlockSize) :
    finalBlockEmbed d hd b i ≠ finalBlockEmbed d hd b' j := by
  intro heq
  have hval : b.val * finalBlockSize + i.val = b'.val * finalBlockSize + j.val :=
    congrArg Fin.val heq
  have hb : b.val ≠ b'.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hb with hlt | hgt
  · have : b.val * finalBlockSize + i.val < b'.val * finalBlockSize :=
      finalBlock_offset_gap hlt i.isLt
    omega
  · have : b'.val * finalBlockSize + j.val < b.val * finalBlockSize :=
      finalBlock_offset_gap hgt j.isLt
    omega

/-! ## Parallel Batcher network -/

/-- One Batcher on block `b`, scatter-embedded into `64^d`. -/
def chvatalFinalBlockNet (d : Nat) (hd : 7 ≤ d) (b : Fin (64 ^ (d - 7))) :
    ComparatorNetwork (64 ^ d) :=
  (bitonicNetwork finalBlockSize).scatterEmbed (64 ^ d) (finalBlockEmbed d hd b)

theorem bitonicNetwork_finalBlockSize_depth_le_903 :
    (bitonicNetwork finalBlockSize).depth ≤ 903 := by
  simpa [finalBlockSize] using bitonicNetwork_2pow42_depth_le_903

theorem chvatalFinalBlockNet_depth_le (d : Nat) (hd : 7 ≤ d)
    (b : Fin (64 ^ (d - 7))) :
    (chvatalFinalBlockNet d hd b).depth ≤ 903 :=
  (depth_scatterEmbed_le (bitonicNetwork finalBlockSize) (64 ^ d)
      (finalBlockEmbed d hd b)).trans bitonicNetwork_finalBlockSize_depth_le_903

theorem chvatalFinalBlockNets_wire_disjoint (d : Nat) (hd : 7 ≤ d)
    {a b : Fin (64 ^ (d - 7))} (hne : a ≠ b)
    (c₁ : Comparator (64 ^ d))
    (hc₁ : c₁ ∈ (chvatalFinalBlockNet d hd a).comparators)
    (c₂ : Comparator (64 ^ d))
    (hc₂ : c₂ ∈ (chvatalFinalBlockNet d hd b).comparators) :
    (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j) := by
  obtain ⟨d₁, _, rfl⟩ := List.mem_map.mp (by
    simpa [chvatalFinalBlockNet, ComparatorNetwork.scatterEmbed] using hc₁)
  obtain ⟨d₂, _, rfl⟩ := List.mem_map.mp (by
    simpa [chvatalFinalBlockNet, ComparatorNetwork.scatterEmbed] using hc₂)
  exact ⟨⟨finalBlockEmbed_disjoint d hd hne d₁.i d₂.i,
      finalBlockEmbed_disjoint d hd hne d₁.i d₂.j⟩,
    ⟨finalBlockEmbed_disjoint d hd hne d₁.j d₂.i,
      finalBlockEmbed_disjoint d hd hne d₁.j d₂.j⟩⟩

/-- Parallel final layer: `64^(d−7)` copies of Batcher on `finalBlockSize` wires. -/
def chvatalParallelFinalNet (d : Nat) (hd : 7 ≤ d) : ComparatorNetwork (64 ^ d) :=
  ⟨(List.finRange (64 ^ (d - 7))).flatMap fun b =>
    (chvatalFinalBlockNet d hd b).comparators⟩

theorem chvatalParallelFinalNet_depth_le (d : Nat) (hd : 7 ≤ d) :
    (chvatalParallelFinalNet d hd).depth ≤ 903 := by
  have hchunk : ∀ b ∈ List.finRange (64 ^ (d - 7)),
      (chvatalFinalBlockNet d hd b).depth ≤ 903 :=
    fun b _ => chvatalFinalBlockNet_depth_le d hd b
  have hdisj :
      (List.finRange (64 ^ (d - 7))).Pairwise (fun a b =>
        ∀ c₁ ∈ (chvatalFinalBlockNet d hd a).comparators,
          ∀ c₂ ∈ (chvatalFinalBlockNet d hd b).comparators,
            (c₁.i ≠ c₂.i ∧ c₁.i ≠ c₂.j) ∧ (c₁.j ≠ c₂.i ∧ c₁.j ≠ c₂.j)) := by
    refine List.Pairwise.imp ?_
      ((List.nodup_iff_pairwise_ne).mp (List.nodup_finRange (64 ^ (d - 7))))
    intro a b hne c₁ hc₁ c₂ hc₂
    exact chvatalFinalBlockNets_wire_disjoint d hd hne c₁ hc₁ c₂ hc₂
  exact depth_flatMap_disjoint (List.finRange (64 ^ (d - 7)))
    (fun b => (chvatalFinalBlockNet d hd b).comparators) 903 hchunk hdisj

theorem chvatalParallelFinalNet_depth_le_paper (d : Nat) (hd : 7 ≤ d) :
    (chvatalParallelFinalNet d hd).depth ≤ finalSorterPaperDepth :=
  chvatalParallelFinalNet_depth_le d hd

theorem chvatalParallelFinalNet_depth_le_budget (d : Nat) (hd : 7 ≤ d) :
    (chvatalParallelFinalNet d hd).depth ≤ bitonicDepthBudget 42 :=
  (chvatalParallelFinalNet_depth_le d hd).trans (le_of_eq bitonicDepthBudget_42.symm)

/-- Depth-only final-stage obligation (no `Sorts`; purity residual remains). -/
structure ParallelFinalDepthObligation (d : Nat) where
  net : ComparatorNetwork (64 ^ d)
  hdepth : net.depth ≤ finalSorterPaperDepth

def ParallelFinalDepthObligation.of_parallelBlocks (d : Nat) (hd : 7 ≤ d) :
    ParallelFinalDepthObligation d where
  net := chvatalParallelFinalNet d hd
  hdepth := chvatalParallelFinalNet_depth_le_paper d hd

/-- Residual: `Sorts` of the parallel final on all inputs. **False in general for
    `d > 7`** (block Batchers do not globally sort arbitrary inputs). The intended
    discharge path is: §7 outsider purity at the meeting level ⇒ each block holds
    the correct keys ⇒ parallel final completes the sort. Kept as a named Prop so
    callers can package conditional results without claiming a false theorem. -/
def ParallelFinalPuritySortResidual (d : Nat) (hd : 7 ≤ d) : Prop :=
  ComparatorNetwork.Sorts.{0} (chvatalParallelFinalNet d hd)

/-- On wires of block `b`, the parallel final agrees with Batcher on that block. -/
theorem chvatalParallelFinalNet_exec_block {d : Nat} (hd : 7 ≤ d)
    {α : Type*} [LinearOrder α] (v : Fin (64 ^ d) → α)
    (b : Fin (64 ^ (d - 7))) (i : Fin finalBlockSize) :
    (chvatalParallelFinalNet d hd).exec v (finalBlockEmbed d hd b i) =
      (bitonicNetwork finalBlockSize).exec (v ∘ finalBlockEmbed d hd b) i := by
  change (parallelScatterFlat (List.finRange (64 ^ (d - 7)))
      (finalBlockEmbed d hd) (bitonicNetwork finalBlockSize)).exec v
      (finalBlockEmbed d hd b i) =
    (bitonicNetwork finalBlockSize).exec (v ∘ finalBlockEmbed d hd b) i
  exact parallelScatterFlat_exec_inside
    (List.finRange (64 ^ (d - 7))) (List.nodup_finRange _)
    (finalBlockEmbed d hd) (bitonicNetwork finalBlockSize)
    (fun a _ha b' _hb hne i j => finalBlockEmbed_disjoint d hd hne i j)
    v b (List.mem_finRange b) i

/-- Cross-block order: every value in block `b` is `≤` every value in a later block. -/
def FinalBlockSeparated (d : Nat) (hd : 7 ≤ d) {α : Type*} [LinearOrder α]
    (v : Fin (64 ^ d) → α) : Prop :=
  ∀ (b b' : Fin (64 ^ (d - 7))), b < b' →
    ∀ (i j : Fin finalBlockSize),
      v (finalBlockEmbed d hd b i) ≤ v (finalBlockEmbed d hd b' j)

/-- Decode any ambient wire as its contiguous final-block coordinates. -/
theorem exists_finalBlockCoords (d : Nat) (hd : 7 ≤ d) (w : Fin (64 ^ d)) :
    ∃ (b : Fin (64 ^ (d - 7))) (i : Fin finalBlockSize),
      w = finalBlockEmbed d hd b i := by
  have hpos : 0 < finalBlockSize := by simp [finalBlockSize]
  have hmul : finalBlockSize * (64 ^ (d - 7)) = 64 ^ d := by
    rw [mul_comm, ← pow64_seven, ← Nat.pow_add, Nat.sub_add_cancel hd]
  have hq : w.val / finalBlockSize < 64 ^ (d - 7) := by
    have hw : w.val < finalBlockSize * (64 ^ (d - 7)) := by
      rw [hmul]; exact w.isLt
    exact Nat.div_lt_of_lt_mul hw
  refine ⟨⟨w.val / finalBlockSize, hq⟩, ⟨w.val % finalBlockSize, Nat.mod_lt _ hpos⟩, ?_⟩
  apply Fin.ext
  -- `finalBlockEmbed` uses `b * finalBlockSize + i`; `div_add_mod` uses the opposite mul order.
  change w.val = (w.val / finalBlockSize) * finalBlockSize + w.val % finalBlockSize
  rw [mul_comm]
  exact (Nat.div_add_mod w.val finalBlockSize).symm

/-- Residual: parallel final is monotone on `FinalBlockSeparated` inputs.
    Needs a "comparator networks permute values" lemma to finish cross-block
    comparisons; same-block case is immediate from `exec_block` + Batcher sorts. -/
def ParallelFinalBlockSeparatedMonotoneResidual (d : Nat) (hd : 7 ≤ d) : Prop :=
  ∀ {α : Type*} [LinearOrder α] (v : Fin (64 ^ d) → α),
    FinalBlockSeparated d hd v →
    Monotone ((chvatalParallelFinalNet d hd).exec v)

/-- At `d = 7` the parallel final is a single full-wire Batcher; `Sorts` holds via
    `chvatalFinalBatcherNet_sorts 7` once the networks are identified (type equality
    `64^7 = finalBlockSize`). Kept as a residual Prop instance path rather than a
    fragile elaborator-heavy transport proof here. -/
theorem ParallelFinalPuritySortResidual_d7_of_batcher
    (h : ComparatorNetwork.Sorts.{0} (chvatalParallelFinalNet 7 (by decide : 7 ≤ 7))) :
    ParallelFinalPuritySortResidual 7 (by decide : 7 ≤ 7) :=
  h

end Chvatal
