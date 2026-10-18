import PacketProfile
import PacketGenMerge
import PacketMergeTreeGen
import PacketReceiverResidue
import AKS.Chvatal.ExecPlacement
import Mathlib.Algebra.Order.Chebyshev

/-! The actual repair atoms are 32-wire rank intervals. This file carries the
sorted-profile scale transfer down to that fragment size. -/

namespace Chvatal.PacketAlignment

open Finset BigOperators

/-- Any merge tree on 4096 wires that has 64 output chunks produces the
exact ideal 64-cell rank profile of its combined Boolean threshold count. -/
theorem genScatterMergeTree_output_profile {N : Nat}
    (tree : PacketMergeTree Bool 4096) (hleaf : tree.leafCount = 64)
    (e : Fin 4096 ↪ Fin N) (v : Fin N → Bool)
    (hRuns : tree.RunsSorted (fun i => v (e i))) (j : Fin 64) :
    boolTrueCount (fun i : Fin 64 =>
      (genScatterMergeTree tree e).exec v
        (genScatterMergeTreeOutputEmbedding tree e (Fin.cast hleaf.symm j) i)) =
      profileCell 64 (boolTrueCount (fun i : Fin 4096 => v (e i))) j.val := by
  let output : Fin 4096 → Bool := fun i => (genScatterMergeTree tree e).exec v (e i)
  have houtput : output = tree.network.exec (v ∘ e) := by
    funext i
    change (genScatter tree.network e).exec v (e i) = _
    exact genScatter_exec_inside _ e v i
  have hsortedNet := PacketMergeTree.network_sorts tree (v ∘ e) hRuns
  have hsorted : Monotone output := by rw [houtput]; exact hsortedNet
  have hcount : boolTrueCount output =
      boolTrueCount (fun i : Fin 4096 => v (e i)) := by
    rw [houtput, boolTrueCount_exec]
    rfl
  have hprofile := @sortedBool_profileCell_trueCount 64 output hsorted
    (boolTrueCount output) rfl j.val j.isLt
  have hchunk : (fun i : Fin 64 =>
      (genScatterMergeTree tree e).exec v
        (genScatterMergeTreeOutputEmbedding tree e (Fin.cast hleaf.symm j) i)) =
      (fun i : Fin 64 => output ⟨j.val * 64 + i.val, by
        have hi := i.isLt
        omega⟩) := by
    funext i
    dsimp [output, genScatterMergeTreeOutputEmbedding, genScatterMergeTree]
    change (genScatter tree.network e).exec v
        (e (PacketMergeTree.chunkIndex tree (Fin.cast hleaf.symm j) i)) =
      (genScatter tree.network e).exec v
        (e ⟨j.val * 64 + i.val, by
          have hi := i.isLt
          omega⟩)
    rw [genScatter_exec_inside, genScatter_exec_inside]
    apply congrArg (fun k : Fin 4096 => tree.network.exec (v ∘ e) k)
    apply Fin.ext
    rw [PacketMergeTree.chunkIndex_val]
    simp [Fin.val_cast, Nat.mul_comm]
  have hprofile' : boolTrueCount (fun i : Fin 64 =>
      output ⟨j.val * 64 + i.val, by omega⟩) =
      profileCell 64 (boolTrueCount output) j.val := by
    simpa [Nat.mul_comm] using hprofile
  calc
    boolTrueCount (fun i : Fin 64 =>
        (genScatterMergeTree tree e).exec v
          (genScatterMergeTreeOutputEmbedding tree e (Fin.cast hleaf.symm j) i)) =
        boolTrueCount (fun i : Fin 64 => output ⟨j.val * 64 + i.val, by
          have hi := i.isLt
          omega⟩) := congrArg boolTrueCount hchunk
    _ = profileCell 64 (boolTrueCount output) j.val := hprofile'
    _ = profileCell 64 (boolTrueCount (fun i : Fin 4096 => v (e i))) j.val := by
      rw [hcount]

/-- A 57-layer merge of 64 sorted 64-wire packets produces the exact ideal
64-cell rank profile of their combined Boolean threshold count. This is the
local change-of-scale law for the 4096-wire cohort merge. -/
theorem packetPowerTree6GroupNet_output_profile {N : Nat}
    (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q)
    (v : Fin N → Bool)
    (hpackets : ∀ j : Fin 64, Monotone (fun i => v (packets j i)))
    (j : Fin 64) :
    boolTrueCount (fun i : Fin 64 =>
      (packetPowerTree6GroupNet (α := Bool) packets hdisjoint).exec v
        (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := Bool))
          (genPacketGroup64Embedding packets hdisjoint)
          (Fin.cast (packetPowerTree6_leafCount (α := Bool)).symm j) i)) =
      profileCell 64
        (boolTrueCount (fun i : Fin 4096 =>
          v (genPacketGroup64Embedding packets hdisjoint i))) j.val := by
  have hRuns := packetPowerTree6_runsSorted_of_packets packets hdisjoint v hpackets
  exact genScatterMergeTree_output_profile (packetPowerTree6 (α := Bool))
    packetPowerTree6_leafCount (genPacketGroup64Embedding packets hdisjoint)
    v hRuns j

/-- The same exact change-of-scale identity holds at every threshold of an
arbitrary ordered input, not just for Boolean-valued data. -/
theorem genScatterMergeTree_output_threshold_profile {N : Nat} {α : Type}
    [LinearOrder α] (tree : PacketMergeTree α 4096)
    (hleaf : tree.leafCount = 64) (e : Fin 4096 ↪ Fin N)
    (v : Fin N → α)
    (hRuns : tree.RunsSorted (fun i => v (e i))) (t : α) (j : Fin 64) :
    boolTrueCount (fun i : Fin 64 => decide (t ≤
      (genScatterMergeTree tree e).exec v
        (genScatterMergeTreeOutputEmbedding tree e (Fin.cast hleaf.symm j) i))) =
      profileCell 64
        (boolTrueCount (fun i : Fin 4096 => decide (t ≤ v (e i)))) j.val := by
  let input : Fin 4096 → Bool := fun i => decide (t ≤ v (e i))
  let output : Fin 4096 → Bool := fun i =>
    decide (t ≤ (genScatterMergeTree tree e).exec v (e i))
  have houtput : output = tree.network.exec input := by
    funext i
    dsimp [output, input]
    calc
      decide (t ≤ (genScatterMergeTree tree e).exec v (e i)) =
          (genScatter tree.network e).exec (fun w => decide (t ≤ v w)) (e i) :=
        (congrFun (genScatter_exec_threshold tree.network e v t) (e i)).symm
      _ = tree.network.exec (fun k => decide (t ≤ v (e k))) i := by
        exact genScatter_exec_inside tree.network e (fun w => decide (t ≤ v w)) i
  have hmap : Monotone (fun x : α => decide (t ≤ x)) := by
    intro x y hxy
    by_cases hx : t ≤ x
    · have hy : t ≤ y := hx.trans hxy
      simp [hx, hy]
    · simp [hx]
  have hsortedNet := PacketMergeTree.network_sorts tree (v ∘ e) hRuns
  have hthreshold : tree.network.exec input =
      fun i => decide (t ≤ tree.network.exec (v ∘ e) i) :=
    exec_threshold tree.network (v ∘ e) t
  have hsorted : Monotone output := by
    rw [houtput, hthreshold]
    exact hmap.comp hsortedNet
  have hcount : boolTrueCount output = boolTrueCount input := by
    rw [houtput, boolTrueCount_exec]
  have hprofile := @sortedBool_profileCell_trueCount 64 output hsorted
    (boolTrueCount output) rfl j.val j.isLt
  have hchunk : (fun i : Fin 64 => decide (t ≤
      (genScatterMergeTree tree e).exec v
        (genScatterMergeTreeOutputEmbedding tree e (Fin.cast hleaf.symm j) i))) =
      (fun i : Fin 64 => output ⟨j.val * 64 + i.val, by
        have hi := i.isLt
        omega⟩) := by
    funext i
    dsimp [output, genScatterMergeTreeOutputEmbedding, genScatterMergeTree]
    change decide (t ≤ (genScatter tree.network e).exec v
        (e (PacketMergeTree.chunkIndex tree (Fin.cast hleaf.symm j) i))) =
      decide (t ≤ (genScatter tree.network e).exec v
        (e ⟨j.val * 64 + i.val, by
          have hi := i.isLt
          omega⟩))
    rw [genScatter_exec_inside, genScatter_exec_inside]
    apply congrArg (fun k : Fin 4096 => decide (t ≤ tree.network.exec (v ∘ e) k))
    apply Fin.ext
    rw [PacketMergeTree.chunkIndex_val]
    simp [Fin.val_cast, Nat.mul_comm]
  have hprofile' : boolTrueCount (fun i : Fin 64 =>
      output ⟨j.val * 64 + i.val, by omega⟩) =
      profileCell 64 (boolTrueCount output) j.val := by
    simpa [Nat.mul_comm] using hprofile
  calc
    _ = boolTrueCount (fun i : Fin 64 =>
        output ⟨j.val * 64 + i.val, by
          have hi := i.isLt
          omega⟩) := congrArg boolTrueCount hchunk
    _ = profileCell 64 (boolTrueCount output) j.val := hprofile'
    _ = profileCell 64 (boolTrueCount input) j.val := by rw [hcount]
    _ = profileCell 64
        (boolTrueCount (fun i : Fin 4096 => decide (t ≤ v (e i)))) j.val := rfl

/-- A complete 4096-wire merge transfers the aggregate threshold-profile
error exactly into its 64 output cells. Reassembly adds no L1 error beyond
the discrepancy of the cohort's total count from its fractional target. -/
theorem genScatterMergeTree_output_threshold_profile_L1_exact {N : Nat}
    {α : Type} [LinearOrder α]
    (tree : PacketMergeTree α 4096) (hleaf : tree.leafCount = 64)
    (e : Fin 4096 ↪ Fin N) (v : Fin N → α)
    (hRuns : tree.RunsSorted (fun i => v (e i))) (t : α)
    (q : Nat) (frac : Real) (hq : q < 4096)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ j : Fin 64,
      |(boolTrueCount (fun i : Fin 64 => decide (t ≤
          (genScatterMergeTree tree e).exec v
            (genScatterMergeTreeOutputEmbedding tree e (Fin.cast hleaf.symm j) i))) : Real) -
        profileCellMean 64 q frac j.val|) =
      |((boolTrueCount (fun i : Fin 4096 => decide (t ≤ v (e i))) : Real) -
        (q + frac))| := by
  let X := boolTrueCount (fun i : Fin 4096 => decide (t ≤ v (e i)))
  have hX : X ≤ 4096 := by
    simpa [X, boolTrueCount] using
      (Fintype.card_subtype_le (fun i : Fin 4096 => decide (t ≤ v (e i)) = true))
  calc
    (∑ j : Fin 64,
        |(boolTrueCount (fun i : Fin 64 => decide (t ≤
            (genScatterMergeTree tree e).exec v
              (genScatterMergeTreeOutputEmbedding tree e (Fin.cast hleaf.symm j) i))) : Real) -
          profileCellMean 64 q frac j.val|) =
      ∑ j : Fin 64,
        |(profileCell 64 X j.val : Real) - profileCellMean 64 q frac j.val| := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [genScatterMergeTree_output_threshold_profile tree hleaf e v hRuns t
        j]
    _ = ∑ j ∈ Finset.range 64,
        |(profileCell 64 X j : Real) - profileCellMean 64 q frac j| :=
      Fin.sum_univ_eq_sum_range
        (fun j : Nat => |(profileCell 64 X j : Real) - profileCellMean 64 q frac j|) 64
    _ = |(X : Real) - (q + frac)| :=
      profileCellMean_L1_exact 64 X q frac hq hX hfrac0 hfrac1
    _ = |((boolTrueCount (fun i : Fin 4096 => decide (t ≤ v (e i))) : Real) -
        (q + frac))| := by rfl

/-- Threshold-profile transfer for a merge tree with any number `K` of
64-wire output packets. This includes the 63-packet unequal tail tree. -/
theorem genScatterMergeTree_output_threshold_profile_k {K N : Nat}
    {α : Type} [LinearOrder α] (tree : PacketMergeTree α (64 * K))
    (hleaf : tree.leafCount = K) (e : Fin (64 * K) ↪ Fin N)
    (v : Fin N → α)
    (hRuns : tree.RunsSorted (fun i => v (e i))) (t : α) (j : Fin K) :
    boolTrueCount (fun i : Fin 64 => decide (t ≤
      (genScatterMergeTree tree e).exec v
        (genScatterMergeTreeOutputEmbedding tree e (Fin.cast hleaf.symm j) i))) =
      profileCell K
        (boolTrueCount (fun i : Fin (64 * K) => decide (t ≤ v (e i)))) j.val := by
  let input : Fin (64 * K) → Bool := fun i => decide (t ≤ v (e i))
  let output : Fin (64 * K) → Bool := fun i =>
    decide (t ≤ (genScatterMergeTree tree e).exec v (e i))
  have houtput : output = tree.network.exec input := by
    funext i
    dsimp [output, input]
    calc
      decide (t ≤ (genScatterMergeTree tree e).exec v (e i)) =
          (genScatter tree.network e).exec (fun w => decide (t ≤ v w)) (e i) :=
        (congrFun (genScatter_exec_threshold tree.network e v t) (e i)).symm
      _ = tree.network.exec (fun k => decide (t ≤ v (e k))) i := by
        exact genScatter_exec_inside tree.network e (fun w => decide (t ≤ v w)) i
  have hmap : Monotone (fun x : α => decide (t ≤ x)) := by
    intro x y hxy
    by_cases hx : t ≤ x
    · have hy : t ≤ y := hx.trans hxy
      simp [hx, hy]
    · simp [hx]
  have hsortedNet := PacketMergeTree.network_sorts tree (v ∘ e) hRuns
  have hthreshold : tree.network.exec input =
      fun i => decide (t ≤ tree.network.exec (v ∘ e) i) :=
    exec_threshold tree.network (v ∘ e) t
  have hsorted : Monotone output := by
    rw [houtput, hthreshold]
    exact hmap.comp hsortedNet
  have hcount : boolTrueCount output = boolTrueCount input := by
    rw [houtput, boolTrueCount_exec]
  have hprofile := @sortedBool_profileCell_trueCount K output hsorted
    (boolTrueCount output) rfl j.val j.isLt
  have hchunk : (fun i : Fin 64 => decide (t ≤
      (genScatterMergeTree tree e).exec v
        (genScatterMergeTreeOutputEmbedding tree e (Fin.cast hleaf.symm j) i))) =
      (fun i : Fin 64 => output ⟨j.val * 64 + i.val, by
        have hi := i.isLt
        omega⟩) := by
    funext i
    dsimp [output, genScatterMergeTreeOutputEmbedding, genScatterMergeTree]
    change decide (t ≤ (genScatter tree.network e).exec v
        (e (PacketMergeTree.chunkIndex tree (Fin.cast hleaf.symm j) i))) =
      decide (t ≤ (genScatter tree.network e).exec v
        (e ⟨j.val * 64 + i.val, by
          have hi := i.isLt
          omega⟩))
    rw [genScatter_exec_inside, genScatter_exec_inside]
    apply congrArg (fun k : Fin (64 * K) => decide (t ≤ tree.network.exec (v ∘ e) k))
    apply Fin.ext
    rw [PacketMergeTree.chunkIndex_val]
    simp [Fin.val_cast, Nat.mul_comm]
  have hprofile' : boolTrueCount (fun i : Fin 64 =>
      output ⟨j.val * 64 + i.val, by omega⟩) =
      profileCell K (boolTrueCount output) j.val := by
    simpa [Nat.mul_comm] using hprofile
  calc
    _ = boolTrueCount (fun i : Fin 64 =>
        output ⟨j.val * 64 + i.val, by
          have hi := i.isLt
          omega⟩) := congrArg boolTrueCount hchunk
    _ = profileCell K (boolTrueCount output) j.val := hprofile'
    _ = profileCell K (boolTrueCount input) j.val := by rw [hcount]
    _ = profileCell K
        (boolTrueCount (fun i : Fin (64 * K) => decide (t ≤ v (e i)))) j.val := rfl

/-- The threshold-profile law for the concrete 57-layer 64-run merge,
assuming its 64 input packets are sorted. -/
theorem packetPowerTree6GroupNet_output_threshold_profile {N : Nat}
    {α : Type} [LinearOrder α]
    (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q)
    (v : Fin N → α)
    (hpackets : ∀ j : Fin 64, Monotone (fun i => v (packets j i)))
    (t : α) (j : Fin 64) :
    boolTrueCount (fun i : Fin 64 => decide (t ≤
      (packetPowerTree6GroupNet (α := α) packets hdisjoint).exec v
        (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α))
          (genPacketGroup64Embedding packets hdisjoint)
          (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) =
      profileCell 64
        (boolTrueCount (fun i : Fin 4096 =>
          decide (t ≤ v (genPacketGroup64Embedding packets hdisjoint i)))) j.val := by
  have hRuns := packetPowerTree6_runsSorted_of_packets packets hdisjoint v hpackets
  exact genScatterMergeTree_output_threshold_profile (packetPowerTree6 (α := α))
    packetPowerTree6_leafCount (genPacketGroup64Embedding packets hdisjoint)
    v hRuns t j

/-! A 4096-wire merge batch reassembles heterogeneous input-packet targets
without creating aggregate L1 profile error. -/

/-- The aggregate output rank-profile error after a 64-packet merge is
exactly the absolute value of the *signed sum* of the input count errors.
Thus opposite source errors cancel completely during reassembly; the
triangle-inequality version below loses this information. -/
theorem packetPowerTree6GroupNet_heterogeneous_profile_error_exact {N : Nat}
    {α : Type} [LinearOrder α]
    (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q)
    (v : Fin N → α)
    (hpackets : ∀ j : Fin 64, Monotone (fun i => v (packets j i)))
    (t : α) (q : Nat) (frac : Real) (μ : Fin 64 → Real)
    (hq : q < 4096) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (hμ : (∑ j : Fin 64, μ j) = q + frac) :
    (∑ j : Fin 64,
      |(boolTrueCount (fun i : Fin 64 => decide (t ≤
          (packetPowerTree6GroupNet (α := α) packets hdisjoint).exec v
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α))
              (genPacketGroup64Embedding packets hdisjoint)
              (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) : Real) -
        profileCellMean 64 q frac j.val|) =
      |∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j)| := by
  let e := genPacketGroup64Embedding packets hdisjoint
  let X := boolTrueCount (fun i : Fin 4096 => decide (t ≤ v (e i)))
  have hsum : X = ∑ j : Fin 64,
      boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) := by
    exact boolTrueCount_genPacketGroup64Embedding_sum packets hdisjoint
      (fun x => decide (t ≤ v x))
  have hscalar : (X : Real) - (q + frac) =
      ∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j) := by
    rw [Finset.sum_sub_distrib]
    have hcounts : (∑ j : Fin 64,
        (boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real)) =
        (X : Real) := by
      exact_mod_cast hsum.symm
    rw [hcounts, hμ]
  have hexact := genScatterMergeTree_output_threshold_profile_L1_exact
    (packetPowerTree6 (α := α)) packetPowerTree6_leafCount e v
    (packetPowerTree6_runsSorted_of_packets packets hdisjoint v hpackets)
    t q frac hq hfrac0 hfrac1
  calc
    _ = |(X : Real) - (q + frac)| := by
      simpa only [e, X, packetPowerTree6GroupNet] using hexact
    _ = |∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j)| :=
      by
        exact congrArg (fun z : Real => |z|) hscalar

/-- Quadratic version of the signed cancellation law: the entire output
rank-profile energy is bounded by the square of the group's net input error.
In particular, a zero-sum input error vector leaves no output profile error. -/
theorem packetPowerTree6GroupNet_heterogeneous_profile_energy_le_signed_sum_sq
    {N : Nat} {α : Type} [LinearOrder α]
    (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q)
    (v : Fin N → α)
    (hpackets : ∀ j : Fin 64, Monotone (fun i => v (packets j i)))
    (t : α) (q : Nat) (frac : Real) (μ : Fin 64 → Real)
    (hq : q < 4096) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (hμ : (∑ j : Fin 64, μ j) = q + frac) :
    (∑ j : Fin 64,
      ((boolTrueCount (fun i : Fin 64 => decide (t ≤
          (packetPowerTree6GroupNet (α := α) packets hdisjoint).exec v
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α))
              (genPacketGroup64Embedding packets hdisjoint)
              (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) : Real) -
        profileCellMean 64 q frac j.val) ^ 2) ≤
      (∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j)) ^ 2 := by
  let outErr (j : Fin 64) : Real :=
    (boolTrueCount (fun i : Fin 64 => decide (t ≤
      (packetPowerTree6GroupNet (α := α) packets hdisjoint).exec v
        (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α))
          (genPacketGroup64Embedding packets hdisjoint)
          (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) : Real) -
      profileCellMean 64 q frac j.val
  have hexact := packetPowerTree6GroupNet_heterogeneous_profile_error_exact
    (N := N) (packets := packets) hdisjoint v hpackets t q frac μ hq hfrac0 hfrac1 hμ
  have hL1 : (∑ j : Fin 64, |outErr j|) =
      |∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j)| := by
    simpa only [outErr] using hexact
  calc
    _ = ∑ j : Fin 64, |outErr j| ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [sq_abs]
    _ ≤ (∑ j : Fin 64, |outErr j|) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => abs_nonneg (outErr j))
    _ = (∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j)) ^ 2 := by
      rw [hL1, sq_abs]

/-- With energy normalized by the 64 output rank cells, reassembly is
nonexpansive relative to the input packet-count energy. More strongly, the
preceding signed-residual bound shows that the within-group zero-sum modes
are projected away. -/
theorem packetPowerTree6GroupNet_heterogeneous_profile_energy_normalized_le
    {N : Nat} {α : Type} [LinearOrder α]
    (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q)
    (v : Fin N → α)
    (hpackets : ∀ j : Fin 64, Monotone (fun i => v (packets j i)))
    (t : α) (q : Nat) (frac : Real) (μ : Fin 64 → Real)
    (hq : q < 4096) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (hμ : (∑ j : Fin 64, μ j) = q + frac) :
    (∑ j : Fin 64,
      ((boolTrueCount (fun i : Fin 64 => decide (t ≤
          (packetPowerTree6GroupNet (α := α) packets hdisjoint).exec v
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α))
              (genPacketGroup64Embedding packets hdisjoint)
              (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) : Real) -
        profileCellMean 64 q frac j.val) ^ 2) / 64 ≤
      ∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j) ^ 2 := by
  have henergy := packetPowerTree6GroupNet_heterogeneous_profile_energy_le_signed_sum_sq
    (N := N) (packets := packets) hdisjoint v hpackets t q frac μ hq hfrac0 hfrac1 hμ
  have hcs : (∑ j : Fin 64, ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j)) ^ 2 ≤
      64 * (∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j) ^ 2) := by
    have h := _root_.sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin 64)))
      (f := fun j : Fin 64 =>
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j))
    simpa using h
  rw [div_le_iff₀ (by norm_num : (0 : Real) < 64)]
  calc
    _ ≤ (∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j)) ^ 2 :=
      henergy
    _ ≤ 64 * ∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j) ^ 2 :=
      hcs
    _ = (∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j) ^ 2) * 64 := by
      ring

/-- The output rank-cell error of a 64-packet merge is bounded by the sum of
the input packets' count errors against arbitrary fractional targets whose
total is the batch target. The reassembly itself contributes no fresh L1
error. -/
theorem packetPowerTree6GroupNet_heterogeneous_profile_error_le {N : Nat}
    {α : Type} [LinearOrder α]
    (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q)
    (v : Fin N → α)
    (hpackets : ∀ j : Fin 64, Monotone (fun i => v (packets j i)))
    (t : α) (q : Nat) (frac : Real) (μ : Fin 64 → Real)
    (hq : q < 4096) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (hμ : (∑ j : Fin 64, μ j) = q + frac) :
    (∑ j : Fin 64,
      |(boolTrueCount (fun i : Fin 64 => decide (t ≤
          (packetPowerTree6GroupNet (α := α) packets hdisjoint).exec v
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α))
              (genPacketGroup64Embedding packets hdisjoint)
              (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) : Real) -
        profileCellMean 64 q frac j.val|) ≤
      ∑ j : Fin 64,
        |(boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j| := by
  let e := genPacketGroup64Embedding packets hdisjoint
  let X := boolTrueCount (fun i : Fin 4096 => decide (t ≤ v (e i)))
  have hsum : X = ∑ j : Fin 64,
      boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) := by
    exact boolTrueCount_genPacketGroup64Embedding_sum packets hdisjoint
      (fun x => decide (t ≤ v x))
  have hscalar : (X : Real) - (q + frac) =
      ∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j) := by
    rw [Finset.sum_sub_distrib]
    have hcounts : (∑ j : Fin 64,
        (boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real)) =
        (X : Real) := by
      exact_mod_cast hsum.symm
    rw [hcounts, hμ]
  have hexact := genScatterMergeTree_output_threshold_profile_L1_exact
    (packetPowerTree6 (α := α)) packetPowerTree6_leafCount e v
    (packetPowerTree6_runsSorted_of_packets packets hdisjoint v hpackets)
    t q frac hq hfrac0 hfrac1
  calc
    _ = |(X : Real) - (q + frac)| := by
      simpa only [e, X, packetPowerTree6GroupNet] using hexact
    _ = |∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j)| :=
      congrArg abs hscalar
    _ ≤ ∑ j : Fin 64,
        |(boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j| := by
      simpa using Finset.abs_sum_le_sum_abs
        (s := Finset.univ) (f := fun j : Fin 64 =>
          (boolTrueCount (fun i : Fin 64 => decide (t ≤ v (packets j i))) : Real) - μ j)

/-- A parallel batch of 4096-wire merge trees preserves the exact threshold
profile on every output chunk of every disjoint block. -/
theorem genScatterMergeTreeBatch_output_threshold_profile {N : Nat}
    {α : Type} [LinearOrder α] (tree : PacketMergeTree α 4096)
    (hleaf : tree.leafCount = 64)
    (supports : List (Fin 4096 ↪ Fin N)) (hnd : supports.Nodup)
    (hdis : ∀ e ∈ supports, ∀ f ∈ supports, e ≠ f →
      ∀ i j, e i ≠ f j)
    (v : Fin N → α)
    (hRuns : ∀ e ∈ supports, tree.RunsSorted (fun i => v (e i)))
    (e : Fin 4096 ↪ Fin N) (he : e ∈ supports)
    (t : α) (j : Fin 64) :
    boolTrueCount (fun i : Fin 64 => decide (t ≤
      (genScatterMergeTreeBatch tree supports).exec v
        (genScatterMergeTreeOutputEmbedding tree e (Fin.cast hleaf.symm j) i))) =
      profileCell 64 (boolTrueCount (fun i : Fin 4096 => decide (t ≤ v (e i))))
        j.val := by
  have hEq : (fun i : Fin 64 => decide (t ≤
      (genScatterMergeTreeBatch tree supports).exec v
        (genScatterMergeTreeOutputEmbedding tree e (Fin.cast hleaf.symm j) i))) =
      (fun i : Fin 64 => decide (t ≤
        (genScatterMergeTree tree e).exec v
          (genScatterMergeTreeOutputEmbedding tree e (Fin.cast hleaf.symm j) i))) := by
    funext i
    change decide (t ≤ (genScatterMergeTreeBatch tree supports).exec v
        (e (PacketMergeTree.chunkIndex tree (Fin.cast hleaf.symm j) i))) =
      decide (t ≤ (genScatterMergeTree tree e).exec v
        (e (PacketMergeTree.chunkIndex tree (Fin.cast hleaf.symm j) i)))
    change decide (t ≤ (genScatterBatch tree.network supports).exec v
        (e (PacketMergeTree.chunkIndex tree (Fin.cast hleaf.symm j) i))) = _
    rw [genScatterBatch_exec_inside tree.network supports hnd hdis v e he
      (PacketMergeTree.chunkIndex tree (Fin.cast hleaf.symm j) i)]
    rfl
  rw [hEq]
  exact genScatterMergeTree_output_threshold_profile tree hleaf e v
    (hRuns e he) t j

/-- The standard divisible-cohort decomposition carries exact rank profiles,
not just sortedness, through all of its parallel full-block merges. -/
theorem packetFamily64BlockList_merge_output_threshold_profile {q N : Nat}
    {α : Type} [LinearOrder α]
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (v : Fin N → α)
    (hpackets : ∀ a, Monotone (fun i => v (packets a i))) (t : α) :
    ∀ e ∈ packetFamily64BlockList packets hdis,
      ∀ j : Fin 64,
        boolTrueCount (fun i : Fin 64 => decide (t ≤
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α))
            (packetFamily64BlockList packets hdis)).exec v
              (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e
                (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) =
        profileCell 64
          (boolTrueCount (fun i : Fin 4096 => decide (t ≤ v (e i)))) j.val := by
  have hnd := packetFamily64BlockList_nodup packets hdis
  have hdisBlocks := packetFamily64BlockList_disjoint packets hdis
  have hRuns : ∀ e ∈ packetFamily64BlockList packets hdis,
      (packetPowerTree6 (α := α)).RunsSorted (fun i => v (e i)) := by
    intro e he
    simp only [packetFamily64BlockList, List.mem_ofFn] at he
    obtain ⟨g, rfl⟩ := he
    have hinner : ∀ {a b : Fin 64}, a ≠ b → ∀ x y,
        packets (packetFamily64BlockIndex g a) x ≠
          packets (packetFamily64BlockIndex g b) y := by
      intro a b hab x y
      apply hdis _ _ ?_ x y
      intro h
      apply hab
      exact packetFamily64BlockIndex_injective g h
    have hlocal := packetPowerTree6_runsSorted_of_packets
      (fun a => packets (packetFamily64BlockIndex g a)) hinner v
      (fun a => hpackets (packetFamily64BlockIndex g a))
    simpa [packetFamily64BlockEmbedding] using hlocal
  intro e he j
  have hleaf := packetPowerTree6_leafCount (α := α)
  exact genScatterMergeTreeBatch_output_threshold_profile
    (packetPowerTree6 (α := α)) hleaf (packetFamily64BlockList packets hdis)
    hnd hdisBlocks v hRuns e he t j

/-- Batch form of the signed-error contraction: each 4096-wire cohort's
output rank-profile energy is charged only to that cohort's net input error,
so cancellation is retained independently across all disjoint blocks. -/
theorem packetFamily64BlockList_merge_heterogeneous_profile_energy_le
    {q N : Nat} {α : Type} [LinearOrder α]
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (v : Fin N → α) (t : α)
    (hpackets : ∀ a, Monotone (fun i => v (packets a i)))
    (μ : Fin (q * 64) → Real) (targetQ : Fin q → Nat)
    (frac : Fin q → Real)
    (hbase : ∀ g, targetQ g < 4096)
    (hfrac0 : ∀ g, 0 ≤ frac g) (hfrac1 : ∀ g, frac g ≤ 1)
    (htarget : ∀ g, (∑ i : Fin 64,
      μ (packetFamily64BlockIndex g i)) = targetQ g + frac g) :
    (∑ g : Fin q, ∑ j : Fin 64,
      ((boolTrueCount (fun i : Fin 64 => decide (t ≤
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α))
            (packetFamily64BlockList packets hdis)).exec v
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α))
              (packetFamily64BlockEmbedding packets hdis g)
              (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) : Real) -
        profileCellMean 64 (targetQ g) (frac g) j.val) ^ 2) ≤
    ∑ g : Fin q,
      (∑ i : Fin 64,
        ((boolTrueCount (fun k : Fin 64 => decide (t ≤ v
          (packets (packetFamily64BlockIndex g i) k))) : Real) -
          μ (packetFamily64BlockIndex g i))) ^ 2 := by
  classical
  let blocks := packetFamily64BlockList packets hdis
  let batch := genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks
  have hprofile := packetFamily64BlockList_merge_output_threshold_profile
    packets hdis v hpackets
  apply Finset.sum_le_sum
  intro g _
  let localPackets : Fin 64 → Fin 64 ↪ Fin N :=
    fun i => packets (packetFamily64BlockIndex g i)
  have hinner : ∀ {i k : Fin 64}, i ≠ k → ∀ x y,
      localPackets i x ≠ localPackets k y := by
    intro i k hik x y
    apply hdis (packetFamily64BlockIndex g i) (packetFamily64BlockIndex g k)
      (by
        intro h
        apply hik
        exact packetFamily64BlockIndex_injective g h) x y
  let e := genPacketGroup64Embedding localPackets hinner
  let X := boolTrueCount (fun k : Fin 4096 => decide (t ≤ v (e k)))
  have hsum : X = ∑ i : Fin 64,
      boolTrueCount (fun k : Fin 64 => decide (t ≤ v (localPackets i k))) := by
    exact boolTrueCount_genPacketGroup64Embedding_sum localPackets hinner
      (fun w => decide (t ≤ v w))
  have hX : X ≤ 4096 := by
    simpa [X, boolTrueCount] using
      (Fintype.card_subtype_le (fun k : Fin 4096 =>
        decide (t ≤ v (e k)) = true))
  have he : packetFamily64BlockEmbedding packets hdis g ∈ blocks := by
    simp [blocks, packetFamily64BlockList]
  have hsourceProfile (j : Fin 64) :
      boolTrueCount (fun i : Fin 64 => decide (t ≤
        batch.exec v (genScatterMergeTreeOutputEmbedding
          (packetPowerTree6 (α := α)) (packetFamily64BlockEmbedding packets hdis g)
          (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) =
        profileCell 64 X j.val := by
    have hp := hprofile t (packetFamily64BlockEmbedding packets hdis g) he j
    simpa [batch, blocks, e, X, packetFamily64BlockEmbedding, localPackets] using hp
  have hL1 :
      (∑ j : Fin 64,
        |(profileCell 64 X j.val : Real) -
          profileCellMean 64 (targetQ g) (frac g) j.val|) =
        |(X : Real) - (targetQ g + frac g)| := by
    exact profileCellMean_L1_exact 64 X (targetQ g) (frac g)
      (hbase g) hX (hfrac0 g) (hfrac1 g)
  have hscalar : (X : Real) - (targetQ g + frac g) =
      ∑ i : Fin 64,
        ((boolTrueCount (fun k : Fin 64 => decide (t ≤ v (localPackets i k))) : Real) -
          μ (packetFamily64BlockIndex g i)) := by
    rw [Finset.sum_sub_distrib]
    have hcounts : (∑ i : Fin 64,
        (boolTrueCount (fun k : Fin 64 => decide (t ≤ v (localPackets i k))) : Real)) =
        (X : Real) := by
      exact_mod_cast hsum.symm
    rw [hcounts, htarget g]
  have hL1out :
      (∑ j : Fin 64,
        |(boolTrueCount (fun i : Fin 64 => decide (t ≤
            batch.exec v (genScatterMergeTreeOutputEmbedding
              (packetPowerTree6 (α := α)) (packetFamily64BlockEmbedding packets hdis g)
              (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) : Real) -
          profileCellMean 64 (targetQ g) (frac g) j.val|) =
        |(X : Real) - (targetQ g + frac g)| := by
    calc
      _ = ∑ j : Fin 64,
          |(profileCell 64 X j.val : Real) -
            profileCellMean 64 (targetQ g) (frac g) j.val| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hsourceProfile j]
      _ = _ := hL1
  have hAbs :
      |(X : Real) - (targetQ g + frac g)| =
        |∑ i : Fin 64,
          ((boolTrueCount (fun k : Fin 64 => decide (t ≤ v (localPackets i k))) : Real) -
            μ (packetFamily64BlockIndex g i))| :=
    congrArg abs hscalar
  have henergy :
      (∑ j : Fin 64,
        ((boolTrueCount (fun i : Fin 64 => decide (t ≤
            batch.exec v (genScatterMergeTreeOutputEmbedding
              (packetPowerTree6 (α := α)) (packetFamily64BlockEmbedding packets hdis g)
              (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) : Real) -
          profileCellMean 64 (targetQ g) (frac g) j.val) ^ 2) ≤
      (∑ i : Fin 64,
        ((boolTrueCount (fun k : Fin 64 => decide (t ≤ v (localPackets i k))) : Real) -
          μ (packetFamily64BlockIndex g i))) ^ 2 := by
    calc
      _ = ∑ j : Fin 64,
          |(boolTrueCount (fun i : Fin 64 => decide (t ≤
              batch.exec v (genScatterMergeTreeOutputEmbedding
                (packetPowerTree6 (α := α)) (packetFamily64BlockEmbedding packets hdis g)
                (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) : Real) -
            profileCellMean 64 (targetQ g) (frac g) j.val| ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [sq_abs]
      _ ≤ (∑ j : Fin 64,
          |(boolTrueCount (fun i : Fin 64 => decide (t ≤
              batch.exec v (genScatterMergeTreeOutputEmbedding
                (packetPowerTree6 (α := α)) (packetFamily64BlockEmbedding packets hdis g)
                (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) : Real) -
            profileCellMean 64 (targetQ g) (frac g) j.val|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => abs_nonneg _)
      _ = |(X : Real) - (targetQ g + frac g)| ^ 2 := by rw [← hL1out]
      _ = _ := by rw [hAbs, sq_abs]
  exact henergy

/-- Exact threshold profiles survive the disjoint full-plus-tail batch: full
blocks retain their 64-cell profiles and the unequal tail retains its
K-cell profile. -/
theorem genMergeTreeFullTailBatch_output_threshold_profile {K N : Nat}
    {α : Type} [LinearOrder α]
    (fullTree : PacketMergeTree α 4096) (hfullLeaf : fullTree.leafCount = 64)
    (tailTree : PacketMergeTree α (64 * K)) (htailLeaf : tailTree.leafCount = K)
    (fullBlocks : List (Fin 4096 ↪ Fin N)) (tail : Fin (64 * K) ↪ Fin N)
    (hnd : fullBlocks.Nodup)
    (hdis : ∀ e ∈ fullBlocks, ∀ f ∈ fullBlocks, e ≠ f → ∀ i j, e i ≠ f j)
    (hsep : ∀ e ∈ fullBlocks, ∀ i j, e i ≠ tail j)
    (v : Fin N → α)
    (hfullRuns : ∀ e ∈ fullBlocks, fullTree.RunsSorted (fun i => v (e i)))
    (htailRuns : tailTree.RunsSorted (fun i => v (tail i))) (t : α) :
    (∀ e ∈ fullBlocks, ∀ j : Fin 64,
      boolTrueCount (fun i : Fin 64 => decide (t ≤
        (genMergeTreeFullTailBatch fullTree tailTree fullBlocks tail).exec v
          (genScatterMergeTreeOutputEmbedding fullTree e
            (Fin.cast hfullLeaf.symm j) i))) =
      profileCell 64 (boolTrueCount (fun i : Fin 4096 => decide (t ≤ v (e i)))) j.val) ∧
    (∀ j : Fin K,
      boolTrueCount (fun i : Fin 64 => decide (t ≤
        (genMergeTreeFullTailBatch fullTree tailTree fullBlocks tail).exec v
          (genScatterMergeTreeOutputEmbedding tailTree tail
            (Fin.cast htailLeaf.symm j) i))) =
      profileCell K (boolTrueCount (fun i : Fin (64 * K) => decide (t ≤ v (tail i))))
        j.val) := by
  let G := genScatterMergeTreeBatch fullTree fullBlocks
  let H := genScatterMergeTree tailTree tail
  have hexec : (genMergeTreeFullTailBatch fullTree tailTree fullBlocks tail).exec v =
      H.exec (G.exec v) := by
    simp [genMergeTreeFullTailBatch, G, H, Untangle.GenNetwork.exec,
      List.foldl_append]
  constructor
  · intro e he j
    have hEq : (fun i : Fin 64 => decide (t ≤
        (genMergeTreeFullTailBatch fullTree tailTree fullBlocks tail).exec v
          (genScatterMergeTreeOutputEmbedding fullTree e
            (Fin.cast hfullLeaf.symm j) i))) =
        (fun i : Fin 64 => decide (t ≤
          G.exec v (genScatterMergeTreeOutputEmbedding fullTree e
            (Fin.cast hfullLeaf.symm j) i))) := by
      funext i
      rw [hexec]
      change decide (t ≤ (genScatter tailTree.network tail).exec (G.exec v)
          (e (PacketMergeTree.chunkIndex fullTree (Fin.cast hfullLeaf.symm j) i))) = _
      exact congrArg (fun x : α => decide (t ≤ x))
        (genScatter_exec_outside tailTree.network tail (G.exec v)
          (e (PacketMergeTree.chunkIndex fullTree (Fin.cast hfullLeaf.symm j) i)) (by
            rintro ⟨k, hk⟩
            exact (hsep e he (PacketMergeTree.chunkIndex fullTree
              (Fin.cast hfullLeaf.symm j) i) k) hk.symm))
    calc
      _ = boolTrueCount (fun i : Fin 64 => decide (t ≤
          G.exec v (genScatterMergeTreeOutputEmbedding fullTree e
            (Fin.cast hfullLeaf.symm j) i))) := congrArg boolTrueCount hEq
      _ = profileCell 64 (boolTrueCount (fun i : Fin 4096 => decide (t ≤ v (e i))))
          j.val := genScatterMergeTreeBatch_output_threshold_profile fullTree
            hfullLeaf fullBlocks hnd hdis v hfullRuns e he t j
  · intro j
    have hEq : (fun i : Fin 64 => decide (t ≤
        (genMergeTreeFullTailBatch fullTree tailTree fullBlocks tail).exec v
          (genScatterMergeTreeOutputEmbedding tailTree tail
            (Fin.cast htailLeaf.symm j) i))) =
        (fun i : Fin 64 => decide (t ≤
          H.exec v (genScatterMergeTreeOutputEmbedding tailTree tail
            (Fin.cast htailLeaf.symm j) i))) := by
      funext i
      rw [hexec]
      change decide (t ≤ H.exec (G.exec v)
          (tail (PacketMergeTree.chunkIndex tailTree (Fin.cast htailLeaf.symm j) i))) = _
      have htailInput : G.exec v ∘ tail = v ∘ tail := by
        funext k
        exact genScatterBatch_exec_outside fullTree.network fullBlocks (tail k) (by
          intro e he heRange
          obtain ⟨k', hk'⟩ := heRange
          exact (hsep e he k' k) hk') v
      have hRaw : H.exec (G.exec v)
          (tail (PacketMergeTree.chunkIndex tailTree (Fin.cast htailLeaf.symm j) i)) =
          H.exec v (tail (PacketMergeTree.chunkIndex tailTree
            (Fin.cast htailLeaf.symm j) i)) := by
        calc
          H.exec (G.exec v)
              (tail (PacketMergeTree.chunkIndex tailTree (Fin.cast htailLeaf.symm j) i)) =
              tailTree.network.exec (G.exec v ∘ tail)
                (PacketMergeTree.chunkIndex tailTree (Fin.cast htailLeaf.symm j) i) :=
            genScatter_exec_inside tailTree.network tail (G.exec v)
              (PacketMergeTree.chunkIndex tailTree (Fin.cast htailLeaf.symm j) i)
          _ = tailTree.network.exec (v ∘ tail)
                (PacketMergeTree.chunkIndex tailTree (Fin.cast htailLeaf.symm j) i) :=
            congrArg (fun f : Fin (64 * K) → α => tailTree.network.exec f
              (PacketMergeTree.chunkIndex tailTree (Fin.cast htailLeaf.symm j) i))
                htailInput
          _ = H.exec v
              (tail (PacketMergeTree.chunkIndex tailTree (Fin.cast htailLeaf.symm j) i)) :=
            (genScatter_exec_inside tailTree.network tail v
              (PacketMergeTree.chunkIndex tailTree (Fin.cast htailLeaf.symm j) i)).symm
      exact congrArg (fun x : α => decide (t ≤ x)) hRaw
    calc
      _ = boolTrueCount (fun i : Fin 64 => decide (t ≤
          H.exec v (genScatterMergeTreeOutputEmbedding tailTree tail
            (Fin.cast htailLeaf.symm j) i))) := congrArg boolTrueCount hEq
      _ = profileCell K
          (boolTrueCount (fun i : Fin (64 * K) => decide (t ≤ v (tail i)))) j.val :=
        genScatterMergeTree_output_threshold_profile_k tailTree htailLeaf
          tail v htailRuns t j

/-- An actual divisible-64 `flowA7` receiver, after its checked correction
stage, can be merged in parallel and exposes the exact threshold profile on
every resulting rank packet. -/
theorem flowA7_receiver_allCases_divisible64_batch_profiles {d : Nat}
    {α : Type} [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (hdiv : 64 ∣ flowA7 d hd b.l (t + 1) / 64) :
    ∃ blocks : List (Fin 4096 ↪ Fin (64 ^ d)),
      blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ i j, e i ≠ f j) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 ∧
      (∀ e ∈ blocks, Monotone (fun i =>
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i))) ∧
      (∀ e ∈ blocks, ∀ j : Fin 64,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e
              (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) ∧
      (∀ e ∈ blocks, ∀ j l : Fin 64, j.val < l.val → ∀ i k,
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
          (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e
            (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i) ≤
        (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
          ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
          (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e
            (Fin.cast (packetPowerTree6_leafCount (α := α)).symm l) k)) ∧
      (∀ e ∈ blocks, ∀ j : Fin 64, ∀ threshold : α,
        boolTrueCount (fun i : Fin 64 => decide (threshold ≤
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e
              (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) =
        profileCell 64
          (boolTrueCount (fun i : Fin 4096 => decide (threshold ≤
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i)))) j.val) := by
  obtain ⟨m, packets, hsorted, hdis, hcover, hcount⟩ :=
    flowA7_receiver_allCases_packetCount hd t ht2 ht b hb hchild v hpack
  have hdivM : 64 ∣ m := by simpa [hcount] using hdiv
  let q := m / 64
  have hq : q * 64 = m := by
    dsimp [q]
    exact Nat.div_mul_cancel hdivM
  let castPackets : Fin (q * 64) → Fin 64 ↪ Fin (64 ^ d) :=
    fun i => packets (Fin.cast hq i)
  have hdis' : ∀ a b, a ≠ b → ∀ x y, castPackets a x ≠ castPackets b y := by
    intro a b hab x y heq
    apply hdis (Fin.cast hq a) (Fin.cast hq b)
    · intro h
      apply hab
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa using hv
    · exact heq
  let blocks := packetFamily64BlockList castPackets hdis'
  have hnd := packetFamily64BlockList_nodup castPackets hdis'
  have hdisBlocks := packetFamily64BlockList_disjoint castPackets hdis'
  have hdepth := packetFamily64BlockList_merge_depth_le (α := α) castPackets hdis'
  have hsortedOut := packetFamily64BlockList_merge_output_sorted castPackets hdis'
    ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
    (fun i => hsorted (Fin.cast hq i))
  refine ⟨blocks, hnd, hdisBlocks, hdepth, ?_, ?_, ?_, ?_⟩
  · exact packetFamily64BlockList_merge_output_blockSorted castPackets hdis'
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
      (fun a => hsorted (Fin.cast hq a))
  · exact hsortedOut
  · exact packetFamily64BlockList_merge_output_valuesOrdered castPackets hdis'
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
      (fun a => hsorted (Fin.cast hq a))
  · intro e he j threshold
    exact packetFamily64BlockList_merge_output_threshold_profile
      castPackets hdis' ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
      (fun i => hsorted (Fin.cast hq i)) threshold e he j

/-- For a divisible-64 receiver, the merged rank packets cover precisely
the receiver's next-stage register. This upgrades the local grouped-block
support theorem to the actual `flowA7` support partition. -/
theorem flowA7_receiver_allCases_divisible64_batch_support {d : Nat}
    {α : Type} [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (hdiv : 64 ∣ flowA7 d hd b.l (t + 1) / 64) :
    ∃ blocks : List (Fin 4096 ↪ Fin (64 ^ d)),
      ∀ w, (∃ e ∈ blocks, ∃ j : Fin (packetPowerTree6 (α := α)).leafCount,
        w ∈ Set.range (genScatterMergeTreeOutputEmbedding
          (packetPowerTree6 (α := α)) e j)) ↔
        w ∈ wireSets (flowSizes7 d hd) (t + 1) b := by
  obtain ⟨m, packets, hsorted, hdis, hcover, hcount⟩ :=
    flowA7_receiver_allCases_packetCount hd t ht2 ht b hb hchild v hpack
  have hdivM : 64 ∣ m := by simpa [hcount] using hdiv
  let q := m / 64
  have hq : q * 64 = m := by
    dsimp [q]
    exact Nat.div_mul_cancel hdivM
  let castPackets : Fin (q * 64) → Fin 64 ↪ Fin (64 ^ d) :=
    fun i => packets (Fin.cast hq i)
  have hdis' : ∀ a b, a ≠ b → ∀ x y, castPackets a x ≠ castPackets b y := by
    intro a b hab x y heq
    apply hdis (Fin.cast hq a) (Fin.cast hq b)
    · intro h
      apply hab
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa using hv
    · exact heq
  let blocks := packetFamily64BlockList castPackets hdis'
  have hsource : ∀ w,
      (∃ a : Fin (q * 64), ∃ i : Fin 64, castPackets a i = w) ↔
        w ∈ wireSets (flowSizes7 d hd) (t + 1) b := by
    intro w
    rw [← hcover]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      packetEmbeddingSupport_mem_iff]
    constructor
    · rintro ⟨a, i, hi⟩
      exact ⟨Fin.cast hq a, i, hi⟩
    · rintro ⟨a, i, hi⟩
      refine ⟨Fin.cast hq.symm a, i, ?_⟩
      simpa using hi
  refine ⟨blocks, ?_⟩
  intro w
  simpa [blocks] using
    (packetFamily64BlockList_output_support castPackets hdis'
      (packetPowerTree6 (α := α)) w).trans (hsource w)

/-- The actual residue-63 receiver is also partitioned exactly by its full
64-packet blocks and final 63-packet tail. Together with
`genMergeTreeFullTailBatch_output_support`, this is the source-side
conservation law for its 57-layer full-plus-tail merge. -/
theorem flowA7_receiver_allCases_residue63_batch_support {d : Nat}
    {α : Type} [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (hrem : (flowA7 d hd b.l (t + 1) / 64) % 64 = 63) :
    ∃ blocks : List (Fin 4096 ↪ Fin (64 ^ d)),
      ∃ tail : Fin 4032 ↪ Fin (64 ^ d),
      ∀ w, (∃ e ∈ blocks, w ∈ Set.range e) ∨ w ∈ Set.range tail ↔
        w ∈ wireSets (flowSizes7 d hd) (t + 1) b := by
  obtain ⟨m, packets, hsorted, hdis, hcover, hcount⟩ :=
    flowA7_receiver_allCases_packetCount hd t ht2 ht b hb hchild v hpack
  have hmrem : m % 64 = 63 := by simpa [hcount] using hrem
  let q := m / 64
  have hsize : m = q * 64 + 63 := by
    have hdecomp := Nat.mod_add_div m 64
    dsimp [q]
    rw [hmrem] at hdecomp
    omega
  let packets' : Fin (q * 64 + 63) → Fin 64 ↪ Fin (64 ^ d) :=
    fun i => packets (Fin.cast hsize.symm i)
  have hdis' : ∀ a b, a ≠ b → ∀ x y, packets' a x ≠ packets' b y := by
    intro a b hab x y heq
    apply hdis (Fin.cast hsize.symm a) (Fin.cast hsize.symm b)
    · intro h
      apply hab
      exact Fin.cast_injective hsize.symm h
    · exact heq
  let prefixPackets : Fin (q * 64) → Fin 64 ↪ Fin (64 ^ d) :=
    fun i => packets' ⟨i.val, by have hi := i.isLt; omega⟩
  let tailPackets : Fin 63 → Fin 64 ↪ Fin (64 ^ d) :=
    fun i => packets' ⟨q * 64 + i.val, by have hi := i.isLt; omega⟩
  have hprefixDis : ∀ a b, a ≠ b → ∀ x y,
      prefixPackets a x ≠ prefixPackets b y := by
    intro a b hab x y heq
    exact hdis' _ _ (by
      intro h
      apply hab
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa using hv) x y heq
  have htailDis : ∀ {a b : Fin 63}, a ≠ b → ∀ x y,
      tailPackets a x ≠ tailPackets b y := by
    intro a b hab x y heq
    exact hdis' _ _ (by
      intro h
      apply hab
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_mk] at hv
      omega) x y heq
  let blocks := packetFamily64BlockList prefixPackets hprefixDis
  let tail := genPacketGroup63Embedding tailPackets htailDis
  have hsource : ∀ w,
      (∃ a : Fin (q * 64 + 63), ∃ i : Fin 64, packets' a i = w) ↔
        w ∈ wireSets (flowSizes7 d hd) (t + 1) b := by
    intro w
    rw [← hcover]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      packetEmbeddingSupport_mem_iff]
    constructor
    · rintro ⟨a, i, hi⟩
      exact ⟨Fin.cast hsize.symm a, i, hi⟩
    · rintro ⟨a, i, hi⟩
      refine ⟨Fin.cast hsize a, i, ?_⟩
      simpa using hi
  refine ⟨blocks, tail, ?_⟩
  intro w
  have hlocal := packetFamily64BlockList_residue63_support packets' hdis' w
  have hlocal' : (∃ e ∈ blocks, w ∈ Set.range e) ∨
      w ∈ Set.range tail ↔
        (∃ a : Fin (q * 64 + 63), ∃ i : Fin 64, packets' a i = w) := by
    simpa [blocks, tail, prefixPackets, tailPackets] using hlocal
  exact hlocal'.trans (hsource w)

set_option maxHeartbeats 600000 in
/-- Actual residue-63 `flowA7` receivers also retain exact threshold
profiles through the full-block plus unequal-tail batch. -/
theorem flowA7_receiver_allCases_residue63_batch_profiles {d : Nat}
    {α : Type} [LinearOrder α]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (v : Fin (64 ^ d) → α)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (hrem : (flowA7 d hd b.l (t + 1) / 64) % 64 = 63) :
    ∃ blocks : List (Fin 4096 ↪ Fin (64 ^ d)), ∃ tail : Fin 4032 ↪ Fin (64 ^ d),
      blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ i j, e i ≠ f j) ∧
      (∀ e ∈ blocks, ∀ i j, e i ≠ tail j) ∧
      (genMergeTreeFullTailBatch (packetPowerTree6 (α := α))
        (packetOddTree6 (α := α)) blocks tail).depth ≤ 57 ∧
      (∀ e ∈ blocks, ∀ j : Fin 64,
        Monotone (fun i =>
          (genMergeTreeFullTailBatch (packetPowerTree6 (α := α))
            (packetOddTree6 (α := α)) blocks tail).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e
              (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) ∧
      (∀ j : Fin 63,
        Monotone (fun i =>
          (genMergeTreeFullTailBatch (packetPowerTree6 (α := α))
            (packetOddTree6 (α := α)) blocks tail).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetOddTree6 (α := α)) tail
              (Fin.cast (packetOddTree6_leafCount (α := α)).symm j) i))) ∧
      (∀ e ∈ blocks, ∀ j : Fin 64, ∀ threshold : α,
        boolTrueCount (fun i : Fin 64 => decide (threshold ≤
          (genMergeTreeFullTailBatch (packetPowerTree6 (α := α))
            (packetOddTree6 (α := α)) blocks tail).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e
              (Fin.cast (packetPowerTree6_leafCount (α := α)).symm j) i))) =
        profileCell 64
          (boolTrueCount (fun i : Fin 4096 => decide (threshold ≤
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (e i)))) j.val) ∧
      (∀ j : Fin 63, ∀ threshold : α,
        boolTrueCount (fun i : Fin 64 => decide (threshold ≤
          (genMergeTreeFullTailBatch (packetPowerTree6 (α := α))
            (packetOddTree6 (α := α)) blocks tail).exec
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            (genScatterMergeTreeOutputEmbedding (packetOddTree6 (α := α)) tail
              (Fin.cast (packetOddTree6_leafCount (α := α)).symm j) i))) =
        profileCell 63
          (boolTrueCount (fun i : Fin 4032 => decide (threshold ≤
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) (tail i)))) j.val) := by
  obtain ⟨blocks, tail, hnodup, hblocksDisjoint, htailDisjoint, hdepth,
      hRunsFull, hRunsTail, hsortedFull, hsortedTail⟩ :=
    flowA7_receiver_allCases_residue63_batch hd t ht2 ht b hb hchild v hpack hrem
  refine ⟨blocks, tail, hnodup, hblocksDisjoint, htailDisjoint, hdepth,
    ?_, ?_, ?_, ?_⟩
  · exact hsortedFull
  · exact hsortedTail
  · intro e he j threshold
    exact (genMergeTreeFullTailBatch_output_threshold_profile (K := 63)
      (packetPowerTree6 (α := α)) (packetPowerTree6_leafCount (α := α))
      (packetOddTree6 (α := α)) (packetOddTree6_leafCount (α := α))
      blocks tail hnodup hblocksDisjoint htailDisjoint
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
      hRunsFull hRunsTail threshold).1 e he j
  · intro j threshold
    exact (genMergeTreeFullTailBatch_output_threshold_profile (K := 63)
      (packetPowerTree6 (α := α)) (packetPowerTree6_leafCount (α := α))
      (packetOddTree6 (α := α)) (packetOddTree6_leafCount (α := α))
      blocks tail hnodup hblocksDisjoint htailDisjoint
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
      hRunsFull hRunsTail threshold).2 j

def profileHalf (K X i : Nat) : Nat :=
  profileTail (32 * K) X (32 * (i + 1)) - profileTail (32 * K) X (32 * i)

private theorem profileTail_interval_count32 (m X a b : Nat)
    (hab : a ≤ b) (hb : b ≤ m) :
    profileTail m X b - profileTail m X a = min (b - a) (X - (m - b)) := by
  by_cases h0 : X ≤ m - b
  · simp [profileTail, h0]
  · by_cases h1 : X ≤ m - a
    · simp only [profileTail, Nat.min_def]
      split_ifs <;> omega
    · simp only [profileTail, Nat.min_def]
      split_ifs <;> omega

/-- Ideal count in any fixed rank interval of a sorted packet. -/
def profileInterval (m X a b : Nat) : Nat :=
  profileTail m X b - profileTail m X a

theorem profileInterval_formula (m X a b : Nat) (hab : a ≤ b) (hb : b ≤ m) :
    profileInterval m X a b = min (b - a) (X - (m - b)) := by
  unfold profileInterval
  exact profileTail_interval_count32 m X a b hab hb

/-- Restricting a suffix profile to a rank cell and then to a subinterval
gives the same count as restricting the original profile directly. -/
theorem profileInterval_restrict_cell (m X c d a b : Nat)
    (hX : X ≤ m) (hcd : c ≤ d) (hd : d ≤ m)
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) :
    profileInterval m X a b =
      profileInterval (d - c) (profileInterval m X c d)
        (a - c) (b - c) := by
  have hlocalAB : a - c ≤ b - c := by omega
  have hlocalB : b - c ≤ d - c := by omega
  have hlen : (b - c) - (a - c) = b - a := by omega
  have htail : (d - c) - (b - c) = d - b := by omega
  rw [profileInterval_formula m X a b hab (by omega),
    profileInterval_formula (d - c) (profileInterval m X c d)
      (a - c) (b - c) hlocalAB hlocalB, hlen, htail,
    profileInterval_formula m X c d hcd hd]
  by_cases hcell : X - (m - d) ≤ d - c
  · rw [Nat.min_eq_right hcell]
    have hsame : X - (m - b) = (X - (m - d)) - (d - b) := by omega
    rw [hsame]
  · have hglobal : b - a ≤ X - (m - b) := by omega
    have hcellFull : d - c ≤ X - (m - d) := by omega
    rw [Nat.min_eq_left hglobal, Nat.min_eq_left hcellFull]
    omega

/-- Packet-local suffix targets need not combine into the suffix target of
their aggregate count, even when the packet supports are consecutive physical
cells. The first packet is full and the second empty: together they have 64
ones, but their first-cell target is 64 while the aggregate 128-rank suffix
target assigns zero to that cell. This rules out target recombination from
packet totals and support alignment alone. -/
theorem profileInterval_packetwise_vs_aggregate_counterexample :
    profileInterval 64 64 0 64 + profileInterval 64 0 0 64 = 64 ∧
    profileInterval 128 64 0 64 = 0 := by
  constructor <;> norm_num [profileInterval, profileTail]

/-- A fixed rank interval's ideal count changes by at most the change in
the packet's total count. This is the local estimate needed when ports select
different fixed rank intervals from a cohort. -/
theorem profileInterval_change_le (m X Y a b : Nat) (hab : a ≤ b) (hb : b ≤ m)
    (hYX : Y ≤ X) : profileInterval m X a b - profileInterval m Y a b ≤ X - Y := by
  rw [profileInterval_formula m X a b hab hb,
    profileInterval_formula m Y a b hab hb]
  by_cases hy : b - a ≤ Y - (m - b)
  · have hx : b - a ≤ X - (m - b) := by omega
    rw [Nat.min_eq_left hy, Nat.min_eq_left hx]
    omega
  · by_cases hx : b - a ≤ X - (m - b)
    · have hy' : Y - (m - b) < b - a := by omega
      rw [Nat.min_eq_left hx, Nat.min_eq_right (Nat.le_of_lt hy')]
      omega
    · have hx' : X - (m - b) < b - a := by omega
      have hy' : Y - (m - b) < b - a := by omega
      rw [Nat.min_eq_right (Nat.le_of_lt hx'), Nat.min_eq_right (Nat.le_of_lt hy')]
      omega

private def blockRankEmbedding {N : Nat} (s : Finset (Fin N))
    (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ s.card) : Fin (hi - lo) ↪ Fin N where
  toFun j := s.orderEmbOfFin rfl ⟨lo + j.val, by
    have hsum := Nat.add_sub_of_le hlo
    have hlt : lo + j.val < hi := by
      calc
        lo + j.val < lo + (hi - lo) := Nat.add_lt_add_left j.isLt _
        _ = hi := hsum
    exact lt_of_lt_of_le hlt hhi⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have he := (s.orderEmbOfFin rfl).injective h
    have hv := congrArg Fin.val he
    simp only [Fin.val_mk] at hv
    omega

private theorem blockRankEmbedding_range {N : Nat} (s : Finset (Fin N))
    (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ s.card) :
    Set.range (blockRankEmbedding s lo hi hlo hhi) = {w | w ∈ blockOf s lo hi} := by
  ext w
  constructor
  · rintro ⟨j, rfl⟩
    change blockRankEmbedding s lo hi hlo hhi j ∈ blockOf s lo hi
    rw [mem_blockOf_iff]
    refine ⟨⟨lo + j.val, by
      have hsum := Nat.add_sub_of_le hlo
      have hlt : lo + j.val < hi := by
        calc
          lo + j.val < lo + (hi - lo) := Nat.add_lt_add_left j.isLt _
          _ = hi := hsum
      exact lt_of_lt_of_le hlt hhi⟩, ?_, ?_, rfl⟩
    · change lo ≤ lo + j.val
      exact Nat.le_add_right _ _
    · change lo + j.val < hi
      have hsum := Nat.add_sub_of_le hlo
      calc
        lo + j.val < lo + (hi - lo) := Nat.add_lt_add_left j.isLt _
        _ = hi := hsum
  · intro hw
    change w ∈ blockOf s lo hi at hw
    rw [mem_blockOf_iff] at hw
    rcases hw with ⟨r, hrlo, hrhi, rfl⟩
    let j : Fin (hi - lo) := ⟨r.val - lo, by omega⟩
    refine ⟨j, ?_⟩
    change s.orderEmbOfFin rfl ⟨lo + j.val, by
      have hsum := Nat.add_sub_of_le hlo
      have hlt : lo + j.val < hi := by
        calc
          lo + j.val < lo + (hi - lo) := Nat.add_lt_add_left j.isLt _
          _ = hi := hsum
      exact lt_of_lt_of_le hlt hhi⟩ = s.orderEmbOfFin rfl r
    apply congrArg (s.orderEmbOfFin rfl)
    apply Fin.ext
    dsimp [j]
    omega

def profileIntervalMean (m q : Nat) (frac : Real) (a b : Nat) : Real :=
  (1 - frac) * profileInterval m q a b +
    frac * profileInterval m (q + 1) a b

/-- The fractional target also restricts exactly: first take the two
neighboring integer target counts on the containing cell, then interpolate
their local subinterval counts. -/
theorem profileIntervalMean_restrict_cell (m q c d a b : Nat) (frac : Real)
    (hq : q + 1 ≤ m) (hcd : c ≤ d) (hd : d ≤ m)
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) :
    profileIntervalMean m q frac a b =
      (1 - frac) * profileInterval (d - c)
        (profileInterval m q c d) (a - c) (b - c) +
        frac * profileInterval (d - c)
          (profileInterval m (q + 1) c d) (a - c) (b - c) := by
  unfold profileIntervalMean
  rw [profileInterval_restrict_cell m q c d a b (by omega)
      hcd hd hca hab hbd,
    profileInterval_restrict_cell m (q + 1) c d a b (by omega)
      hcd hd hca hab hbd]


/-- Count-profile contributed by any selected family of rank intervals. A
fixed owner assigns each interval to its eventual receiver. -/
def profileIntervalOwnerCount {D : Type} [DecidableEq D] {m p : Nat}
    (cuts : Nat → Nat) (owner : Fin p → D) (destination : D) (X : Nat) : Nat :=
  ∑ i : Fin p,
    if owner i = destination then
      profileInterval m X (cuts i.val) (cuts (i.val + 1))
    else 0

/-- Count-profile of a specified finite family of rank intervals. -/
def profileIntervalSelectedCount {m : Nat} (cuts : Nat → Nat)
    (selected : Finset Nat) (X : Nat) : Nat :=
  ∑ i ∈ selected, profileInterval m X (cuts i) (cuts (i + 1))

/-- A fractional ideal profile assigns each rank interval a mean between zero
and that interval's capacity. This lets selected interval means define a
valid next receiver threshold target without a separate common-mean ansatz. -/
theorem profileIntervalMean_bounds (m q a b : Nat) (frac : Real)
    (hab : a ≤ b) (hb : b ≤ m)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    0 ≤ profileIntervalMean m q frac a b ∧
      profileIntervalMean m q frac a b ≤ (b - a : Nat) := by
  have hx0 : 0 ≤ (profileInterval m q a b : Real) := by
    rw [profileInterval_formula m q a b hab hb]
    exact_mod_cast Nat.zero_le (min (b - a) (q - (m - b)))
  have hy0 : 0 ≤ (profileInterval m (q + 1) a b : Real) := by
    rw [profileInterval_formula m (q + 1) a b hab hb]
    exact_mod_cast Nat.zero_le (min (b - a) (q + 1 - (m - b)))
  have hxle : (profileInterval m q a b : Real) ≤ (b - a : Nat) := by
    rw [profileInterval_formula m q a b hab hb]
    exact_mod_cast Nat.min_le_left _ _
  have hyle : (profileInterval m (q + 1) a b : Real) ≤ (b - a : Nat) := by
    rw [profileInterval_formula m (q + 1) a b hab hb]
    exact_mod_cast Nat.min_le_left _ _
  unfold profileIntervalMean
  constructor <;> nlinarith

private theorem profileTail_mono_r (m X : Nat) : Monotone (profileTail m X) := by
  intro a b hab
  simp only [profileTail]
  omega

private theorem sum_profileIntervals_partition (m p X : Nat) (cuts : Nat → Nat)
    (hstart : cuts 0 = 0) (hmono : Monotone cuts) (hend : cuts p = m) :
    (∑ i ∈ range p, profileInterval m X (cuts i) (cuts (i + 1))) =
      profileTail m X m - profileTail m X 0 := by
  unfold profileInterval
  have htail : Monotone (fun i => profileTail m X (cuts i)) :=
    (profileTail_mono_r m X).comp hmono
  rw [Finset.sum_range_tsub htail p]
  rw [hend, hstart]

private theorem profileInterval_mono_X (m X Y a b : Nat) (hab : a ≤ b) (hb : b ≤ m)
    (hXY : Y ≤ X) : profileInterval m Y a b ≤ profileInterval m X a b := by
  rw [profileInterval_formula m Y a b hab hb, profileInterval_formula m X a b hab hb]
  exact min_le_min le_rfl (Nat.sub_le_sub_right hXY _)

/-- On any containing rank cell, the fractional global target induces exactly
a local fractional target. The cell's integer target increases by either zero
or one across adjacent global thresholds; in the zero case the local
interpolation parameter is zero. -/
theorem profileIntervalMean_restrict_cell_local (m q c d a b : Nat) (frac : Real)
    (hq : q + 1 ≤ m) (hcd : c ≤ d) (hd : d ≤ m)
    (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) :
    profileIntervalMean m q frac a b =
      profileIntervalMean (d - c) (profileInterval m q c d)
        (if profileInterval m (q + 1) c d = profileInterval m q c d
         then 0 else frac) (a - c) (b - c) := by
  have hmono := profileInterval_mono_X m (q + 1) q c d hcd hd (by omega)
  have hchange := profileInterval_change_le m (q + 1) q c d hcd hd (by omega)
  have hstep : profileInterval m (q + 1) c d = profileInterval m q c d ∨
      profileInterval m (q + 1) c d = profileInterval m q c d + 1 := by omega
  rw [profileIntervalMean_restrict_cell m q c d a b frac hq hcd hd hca hab hbd]
  by_cases heq : profileInterval m (q + 1) c d = profileInterval m q c d
  · simp [profileIntervalMean, heq]
    ring
  · have hsucc : profileInterval m (q + 1) c d =
        profileInterval m q c d + 1 := by omega
    simp [profileIntervalMean, heq, hsucc]

/-- Interpolation between adjacent integer profiles stays between those
profiles on every rank interval. -/
theorem profileIntervalMean_between (m q a b : Nat) (frac : Real)
    (hab : a ≤ b) (hb : b ≤ m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (profileInterval m q a b : Real) ≤ profileIntervalMean m q frac a b ∧
      profileIntervalMean m q frac a b ≤
        (profileInterval m (q + 1) a b : Real) := by
  have hmono := profileInterval_mono_X m (q + 1) q a b hab hb (by omega)
  have hdelta : 0 ≤ (profileInterval m (q + 1) a b : Real) -
      profileInterval m q a b := by exact_mod_cast Nat.zero_le (profileInterval m (q + 1) a b - profileInterval m q a b)
  have hdelta' : (profileInterval m q a b : Real) ≤
      profileInterval m (q + 1) a b := by exact_mod_cast hmono
  unfold profileIntervalMean
  constructor
  · have hprod := mul_nonneg hfrac0 hdelta
    nlinarith
  · have hprod := mul_nonneg (sub_nonneg.mpr hfrac1) hdelta
    nlinarith

/-- If an actual threshold cut is to the left of its interpolated target,
then every rank subinterval has error of the same sign. This is the local
form of the sorted-profile L1 identity and lets the error be routed by piece
ownership without cancellations inside one source. -/
theorem profileInterval_error_nonpos_of_X_le_target (m X q a b : Nat) (frac : Real)
    (hab : a ≤ b) (hb : b ≤ m) (hX : X ≤ q)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (profileInterval m X a b : Real) ≤ profileIntervalMean m q frac a b := by
  have hXq : profileInterval m X a b ≤ profileInterval m q a b :=
    profileInterval_mono_X m q X a b hab hb (by omega)
  have hqMean := (profileIntervalMean_between m q a b frac hab hb hfrac0 hfrac1).1
  exact le_trans (by exact_mod_cast hXq) hqMean

/-- If an actual threshold cut is to the right of its interpolated target,
then every rank subinterval has error of the opposite common sign. -/
theorem profileInterval_error_nonneg_of_target_le_X (m X q a b : Nat) (frac : Real)
    (hab : a ≤ b) (hb : b ≤ m) (hX : q + 1 ≤ X)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    profileIntervalMean m q frac a b ≤ (profileInterval m X a b : Real) := by
  have hqX : profileInterval m (q + 1) a b ≤ profileInterval m X a b :=
    profileInterval_mono_X m X (q + 1) a b hab hb (by omega)
  have hMeanq := (profileIntervalMean_between m q a b frac hab hb hfrac0 hfrac1).2
  exact le_trans hMeanq (by exact_mod_cast hqX)

/-- The interpolated interval target is monotone in its underlying real
threshold count `q + frac`. The integer boundary case is exact, so changing
the floor does not introduce a discontinuity. -/
theorem profileIntervalMean_mono_mean (m q₁ q₂ a b : Nat)
    (frac₁ frac₂ : Real) (hab : a ≤ b) (hb : b ≤ m)
    (hfrac₁0 : 0 ≤ frac₁) (hfrac₁1 : frac₁ ≤ 1)
    (hfrac₂0 : 0 ≤ frac₂) (hfrac₂1 : frac₂ ≤ 1)
    (hmean : (q₁ : Real) + frac₁ ≤ (q₂ : Real) + frac₂) :
    profileIntervalMean m q₁ frac₁ a b ≤ profileIntervalMean m q₂ frac₂ a b := by
  by_cases h₁₂ : q₁ ≤ q₂
  · by_cases heq : q₁ = q₂
    · subst q₂
      have hfrac : frac₁ ≤ frac₂ := by nlinarith
      have hmono := profileInterval_mono_X m (q₁ + 1) q₁ a b hab hb (by omega)
      have hdelta : 0 ≤ (profileInterval m (q₁ + 1) a b : Real) -
          profileInterval m q₁ a b := by exact_mod_cast Nat.zero_le _
      unfold profileIntervalMean
      have hprod := mul_nonneg (sub_nonneg.mpr hfrac) hdelta
      nlinarith [show (profileInterval m q₁ a b : Real) ≤
        profileInterval m (q₁ + 1) a b by exact_mod_cast hmono]
    · have hlt : q₁ < q₂ := by omega
      have hleft := (profileIntervalMean_between m q₁ a b frac₁ hab hb
        hfrac₁0 hfrac₁1).2
      have hright := (profileIntervalMean_between m q₂ a b frac₂ hab hb
        hfrac₂0 hfrac₂1).1
      have hmidNat := profileInterval_mono_X m q₂ (q₁ + 1) a b hab hb (by omega)
      have hmid : (profileInterval m (q₁ + 1) a b : Real) ≤
          (profileInterval m q₂ a b : Real) := by exact_mod_cast hmidNat
      exact le_trans hleft (le_trans hmid hright)
  · have hlt : q₂ < q₁ := by omega
    by_cases hsucc : q₂ + 1 = q₁
    · have hqreal : (q₁ : Real) = (q₂ : Real) + 1 := by exact_mod_cast hsucc.symm
      have hf₁ : frac₁ = 0 := by rw [hqreal] at hmean; nlinarith
      have hf₂ : frac₂ = 1 := by rw [hqreal] at hmean; nlinarith
      rw [← hsucc, hf₁, hf₂]
      simp [profileIntervalMean]
    · have hgap : q₂ + 1 < q₁ := by omega
      have hqle : q₁ ≤ q₂ + 1 := by
        have hqleReal : (q₁ : Real) ≤ (q₂ : Real) + 1 := by nlinarith
        exact_mod_cast hqleReal
      omega

/-- Any real threshold target in a positive-capacity register can be encoded
as `q + frac` with `q` strictly below capacity and `frac ∈ [0,1]`. The full
capacity endpoint uses the equivalent representation `(m-1)+1`. -/
theorem realTarget_has_integer_fraction (m : Nat) (μ : Real)
    (hm : 0 < m) (hμ0 : 0 ≤ μ) (hμm : μ ≤ (m : Real)) :
    ∃ q : Nat, q < m ∧ ∃ frac : Real,
      0 ≤ frac ∧ frac ≤ 1 ∧ (q : Real) + frac = μ := by
  by_cases htop : μ = (m : Real)
  · refine ⟨m - 1, by omega, 1, by norm_num, by norm_num, ?_⟩
    have hcast : ((m - 1 : Nat) : Real) + 1 = (m : Real) := by
      have hn : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
      exact_mod_cast hn
    rw [htop]
    exact hcast
  · have hμlt : μ < (m : Real) := by
      by_contra h
      have hmμ : (m : Real) ≤ μ := le_of_not_gt h
      exact htop (le_antisymm hμm hmμ)
    have hfloorle : (Nat.floor μ : Real) ≤ μ := Nat.floor_le hμ0
    have hfloorlt : μ < (Nat.floor μ : Real) + 1 := Nat.lt_floor_add_one μ
    have hq_lt_real : (Nat.floor μ : Real) < (m : Real) := lt_of_le_of_lt hfloorle hμlt
    have hq_lt : Nat.floor μ < m := by exact_mod_cast hq_lt_real
    refine ⟨Nat.floor μ, hq_lt, μ - (Nat.floor μ : Real), ?_, ?_, ?_⟩
    · dsimp
      linarith
    · dsimp
      linarith
    · dsimp
      ring

private theorem cuts_le_end (p : Nat) (cuts : Nat → Nat) (hcuts : Monotone cuts)
    (i : Nat) (hi : i ≤ p) : cuts i ≤ cuts p := hcuts hi

private theorem profileInterval_partition_total (m p X : Nat) (cuts : Nat → Nat)
    (hstart : cuts 0 = 0) (hcuts : Monotone cuts) (hend : cuts p = m)
    (hX : X ≤ m) : (∑ i ∈ range p, profileInterval m X (cuts i) (cuts (i + 1))) = X := by
  rw [sum_profileIntervals_partition m p X cuts hstart hcuts hend]
  simp only [profileTail]
  omega

/-- The interpolated ideal means of a partition sum to the chosen fractional
target, including both the full-capacity and zero-capacity endpoint cases. -/
theorem profileIntervalMean_partition_sum (m p q : Nat) (frac : Real)
    (cuts : Nat → Nat) (hstart : cuts 0 = 0) (hcuts : Monotone cuts)
    (hend : cuts p = m) (hq : q ≤ m) (hfrac0 : 0 ≤ frac)
    (hfrac1 : frac ≤ 1) (hendpoint : q = m → frac = 0) :
    (∑ i ∈ range p,
      profileIntervalMean m q frac (cuts i) (cuts (i + 1))) = q + frac := by
  by_cases hq' : q < m
  · have hqsum : (∑ i ∈ range p,
        (profileInterval m q (cuts i) (cuts (i + 1)) : Real)) = q := by
      exact_mod_cast profileInterval_partition_total m p q cuts hstart hcuts hend (by omega)
    have hq1sum : (∑ i ∈ range p,
        (profileInterval m (q + 1) (cuts i) (cuts (i + 1)) : Real)) = q + 1 := by
      exact_mod_cast profileInterval_partition_total m p (q + 1) cuts hstart hcuts hend (by omega)
    unfold profileIntervalMean
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hqsum, hq1sum]
    ring_nf
  · have hqeq : q = m := by omega
    have hf : frac = 0 := hendpoint hqeq
    subst q
    rw [hf]
    unfold profileIntervalMean
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    exact_mod_cast profileInterval_partition_total m p m cuts hstart hcuts hend (by omega)

/-- Interpolated ideal counts are additive when any interval is cut into
consecutive subintervals. This lets a receiver's selected target be refined
at macro-block boundaries without changing the target assigned to the whole
receiver interval. -/
theorem profileIntervalMean_partition_sum_interval (m p q a b : Nat)
    (frac : Real) (cuts : Nat → Nat)
    (hstart : cuts 0 = a) (hcuts : Monotone cuts) (hend : cuts p = b)
    (hab : a ≤ b) (hb : b ≤ m) :
    (∑ i ∈ range p,
      profileIntervalMean m q frac (cuts i) (cuts (i + 1))) =
        profileIntervalMean m q frac a b := by
  have hpartition (X : Nat) :
      (∑ i ∈ range p,
        profileInterval m X (cuts i) (cuts (i + 1))) =
          profileInterval m X a b := by
    unfold profileInterval
    have htail : Monotone (fun i => profileTail m X (cuts i)) :=
      (profileTail_mono_r m X).comp hcuts
    rw [Finset.sum_range_tsub htail p, hend, hstart]
  have hq : (∑ i ∈ range p,
      (profileInterval m q (cuts i) (cuts (i + 1)) : Real)) =
        (profileInterval m q a b : Real) := by
    exact_mod_cast hpartition q
  have hq1 : (∑ i ∈ range p,
      (profileInterval m (q + 1) (cuts i) (cuts (i + 1)) : Real)) =
        (profileInterval m (q + 1) a b : Real) := by
    exact_mod_cast hpartition (q + 1)
  unfold profileIntervalMean
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hq, hq1]

/-- A receiver interval contained in the complete-block prefix of a port can
be cut at every 4096-rank macro boundary without changing its ideal target.
Clamping the grid cuts to the receiver interval accounts for its two partial
boundary blocks; zero-length pieces contribute zero. -/
theorem profileIntervalMean_partition_sum_4096_grid (m Q q a b : Nat)
    (frac : Real) (hab : a ≤ b) (hb : b ≤ m) (hgrid : b ≤ 4096 * Q) :
    (∑ i ∈ range Q,
      profileIntervalMean m q frac
        (min b (max a (4096 * i)))
        (min b (max a (4096 * (i + 1))))) =
      profileIntervalMean m q frac a b := by
  let cuts : Nat → Nat := fun i => min b (max a (4096 * i))
  have hstart : cuts 0 = a := by
    simp [cuts, Nat.min_eq_right hab]
  have hcuts : Monotone cuts := by
    intro i j hij
    dsimp [cuts]
    exact min_le_min_left _ (max_le_max_left _ (Nat.mul_le_mul_left 4096 hij))
  have hend : cuts Q = b := by
    dsimp [cuts]
    have hbmax : b ≤ max a (4096 * Q) :=
      le_trans hgrid (Nat.le_max_right _ _)
    rw [Nat.min_eq_left hbmax]
  simpa only [cuts] using
    profileIntervalMean_partition_sum_interval m Q q a b frac cuts
      hstart hcuts hend hab hb

/-- Abstract L1 conservation for any finite family of monotone count
profiles whose total is the packet's count. This applies even when the
destination rank sets are scattered rather than contiguous intervals. -/
theorem monotoneCountDecomposition_L1_exact {ι : Type} [Fintype ι]
    (F : ι → Nat → Nat) (m X q : Nat) (frac : Real)
    (hX : X ≤ m) (hq : q < m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (hsum : ∀ z ≤ m, (∑ i : ι, (F i z : Real)) = z)
    (hmono : ∀ i a b, a ≤ b → F i a ≤ F i b) :
    (∑ i : ι,
      |(F i X : Real) -
        ((1 - frac) * F i q + frac * F i (q + 1))|) =
      |(X : Real) - (q + frac)| := by
  have hq1 : q + 1 ≤ m := by omega
  have hmean : (∑ i : ι,
      ((1 - frac) * (F i q : Real) + frac * (F i (q + 1) : Real))) = q + frac := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hsum q (by omega), hsum (q + 1) hq1]
    push_cast
    ring_nf
  have hXsum : (∑ i : ι, (F i X : Real)) = X := hsum X hX
  by_cases hXq : X ≤ q
  · have hpoint : ∀ i : ι,
        (F i X : Real) ≤ (1 - frac) * F i q + frac * F i (q + 1) := by
      intro i
      have hbase : F i X ≤ F i q := hmono i X q hXq
      have hstep : F i q ≤ F i (q + 1) := hmono i q (q + 1) (by omega)
      have hbaseR : (F i X : Real) ≤ F i q := by exact_mod_cast hbase
      have hstepR : (F i q : Real) ≤ F i (q + 1) := by exact_mod_cast hstep
      nlinarith [hbaseR, hstepR, hfrac0, hfrac1]
    calc
      _ = ∑ i : ι,
          ((1 - frac) * (F i q : Real) + frac * (F i (q + 1) : Real) -
            (F i X : Real)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_of_nonpos (by linarith [hpoint i])]
        ring
      _ = (q + frac) - X := by rw [Finset.sum_sub_distrib, hmean, hXsum]
      _ = |(X : Real) - (q + frac)| := by
        have hXR : (X : Real) ≤ q := by exact_mod_cast hXq
        rw [abs_of_nonpos (by linarith [hXR, hfrac0])]
        ring
  · have hXq1 : q + 1 ≤ X := by omega
    have hpoint : ∀ i : ι,
        (1 - frac) * F i q + frac * F i (q + 1) ≤ (F i X : Real) := by
      intro i
      have hbase : F i (q + 1) ≤ F i X := hmono i (q + 1) X hXq1
      have hstep : F i q ≤ F i (q + 1) := hmono i q (q + 1) (by omega)
      have hbaseR : (F i (q + 1) : Real) ≤ F i X := by exact_mod_cast hbase
      have hstepR : (F i q : Real) ≤ F i (q + 1) := by exact_mod_cast hstep
      nlinarith [hbaseR, hstepR, hfrac0, hfrac1]
    calc
      _ = ∑ i : ι,
          ((F i X : Real) -
            ((1 - frac) * (F i q : Real) + frac * (F i (q + 1) : Real))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_of_nonneg (by linarith [hpoint i])]
      _ = X - (q + frac) := by rw [Finset.sum_sub_distrib, hXsum, hmean]
      _ = |(X : Real) - (q + frac)| := by
        have hXR : (q : Real) + 1 ≤ X := by exact_mod_cast hXq1
        rw [abs_of_nonneg (by linarith [hXR, hfrac1])]

/-- A monotone count decomposition has a once-only L2 charge: the squared
errors of all component counts sum to at most the squared error of their
total count. This applies to scattered packet supports as well as contiguous
rank intervals. -/
theorem monotoneCountDecomposition_L2_le {ι : Type} [Fintype ι]
    (F : ι → Nat → Nat) (m X q : Nat) (frac : Real)
    (hX : X ≤ m) (hq : q < m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (hsum : ∀ z ≤ m, (∑ i : ι, (F i z : Real)) = z)
    (hmono : ∀ i a b, a ≤ b → F i a ≤ F i b) :
    (∑ i : ι,
      ((F i X : Real) - ((1 - frac) * F i q + frac * F i (q + 1))) ^ 2) ≤
      ((X : Real) - (q + frac)) ^ 2 := by
  have hL1 := monotoneCountDecomposition_L1_exact
    F m X q frac hX hq hfrac0 hfrac1 hsum hmono
  calc
    _ = ∑ i : ι,
        |(F i X : Real) - ((1 - frac) * F i q + frac * F i (q + 1))| ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [sq_abs]
    _ ≤ (∑ i : ι,
        |(F i X : Real) - ((1 - frac) * F i q + frac * F i (q + 1))|) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)
    _ = ((X : Real) - (q + frac)) ^ 2 := by rw [hL1, sq_abs]

/-- Count the ranks in a suffix assigned to each destination by an arbitrary
wire-to-destination map. -/
def assignedRankCount {ι : Type} [Fintype ι] [DecidableEq ι] {m : Nat}
    (owner : Fin m → ι) (suffix : Nat → Fin m → Bool)
    (destination : ι) (X : Nat) : Nat :=
  ∑ k : Fin m, if destination = owner k ∧ suffix X k = true then 1 else 0

/-- A fixed rank-owner map sends monotone suffix counts to monotone counts in
each destination. -/
theorem assignedRankCount_mono {ι : Type} [Fintype ι] [DecidableEq ι]
    {m : Nat} (owner : Fin m → ι) (suffix : Nat → Fin m → Bool)
    (destination : ι) (X Y : Nat)
    (hmono : X ≤ Y → ∀ k, suffix X k = true → suffix Y k = true)
    (hXY : X ≤ Y) :
    assignedRankCount owner suffix destination X ≤
      assignedRankCount owner suffix destination Y := by
  unfold assignedRankCount
  apply Finset.sum_le_sum
  intro k _
  by_cases howner : destination = owner k
  · by_cases hX : suffix X k = true
    · have hY := hmono hXY k hX
      simp [howner, hX, hY]
    · simp [howner, hX]
  · simp [howner]

/-- For any partition of ranks among destinations, the suffix counts are
monotone and sum to the suffix size. The preceding abstract L1 lemma then
shows that arbitrary scattered destination subsets incur no profile error
beyond the coarse packet-count error. -/
theorem assignedRankProfiles_L1_exact {ι : Type} [Fintype ι] [DecidableEq ι] {m : Nat}
    (owner : Fin m → ι) (suffix : Nat → Fin m → Bool)
    (X q : Nat) (frac : Real)
    (hX : X ≤ m) (hq : q < m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (hsuffix : ∀ z ≤ m,
      (∑ k : Fin m, if suffix z k = true then 1 else 0) = z)
    (hmonoSuffix : ∀ a b, a ≤ b → ∀ k, suffix a k = true → suffix b k = true) :
    (∑ destination : ι,
      |(assignedRankCount owner suffix destination X : Real) -
        ((1 - frac) * assignedRankCount owner suffix destination q +
          frac * assignedRankCount owner suffix destination (q + 1))|) =
      |(X : Real) - (q + frac)| := by
  have hsum (z : Nat) (hz : z ≤ m) :
      (∑ destination : ι,
        (assignedRankCount owner suffix destination z : Real)) = z := by
    have hnat :
        (∑ destination : ι, assignedRankCount owner suffix destination z) = z := by
      calc
        _ = ∑ k : Fin m, ∑ destination : ι,
            if destination = owner k ∧ suffix z k = true then 1 else 0 := by
          simp only [assignedRankCount]
          exact Finset.sum_comm
        _ = ∑ k : Fin m, if suffix z k = true then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hsk : suffix z k = true
          · simp only [hsk, and_true]
            rw [Fintype.sum_eq_single (owner k)]
            · simp
            · intro destination hne
              simp [hne]
          · simp [hsk]
        _ = z := hsuffix z hz
    exact_mod_cast hnat
  have hmono : ∀ (destination : ι) a b, a ≤ b →
      assignedRankCount owner suffix destination a ≤
        assignedRankCount owner suffix destination b := by
    intro destination a b hab
    unfold assignedRankCount
    apply Finset.sum_le_sum
    intro k _
    by_cases ho : destination = owner k
    · by_cases hs : suffix a k = true
      · have hs' := hmonoSuffix a b hab k hs
        simp [ho, hs, hs']
      · simp [ho, hs]
    · simp [ho]
  exact monotoneCountDecomposition_L1_exact
    (assignedRankCount owner suffix) m X q frac hX hq hfrac0 hfrac1 hsum hmono

/-- After summing scattered rank counts over packets into each destination,
the receiver's squared profile error is bounded by packet-count energy with
only the number of source packets as multiplier. -/
theorem assignedRankProfiles_aggregate_L2 {ι : Type} [Fintype ι] [DecidableEq ι]
    {c m : Nat} (owner : Fin c → Fin m → ι) (suffix : Nat → Fin m → Bool)
    (X : Fin c → Nat) (q : Nat) (frac : Real)
    (hX : ∀ p, X p ≤ m) (hq : q < m)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (hsuffix : ∀ z ≤ m,
      (∑ k : Fin m, if suffix z k = true then 1 else 0) = z)
    (hmonoSuffix : ∀ a b, a ≤ b → ∀ k, suffix a k = true → suffix b k = true) :
    (∑ destination : ι,
      (Finset.univ.sum (fun (packet : Fin c) =>
        (assignedRankCount (owner packet) suffix destination (X packet) : Real) -
          ((1 - frac) * assignedRankCount (owner packet) suffix destination q +
            frac * assignedRankCount (owner packet) suffix destination (q + 1)))) ^ 2) ≤
      (c : Real) * Finset.univ.sum (fun (packet : Fin c) =>
        ((X packet : Real) - (q + frac)) ^ 2) := by
  let err (packet : Fin c) (destination : ι) : Real :=
    (assignedRankCount (owner packet) suffix destination (X packet) : Real) -
      ((1 - frac) * assignedRankCount (owner packet) suffix destination q +
        frac * assignedRankCount (owner packet) suffix destination (q + 1))
  have hL1 (packet : Fin c) :
      (∑ destination : ι, |err packet destination|) =
        |(X packet : Real) - (q + frac)| := by
    simpa [err] using assignedRankProfiles_L1_exact
      (owner packet) suffix (X packet) q frac (hX packet) hq hfrac0 hfrac1
      hsuffix hmonoSuffix
  have hwithin (packet : Fin c) :
      (∑ destination : ι, (err packet destination) ^ 2) ≤
        ((X packet : Real) - (q + frac)) ^ 2 := by
    calc
      _ = ∑ destination : ι, |err packet destination| ^ 2 := by
        apply Finset.sum_congr rfl
        intro destination _
        rw [sq_abs]
      _ ≤ (∑ destination : ι, |err packet destination|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun destination _ => abs_nonneg _)
      _ = _ := by rw [hL1 packet, sq_abs]
  calc
    _ ≤ ∑ destination : ι,
        (∑ packet : Fin c, |err packet destination|) ^ 2 := by
      apply Finset.sum_le_sum
      intro destination _
      have htriangle :
          |∑ packet : Fin c, err packet destination| ≤
            ∑ packet : Fin c, |err packet destination| :=
        Finset.abs_sum_le_sum_abs _ _
      have hnonneg : 0 ≤ ∑ packet : Fin c, |err packet destination| :=
        Finset.sum_nonneg (fun packet _ => abs_nonneg _)
      have hleftnonneg : 0 ≤ |∑ packet : Fin c, err packet destination| :=
        abs_nonneg _
      calc
        (∑ packet : Fin c, err packet destination) ^ 2 =
            |∑ packet : Fin c, err packet destination| ^ 2 := (sq_abs _).symm
        _ ≤ (∑ packet : Fin c, |err packet destination|) ^ 2 := by
          nlinarith [htriangle, hleftnonneg, hnonneg]
    _ ≤ ∑ destination : ι,
        (c : Real) * ∑ packet : Fin c, (err packet destination) ^ 2 := by
      apply Finset.sum_le_sum
      intro destination _
      have hcs := _root_.sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin c)))
        (f := fun packet => |err packet destination|)
      simpa [sq_abs] using hcs
    _ = (c : Real) * ∑ packet : Fin c,
        ∑ destination : ι, (err packet destination) ^ 2 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ (c : Real) * ∑ packet : Fin c,
        ((X packet : Real) - (q + frac)) ^ 2 := by
      have hc : (0 : Real) ≤ c := by positivity
      apply mul_le_mul_of_nonneg_left _ hc
      apply Finset.sum_le_sum
      intro packet _
      exact hwithin packet

/-- The same receiver aggregation works when each source packet carries its
own fractional target, as in a routed layer whose source bags have different
profile means. -/
theorem assignedRankProfiles_aggregate_L2_var {ι : Type} [Fintype ι] [DecidableEq ι]
    {c m : Nat} (owner : Fin c → Fin m → ι) (suffix : Nat → Fin m → Bool)
    (X q : Fin c → Nat) (frac : Fin c → Real)
    (hX : ∀ p, X p ≤ m) (hq : ∀ p, q p < m)
    (hfrac0 : ∀ p, 0 ≤ frac p) (hfrac1 : ∀ p, frac p ≤ 1)
    (hsuffix : ∀ z ≤ m,
      (∑ k : Fin m, if suffix z k = true then 1 else 0) = z)
    (hmonoSuffix : ∀ a b, a ≤ b → ∀ k, suffix a k = true → suffix b k = true) :
    (∑ destination : ι,
      (Finset.univ.sum (fun (packet : Fin c) =>
        (assignedRankCount (owner packet) suffix destination (X packet) : Real) -
          ((1 - frac packet) * assignedRankCount (owner packet) suffix destination (q packet) +
            frac packet * assignedRankCount (owner packet) suffix destination (q packet + 1)))) ^ 2) ≤
      (c : Real) * Finset.univ.sum (fun (packet : Fin c) =>
        ((X packet : Real) - (q packet + frac packet)) ^ 2) := by
  let err (packet : Fin c) (destination : ι) : Real :=
    (assignedRankCount (owner packet) suffix destination (X packet) : Real) -
      ((1 - frac packet) * assignedRankCount (owner packet) suffix destination (q packet) +
        frac packet * assignedRankCount (owner packet) suffix destination (q packet + 1))
  have hL1 (packet : Fin c) :
      (∑ destination : ι, |err packet destination|) =
        |(X packet : Real) - (q packet + frac packet)| := by
    simpa [err] using assignedRankProfiles_L1_exact
      (owner packet) suffix (X packet) (q packet) (frac packet) (hX packet)
      (hq packet) (hfrac0 packet) (hfrac1 packet) hsuffix hmonoSuffix
  have hwithin (packet : Fin c) :
      (∑ destination : ι, (err packet destination) ^ 2) ≤
        ((X packet : Real) - (q packet + frac packet)) ^ 2 := by
    calc
      _ = ∑ destination : ι, |err packet destination| ^ 2 := by
        apply Finset.sum_congr rfl
        intro destination _
        rw [sq_abs]
      _ ≤ (∑ destination : ι, |err packet destination|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun destination _ => abs_nonneg _)
      _ = _ := by rw [hL1 packet, sq_abs]
  calc
    _ ≤ ∑ destination : ι,
        (∑ packet : Fin c, |err packet destination|) ^ 2 := by
      apply Finset.sum_le_sum
      intro destination _
      have htriangle :
          |∑ packet : Fin c, err packet destination| ≤
            ∑ packet : Fin c, |err packet destination| :=
        Finset.abs_sum_le_sum_abs _ _
      have hnonneg : 0 ≤ ∑ packet : Fin c, |err packet destination| :=
        Finset.sum_nonneg (fun packet _ => abs_nonneg _)
      have hleftnonneg : 0 ≤ |∑ packet : Fin c, err packet destination| :=
        abs_nonneg _
      calc
        (∑ packet : Fin c, err packet destination) ^ 2 =
            |∑ packet : Fin c, err packet destination| ^ 2 := (sq_abs _).symm
        _ ≤ (∑ packet : Fin c, |err packet destination|) ^ 2 := by
          nlinarith [htriangle, hleftnonneg, hnonneg]
    _ ≤ ∑ destination : ι,
        (c : Real) * ∑ packet : Fin c, (err packet destination) ^ 2 := by
      apply Finset.sum_le_sum
      intro destination _
      have hcs := _root_.sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin c)))
        (f := fun packet => |err packet destination|)
      simpa [sq_abs] using hcs
    _ = (c : Real) * ∑ packet : Fin c,
        ∑ destination : ι, (err packet destination) ^ 2 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ (c : Real) * Finset.univ.sum (fun (packet : Fin c) =>
        ((X packet : Real) - (q packet + frac packet)) ^ 2) := by
      have hc : (0 : Real) ≤ c := by positivity
      apply mul_le_mul_of_nonneg_left _ hc
      apply Finset.sum_le_sum
      intro packet _
      exact hwithin packet

/-- Overlap-sensitive form of the finite-source L2 aggregation inequality.
If at most `r` source profiles have nonzero discrepancy at any one
destination, the global charge is `r` rather than the total source count. -/
theorem finiteErrorProfiles_aggregate_L2_overlap
    {G D : Type} [Fintype G] [DecidableEq G] [Fintype D] [DecidableEq D]
    (error : G → D → Real) (energy : G → Real) (r : Nat)
    (hoverlap : ∀ destination,
      ((Finset.univ : Finset G).filter (fun g => error g destination ≠ 0)).card ≤ r)
    (hwithin : ∀ g, (∑ destination : D, (error g destination) ^ 2) ≤ energy g) :
    (∑ destination : D, (∑ g : G, error g destination) ^ 2) ≤
      (r : Real) * ∑ g : G, energy g := by
  classical
  have hpoint (destination : D) :
      (∑ g : G, error g destination) ^ 2 ≤
        (r : Real) * ∑ g : G, (error g destination) ^ 2 := by
    let active := (Finset.univ : Finset G).filter
      (fun g => error g destination ≠ 0)
    have hsum : (∑ g : G, error g destination) =
        ∑ g ∈ active, error g destination := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro g hg hnot
      have hzero : error g destination = 0 := by
        by_contra hn
        exact hnot (by simp [active, hn])
      simp [hzero]
    have hcs := _root_.sq_sum_le_card_mul_sum_sq
      (s := active) (f := fun g => error g destination)
    have hcard : (active.card : Real) ≤ r := by
      exact_mod_cast hoverlap destination
    have hnonneg : 0 ≤ ∑ g ∈ active, (error g destination) ^ 2 :=
      Finset.sum_nonneg (fun g hg => sq_nonneg _)
    have hactive_le :
        (∑ g ∈ active, (error g destination) ^ 2) ≤
          ∑ g : G, (error g destination) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro g hg hnot
      exact sq_nonneg _
    rw [hsum]
    calc
      (∑ g ∈ active, error g destination) ^ 2 ≤
          (active.card : Real) * ∑ g ∈ active, (error g destination) ^ 2 := by
        simpa using hcs
      _ ≤ (r : Real) * ∑ g ∈ active, (error g destination) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard hnonneg
      _ ≤ (r : Real) * ∑ g : G, (error g destination) ^ 2 :=
        mul_le_mul_of_nonneg_left hactive_le (by positivity)
  calc
    _ ≤ ∑ destination : D,
        (r : Real) * ∑ g : G, (error g destination) ^ 2 := by
      apply Finset.sum_le_sum
      intro destination hdestination
      exact hpoint destination
    _ = (r : Real) * ∑ g : G, ∑ destination : D,
        (error g destination) ^ 2 := by
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ (r : Real) * ∑ g : G, energy g := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro g hg
      exact hwithin g

/-! The abstract rank-owner interface can be realized directly by the actual
disjoint, complete `WireFlow` register partition. -/

/-- The unique `WireFlow` register containing a physical wire at time `t`. -/
noncomputable def wireSetOwner {d tf : Nat} (F : FlowSizes d tf) (t : Nat)
    (ht : t ≤ tf) (w : Fin (64 ^ d)) : KBag 64 d :=
  Classical.choose (wireSets_complete F ht w)

theorem wireSetOwner_mem {d tf : Nat} (F : FlowSizes d tf) (t : Nat)
    (ht : t ≤ tf) (w : Fin (64 ^ d)) :
    w ∈ wireSets F t (wireSetOwner F t ht w) :=
  Classical.choose_spec (wireSets_complete F ht w)

/-- Owner equality is exactly membership in that register. Completeness gives
an owner, and `wireSets_disjoint` makes it unique. -/
theorem wireSetOwner_eq_iff_mem {d tf : Nat} (F : FlowSizes d tf) (t : Nat)
    (ht : t ≤ tf) (w : Fin (64 ^ d)) (b : KBag 64 d) :
    wireSetOwner F t ht w = b ↔ w ∈ wireSets F t b := by
  constructor
  · intro h
    rw [← h]
    exact wireSetOwner_mem F t ht w
  · intro hb
    by_contra hne
    have hdis := wireSets_disjoint F ht (wireSetOwner F t ht w) b hne
    exact (Finset.disjoint_left.mp hdis) (wireSetOwner_mem F t ht w) hb

/-- Assign each rank of a scattered packet to the unique actual register
containing its physical wire. -/
noncomputable def wireSetPacketRankOwner {d tf m : Nat} {ι : Type}
    (F : FlowSizes d tf) (t : Nat) (ht : t ≤ tf)
    (packets : ι → Fin m ↪ Fin (64 ^ d)) (packet : ι) :
    Fin m → KBag 64 d :=
  fun k => wireSetOwner F t ht (packets packet k)

/-- The abstract assigned-rank count for this owner map is exactly the count
of selected packet ranks whose physical wires lie in the actual destination
register. This is the concrete counting bridge needed before applying the
scattered-profile energy inequality to a scheduler stage. -/
theorem assignedRankCount_wireSetPacketRankOwner {d tf m : Nat} {ι : Type}
    (F : FlowSizes d tf) (t : Nat) (ht : t ≤ tf)
    (packets : ι → Fin m ↪ Fin (64 ^ d)) (packet : ι)
    (suffix : Nat → Fin m → Bool) (destination : KBag 64 d) (X : Nat) :
    assignedRankCount (wireSetPacketRankOwner F t ht packets packet)
      suffix destination X =
    ∑ k : Fin m,
      if packets packet k ∈ wireSets F t destination ∧ suffix X k = true
      then 1 else 0 := by
  unfold assignedRankCount wireSetPacketRankOwner
  apply Finset.sum_congr rfl
  intro k hk
  have howner : destination = wireSetOwner F t ht (packets packet k) ↔
      packets packet k ∈ wireSets F t destination := by
    constructor
    · intro heq
      rw [heq]
      exact wireSetOwner_mem F t ht (packets packet k)
    · intro hmem
      by_contra hne
      have hdis := wireSets_disjoint F ht destination
        (wireSetOwner F t ht (packets packet k)) hne
      exact (Finset.disjoint_left.mp hdis) hmem
        (wireSetOwner_mem F t ht (packets packet k))
  simp only [howner]

/-- A finite sum of Boolean indicators is the cardinality of the corresponding
subtype. -/
theorem finSum_ite_one_eq_card_subtype {ι : Type} [Fintype ι]
    (P : ι → Prop) [DecidablePred P] :
    (∑ i : ι, if P i then 1 else 0) = Fintype.card {i // P i} := by
  classical
  calc
    (∑ i : ι, if P i then 1 else 0) =
        (Finset.univ.filter P).card := by
      rw [← Finset.sum_filter]
      simp
    _ = Fintype.card {i // P i} := by
      rw [Fintype.card_subtype]

/-- Linear interpolation of a monotone integer count profile is monotone in
the underlying real target, including when the floor crosses an integer. -/
def natProfileInterp (F : Nat → Nat) (q : Nat) (frac : Real) : Real :=
  (1 - frac) * (F q : Real) + frac * (F (q + 1) : Real)

/-- Summing the ideal means of the intervals assigned to one destination is
exactly the interpolation of that destination's integer count profile. -/
theorem profileIntervalOwnerMean_eq_interp {D : Type} [DecidableEq D]
    {m p : Nat} (cuts : Nat → Nat) (owner : Fin p → D) (destination : D)
    (q : Nat) (frac : Real) :
    (∑ i : Fin p, if owner i = destination then
      profileIntervalMean m q frac (cuts i.val) (cuts (i.val + 1)) else 0) =
      natProfileInterp
        (profileIntervalOwnerCount (m := m) cuts owner destination) q frac := by
  classical
  calc
    _ = ∑ i : Fin p,
        ((1 - frac) * (if owner i = destination then
            (profileInterval m q (cuts i.val) (cuts (i.val + 1)) : Real) else 0) +
          frac * (if owner i = destination then
            (profileInterval m (q + 1) (cuts i.val) (cuts (i.val + 1)) : Real) else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : owner i = destination <;>
        simp [profileIntervalMean, h]
    _ = (1 - frac) *
          (∑ i : Fin p, if owner i = destination then
            (profileInterval m q (cuts i.val) (cuts (i.val + 1)) : Real) else 0) +
        frac * (∑ i : Fin p, if owner i = destination then
          (profileInterval m (q + 1) (cuts i.val) (cuts (i.val + 1)) : Real) else 0) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by
      simp [natProfileInterp, profileIntervalOwnerCount]

/-- The scheduler's ideal target for any selected family of rank intervals is
the linear interpolation of that family's integer interval-count profile. -/
theorem profileIntervalSelectedMean_eq_interp {m : Nat}
    (cuts : Nat → Nat) (selected : Finset Nat) (q : Nat) (frac : Real) :
    (∑ i ∈ selected,
      profileIntervalMean m q frac (cuts i) (cuts (i + 1))) =
      natProfileInterp (profileIntervalSelectedCount (m := m) cuts selected) q frac := by
  classical
  unfold profileIntervalMean natProfileInterp profileIntervalSelectedCount
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  push_cast
  ring

theorem natProfileInterp_between (F : Nat → Nat) (hF : Monotone F)
    (q : Nat) (frac : Real) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (F q : Real) ≤ natProfileInterp F q frac ∧
      natProfileInterp F q frac ≤ F (q + 1) := by
  have hstepNat := hF (Nat.le_succ q)
  have hstep : (F q : Real) ≤ F (q + 1) := by exact_mod_cast hstepNat
  constructor <;> unfold natProfileInterp <;> nlinarith [
    mul_nonneg hfrac0 (show (0 : Real) ≤ F (q + 1) - F q by linarith),
    mul_nonneg (sub_nonneg.mpr hfrac1)
      (show (0 : Real) ≤ F (q + 1) - F q by linarith)]

theorem natProfileInterp_mono_mean (F : Nat → Nat) (hF : Monotone F)
    (q₁ q₂ : Nat) (frac₁ frac₂ : Real)
    (hfrac₁0 : 0 ≤ frac₁) (hfrac₁1 : frac₁ ≤ 1)
    (hfrac₂0 : 0 ≤ frac₂) (hfrac₂1 : frac₂ ≤ 1)
    (hmean : (q₁ : Real) + frac₁ ≤ (q₂ : Real) + frac₂) :
    natProfileInterp F q₁ frac₁ ≤ natProfileInterp F q₂ frac₂ := by
  by_cases hq : q₁ ≤ q₂
  · by_cases heq : q₁ = q₂
    · subst q₂
      have hfrac : frac₁ ≤ frac₂ := by nlinarith
      have hstepNat := hF (Nat.le_succ q₁)
      have hstep : (F q₁ : Real) ≤ F (q₁ + 1) := by exact_mod_cast hstepNat
      unfold natProfileInterp
      nlinarith [mul_nonneg (show (0 : Real) ≤ frac₂ - frac₁ by linarith)
        (show (0 : Real) ≤ F (q₁ + 1) - F q₁ by linarith)]
    · have hlt : q₁ < q₂ := by omega
      have hleft := (natProfileInterp_between F hF q₁ frac₁ hfrac₁0 hfrac₁1).2
      have hright := (natProfileInterp_between F hF q₂ frac₂ hfrac₂0 hfrac₂1).1
      have hmidNat := hF (Nat.succ_le_of_lt hlt)
      have hmid : (F (q₁ + 1) : Real) ≤ F q₂ := by exact_mod_cast hmidNat
      exact le_trans hleft (le_trans hmid hright)
  · have hlt : q₂ < q₁ := by omega
    have hqleReal : (q₁ : Real) ≤ (q₂ : Real) + 1 := by nlinarith
    have hqle : q₁ ≤ q₂ + 1 := by exact_mod_cast hqleReal
    have hsucc : q₂ + 1 = q₁ := by omega
    have hcast : (q₁ : Real) = (q₂ : Real) + 1 := by exact_mod_cast hsucc.symm
    have hmean' : (q₂ : Real) + 1 + frac₁ ≤ (q₂ : Real) + frac₂ := by
      rw [← hcast]
      exact hmean
    have hf₁ : frac₁ = 0 := by nlinarith [hfrac₂1]
    have hf₂ : frac₂ = 1 := by nlinarith [hfrac₁0]
    rw [hf₁, hf₂]
    rw [← hsucc]
    simp [natProfileInterp]

/-- Finite sums of packet count interpolants remain monotone when each
packet's integer count profile is monotone and its real target is monotone.
This is the profile-level closure needed when packets are regrouped by their
actual `WireFlow` owner. -/
theorem natProfileInterp_sum_mono {ι Θ : Type} [Fintype ι]
    (F : ι → Nat → Nat) (q : Θ → ι → Nat) (frac : Θ → ι → Real)
    (hF : ∀ packet, Monotone (F packet))
    (hfrac0 : ∀ θ packet, 0 ≤ frac θ packet)
    (hfrac1 : ∀ θ packet, frac θ packet ≤ 1)
    (hmono : ∀ θ₁ θ₂ packet,
      (q θ₁ packet : Real) + frac θ₁ packet ≤
        (q θ₂ packet : Real) + frac θ₂ packet)
    (θ₁ θ₂ : Θ) :
    (∑ packet, natProfileInterp (F packet) (q θ₁ packet)
      (frac θ₁ packet)) ≤
      ∑ packet, natProfileInterp (F packet) (q θ₂ packet)
        (frac θ₂ packet) := by
  apply Finset.sum_le_sum
  intro packet _
  exact natProfileInterp_mono_mean (F packet) (hF packet)
    (q θ₁ packet) (q θ₂ packet) (frac θ₁ packet) (frac θ₂ packet)
    (hfrac0 θ₁ packet) (hfrac1 θ₁ packet)
    (hfrac0 θ₂ packet) (hfrac1 θ₂ packet)
    (hmono θ₁ θ₂ packet)

/-- The preceding closure applies to actual scattered ownership: each packet
may contribute an arbitrary subset of its ranks to a destination, provided
the packet's rank prefixes are nested. The resulting sum of destination
profile means is monotone in the packet targets. -/
theorem assignedRankInterp_sum_mono {κ Θ D : Type} [Fintype κ]
    [Fintype D] [DecidableEq D] {m : Nat}
    (owner : κ → Fin m → D) (rankPrefix : κ → Nat → Fin m → Bool)
    (destination : D) (q : Θ → κ → Nat) (frac : Θ → κ → Real)
    (hprefix : ∀ packet a b, a ≤ b → ∀ k,
      rankPrefix packet a k = true → rankPrefix packet b k = true)
    (hfrac0 : ∀ θ packet, 0 ≤ frac θ packet)
    (hfrac1 : ∀ θ packet, frac θ packet ≤ 1)
    (htarget : ∀ θ₁ θ₂ packet,
      (q θ₁ packet : Real) + frac θ₁ packet ≤
        (q θ₂ packet : Real) + frac θ₂ packet)
    (θ₁ θ₂ : Θ) :
    (∑ packet, natProfileInterp
      (assignedRankCount (owner packet) (rankPrefix packet) destination)
      (q θ₁ packet) (frac θ₁ packet)) ≤
      ∑ packet, natProfileInterp
        (assignedRankCount (owner packet) (rankPrefix packet) destination)
        (q θ₂ packet) (frac θ₂ packet) := by
  apply natProfileInterp_sum_mono
    (F := fun packet z =>
      assignedRankCount (owner packet) (rankPrefix packet) destination z)
    q frac ?_ hfrac0 hfrac1 htarget θ₁ θ₂
  intro packet a b hab
  exact assignedRankCount_mono (owner packet) (rankPrefix packet) destination a b
    (fun _ => hprefix packet a b hab) hab

/-- Concrete WireFlow form of `assignedRankInterp_sum_mono`: assigning every
rank of each scattered packet to its containing current register preserves
monotonicity of the summed fractional destination targets. -/
theorem wireSetPacketRankInterp_sum_mono {d tf m : Nat} {κ Θ : Type}
    [Fintype κ]
    (F : FlowSizes d tf) (t : Nat) (ht : t ≤ tf)
    (packets : κ → Fin m ↪ Fin (64 ^ d))
    (rankPrefix : κ → Nat → Fin m → Bool)
    (receiver : KBag 64 d) (q : Θ → κ → Nat) (frac : Θ → κ → Real)
    (hprefix : ∀ packet a b, a ≤ b → ∀ k,
      rankPrefix packet a k = true → rankPrefix packet b k = true)
    (hfrac0 : ∀ θ packet, 0 ≤ frac θ packet)
    (hfrac1 : ∀ θ packet, frac θ packet ≤ 1)
    (htarget : ∀ θ₁ θ₂ packet,
      (q θ₁ packet : Real) + frac θ₁ packet ≤
        (q θ₂ packet : Real) + frac θ₂ packet)
    (θ₁ θ₂ : Θ) :
    (∑ packet, natProfileInterp
      (assignedRankCount
        (wireSetPacketRankOwner F t ht packets packet)
        (rankPrefix packet) receiver)
      (q θ₁ packet) (frac θ₁ packet)) ≤
      ∑ packet, natProfileInterp
        (assignedRankCount
          (wireSetPacketRankOwner F t ht packets packet)
          (rankPrefix packet) receiver)
        (q θ₂ packet) (frac θ₂ packet) := by
  exact assignedRankInterp_sum_mono
    (fun packet => wireSetPacketRankOwner F t ht packets packet)
    rankPrefix receiver q frac hprefix hfrac0 hfrac1 htarget θ₁ θ₂

/-- If a family of disjoint packet embeddings covers all wires, then summing
its rank-owner threshold counts gives exactly the threshold count in any
actual `WireFlow` register. This turns the abstract scattered-rank accounting
into the physical receiver count used by the scheduler. -/
theorem packetRankOwner_trueCountOn_eq_of_partition {d tf m : Nat}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : FlowSizes d tf) (t : Nat) (ht : t ≤ tf)
    (packets : ι → Fin m ↪ Fin (64 ^ d))
    (hdisjoint : ∀ {p p' : ι}, p ≠ p' → ∀ i j,
      packets p i ≠ packets p' j)
    (hcover : ∀ w : Fin (64 ^ d), ∃ p i, packets p i = w)
    (v : Fin (64 ^ d) → Bool) (destination : KBag 64 d) :
    (∑ p : ι,
      assignedRankCount (wireSetPacketRankOwner F t ht packets p)
        (fun _ i => v (packets p i)) destination 0) =
      trueCountOn (wireSets F t destination) v := by
  classical
  let P : ι × Fin m → Prop := fun z =>
    wireSetOwner F t ht (packets z.1 z.2) = destination ∧
      v (packets z.1 z.2) = true
  let source := {z : ι × Fin m // P z}
  let target := {w : {w : Fin (64 ^ d) // w ∈ wireSets F t destination} //
    v w.val = true}
  have hflatInj : Function.Injective (fun z : ι × Fin m =>
      packets z.1 z.2) := by
    intro z z' h
    have hp : z.1 = z'.1 := by
      by_contra hne
      exact (hdisjoint hne z.2 z'.2) h
    apply Prod.ext
    · exact hp
    · change packets z.1 z.2 = packets z'.1 z'.2 at h
      rw [hp] at h
      exact (packets z'.1).injective h
  let f : source → target := fun z =>
    ⟨⟨packets z.val.1 z.val.2,
      (wireSetOwner_eq_iff_mem F t ht (packets z.val.1 z.val.2) destination).1
        z.property.1⟩,
      z.property.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z z' hzz'
      apply Subtype.ext
      exact hflatInj (congrArg (fun w : target => w.val.val) hzz')
    · intro w
      obtain ⟨p, i, hpi⟩ := hcover w.val.val
      have hmem : w.val.val ∈ wireSets F t destination := w.val.property
      have howner : wireSetOwner F t ht (packets p i) = destination := by
        apply (wireSetOwner_eq_iff_mem F t ht (packets p i) destination).2
        simpa only [hpi] using hmem
      have hv : v (packets p i) = true := by simpa [hpi] using w.property
      refine ⟨⟨(p, i), ⟨howner, hv⟩⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hpi
  have hcard : Fintype.card source = Fintype.card target :=
    Fintype.card_congr (Equiv.ofBijective f hf)
  have hsum : (∑ p : ι,
      assignedRankCount (wireSetPacketRankOwner F t ht packets p)
        (fun _ i => v (packets p i)) destination 0) = Fintype.card source := by
    calc
      _ = ∑ p : ι, ∑ i : Fin m,
          if P (p, i) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [assignedRankCount_wireSetPacketRankOwner]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [P, wireSetOwner_eq_iff_mem]
      _ = ∑ p : ι, Fintype.card {i : Fin m // P (p, i)} := by
        apply Finset.sum_congr rfl
        intro p hp
        exact finSum_ite_one_eq_card_subtype (fun i : Fin m => P (p, i))
      _ = Fintype.card (Σ p : ι, {i : Fin m // P (p, i)}) := by
        rw [Fintype.card_sigma]
      _ = Fintype.card source := by
        apply Fintype.card_congr
        refine Equiv.mk (fun z => ⟨(z.1, z.2.1), z.2.2⟩)
          (fun z => ⟨z.1.1, ⟨z.1.2, z.2⟩⟩) ?_ ?_
        · intro z
          rfl
        · intro z
          rfl
  unfold trueCountOn
  exact hsum.trans hcard

/-- Restricted form of the rank-owner count identity: a disjoint packet family
that partitions one destination register suffices; it need not cover the full
wire universe. -/
theorem packetRankOwner_trueCountOn_eq_of_local_partition {d tf m : Nat}
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : FlowSizes d tf) (t : Nat) (ht : t ≤ tf)
    (packets : ι → Fin m ↪ Fin (64 ^ d))
    (hdisjoint : ∀ {p p' : ι}, p ≠ p' → ∀ i j,
      packets p i ≠ packets p' j)
    (destination : KBag 64 d)
    (hcover : ∀ w ∈ wireSets F t destination, ∃ p i, packets p i = w)
    (v : Fin (64 ^ d) → Bool) :
    (∑ p : ι,
      assignedRankCount (wireSetPacketRankOwner F t ht packets p)
        (fun _ i => v (packets p i)) destination 0) =
      trueCountOn (wireSets F t destination) v := by
  classical
  let P : ι × Fin m → Prop := fun z =>
    packets z.1 z.2 ∈ wireSets F t destination ∧
      v (packets z.1 z.2) = true
  let source := {z : ι × Fin m // P z}
  let target := {w : {w : Fin (64 ^ d) // w ∈ wireSets F t destination} //
    v w.val = true}
  have hflatInj : Function.Injective (fun z : ι × Fin m => packets z.1 z.2) := by
    intro z z' h
    have hp : z.1 = z'.1 := by
      by_contra hne
      exact (hdisjoint hne z.2 z'.2) h
    apply Prod.ext
    · exact hp
    · change packets z.1 z.2 = packets z'.1 z'.2 at h
      rw [hp] at h
      exact (packets z'.1).injective h
  let f : source → target := fun z =>
    ⟨⟨packets z.val.1 z.val.2,
      z.property.1⟩, z.property.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z z' hzz'
      apply Subtype.ext
      exact hflatInj (congrArg (fun w : target => w.val.val) hzz')
    · intro w
      obtain ⟨p, i, hpi⟩ := hcover w.val.val w.val.property
      have hmem : packets p i ∈ wireSets F t destination := by
        simpa only [hpi] using w.val.property
      have hv : v (packets p i) = true := by simpa [hpi] using w.property
      refine ⟨⟨(p, i), ⟨hmem, hv⟩⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hpi
  have hcard : Fintype.card source = Fintype.card target :=
    Fintype.card_congr (Equiv.ofBijective f hf)
  have hsum : (∑ p : ι,
      assignedRankCount (wireSetPacketRankOwner F t ht packets p)
        (fun _ i => v (packets p i)) destination 0) = Fintype.card source := by
    calc
      _ = ∑ p : ι, ∑ i : Fin m, if P (p, i) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [assignedRankCount_wireSetPacketRankOwner]
      _ = ∑ p : ι, Fintype.card {i : Fin m // P (p, i)} := by
        apply Finset.sum_congr rfl
        intro p hp
        exact finSum_ite_one_eq_card_subtype (fun i : Fin m => P (p, i))
      _ = Fintype.card (Σ p : ι, {i : Fin m // P (p, i)}) := by
        rw [Fintype.card_sigma]
      _ = Fintype.card source := by
        apply Fintype.card_congr
        refine Equiv.mk (fun z => ⟨(z.1, z.2.1), z.2.2⟩)
          (fun z => ⟨z.1.1, ⟨z.1.2, z.2⟩⟩) ?_ ?_
        · intro z
          rfl
        · intro z
          rfl
  unfold trueCountOn
  exact hsum.trans hcard

theorem packetRankOwner_trueCountOn_intersection
    {d tf m : Nat} {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : FlowSizes d tf) (t : Nat) (ht : t ≤ tf)
    (packets : ι → Fin m ↪ Fin (64 ^ d))
    (hdisjoint : ∀ {p p' : ι}, p ≠ p' → ∀ i j, packets p i ≠ packets p' j)
    (support : Finset (Fin (64 ^ d)))
    (hsubset : ∀ p i, packets p i ∈ support)
    (hcover : ∀ w ∈ support, ∃ p i, packets p i = w)
    (destination : KBag 64 d) (v : Fin (64 ^ d) → Bool) :
    (∑ p : ι,
      assignedRankCount (wireSetPacketRankOwner F t ht packets p)
        (fun _ i => v (packets p i)) destination 0) =
      trueCountOn (support ∩ wireSets F t destination) v := by
  classical
  let supportDest : Finset (Fin (64 ^ d)) := support ∩ wireSets F t destination
  let P : ι × Fin m → Prop := fun z =>
    packets z.1 z.2 ∈ support ∧
      packets z.1 z.2 ∈ wireSets F t destination ∧
        v (packets z.1 z.2) = true
  let source := {z : ι × Fin m // P z}
  let target := {w : supportDest // v w.val = true}
  have hflatInj : Function.Injective (fun z : ι × Fin m => packets z.1 z.2) := by
    intro z z' h
    have hp : z.1 = z'.1 := by
      by_contra hne
      exact (hdisjoint hne z.2 z'.2) h
    apply Prod.ext
    · exact hp
    · change packets z.1 z.2 = packets z'.1 z'.2 at h
      rw [hp] at h
      exact (packets z'.1).injective h
  let f : source → target := fun z =>
    ⟨⟨packets z.val.1 z.val.2,
        Finset.mem_inter.mpr ⟨z.property.1, z.property.2.1⟩⟩, z.property.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z z' hzz'
      apply Subtype.ext
      exact hflatInj (congrArg (fun w : target => w.val.val) hzz')
    · intro w
      have hwinter := Finset.mem_inter.mp w.val.property
      obtain ⟨p, i, hpi⟩ := hcover w.val.val hwinter.1
      have hsupport : packets p i ∈ support := by simpa [hpi] using hwinter.1
      have hdestination : packets p i ∈ wireSets F t destination := by
        simpa [hpi] using hwinter.2
      have htrue : v (packets p i) = true := by simpa [hpi] using w.property
      refine ⟨⟨(p, i), ⟨hsupport, hdestination, htrue⟩⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hpi
  have hcard : Fintype.card source = Fintype.card target :=
    Fintype.card_congr (Equiv.ofBijective f hf)
  have hsum : (∑ p : ι,
      assignedRankCount (wireSetPacketRankOwner F t ht packets p)
        (fun _ i => v (packets p i)) destination 0) = Fintype.card source := by
    calc
      _ = ∑ p : ι, ∑ i : Fin m, if P (p, i) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [assignedRankCount_wireSetPacketRankOwner]
        apply Finset.sum_congr rfl
        intro i _
        simp [P, hsubset p i]
      _ = ∑ p : ι, Fintype.card {i : Fin m // P (p, i)} := by
        apply Finset.sum_congr rfl
        intro p _
        exact finSum_ite_one_eq_card_subtype (fun i : Fin m => P (p, i))
      _ = Fintype.card (Σ p : ι, {i : Fin m // P (p, i)}) := by
        rw [Fintype.card_sigma]
      _ = Fintype.card source := by
        apply Fintype.card_congr
        refine Equiv.mk (fun z => ⟨(z.1, z.2.1), z.2.2⟩)
          (fun z => ⟨z.1.1, ⟨z.1.2, z.2⟩⟩) ?_ ?_
        · intro z
          rfl
        · intro z
          rfl
  have htarget : trueCountOn supportDest v =
      Fintype.card target := by
    simp [supportDest, target, trueCountOn]
  exact hsum.trans (hcard.trans htarget.symm)

theorem profileInterval_partition_L1_exact (m p X q : Nat) (frac : Real)
    (cuts : Nat → Nat) (hstart : cuts 0 = 0) (hcuts : Monotone cuts)
    (hend : cuts p = m) (hX : X ≤ m) (hq : q < m)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ range p,
      |(profileInterval m X (cuts i) (cuts (i + 1)) : Real) -
        profileIntervalMean m q frac (cuts i) (cuts (i + 1))|) =
      |(X : Real) - (q + frac)| := by
  have hmean : (∑ i ∈ range p,
      profileIntervalMean m q frac (cuts i) (cuts (i + 1))) = q + frac := by
    have hqsum : (∑ i ∈ range p,
        (profileInterval m q (cuts i) (cuts (i + 1)) : Real)) = q := by
      exact_mod_cast profileInterval_partition_total m p q cuts hstart hcuts hend (by omega)
    have hq1sum : (∑ i ∈ range p,
        (profileInterval m (q + 1) (cuts i) (cuts (i + 1)) : Real)) = q + 1 := by
      exact_mod_cast profileInterval_partition_total m p (q + 1) cuts hstart hcuts hend (by omega)
    unfold profileIntervalMean
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hqsum, hq1sum]
    ring
  have hxsum := profileInterval_partition_total m p X cuts hstart hcuts hend hX
  have hxsumR : (∑ i ∈ range p,
      (profileInterval m X (cuts i) (cuts (i + 1)) : Real)) = X := by exact_mod_cast hxsum
  by_cases hXq : X ≤ q
  · have hpoint : ∀ i ∈ range p,
        (profileInterval m X (cuts i) (cuts (i + 1)) : Real) ≤
          profileIntervalMean m q frac (cuts i) (cuts (i + 1)) := by
      intro i hi
      have hi' : i < p := mem_range.mp hi
      have hab : cuts i ≤ cuts (i + 1) := hcuts (Nat.le_succ i)
      have hb : cuts (i + 1) ≤ m := by
        rw [← hend]
        exact hcuts (by omega)
      have hbase := profileInterval_mono_X m q X (cuts i) (cuts (i + 1)) hab hb (by omega)
      have hnext := profileInterval_mono_X m (q + 1) q (cuts i) (cuts (i + 1)) hab hb (by omega)
      unfold profileIntervalMean
      have hn : (profileInterval m q (cuts i) (cuts (i + 1)) : Real) ≤
          profileInterval m (q + 1) (cuts i) (cuts (i + 1)) := by exact_mod_cast hnext
      have hb' : (profileInterval m X (cuts i) (cuts (i + 1)) : Real) ≤
          profileInterval m q (cuts i) (cuts (i + 1)) := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range p,
          |(profileInterval m X (cuts i) (cuts (i + 1)) : Real) -
            profileIntervalMean m q frac (cuts i) (cuts (i + 1))|) =
          ∑ i ∈ range p,
            (profileIntervalMean m q frac (cuts i) (cuts (i + 1)) -
              (profileInterval m X (cuts i) (cuts (i + 1)) : Real)) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonpos (by linarith [hpoint i hi])]
        ring
      _ = (∑ i ∈ range p,
          profileIntervalMean m q frac (cuts i) (cuts (i + 1))) -
          (∑ i ∈ range p,
            (profileInterval m X (cuts i) (cuts (i + 1)) : Real)) := by rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        calc
          _ = (q + frac) - X := by rw [hmean, hxsumR]
          _ = |(X : Real) - (q + frac)| := by
            have hXR : (X : Real) ≤ q := by exact_mod_cast hXq
            rw [abs_of_nonpos (by linarith [hXR, hfrac0])]
            ring
  · have hX' : q + 1 ≤ X := by omega
    have hpoint : ∀ i ∈ range p,
        profileIntervalMean m q frac (cuts i) (cuts (i + 1)) ≤
          (profileInterval m X (cuts i) (cuts (i + 1)) : Real) := by
      intro i hi
      have hi' : i < p := mem_range.mp hi
      have hab : cuts i ≤ cuts (i + 1) := hcuts (Nat.le_succ i)
      have hb : cuts (i + 1) ≤ m := by
        rw [← hend]
        exact hcuts (by omega)
      have hbase := profileInterval_mono_X m X (q + 1) (cuts i) (cuts (i + 1)) hab hb (by omega)
      have hnext := profileInterval_mono_X m (q + 1) q (cuts i) (cuts (i + 1)) hab hb (by omega)
      unfold profileIntervalMean
      have hn : (profileInterval m q (cuts i) (cuts (i + 1)) : Real) ≤
          profileInterval m (q + 1) (cuts i) (cuts (i + 1)) := by exact_mod_cast hnext
      have hb' : (profileInterval m (q + 1) (cuts i) (cuts (i + 1)) : Real) ≤
          profileInterval m X (cuts i) (cuts (i + 1)) := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range p,
          |(profileInterval m X (cuts i) (cuts (i + 1)) : Real) -
            profileIntervalMean m q frac (cuts i) (cuts (i + 1))|) =
          ∑ i ∈ range p,
            ((profileInterval m X (cuts i) (cuts (i + 1)) : Real) -
              profileIntervalMean m q frac (cuts i) (cuts (i + 1))) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonneg (by linarith [hpoint i hi])]
      _ = (∑ i ∈ range p,
          (profileInterval m X (cuts i) (cuts (i + 1)) : Real)) -
          (∑ i ∈ range p,
            profileIntervalMean m q frac (cuts i) (cuts (i + 1))) := by rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        calc
          _ = X - (q + frac) := by rw [hxsumR, hmean]
          _ = |(X : Real) - (q + frac)| := by
            have hXR : (q : Real) + 1 ≤ X := by exact_mod_cast hX'
            rw [abs_of_nonneg (by linarith [hXR, hfrac1])]

/-- The exact interval-partition error identity also covers the full and empty
profile endpoints. At positive capacity, `q=m` is represented by the equivalent
strict form `(m-1)+1`; at zero capacity all terms vanish. -/
theorem profileInterval_partition_L1_exact_allow_endpoint
    (m p X q : Nat) (frac : Real) (cuts : Nat → Nat)
    (hstart : cuts 0 = 0) (hcuts : Monotone cuts) (hend : cuts p = m)
    (hX : X ≤ m) (hq : q ≤ m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (hendpoint : q = m → frac = 0) :
    (∑ i ∈ range p,
      |(profileInterval m X (cuts i) (cuts (i + 1)) : Real) -
        profileIntervalMean m q frac (cuts i) (cuts (i + 1))|) =
      |(X : Real) - (q + frac)| := by
  by_cases hm : 0 < m
  · by_cases hq' : q < m
    · exact profileInterval_partition_L1_exact m p X q frac cuts
        hstart hcuts hend hX hq' hfrac0 hfrac1
    · have hqeq : q = m := by omega
      have hf : frac = 0 := hendpoint hqeq
      have hcast : ((m - 1 : Nat) : Real) + 1 = (m : Real) := by
        have hn : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
        exact_mod_cast hn
      have hmeanEq (a b : Nat) :
          profileIntervalMean m q frac a b =
            profileIntervalMean m (m - 1) 1 a b := by
        rw [hqeq, hf]
        simp only [profileIntervalMean]
        rw [show m - 1 + 1 = m by omega]
        ring
      calc
        _ = ∑ i ∈ range p,
            |(profileInterval m X (cuts i) (cuts (i + 1)) : Real) -
              profileIntervalMean m (m - 1) 1 (cuts i) (cuts (i + 1))| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hmeanEq]
        _ = |(X : Real) - ((m - 1 : Nat) + 1)| :=
          profileInterval_partition_L1_exact m p X (m - 1) 1 cuts
            hstart hcuts hend hX (by omega) (by norm_num) (by norm_num)
        _ = |(X : Real) - (q + frac)| := by
          rw [hqeq, hf, hcast]
          simp
  · have hm0 : m = 0 := by omega
    have hq0 : q = 0 := by omega
    have hX0 : X = 0 := by omega
    have hqeq : q = m := by omega
    have hf : frac = 0 := hendpoint hqeq
    have hcut0 (i : Nat) (hi : i ≤ p) : cuts i = 0 := by
      have hle := hcuts hi
      rw [hend, hm0] at hle
      omega
    calc
      _ = ∑ i ∈ range p, (0 : Real) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < p := Finset.mem_range.mp hi
        simp [profileInterval, profileTail, profileIntervalMean, hm0, hX0, hq0, hf,
          hcut0 i (by omega), hcut0 (i + 1) (by omega)]
      _ = |(X : Real) - (q + frac)| := by simp [hX0, hq0, hf]

/-- The actual count in a half-open rank interval of an increasing Boolean
packet is its ideal profile count. -/
theorem sortedBool_rankInterval_trueCount {m : Nat} (v : Fin m → Bool)
    (hv : Monotone v) (a b : Nat) (hab : a ≤ b) (hb : b ≤ m) :
    boolTrueCount (fun j : Fin (b - a) => v ⟨a + j.val, by have hj := j.isLt; omega⟩) =
      profileInterval m (boolTrueCount v) a b := by
  let hsumB : b + (m - b) = m := Nat.add_sub_of_le hb
  let hsumA : a + (m - a) = m := Nat.add_sub_of_le (le_trans hab hb)
  let hsum : a + (b - a) = b := Nat.add_sub_of_le hab
  let A : Fin a → Bool := fun i => v (Fin.cast hsumA (Fin.castAdd (m - a) i))
  let B : Fin b → Bool := fun i => v (Fin.cast hsumB (Fin.castAdd (m - b) i))
  let C : Fin (b - a) → Bool := fun j => v ⟨a + j.val, by have hj := j.isLt; omega⟩
  have he : Fin.append A C = B ∘ Fin.cast hsum := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [Fin.append_left, Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [A, B, Fin.val_cast, Fin.val_castAdd, Fin.val_mk]
    · simp only [Fin.append_right, Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [B, C, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_mk]
  have hcounts : boolTrueCount B = boolTrueCount A + boolTrueCount C := by
    calc
      boolTrueCount B = boolTrueCount (B ∘ Fin.cast hsum) := (boolTrueCount_finCast hsum B).symm
      _ = boolTrueCount (Fin.append A C) := congrArg boolTrueCount he.symm
      _ = boolTrueCount A + boolTrueCount C := boolTrueCount_append_general A C
  have hA := sortedBool_prefix_trueCount v hv (le_trans hab hb)
  have hB := sortedBool_prefix_trueCount v hv hb
  change boolTrueCount A = _ at hA
  change boolTrueCount B = _ at hB
  have hC : boolTrueCount C =
      (boolTrueCount v - (m - b)) - (boolTrueCount v - (m - a)) := by omega
  change boolTrueCount C = profileInterval m (boolTrueCount v) a b
  unfold profileInterval profileTail
  rw [hC]

/-- Sorting two ascending 64-wire Boolean runs makes the physical first and
second 64-wire rank cells follow the clamped rank profile of the total count.
This is distinct from the balanced counts in the logical even/odd dealt
packets. -/
theorem oddEvenMerge128_physicalHalf_counts (v : Fin 128 → Bool)
    (hA : Monotone (fun i : Fin 64 => v (Fin.castAdd 64 i)))
    (hB : Monotone (fun i : Fin 64 => v (Fin.natAdd 64 i))) :
    let w := (oddEvenMergeNet 7).exec v
    boolTrueCount (fun i : Fin 64 => w ⟨i.val, by omega⟩) =
        min 64 (boolTrueCount v - 64) ∧
      boolTrueCount (fun i : Fin 64 => w ⟨64 + i.val, by omega⟩) =
        min 64 (boolTrueCount v) := by
  let w := (oddEvenMergeNet 7).exec v
  have hsorted : Monotone w := by
    dsimp [w]
    exact oddEvenMergeNet_sorts_two_runs 6 v ⟨hA, hB⟩
  have hcount : boolTrueCount w = boolTrueCount v :=
    boolTrueCount_exec (oddEvenMergeNet 7) v
  have hfirstProfile := sortedBool_rankInterval_trueCount w hsorted 0 64
    (by omega) (by omega)
  have hfirst : boolTrueCount (fun i : Fin 64 => w ⟨i.val, by omega⟩) =
      min 64 (boolTrueCount v - 64) := by
    have hfirst' : boolTrueCount (fun i : Fin 64 => w ⟨i.val, by omega⟩) =
        profileInterval 128 (boolTrueCount w) 0 64 := by
      simpa [w] using hfirstProfile
    rw [profileInterval_formula 128 (boolTrueCount w) 0 64 (by omega) (by omega),
      hcount] at hfirst'
    exact hfirst'
  have hsecondProfile := sortedBool_rankInterval_trueCount w hsorted 64 128
    (by omega) (by omega)
  have hsecond : boolTrueCount (fun i : Fin 64 => w ⟨64 + i.val, by omega⟩) =
      min 64 (boolTrueCount v) := by
    have hsecond' : boolTrueCount (fun i : Fin 64 => w ⟨64 + i.val, by omega⟩) =
        profileInterval 128 (boolTrueCount w) 64 128 := by
      simpa [w] using hsecondProfile
    rw [profileInterval_formula 128 (boolTrueCount w) 64 128 (by omega) (by omega),
      hcount] at hsecond'
    exact hsecond'
  exact ⟨hfirst, hsecond⟩

/-- At total count 64, the positional 64-wire cells become maximally
imbalanced after the merge, although the logical even/odd dealt packets each
have count 32. Thus positional-cell variance cannot be substituted for the
logical packet variance in the mixing recurrence. -/
theorem oddEvenMerge128_balanced_deal_vs_physical_halves (v : Fin 128 → Bool)
    (hA : Monotone (fun i : Fin 64 => v (Fin.castAdd 64 i)))
    (hB : Monotone (fun i : Fin 64 => v (Fin.natAdd 64 i)))
    (hcount : boolTrueCount v = 64) :
    let w := (oddEvenMergeNet 7).exec v
    (boolTrueCount (fun i : Fin 64 => w ⟨i.val, by omega⟩) = 0 ∧
      boolTrueCount (fun i : Fin 64 => w ⟨64 + i.val, by omega⟩) = 64) ∧
    (boolTrueCount (fun i : Fin 64 => w (evenWire 64 i)) = 32 ∧
      boolTrueCount (fun i : Fin 64 => w (oddWire 64 i)) = 32) := by
  let w := (oddEvenMergeNet 7).exec v
  have hsorted : Monotone w := by
    dsimp [w]
    exact oddEvenMergeNet_sorts_two_runs 6 v ⟨hA, hB⟩
  have hphys := oddEvenMerge128_physicalHalf_counts v hA hB
  have hparity := sorted_bool_parity_counts (m := 64) w hsorted
  rw [boolTrueCount_exec] at hparity
  have hphysical :
      boolTrueCount (fun i : Fin 64 => w ⟨i.val, by omega⟩) = 0 ∧
      boolTrueCount (fun i : Fin 64 => w ⟨64 + i.val, by omega⟩) = 64 := by
    simpa [w, hcount] using hphys
  have hdealt :
      boolTrueCount (fun i : Fin 64 => w (evenWire 64 i)) = 32 ∧
      boolTrueCount (fun i : Fin 64 => w (oddWire 64 i)) = 32 := by
    constructor <;> have h := hparity.1 <;> omega
  exact ⟨hphysical, hdealt⟩

/-- In particular, merging two already balanced 64-wire packets starts with
physical cell counts `(32,32)` and ends with physical counts `(0,64)`, even
though its logical dealt packets still have counts `(32,32)`. -/
theorem oddEvenMerge128_balanced_inputs_shift_physical_profile
    (v : Fin 128 → Bool)
    (hA : Monotone (fun i : Fin 64 => v (Fin.castAdd 64 i)))
    (hB : Monotone (fun i : Fin 64 => v (Fin.natAdd 64 i)))
    (hAcount : boolTrueCount (fun i : Fin 64 => v (Fin.castAdd 64 i)) = 32)
    (hBcount : boolTrueCount (fun i : Fin 64 => v (Fin.natAdd 64 i)) = 32) :
    let w := (oddEvenMergeNet 7).exec v
    (boolTrueCount (fun i : Fin 64 => v (Fin.castAdd 64 i)) = 32 ∧
      boolTrueCount (fun i : Fin 64 => v (Fin.natAdd 64 i)) = 32) ∧
    (boolTrueCount (fun i : Fin 64 => w ⟨i.val, by omega⟩) = 0 ∧
      boolTrueCount (fun i : Fin 64 => w ⟨64 + i.val, by omega⟩) = 64) ∧
    (boolTrueCount (fun i : Fin 64 => w (evenWire 64 i)) = 32 ∧
      boolTrueCount (fun i : Fin 64 => w (oddWire 64 i)) = 32) := by
  have htotal : boolTrueCount v = 64 := by
    rw [boolTrueCount_halves (m := 64) v, hAcount, hBcount]
  have hprofile := oddEvenMerge128_balanced_deal_vs_physical_halves
    v hA hB htotal
  exact ⟨⟨hAcount, hBcount⟩, hprofile.1, hprofile.2⟩

/-- The deterministic doubled centered energy of the two physical 64-rank
halves of a sorted 128-wire Boolean profile with `H` ones. This is the
phase-specific baseline to subtract when comparing physical halves with the
logical even/odd dealt packets. -/
theorem oddEvenMerge128_physicalHalf_doubledEnergy (H : Nat) (hH : H ≤ 128) :
    let a : ℤ := (min 64 (H - 64) : Nat)
    let b : ℤ := (min 64 H : Nat)
    (2 * a - H) ^ 2 + (2 * b - H) ^ 2 =
      2 * ((min H (128 - H) : Nat) : ℤ) ^ 2 := by
  dsimp
  by_cases h : H ≤ 64
  · have hsub : H - 64 = 0 := by omega
    have hminA : min 64 (H - 64) = 0 := by omega
    have hminB : min 64 H = H := Nat.min_eq_right h
    have hminH : min H (128 - H) = H := by omega
    rw [hminA, hminB, hminH]
    ring
  · have hlow : 64 ≤ H := by omega
    have hsub_le : H - 64 ≤ 64 := by omega
    have hminA : min 64 (H - 64) = H - 64 := Nat.min_eq_right hsub_le
    have hminB : min 64 H = 64 := Nat.min_eq_left hlow
    have hminH : min H (128 - H) = 128 - H := by omega
    rw [hminA, hminB, hminH]
    rw [Int.natCast_sub hlow, Int.natCast_sub hH]
    ring

/-- The 64-wire odd-even merge has the corresponding exact physical-half
profile: its first and second 32-wire cells are the clamped rank intervals of
the fully sorted output. -/
theorem oddEvenMerge64_physicalHalf_counts (v : Fin 64 → Bool)
    (hA : Monotone (fun i : Fin 32 => v (Fin.castAdd 32 i)))
    (hB : Monotone (fun i : Fin 32 => v (Fin.natAdd 32 i))) :
    let w := (oddEvenMergeNet 6).exec v
    boolTrueCount (fun i : Fin 32 => w ⟨i.val, by omega⟩) =
        min 32 (boolTrueCount v - 32) ∧
      boolTrueCount (fun i : Fin 32 => w ⟨32 + i.val, by omega⟩) =
        min 32 (boolTrueCount v) := by
  let w := (oddEvenMergeNet 6).exec v
  have hsorted : Monotone w := by
    dsimp [w]
    exact oddEvenMergeNet_sorts_two_runs 5 v ⟨hA, hB⟩
  have hcount : boolTrueCount w = boolTrueCount v :=
    boolTrueCount_exec (oddEvenMergeNet 6) v
  have hfirstProfile := sortedBool_rankInterval_trueCount w hsorted 0 32
    (by omega) (by omega)
  have hfirst : boolTrueCount (fun i : Fin 32 => w ⟨i.val, by omega⟩) =
      min 32 (boolTrueCount v - 32) := by
    have hfirst' : boolTrueCount (fun i : Fin 32 => w ⟨i.val, by omega⟩) =
        profileInterval 64 (boolTrueCount w) 0 32 := by
      simpa [w] using hfirstProfile
    rw [profileInterval_formula 64 (boolTrueCount w) 0 32 (by omega) (by omega),
      hcount] at hfirst'
    exact hfirst'
  have hsecondProfile := sortedBool_rankInterval_trueCount w hsorted 32 64
    (by omega) (by omega)
  have hsecond : boolTrueCount (fun i : Fin 32 => w ⟨32 + i.val, by omega⟩) =
      min 32 (boolTrueCount v) := by
    have hsecond' : boolTrueCount (fun i : Fin 32 => w ⟨32 + i.val, by omega⟩) =
        profileInterval 64 (boolTrueCount w) 32 64 := by
      simpa [w] using hsecondProfile
    rw [profileInterval_formula 64 (boolTrueCount w) 32 64 (by omega) (by omega),
      hcount] at hsecond'
    exact hsecond'
  exact ⟨hfirst, hsecond⟩

/-- At total count 32, the physical halves after the 64-wire merge have
counts `(0,32)`, while the logical even/odd dealt packets still have `(16,16)`.
This is the 64-wire phase offset that a cross-stage variance invariant must
subtract. -/
theorem oddEvenMerge64_balanced_deal_vs_physical_halves (v : Fin 64 → Bool)
    (hA : Monotone (fun i : Fin 32 => v (Fin.castAdd 32 i)))
    (hB : Monotone (fun i : Fin 32 => v (Fin.natAdd 32 i)))
    (hcount : boolTrueCount v = 32) :
    let w := (oddEvenMergeNet 6).exec v
    (boolTrueCount (fun i : Fin 32 => w ⟨i.val, by omega⟩) = 0 ∧
      boolTrueCount (fun i : Fin 32 => w ⟨32 + i.val, by omega⟩) = 32) ∧
    (boolTrueCount (fun i : Fin 32 => w (evenWire 32 i)) = 16 ∧
      boolTrueCount (fun i : Fin 32 => w (oddWire 32 i)) = 16) := by
  let w := (oddEvenMergeNet 6).exec v
  have hsorted : Monotone w := by
    dsimp [w]
    exact oddEvenMergeNet_sorts_two_runs 5 v ⟨hA, hB⟩
  have hphys := oddEvenMerge64_physicalHalf_counts v hA hB
  have hparity := sorted_bool_parity_counts (m := 32) w hsorted
  rw [boolTrueCount_exec] at hparity
  have hphysical :
      boolTrueCount (fun i : Fin 32 => w ⟨i.val, by omega⟩) = 0 ∧
      boolTrueCount (fun i : Fin 32 => w ⟨32 + i.val, by omega⟩) = 32 := by
    simpa [w, hcount] using hphys
  have hdealt :
      boolTrueCount (fun i : Fin 32 => w (evenWire 32 i)) = 16 ∧
      boolTrueCount (fun i : Fin 32 => w (oddWire 32 i)) = 16 := by
    constructor <;> have h := hparity.1 <;> omega
  exact ⟨hphysical, hdealt⟩

/-- The logical parity packets after the 64-wire merge have only the parity
residual energy: zero for even total count and two for odd total count. -/
theorem oddEvenMerge64_dealt_doubledEnergy (v : Fin 64 → Bool)
    (hA : Monotone (fun i : Fin 32 => v (Fin.castAdd 32 i)))
    (hB : Monotone (fun i : Fin 32 => v (Fin.natAdd 32 i))) :
    let w := (oddEvenMergeNet 6).exec v
    let H := boolTrueCount v
    (2 * (boolTrueCount (fun i : Fin 32 => w (evenWire 32 i)) : ℤ) - H) ^ 2 +
      (2 * (boolTrueCount (fun i : Fin 32 => w (oddWire 32 i)) : ℤ) - H) ^ 2 =
        if H % 2 = 0 then 0 else 2 := by
  let w := (oddEvenMergeNet 6).exec v
  let H := boolTrueCount v
  have hsorted : Monotone w := by
    dsimp [w]
    exact oddEvenMergeNet_sorts_two_runs 5 v ⟨hA, hB⟩
  have hparity := sorted_bool_parity_counts (m := 32) w hsorted
  rw [boolTrueCount_exec] at hparity
  dsimp [H]
  by_cases heven : boolTrueCount v % 2 = 0
  · let q := boolTrueCount v / 2
    have hquot : boolTrueCount v = 2 * q := by dsimp [q]; omega
    have hq : boolTrueCount v / 2 = q := rfl
    have hceil : (boolTrueCount v + 1) / 2 = q := by dsimp [q]; omega
    rw [hparity.1, hparity.2, hq, hceil, hquot]
    have hmod : (2 * q) % 2 = 0 := by omega
    rw [if_pos hmod]
    push_cast
    ring
  · have hquot : boolTrueCount v = 2 * (boolTrueCount v / 2) + 1 := by omega
    let q := boolTrueCount v / 2
    have hq : boolTrueCount v / 2 = q := rfl
    have hceil : (boolTrueCount v + 1) / 2 = q + 1 := by dsimp [q]; omega
    have hquot' : boolTrueCount v = 2 * q + 1 := by simpa [q] using hquot
    rw [hparity.1, hparity.2, hq, hceil, hquot']
    have hmod : ¬(2 * q + 1) % 2 = 0 := by omega
    rw [if_neg hmod]
    push_cast
    ring

/-- The parity residual energy of a dealt pair is paid for by the input
imbalance of two runs. Combined with `oddEvenMerge64_dealt_doubledEnergy`,
this is the scalar one-merge nonincrease inequality. -/
theorem parityEnergy_le_twoRunInputEnergy (A B : Nat) :
    (if (A + B) % 2 = 0 then 0 else 2 : ℤ) ≤
      (2 * (A : ℤ) - ((A + B : Nat) : ℤ)) ^ 2 +
        (2 * (B : ℤ) - ((A + B : Nat) : ℤ)) ^ 2 := by
  have hformula :
      (2 * (A : ℤ) - ((A + B : Nat) : ℤ)) ^ 2 +
        (2 * (B : ℤ) - ((A + B : Nat) : ℤ)) ^ 2 =
          2 * ((A : ℤ) - (B : ℤ)) ^ 2 := by
    push_cast
    ring
  push_cast at hformula
  by_cases heven : (A + B) % 2 = 0
  · simp [heven]
    push_cast
    rw [hformula]
    positivity
  · have hne : A ≠ B := by
      intro hAB
      subst B
      omega
    rw [if_neg heven]
    push_cast
    rw [hformula]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hgap : (1 : ℤ) ≤ (B : ℤ) - (A : ℤ) := by
        have hn : A + 1 ≤ B := Nat.succ_le_of_lt hlt
        omega
      nlinarith
    · have hgap : (1 : ℤ) ≤ (A : ℤ) - (B : ℤ) := by
        have hn : B + 1 ≤ A := Nat.succ_le_of_lt hgt
        omega
      nlinarith

/-- The 64-wire odd-even merge contracts the doubled centered threshold-count
energy of two sorted input runs when measured on its dealt output lanes. -/
theorem oddEvenMerge64_dealt_energy_le_input (v : Fin 64 → Bool)
    (hA : Monotone (fun i : Fin 32 => v (Fin.castAdd 32 i)))
    (hB : Monotone (fun i : Fin 32 => v (Fin.natAdd 32 i))) :
    let A := boolTrueCount (fun i : Fin 32 => v (Fin.castAdd 32 i))
    let B := boolTrueCount (fun i : Fin 32 => v (Fin.natAdd 32 i))
    let w := (oddEvenMergeNet 6).exec v
    (2 * (boolTrueCount (fun i : Fin 32 => w (evenWire 32 i)) : ℤ) -
        boolTrueCount v) ^ 2 +
      (2 * (boolTrueCount (fun i : Fin 32 => w (oddWire 32 i)) : ℤ) -
        boolTrueCount v) ^ 2 ≤
      (2 * (A : ℤ) - boolTrueCount v) ^ 2 +
        (2 * (B : ℤ) - boolTrueCount v) ^ 2 := by
  let A := boolTrueCount (fun i : Fin 32 => v (Fin.castAdd 32 i))
  let B := boolTrueCount (fun i : Fin 32 => v (Fin.natAdd 32 i))
  let w := (oddEvenMergeNet 6).exec v
  have htotal : boolTrueCount v = A + B := by
    dsimp [A, B]
    exact boolTrueCount_halves (m := 32) v
  calc
    (2 * (boolTrueCount (fun i : Fin 32 => w (evenWire 32 i)) : ℤ) -
        boolTrueCount v) ^ 2 +
      (2 * (boolTrueCount (fun i : Fin 32 => w (oddWire 32 i)) : ℤ) -
        boolTrueCount v) ^ 2 =
          (if boolTrueCount v % 2 = 0 then 0 else 2 : ℤ) := by
            exact oddEvenMerge64_dealt_doubledEnergy v hA hB
    _ ≤ (2 * (A : ℤ) - boolTrueCount v) ^ 2 +
        (2 * (B : ℤ) - boolTrueCount v) ^ 2 := by
          have hbound := parityEnergy_le_twoRunInputEnergy A B
          simpa [htotal] using hbound

/-- Doubled centered count energy of the two logical parity lanes after the
64-wire merge. -/
def oddEvenMerge64DealtEnergy (v : Fin 64 → Bool) : ℤ :=
  let w := (oddEvenMergeNet 6).exec v
  (2 * (boolTrueCount (fun i : Fin 32 => w (evenWire 32 i)) : ℤ) -
      boolTrueCount v) ^ 2 +
    (2 * (boolTrueCount (fun i : Fin 32 => w (oddWire 32 i)) : ℤ) -
      boolTrueCount v) ^ 2

/-- Doubled centered count energy between the physical lower and upper
32-wire input runs. -/
def oddEvenMerge64InputEnergy (v : Fin 64 → Bool) : ℤ :=
  let A := boolTrueCount (fun i : Fin 32 => v (Fin.castAdd 32 i))
  let B := boolTrueCount (fun i : Fin 32 => v (Fin.natAdd 32 i))
  (2 * (A : ℤ) - boolTrueCount v) ^ 2 +
    (2 * (B : ℤ) - boolTrueCount v) ^ 2

/-- Doubled centered count energy of the actual even/odd rank lanes of an
already sorted 64-wire packet. -/
def oddEvenMerge64ParityEnergy (v : Fin 64 → Bool) : ℤ :=
  (2 * (boolTrueCount (fun i : Fin 32 => v (evenWire 32 i)) : ℤ) -
      boolTrueCount v) ^ 2 +
    (2 * (boolTrueCount (fun i : Fin 32 => v (oddWire 32 i)) : ℤ) -
      boolTrueCount v) ^ 2

/-- On an already sorted 64-wire packet, the odd-even merge is the identity.
Thus its dealt-lane contraction is a pure rank reindexing into the actual
even and odd 32-wire supports, with no additional comparator depth. -/
theorem oddEvenMerge64_monotone_parity_energy_le_input (v : Fin 64 → Bool)
    (hv : Monotone v) :
    oddEvenMerge64ParityEnergy v ≤ oddEvenMerge64InputEnergy v := by
  have hA : Monotone (fun i : Fin 32 => v (Fin.castAdd 32 i)) := by
    intro i j hij
    apply hv
    apply Fin.mk_le_mk.mpr
    exact Fin.mk_le_mk.mp hij
  have hB : Monotone (fun i : Fin 32 => v (Fin.natAdd 32 i)) := by
    intro i j hij
    apply hv
    apply Fin.mk_le_mk.mpr
    have hval := Fin.mk_le_mk.mp hij
    change 32 + i.val ≤ 32 + j.val
    omega
  have hcontract := oddEvenMerge64_dealt_energy_le_input v hA hB
  have hidentity : (oddEvenMergeNet 6).exec v = v := by
    exact (oddEvenMergeNet 6).exec_eq_of_monotone hv
  simpa only [oddEvenMerge64DealtEnergy, oddEvenMerge64ParityEnergy,
    oddEvenMerge64InputEnergy, hidentity] using hcontract

/-- The sorted packet's two parity lanes have exactly the unavoidable
zero-or-two residual, according to the parity of its total threshold count. -/
theorem oddEvenMerge64_monotone_parity_energy_eq_residual (v : Fin 64 → Bool)
    (hv : Monotone v) :
    oddEvenMerge64ParityEnergy v =
      if boolTrueCount v % 2 = 0 then 0 else 2 := by
  have hA : Monotone (fun i : Fin 32 => v (Fin.castAdd 32 i)) := by
    intro i j hij
    apply hv
    apply Fin.mk_le_mk.mpr
    exact Fin.mk_le_mk.mp hij
  have hB : Monotone (fun i : Fin 32 => v (Fin.natAdd 32 i)) := by
    intro i j hij
    apply hv
    apply Fin.mk_le_mk.mpr
    have hval := Fin.mk_le_mk.mp hij
    change 32 + i.val ≤ 32 + j.val
    omega
  have hidentity : (oddEvenMergeNet 6).exec v = v := by
    exact (oddEvenMergeNet 6).exec_eq_of_monotone hv
  have hexact := oddEvenMerge64_dealt_doubledEnergy v hA hB
  simpa only [oddEvenMerge64DealtEnergy, oddEvenMerge64ParityEnergy,
    hidentity] using hexact

/-- For a sorted 64-wire Boolean profile, its physical-half input energy is
determined exactly by its total count: `2 * min(H, 64-H)^2`. -/
theorem oddEvenMerge64_monotone_input_energy_eq_phase (v : Fin 64 → Bool)
    (hv : Monotone v) :
    oddEvenMerge64InputEnergy v =
      2 * ((min (boolTrueCount v) (64 - boolTrueCount v) : Nat) : ℤ) ^ 2 := by
  have hA : Monotone (fun i : Fin 32 => v (Fin.castAdd 32 i)) := by
    intro i j hij
    apply hv
    apply Fin.mk_le_mk.mpr
    exact Fin.mk_le_mk.mp hij
  have hB : Monotone (fun i : Fin 32 => v (Fin.natAdd 32 i)) := by
    intro i j hij
    apply hv
    apply Fin.mk_le_mk.mpr
    have hval := Fin.mk_le_mk.mp hij
    change 32 + i.val ≤ 32 + j.val
    omega
  have hidentity : (oddEvenMergeNet 6).exec v = v := by
    exact (oddEvenMergeNet 6).exec_eq_of_monotone hv
  have hprofile := oddEvenMerge64_physicalHalf_counts v hA hB
  simp only [hidentity] at hprofile
  have hH : boolTrueCount v ≤ 64 := by
    simpa [boolTrueCount] using
      (Fintype.card_subtype_le (fun i : Fin 64 => v i = true))
  have hAcount : boolTrueCount
      (fun i : Fin 32 => v (Fin.castAdd 32 i)) =
        min 32 (boolTrueCount v - 32) := by
    simpa [Fin.castAdd] using hprofile.1
  have hBcount : boolTrueCount
      (fun i : Fin 32 => v (Fin.natAdd 32 i)) =
        min 32 (boolTrueCount v) := by
    simpa [Fin.natAdd] using hprofile.2
  dsimp [oddEvenMerge64InputEnergy]
  rw [hAcount, hBcount]
  by_cases h : boolTrueCount v ≤ 32
  · have hAmin : min 32 (boolTrueCount v - 32) = 0 := by omega
    have hBmin : min 32 (boolTrueCount v) = boolTrueCount v := Nat.min_eq_right h
    have hHmin : min (boolTrueCount v) (64 - boolTrueCount v) =
        boolTrueCount v := by omega
    rw [hAmin, hBmin, hHmin]
    push_cast
    ring
  · have hlow : 32 ≤ boolTrueCount v := by omega
    have hsub : boolTrueCount v - 32 ≤ 32 := by omega
    have hAmin : min 32 (boolTrueCount v - 32) = boolTrueCount v - 32 :=
      Nat.min_eq_right hsub
    have hBmin : min 32 (boolTrueCount v) = 32 := Nat.min_eq_left hlow
    have hHmin : min (boolTrueCount v) (64 - boolTrueCount v) =
        64 - boolTrueCount v := by omega
    rw [hAmin, hBmin, hHmin]
    rw [Int.natCast_sub hlow, Int.natCast_sub hH]
    ring

/-- Exact local dissipation on a sorted 64-wire threshold profile. It is the
physical-half phase energy minus the parity residual of the two rank lanes. -/
theorem oddEvenMerge64_monotone_energy_drop_eq_phase (v : Fin 64 → Bool)
    (hv : Monotone v) :
    oddEvenMerge64InputEnergy v - oddEvenMerge64ParityEnergy v =
      2 * ((min (boolTrueCount v) (64 - boolTrueCount v) : Nat) : ℤ) ^ 2 -
        (if boolTrueCount v % 2 = 0 then 0 else 2 : ℤ) := by
  rw [oddEvenMerge64_monotone_input_energy_eq_phase v hv,
    oddEvenMerge64_monotone_parity_energy_eq_residual v hv]

/-- The ideal count in a sorted parity lane when a 64-profile has `X` ones. -/
def oddEvenMerge64_parityCount (lane : Bool) (X : Nat) : Nat :=
  if lane then (X + 1) / 2 else X / 2

/-- Fractional ideal count for one parity lane, obtained by interpolating its
two neighboring integer profiles. -/
def oddEvenMerge64_parityMean (lane : Bool) (q : Nat) (frac : Real) : Real :=
  (1 - frac) * oddEvenMerge64_parityCount lane q +
    frac * oddEvenMerge64_parityCount lane (q + 1)

/-- Integer floor code for the induced target in a parity lane. The full
32-one endpoint is represented as `31 + 1`, so it remains admissible for the
rank-suffix interpolation theorem. -/
def oddEvenMerge64_parityCodeFloor (lane : Bool) (q : Nat) : Nat :=
  min 31 (oddEvenMerge64_parityCount lane q)

/-- Fractional part of the induced lane target, with the saturated endpoint
encoded as `31 + 1`. -/
def oddEvenMerge64_parityCodeFrac (lane : Bool) (q : Nat) (frac : Real) : Real :=
  if oddEvenMerge64_parityCount lane q = 32 then 1
  else if oddEvenMerge64_parityCount lane (q + 1) =
      oddEvenMerge64_parityCount lane q + 1 then frac else 0

/-- The parity-lane target always has an admissible integer-plus-fraction
encoding on the 32 ranks, including the parent target interval `[63,64]`. -/
theorem oddEvenMerge64_parityMean_eq_code (lane : Bool) (q : Nat)
    (frac : Real) (hq : q < 64) :
    oddEvenMerge64_parityMean lane q frac =
        (oddEvenMerge64_parityCodeFloor lane q : Real) +
          oddEvenMerge64_parityCodeFrac lane q frac := by
  have hcount : oddEvenMerge64_parityCount lane q ≤ 32 := by
    cases lane <;> simp [oddEvenMerge64_parityCount] <;> omega
  have hstepLo : oddEvenMerge64_parityCount lane q ≤
      oddEvenMerge64_parityCount lane (q + 1) := by
    cases lane
    · exact Nat.div_le_div_right (Nat.le_succ q)
    · exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.le_succ q) 1)
  have hstepHi : oddEvenMerge64_parityCount lane (q + 1) ≤
      oddEvenMerge64_parityCount lane q + 1 := by
    cases lane <;> simp [oddEvenMerge64_parityCount] <;> omega
  by_cases hfull : oddEvenMerge64_parityCount lane q = 32
  · have hnext : oddEvenMerge64_parityCount lane (q + 1) = 32 := by
      cases lane <;> simp [oddEvenMerge64_parityCount] at hfull ⊢ <;> omega
    simp [oddEvenMerge64_parityMean, oddEvenMerge64_parityCodeFloor,
      oddEvenMerge64_parityCodeFrac, hfull, hnext]
    ring
  · have hbelow : oddEvenMerge64_parityCount lane q ≤ 31 := by omega
    have hfloor : oddEvenMerge64_parityCodeFloor lane q =
        oddEvenMerge64_parityCount lane q := by
      simp [oddEvenMerge64_parityCodeFloor, Nat.min_eq_right hbelow]
    by_cases hrise : oddEvenMerge64_parityCount lane (q + 1) =
        oddEvenMerge64_parityCount lane q + 1
    · simp [oddEvenMerge64_parityMean, oddEvenMerge64_parityCodeFloor,
        oddEvenMerge64_parityCodeFrac, hfull, hrise, Nat.min_eq_right hbelow]
      push_cast
      ring
    · have hflat : oddEvenMerge64_parityCount lane (q + 1) =
          oddEvenMerge64_parityCount lane q := by omega
      simp [oddEvenMerge64_parityMean, oddEvenMerge64_parityCodeFloor,
        oddEvenMerge64_parityCodeFrac, hfull, hrise, hflat,
        Nat.min_eq_right hbelow]
      push_cast
      ring

/-- The chosen lane floor is below the lane width and its fraction lies in
the unit interval whenever the parent fraction does. -/
theorem oddEvenMerge64_parityCode_valid (lane : Bool) (q : Nat)
    (frac : Real) (hq : q < 64) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    oddEvenMerge64_parityCodeFloor lane q < 32 ∧
      0 ≤ oddEvenMerge64_parityCodeFrac lane q frac ∧
      oddEvenMerge64_parityCodeFrac lane q frac ≤ 1 := by
  have hcount : oddEvenMerge64_parityCount lane q ≤ 32 := by
    cases lane <;> simp [oddEvenMerge64_parityCount] <;> omega
  constructor
  · simp [oddEvenMerge64_parityCodeFloor]
  · constructor
    · unfold oddEvenMerge64_parityCodeFrac
      split_ifs <;> linarith
    · unfold oddEvenMerge64_parityCodeFrac
      split_ifs <;> linarith

/-- Parity-lane targets preserve the order of fractional parent targets. This
lets a packetwise monotone target sequence pass through the even/odd rebin. -/
theorem oddEvenMerge64_parityMean_mono (lane : Bool)
    (q₁ q₂ : Nat) (frac₁ frac₂ : Real)
    (hfrac₁0 : 0 ≤ frac₁) (hfrac₁1 : frac₁ ≤ 1)
    (hfrac₂0 : 0 ≤ frac₂) (hfrac₂1 : frac₂ ≤ 1)
    (hmean : (q₁ : Real) + frac₁ ≤ (q₂ : Real) + frac₂) :
    oddEvenMerge64_parityMean lane q₁ frac₁ ≤
      oddEvenMerge64_parityMean lane q₂ frac₂ := by
  unfold oddEvenMerge64_parityMean
  apply natProfileInterp_mono_mean (oddEvenMerge64_parityCount lane)
  · intro a b hab
    cases lane
    · exact Nat.div_le_div_right hab
    · exact Nat.div_le_div_right (Nat.add_le_add_right hab 1)
  · exact hfrac₁0
  · exact hfrac₁1
  · exact hfrac₂0
  · exact hfrac₂1
  · exact hmean

/-- Splitting a sorted 64-wire threshold profile into its even/odd rank lanes
preserves aggregate absolute error exactly for every fractional target. -/
theorem oddEvenMerge64_parity_rebin_L1_exact (v : Fin 64 → Bool)
    (hv : Monotone v) (q : Nat) (frac : Real) (hq : q < 64)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ lane : Bool,
      |(boolTrueCount (fun i : Fin 32 =>
          if lane then v (oddWire 32 i) else v (evenWire 32 i)) : Real) -
        oddEvenMerge64_parityMean lane q frac|) =
      |(boolTrueCount v : Real) - (q + frac)| := by
  let F : Bool → Nat → Nat := oddEvenMerge64_parityCount
  let lanes : Bool → Fin 32 → Bool := fun lane i =>
    if lane then v (oddWire 32 i) else v (evenWire 32 i)
  have hparity := sorted_bool_parity_counts (m := 32) v hv
  have hprofile (lane : Bool) : boolTrueCount (lanes lane) = F lane (boolTrueCount v) := by
    cases lane <;> simp [lanes, F, oddEvenMerge64_parityCount, hparity]
  have htotal (z : Nat) (hz : z ≤ 64) :
      (∑ lane : Bool, (F lane z : Real)) = z := by
    rw [Fintype.sum_bool]
    simp [F, oddEvenMerge64_parityCount]
    have hdiv : z / 2 + (z + 1) / 2 = z := by
      by_cases heven : z % 2 = 0
      · have hdecomp := Nat.mod_add_div z 2
        rw [heven] at hdecomp
        have hceil : (z + 1) / 2 = z / 2 := by omega
        omega
      · have hmod : z % 2 = 1 := by omega
        have hdecomp := Nat.mod_add_div z 2
        rw [hmod] at hdecomp
        have hceil : (z + 1) / 2 = z / 2 + 1 := by omega
        omega
    have hdiv' : (z + 1) / 2 + z / 2 = z := by omega
    exact_mod_cast hdiv'
  have hmono : ∀ lane a b, a ≤ b → F lane a ≤ F lane b := by
    intro lane a b hab
    cases lane
    · exact Nat.div_le_div_right hab
    · exact Nat.div_le_div_right (Nat.add_le_add_right hab 1)
  calc
    (∑ lane : Bool,
        |(boolTrueCount (lanes lane) : Real) - oddEvenMerge64_parityMean lane q frac|) =
      ∑ lane : Bool,
        |(F lane (boolTrueCount v) : Real) -
          ((1 - frac) * F lane q + frac * F lane (q + 1))| := by
      apply Finset.sum_congr rfl
      intro lane _
      rw [hprofile lane]
      rfl
    _ = |(boolTrueCount v : Real) - (q + frac)| := by
      simpa [F, oddEvenMerge64_parityMean] using
        monotoneCountDecomposition_L1_exact F 64 (boolTrueCount v) q frac
          (by simpa [boolTrueCount] using
            (Fintype.card_subtype_le (fun i : Fin 64 => v i = true)))
          hq hfrac0 hfrac1 htotal hmono

/-- A monotone Boolean profile is exactly the terminal suffix whose length
is its true count. -/
theorem monotoneBool_eq_countSuffix {m : Nat} (v : Fin m → Bool)
    (hv : Monotone v) (k : Fin m) :
    v k = decide (m - boolTrueCount v ≤ k.val) := by
  by_cases hk : v k = true
  · let r := m - k.val
    have hr : r ≤ m := by dsimp [r]; omega
    have htail (j : Fin r) :
        v (Fin.cast (Nat.sub_add_cancel hr) (Fin.natAdd (m - r) j)) = true := by
      have hle : k ≤ Fin.cast (Nat.sub_add_cancel hr) (Fin.natAdd (m - r) j) :=
        Fin.le_def.mpr (by simp only [Fin.val_cast, Fin.val_natAdd]; dsimp [r]; omega)
      have hmono := hv hle
      rw [hk] at hmono
      exact Bool.le_antisymm (Bool.le_true _) hmono
    have hcount := sortedBool_suffix_trueCount v hv hr
    have hfull : boolTrueCount (fun j : Fin r =>
        v (Fin.cast (Nat.sub_add_cancel hr) (Fin.natAdd (m - r) j))) = r := by
      simp [htail, boolTrueCount]
    rw [hfull] at hcount
    have hloc : r ≤ boolTrueCount v := by omega
    have hloc' : m - boolTrueCount v ≤ k.val := by dsimp [r] at hloc; omega
    simp [hk, hloc']
  · have hkfalse : v k = false := Bool.eq_false_of_not_eq_true hk
    let r := k.val + 1
    have hr : r ≤ m := by dsimp [r]; omega
    have hprefix (i : Fin r) :
        v (Fin.cast (Nat.add_sub_of_le hr) (Fin.castAdd (m - r) i)) = false := by
      have hik : i.val ≤ k.val := by dsimp [r] at i; omega
      have hle : Fin.cast (Nat.add_sub_of_le hr) (Fin.castAdd (m - r) i) ≤ k :=
        Fin.le_def.mpr (by simp only [Fin.val_cast, Fin.val_castAdd]; exact hik)
      have hval := hv hle
      rw [hkfalse] at hval
      exact Bool.le_antisymm hval (Bool.false_le _)
    have hcount := sortedBool_prefix_trueCount v hv hr
    have hzero : boolTrueCount (fun i : Fin r =>
        v (Fin.cast (Nat.add_sub_of_le hr) (Fin.castAdd (m - r) i))) = 0 := by
      simp [hprefix, boolTrueCount]
    rw [hzero] at hcount
    have hloc : boolTrueCount v ≤ m - (k.val + 1) := by omega
    have hloc' : ¬ m - boolTrueCount v ≤ k.val := by omega
    simp [hkfalse, hloc']

/-- The canonical terminal suffix of length `z` has exactly `z` true bits. -/
theorem boolTrueCount_countSuffix (m z : Nat) (hz : z ≤ m) :
    boolTrueCount (fun k : Fin m => decide (m - z ≤ k.val)) = z := by
  let e : {k : Fin m // decide (m - z ≤ k.val) = true} ≃ Fin z :=
    { toFun := fun k => ⟨k.val.val - (m - z), by
        have hk := k.property
        simp only [decide_eq_true_eq] at hk
        omega⟩
      invFun := fun j => ⟨⟨m - z + j.val, by omega⟩, by
        simp only [decide_eq_true_eq]
        omega⟩
      left_inv := by
        intro k
        apply Subtype.ext
        apply Fin.ext
        simp only [Fin.val_mk]
        have hk := k.property
        simp only [decide_eq_true_eq] at hk
        omega
      right_inv := by
        intro j
        apply Fin.ext
        simp }
  unfold boolTrueCount
  rw [Fintype.card_congr e]
  exact Fintype.card_fin z

/-- Number of true lane ranks owned by one destination. -/
def assignedBitCount {D : Type} [DecidableEq D] {m : Nat}
    (owner : Fin m → D) (bits : Fin m → Bool) (destination : D) : Nat :=
  ∑ k : Fin m, if destination = owner k ∧ bits k = true then 1 else 0

/-- For a monotone Boolean lane, ownership by arbitrary destinations has the
exact L1 profile error predicted by its rank-suffix interpolation. -/
theorem monotoneBits_assignedRankProfiles_L1_exact
    {D : Type} [Fintype D] [DecidableEq D] {m : Nat}
    (owner : Fin m → D) (bits : Fin m → Bool) (hbits : Monotone bits)
    (X q : Nat) (frac : Real) (hX : boolTrueCount bits = X)
    (hq : q < m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ destination : D,
      |(assignedBitCount owner bits destination : Real) -
        ((1 - frac) * assignedRankCount owner
            (fun z k => decide (m - z ≤ k.val)) destination q +
          frac * assignedRankCount owner
            (fun z k => decide (m - z ≤ k.val)) destination (q + 1))|) =
      |(X : Real) - (q + frac)| := by
  let suffix : Nat → Fin m → Bool := fun z k => decide (m - z ≤ k.val)
  have hXbound : X ≤ m := by
    rw [← hX]
    simpa [boolTrueCount] using
      (Fintype.card_subtype_le (fun k : Fin m => bits k = true))
  have hactual (destination : D) :
      assignedBitCount owner bits destination =
        assignedRankCount owner suffix destination X := by
    unfold assignedBitCount assignedRankCount
    apply Finset.sum_congr rfl
    intro k hk
    rw [monotoneBool_eq_countSuffix bits hbits k, hX]
  have hcard : ∀ z ≤ m,
      (∑ k : Fin m, if suffix z k = true then 1 else 0) = z := by
    intro z hz
    calc
      (∑ k : Fin m, if suffix z k = true then 1 else 0) =
          Fintype.card {k : Fin m // suffix z k = true} :=
        finSum_ite_one_eq_card_subtype (fun k : Fin m => suffix z k = true)
      _ = boolTrueCount (fun k : Fin m => suffix z k) := rfl
      _ = z := by simpa [suffix] using boolTrueCount_countSuffix m z hz
  have hmono : ∀ a b, a ≤ b → ∀ k, suffix a k = true → suffix b k = true := by
    intro a b hab k ha
    simp only [suffix, decide_eq_true_eq] at ha ⊢
    omega
  have hassigned := assignedRankProfiles_L1_exact owner suffix X q frac
    hXbound hq hfrac0 hfrac1 hcard hmono
  simpa only [hactual] using hassigned

/-- Destination-wise L2 aggregation for a cohort of sorted Boolean rank
profiles with heterogeneous fractional targets. It uses the actual bits at
each rank and charges only the number of source blocks. -/
theorem monotoneBits_assignedRankProfiles_aggregate_L2_var
    {D : Type} [Fintype D] [DecidableEq D] {c m : Nat}
    (owner : Fin c → Fin m → D) (bits : Fin c → Fin m → Bool)
    (hbits : ∀ g, Monotone (bits g))
    (targetQ : Fin c → Nat) (frac : Fin c → Real)
    (hq : ∀ g, targetQ g < m)
    (hfrac0 : ∀ g, 0 ≤ frac g) (hfrac1 : ∀ g, frac g ≤ 1) :
    (∑ destination : D,
      (Finset.univ.sum (fun g : Fin c =>
        (assignedBitCount (owner g) (bits g) destination : Real) -
          ((1 - frac g) * assignedRankCount (owner g)
            (fun z k => decide (m - z ≤ k.val)) destination (targetQ g) +
            frac g * assignedRankCount (owner g)
              (fun z k => decide (m - z ≤ k.val)) destination (targetQ g + 1)))) ^ 2) ≤
      (c : Real) * Finset.univ.sum (fun g : Fin c =>
        ((boolTrueCount (bits g) : Real) - (targetQ g + frac g)) ^ 2) := by
  classical
  let suffix : Nat → Fin m → Bool := fun z k => decide (m - z ≤ k.val)
  let X : Fin c → Nat := fun g => boolTrueCount (bits g)
  have hX : ∀ g, X g ≤ m := by
    intro g
    simpa [X, boolTrueCount] using
      (Fintype.card_subtype_le (fun k : Fin m => bits g k = true))
  have hsuffix : ∀ z ≤ m,
      (∑ k : Fin m, if suffix z k = true then 1 else 0) = z := by
    intro z hz
    calc
      (∑ k : Fin m, if suffix z k = true then 1 else 0) =
          boolTrueCount (fun k : Fin m => decide (m - z ≤ k.val)) := by
        exact finSum_ite_one_eq_card_subtype _
      _ = z := boolTrueCount_countSuffix m z hz
  have hmonoSuffix : ∀ a b, a ≤ b → ∀ k,
      suffix a k = true → suffix b k = true := by
    intro a b hab k ha
    simp only [suffix, decide_eq_true_eq] at ha ⊢
    omega
  have hactual (g : Fin c) (destination : D) :
      assignedBitCount (owner g) (bits g) destination =
        assignedRankCount (owner g) suffix destination (X g) := by
    unfold assignedBitCount assignedRankCount
    apply Finset.sum_congr rfl
    intro k hk
    rw [monotoneBool_eq_countSuffix (bits g) (hbits g) k]
  have hagg := assignedRankProfiles_aggregate_L2_var
    (owner := owner) (suffix := suffix) (X := X) (q := targetQ) (frac := frac)
    hX hq hfrac0 hfrac1 hsuffix hmonoSuffix
  simpa only [hactual, suffix, X] using hagg

/-- Endpoint-safe version of the monotone Boolean rank-profile bound. A full
target `m` is represented as `(m - 1) + 1`, so it uses the already-proved
interior interpolation theorem without asking for a nonexistent rank `m+1`.
-/
theorem monotoneBits_assignedRankProfiles_aggregate_L2_var_allow_endpoint
    {D : Type} [Fintype D] [DecidableEq D] {c m : Nat} (hm : 0 < m)
    (owner : Fin c → Fin m → D) (bits : Fin c → Fin m → Bool)
    (hbits : ∀ g, Monotone (bits g))
    (targetQ : Fin c → Nat) (frac : Fin c → Real)
    (hq : ∀ g, targetQ g ≤ m)
    (hendpoint : ∀ g, targetQ g = m → frac g = 0)
    (hfrac0 : ∀ g, 0 ≤ frac g) (hfrac1 : ∀ g, frac g ≤ 1) :
    (∑ destination : D,
      (Finset.univ.sum (fun g : Fin c =>
        (assignedBitCount (owner g) (bits g) destination : Real) -
          ((1 - frac g) * assignedRankCount (owner g)
            (fun z k => decide (m - z ≤ k.val)) destination (targetQ g) +
            frac g * assignedRankCount (owner g)
              (fun z k => decide (m - z ≤ k.val)) destination (targetQ g + 1)))) ^ 2) ≤
      (c : Real) * Finset.univ.sum (fun g : Fin c =>
        ((boolTrueCount (bits g) : Real) - (targetQ g + frac g)) ^ 2) := by
  let q' : Fin c → Nat := fun g => if targetQ g < m then targetQ g else m - 1
  let frac' : Fin c → Real := fun g => if targetQ g < m then frac g else 1
  have hq' : ∀ g, q' g < m := by
    intro g
    by_cases h : targetQ g < m
    · simp [q', h]
    · have hbound := hq g
      have heq : targetQ g = m := by omega
      have hsub : m - 1 < m := by omega
      simpa [q', h] using hsub
  have hf0 : ∀ g, 0 ≤ frac' g := by
    intro g
    by_cases h : targetQ g < m <;> simp [frac', h]
    exact hfrac0 g
  have hf1 : ∀ g, frac' g ≤ 1 := by
    intro g
    by_cases h : targetQ g < m <;> simp [frac', h]
    exact hfrac1 g
  have htarget : ∀ g, q' g + frac' g = targetQ g + frac g := by
    intro g
    by_cases h : targetQ g < m
    · simp [q', frac', h]
    · have hbound := hq g
      have heq : targetQ g = m := by omega
      have hfrac := hendpoint g heq
      have hnat : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
      simp [q', frac', h, heq, hfrac, hnat]
      exact_mod_cast hnat
  have hprofile (g : Fin c) (destination : D) :
      (1 - frac' g) * assignedRankCount (owner g)
          (fun z k => decide (m - z ≤ k.val)) destination (q' g) +
        frac' g * assignedRankCount (owner g)
          (fun z k => decide (m - z ≤ k.val)) destination (q' g + 1) =
      (1 - frac g) * assignedRankCount (owner g)
          (fun z k => decide (m - z ≤ k.val)) destination (targetQ g) +
        frac g * assignedRankCount (owner g)
          (fun z k => decide (m - z ≤ k.val)) destination (targetQ g + 1) := by
    by_cases h : targetQ g < m
    · simp [q', frac', h]
    · have hbound := hq g
      have heq : targetQ g = m := by omega
      have hfrac := hendpoint g heq
      have hnat : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
      simp [q', frac', h, heq, hfrac, hnat]
  have hcore := monotoneBits_assignedRankProfiles_aggregate_L2_var
    owner bits hbits q' frac' hq' hf0 hf1
  simpa only [hprofile, htarget] using hcore

/-- Boolean threshold values on the full logical ranks of each 4096-wire
merge output. -/
def packetFamily64BlockList_mergeThresholdBits {q N : Nat} {α : Type}
    [LinearOrder α]
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (v : Fin N → α) (t : α) : Fin q → Fin 4096 → Bool :=
  fun g k => decide (t ≤
    (genScatterMergeTreeBatch (packetPowerTree6 (α := α))
      (packetFamily64BlockList packets hdis)).exec v
        (packetFamily64BlockEmbedding packets hdis g k))

/-- The 57-layer full-block merge admits the arbitrary physical rank-owner L2
estimate directly on its 4096 logical output ranks. Sortedness is discharged
from the checked merge-tree block-order theorem, so this adapter does not
rebin through 64 output packets. -/
theorem packetFamily64BlockList_merge_wholeBlock_owner_L2_le
    {q N : Nat} {α D : Type} [LinearOrder α]
    [Fintype D] [DecidableEq D]
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (v : Fin N → α)
    (hpackets : ∀ a, Monotone (fun i => v (packets a i)))
    (t : α)
    (owner : Fin q → Fin 4096 → D)
    (targetQ : Fin q → Nat) (frac : Fin q → Real)
    (hq : ∀ g, targetQ g ≤ 4096)
    (hendpoint : ∀ g, targetQ g = 4096 → frac g = 0)
    (hfrac0 : ∀ g, 0 ≤ frac g) (hfrac1 : ∀ g, frac g ≤ 1) :
    (∑ destination : D,
      Finset.univ.sum (fun g : Fin q =>
        (assignedBitCount (owner g)
          (packetFamily64BlockList_mergeThresholdBits packets hdis v t g)
          destination : Real) -
          ((1 - frac g) * assignedRankCount (owner g)
            (fun z k => decide (4096 - z ≤ k.val)) destination (targetQ g) +
            frac g * assignedRankCount (owner g)
              (fun z k => decide (4096 - z ≤ k.val)) destination (targetQ g + 1))) ^ 2) ≤
      (q : Real) * Finset.univ.sum (fun g : Fin q =>
        ((boolTrueCount
          (packetFamily64BlockList_mergeThresholdBits packets hdis v t g) : Real) -
          (targetQ g + frac g)) ^ 2) := by
  let bits := packetFamily64BlockList_mergeThresholdBits packets hdis v t
  have hbits : ∀ g, Monotone (bits g) := by
    intro g
    let e := packetFamily64BlockEmbedding packets hdis g
    have he : e ∈ packetFamily64BlockList packets hdis := by
      simp [e, packetFamily64BlockList]
    have hsorted := packetFamily64BlockList_merge_output_blockSorted
      packets hdis v hpackets e he
    have hthreshold : Monotone (fun x : α => decide (t ≤ x)) := by
      intro x y hxy
      by_cases hx : t ≤ x
      · have hy : t ≤ y := hx.trans hxy
        simp [hx, hy]
      · simp [hx]
    exact hthreshold.comp (by simpa [bits, e] using hsorted)
  have henergy := monotoneBits_assignedRankProfiles_aggregate_L2_var_allow_endpoint
    (m := 4096) (by omega) owner bits hbits targetQ frac hq hendpoint hfrac0 hfrac1
  simpa only [bits] using henergy

private theorem blockOf_rankOrder_of_separated {N : Nat}
    (p : Finset (Fin N)) (lo₁ hi₁ lo₂ hi₂ : Nat)
    (hhi₁ : hi₁ ≤ p.card) (hhi₂ : hi₂ ≤ p.card) (hsep : hi₁ ≤ lo₂)
    {x y : Fin N}
    (hx : x ∈ Chvatal.blockOf p lo₁ hi₁)
    (hy : y ∈ Chvatal.blockOf p lo₂ hi₂) : x.val < y.val := by
  have hx' := Chvatal.mem_blockOf.mp hx
  have hy' := Chvatal.mem_blockOf.mp hy
  have hrank : Chvatal.rankIn p x < Chvatal.rankIn p y := by omega
  by_contra hn
  have hback : y.val ≤ x.val := by omega
  by_cases heq : y.val = x.val
  · have hxy : y = x := Fin.ext heq
    subst y
    omega
  · have hlt : y.val < x.val := by omega
    have hrev := Chvatal.rankIn_lt_rankIn hy'.1
      (Fin.lt_iff_val_lt_val.mpr hlt)
    omega

/-- Intersecting two rank intervals of the same support is again the rank
interval with the intersected endpoints. This is the set-level bridge between
a port-local macro block and one of its outgoing WireFlow pieces. -/
theorem blockOf_inter_eq {N : Nat} (s : Finset (Fin N))
    (a b c d : Nat) :
    Chvatal.blockOf s a b ∩ Chvatal.blockOf s c d =
      Chvatal.blockOf s (max a c) (min b d) := by
  ext w
  simp only [Finset.mem_inter, Chvatal.mem_blockOf]
  constructor
  · rintro ⟨⟨hw, ha, hb⟩, ⟨_, hc, hd⟩⟩
    exact ⟨hw, max_le ha hc, lt_min hb hd⟩
  · rintro ⟨hw, hlo, hhi⟩
    exact ⟨⟨hw, le_trans (le_max_left _ _) hlo,
        lt_of_lt_of_le hhi (min_le_left _ _)⟩,
      ⟨hw, le_trans (le_max_right _ _) hlo,
        lt_of_lt_of_le hhi (min_le_right _ _)⟩⟩

private theorem blockOf_convex_of_wireOrder {N : Nat}
    (s : Finset (Fin N)) (lo hi : Nat)
    {x z y : Fin N} (hx : x ∈ Chvatal.blockOf s lo hi)
    (hzs : z ∈ s) (hy : y ∈ Chvatal.blockOf s lo hi)
    (hxz : x.val < z.val) (hzy : z.val < y.val) :
    z ∈ Chvatal.blockOf s lo hi := by
  have hx' := Chvatal.mem_blockOf.mp hx
  have hy' := Chvatal.mem_blockOf.mp hy
  have hxzRank := Chvatal.rankIn_lt_rankIn hx'.1
    (Fin.lt_iff_val_lt_val.mpr hxz)
  have hzyRank := Chvatal.rankIn_lt_rankIn hzs
    (Fin.lt_iff_val_lt_val.mpr hzy)
  apply Chvatal.mem_blockOf.mpr
  exact ⟨hzs, by omega, by omega⟩

/-- A physical rank interval can partially cut at most two consecutive
4096-rank groups of any sub-support. This is the geometric fact needed for
port-local grouping; it does not apply to groups transposed across ports. -/
theorem not_three_partial_rankGroups {N : Nat}
    (s p : Finset (Fin N)) (hps : p ⊆ s) (lo hi Q : Nat)
    (hQ : 4096 * Q ≤ p.card)
    (k₁ k₂ k₃ : Fin Q) (h₁₂ : k₁.val < k₂.val) (h₂₃ : k₂.val < k₃.val)
    (hpartial₁ : ((Chvatal.blockOf p (4096 * k₁.val)
      (4096 * (k₁.val + 1))) ∩ Chvatal.blockOf s lo hi).Nonempty)
    (hpartial₂ : ((Chvatal.blockOf p (4096 * k₂.val)
      (4096 * (k₂.val + 1))) \ Chvatal.blockOf s lo hi).Nonempty)
    (hpartial₃ : ((Chvatal.blockOf p (4096 * k₃.val)
      (4096 * (k₃.val + 1))) ∩ Chvatal.blockOf s lo hi).Nonempty) : False := by
  obtain ⟨x, hx⟩ := hpartial₁
  obtain ⟨z, hz⟩ := hpartial₂
  obtain ⟨y, hy⟩ := hpartial₃
  have hx' := Finset.mem_inter.mp hx
  have hy' := Finset.mem_inter.mp hy
  have hz' := Finset.mem_sdiff.mp hz
  have hk₁ : 4096 * (k₁.val + 1) ≤ p.card := by
    have hk : k₁.val + 1 ≤ Q := by omega
    omega
  have hk₂ : 4096 * (k₂.val + 1) ≤ p.card := by
    have hk : k₂.val + 1 ≤ Q := by omega
    omega
  have hk₃ : 4096 * (k₃.val + 1) ≤ p.card := by
    have hk : k₃.val + 1 ≤ Q := by omega
    omega
  have hxz := blockOf_rankOrder_of_separated p
    (4096 * k₁.val) (4096 * (k₁.val + 1))
    (4096 * k₂.val) (4096 * (k₂.val + 1)) hk₁ hk₂ (by omega)
    hx'.1 hz'.1
  have hzy := blockOf_rankOrder_of_separated p
    (4096 * k₂.val) (4096 * (k₂.val + 1))
    (4096 * k₃.val) (4096 * (k₃.val + 1)) hk₂ hk₃ (by omega)
    hz'.1 hy'.1
  have hzP := (Chvatal.mem_blockOf.mp hz'.1).1
  have hzInS := hps hzP
  have hzInInterval := blockOf_convex_of_wireOrder s lo hi hx'.2 hzInS
    hy'.2 hxz hzy
  exact hz'.2 hzInInterval

/-- Rank-group indices whose groups meet a destination interval both inside
and outside. -/
def partialRankGroupIndices {N : Nat} (s p : Finset (Fin N))
    (lo hi Q : Nat) : Finset (Fin Q) :=
  Finset.univ.filter fun k =>
    (Chvatal.blockOf p (4096 * k.val) (4096 * (k.val + 1)) ∩
      Chvatal.blockOf s lo hi).Nonempty ∧
    (Chvatal.blockOf p (4096 * k.val) (4096 * (k.val + 1)) \
      Chvatal.blockOf s lo hi).Nonempty

/-- For a sub-support p of s, a single rank interval in s has at most two
partially intersected consecutive 4096-rank groups of p. This turns the
geometric no-three theorem into the cardinality form used by overlap bounds. -/
theorem partialRankGroupIndices_card_le_two {N : Nat}
    (s p : Finset (Fin N)) (hps : p ⊆ s) (lo hi Q : Nat)
    (hQ : 4096 * Q ≤ p.card) :
    (partialRankGroupIndices s p lo hi Q).card ≤ 2 := by
  by_contra hcard
  have ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card.mp (by omega : 2 < (partialRankGroupIndices s p lo hi Q).card)
  have horder :
      (a.val < b.val ∧ b.val < c.val) ∨
      (a.val < c.val ∧ c.val < b.val) ∨
      (b.val < a.val ∧ a.val < c.val) ∨
      (b.val < c.val ∧ c.val < a.val) ∨
      (c.val < a.val ∧ a.val < b.val) ∨
      (c.val < b.val ∧ b.val < a.val) := by omega
  have hpartial (k : Fin Q) (hk : k ∈ partialRankGroupIndices s p lo hi Q) :=
    (Finset.mem_filter.mp hk).2
  rcases horder with h | h | h | h | h | h
  all_goals
    have hna := hpartial a ha
    have hnb := hpartial b hb
    have hnc := hpartial c hc
    rcases h with ⟨h₁, h₂⟩
    rcases hna with ⟨haIn, haOut⟩
    rcases hnb with ⟨hbIn, hbOut⟩
    rcases hnc with ⟨hcIn, hcOut⟩
    first
    | exact (not_three_partial_rankGroups s p hps lo hi Q hQ a b c h₁ h₂
        haIn hbOut hcIn).elim
    | exact (not_three_partial_rankGroups s p hps lo hi Q hQ a c b h₁ h₂
        haIn hcOut hbIn).elim
    | exact (not_three_partial_rankGroups s p hps lo hi Q hQ b a c h₁ h₂
        hbIn haOut hcIn).elim
    | exact (not_three_partial_rankGroups s p hps lo hi Q hQ b c a h₁ h₂
        hbIn hcOut haIn).elim
    | exact (not_three_partial_rankGroups s p hps lo hi Q hQ c a b h₁ h₂
        hcIn haOut hbIn).elim
    | exact (not_three_partial_rankGroups s p hps lo hi Q hQ c b a h₁ h₂
        hcIn hbOut haIn).elim

/-- A rank interval cannot partially cut three ordered equal-width rank
groups even when their grid is shifted, provided the groups lie in the
destination support. -/
theorem not_three_partial_rankIntervals {N : Nat}
    (source destination : Finset (Fin N)) (base lo hi Q : Nat)
    (hcomplete : base + 4096 * Q ≤ source.card)
    (hcontained : ∀ k : Fin Q,
      Chvatal.blockOf source (base + 4096 * k.val)
        (base + 4096 * (k.val + 1)) ⊆ destination)
    (k₁ k₂ k₃ : Fin Q) (h₁₂ : k₁.val < k₂.val) (h₂₃ : k₂.val < k₃.val)
    (hpartial₁ : ((Chvatal.blockOf source (base + 4096 * k₁.val)
      (base + 4096 * (k₁.val + 1))) ∩ Chvatal.blockOf destination lo hi).Nonempty)
    (hpartial₂ : ((Chvatal.blockOf source (base + 4096 * k₂.val)
      (base + 4096 * (k₂.val + 1))) \
        Chvatal.blockOf destination lo hi).Nonempty)
    (hpartial₃ : ((Chvatal.blockOf source (base + 4096 * k₃.val)
      (base + 4096 * (k₃.val + 1))) ∩ Chvatal.blockOf destination lo hi).Nonempty) :
    False := by
  obtain ⟨x, hx⟩ := hpartial₁
  obtain ⟨z, hz⟩ := hpartial₂
  obtain ⟨y, hy⟩ := hpartial₃
  have hx' := Finset.mem_inter.mp hx
  have hy' := Finset.mem_inter.mp hy
  have hz' := Finset.mem_sdiff.mp hz
  have hk₁ : base + 4096 * (k₁.val + 1) ≤ source.card := by
    have hk : k₁.val + 1 ≤ Q := by omega
    calc
      base + 4096 * (k₁.val + 1) ≤ base + 4096 * Q :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 4096 hk) _
      _ ≤ source.card := hcomplete
  have hk₂ : base + 4096 * (k₂.val + 1) ≤ source.card := by
    have hk : k₂.val + 1 ≤ Q := by omega
    calc
      base + 4096 * (k₂.val + 1) ≤ base + 4096 * Q :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 4096 hk) _
      _ ≤ source.card := hcomplete
  have hk₃ : base + 4096 * (k₃.val + 1) ≤ source.card := by
    have hk : k₃.val + 1 ≤ Q := by omega
    calc
      base + 4096 * (k₃.val + 1) ≤ base + 4096 * Q :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 4096 hk) _
      _ ≤ source.card := hcomplete
  have hgap₁₂ : base + 4096 * (k₁.val + 1) ≤ base + 4096 * k₂.val := by
    have hk : k₁.val + 1 ≤ k₂.val := by omega
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 4096 hk) _
  have hgap₂₃ : base + 4096 * (k₂.val + 1) ≤ base + 4096 * k₃.val := by
    have hk : k₂.val + 1 ≤ k₃.val := by omega
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 4096 hk) _
  have hxz := blockOf_rankOrder_of_separated source
    (base + 4096 * k₁.val) (base + 4096 * (k₁.val + 1))
    (base + 4096 * k₂.val) (base + 4096 * (k₂.val + 1))
    hk₁ hk₂ hgap₁₂ hx'.1 hz'.1
  have hzy := blockOf_rankOrder_of_separated source
    (base + 4096 * k₂.val) (base + 4096 * (k₂.val + 1))
    (base + 4096 * k₃.val) (base + 4096 * (k₃.val + 1))
    hk₂ hk₃ hgap₂₃ hz'.1 hy'.1
  have hzDestination := hcontained k₂ hz'.1
  have hzInInterval := blockOf_convex_of_wireOrder destination lo hi
    hx'.2 hzDestination hy'.2 hxz hzy
  exact hz'.2 hzInInterval

/-- Indices of shifted source-rank groups partially intersecting one
destination rank interval. -/
def partialRankIntervalIndices {N : Nat} (source destination : Finset (Fin N))
    (base lo hi Q : Nat) : Finset (Fin Q) :=
  Finset.univ.filter fun k =>
    (Chvatal.blockOf source (base + 4096 * k.val)
      (base + 4096 * (k.val + 1)) ∩ Chvatal.blockOf destination lo hi).Nonempty ∧
    (Chvatal.blockOf source (base + 4096 * k.val)
      (base + 4096 * (k.val + 1)) \
        Chvatal.blockOf destination lo hi).Nonempty

/-- The shifted-grid geometric lemma gives a cardinal overlap bound of two
partial groups per source stream and destination interval. -/
theorem partialRankIntervalIndices_card_le_two {N : Nat}
    (source destination : Finset (Fin N)) (base lo hi Q : Nat)
    (hcomplete : base + 4096 * Q ≤ source.card)
    (hcontained : ∀ k : Fin Q,
      Chvatal.blockOf source (base + 4096 * k.val)
        (base + 4096 * (k.val + 1)) ⊆ destination) :
    (partialRankIntervalIndices source destination base lo hi Q).card ≤ 2 := by
  let A := partialRankIntervalIndices source destination base lo hi Q
  have hno (a b c : Fin Q) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
      (hab : a.val < b.val) (hbc : b.val < c.val) : False := by
    have hpa := (Finset.mem_filter.mp ha).2
    have hpb := (Finset.mem_filter.mp hb).2
    have hpc := (Finset.mem_filter.mp hc).2
    exact not_three_partial_rankIntervals source destination base lo hi Q
      hcomplete hcontained a b c hab hbc hpa.1 hpb.2 hpc.1
  by_contra hcard
  change ¬ A.card ≤ 2 at hcard
  have hthree : 2 < A.card := by omega
  have ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hthree
  have horder :
      (a.val < b.val ∧ b.val < c.val) ∨
      (a.val < c.val ∧ c.val < b.val) ∨
      (b.val < a.val ∧ a.val < c.val) ∨
      (b.val < c.val ∧ c.val < a.val) ∨
      (c.val < a.val ∧ a.val < b.val) ∨
      (c.val < b.val ∧ b.val < a.val) := by omega
  rcases horder with h | h | h | h | h | h
  · exact hno a b c ha hb hc h.1 h.2
  · exact hno a c b ha hc hb h.1 h.2
  · exact hno b a c hb ha hc h.1 h.2
  · exact hno b c a hb hc ha h.1 h.2
  · exact hno c a b hc ha hb h.1 h.2
  · exact hno c b a hc hb ha h.1 h.2

/-- At time six, level two is an ordinary interior node. Its down-port length
is exactly the displayed power difference, so the number of 4096-wire groups
spanned by one port grows with dimension. This is a concrete scale check for
the macro-overlap audit; it does not assert that every such group has nonzero
profile error. -/
theorem flowDown7_levelTwo_timeSix_eq {d : Nat} (hd : 11 ≤ d) :
    flowDown7 d (by omega) 2 6 = 64 ^ (d - 5) - 64 ^ (d - 9) := by
  have hd7 : 7 ≤ d := by omega
  have hα : alpha7 d 6 = 0 := by
    simp [alpha7, alphaStarLower, ceilParity,
      show 6 ≠ 0 by omega, show 6 ≠ 1 by omega,
      show 6 + 5 ≤ d by omega]
  have hω : omega7 d 6 = 4 := by
    norm_num [omega7, omegaStarLower, ceilParity]
  have hactive : Active d 2 6 := by
    unfold Active
    rw [hα, hω]
    refine ⟨?_, by omega, by omega, by norm_num⟩
    unfold tf7
    omega
  have hcast := cast_flowDown7 d hd7 2 6 (by omega) (by unfold tf7; omega)
  have hflow : flowDown d 2 6 =
      (64 : Rat) ^ (d - 5) - 64 ^ (d - 9) := by
    rw [flowDown_mid d hactive (by intro hi; rw [hα] at hi; omega)
      (by rw [hω]; omega)]
    rw [capacity_eq_pow d 2 6 (d - 4) (by omega)]
    push_cast
    have hratio :
        ((4096 * 64 - (1 / 64 : Rat)) * (64 : Rat) ^ (d - 4) /
            (4096 * 64 ^ 2 : Rat)) =
          (64 : Rat) ^ (d - 4) / 64 - (64 : Rat) ^ (d - 4) / 64 ^ 5 := by
      norm_num
      ring
    rw [hratio]
    have hpow1 : (64 : Rat) ^ (d - 4) / 64 = (64 : Rat) ^ (d - 5) := by
      rw [show d - 4 = (d - 5) + 1 by omega, pow_succ]
      norm_num
    have hpow5 : (64 : Rat) ^ (d - 4) / 64 ^ 5 = (64 : Rat) ^ (d - 9) := by
      rw [show d - 4 = (d - 9) + 5 by omega, pow_add]
      norm_num
    rw [hpow1, hpow5]
  have hle : 64 ^ (d - 9) ≤ 64 ^ (d - 5) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hRat : (flowDown7 d hd7 2 6 : Rat) =
      ((64 ^ (d - 5) - 64 ^ (d - 9) : Nat) : Rat) := by
    rw [hcast, hflow, Nat.cast_sub hle]
    push_cast
    rfl
  apply Nat.cast_injective (R := Rat)
  exact hRat

/-- Exact number of complete 4096-wire groups in the time-six down-port at
level two; this count diverges with `d`. -/
theorem flowDown7_levelTwo_timeSix_div4096_eq {d : Nat} (hd : 11 ≤ d) :
    flowDown7 d (by omega) 2 6 / 4096 = 64 ^ (d - 7) - 64 ^ (d - 11) := by
  rw [flowDown7_levelTwo_timeSix_eq hd]
  have hfirst : 64 ^ (d - 5) = 4096 * 64 ^ (d - 7) := by
    rw [show d - 5 = (d - 7) + 2 by omega, pow_add]
    norm_num
    ring
  have hsecond : 64 ^ (d - 9) = 4096 * 64 ^ (d - 11) := by
    rw [show d - 9 = (d - 11) + 2 by omega, pow_add]
    norm_num
    ring
  rw [hfirst, hsecond]
  omega

/-- If each destination receives nonzero rank-profile discrepancy from at
most `k` of the 4096-rank merge blocks, their aggregate squared error is
charged with `k`, independent of the total number of blocks. Each individual
block's destination errors have energy at most its scalar rank-count error;
the unresolved scheduler obligation is the stated support-overlap bound. -/
theorem packetFamily64BlockList_merge_wholeBlock_owner_L2_le_of_overlap
    {q N : Nat} {α D : Type} [LinearOrder α]
    [Fintype D] [DecidableEq D]
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (v : Fin N → α)
    (hpackets : ∀ a, Monotone (fun i => v (packets a i)))
    (t : α)
    (owner : Fin q → Fin 4096 → D)
    (targetQ : Fin q → Nat) (frac : Fin q → Real)
    (hq : ∀ g, targetQ g ≤ 4096)
    (hendpoint : ∀ g, targetQ g = 4096 → frac g = 0)
    (hfrac0 : ∀ g, 0 ≤ frac g) (hfrac1 : ∀ g, frac g ≤ 1)
    (k : Nat)
    (hoverlap : ∀ destination,
      ((Finset.univ : Finset (Fin q)).filter (fun g =>
        (assignedBitCount (owner g)
            (packetFamily64BlockList_mergeThresholdBits packets hdis v t g)
            destination : Real) -
          ((1 - frac g) * assignedRankCount (owner g)
              (fun z j => decide (4096 - z ≤ j.val)) destination (targetQ g) +
            frac g * assignedRankCount (owner g)
              (fun z j => decide (4096 - z ≤ j.val)) destination (targetQ g + 1)) ≠ 0)).card ≤ k) :
    (Finset.univ.sum (fun (destination : D) =>
      (let total : Real := Finset.univ.sum (fun (g : Fin q) =>
        (assignedBitCount (owner g)
            (packetFamily64BlockList_mergeThresholdBits packets hdis v t g)
            destination : Real) -
          ((1 - frac g) * assignedRankCount (owner g)
              (fun z j => decide (4096 - z ≤ j.val)) destination (targetQ g) +
            frac g * assignedRankCount (owner g)
              (fun z j => decide (4096 - z ≤ j.val)) destination (targetQ g + 1)))
       total ^ 2))) ≤
      (k : Real) * Finset.univ.sum (fun (g : Fin q) =>
        ((boolTrueCount
          (packetFamily64BlockList_mergeThresholdBits packets hdis v t g) : Real) -
            (targetQ g + frac g)) ^ 2) := by
  let bits := packetFamily64BlockList_mergeThresholdBits packets hdis v t
  let err (g : Fin q) (destination : D) : Real :=
    (assignedBitCount (owner g) (bits g) destination : Real) -
      ((1 - frac g) * assignedRankCount (owner g)
          (fun z j => decide (4096 - z ≤ j.val)) destination (targetQ g) +
        frac g * assignedRankCount (owner g)
          (fun z j => decide (4096 - z ≤ j.val)) destination (targetQ g + 1))
  let energy (g : Fin q) : Real :=
    ((boolTrueCount (bits g) : Real) - (targetQ g + frac g)) ^ 2
  have hbits : ∀ g, Monotone (bits g) := by
    intro g
    let e := packetFamily64BlockEmbedding packets hdis g
    have he : e ∈ packetFamily64BlockList packets hdis := by
      simp [e, packetFamily64BlockList]
    have hsorted := packetFamily64BlockList_merge_output_blockSorted
      packets hdis v hpackets e he
    have hthreshold : Monotone (fun x : α => decide (t ≤ x)) := by
      intro x y hxy
      by_cases hx : t ≤ x
      · have hy : t ≤ y := hx.trans hxy
        simp [hx, hy]
      · simp [hx]
    exact hthreshold.comp (by simpa [bits, e] using hsorted)
  have hwithin (g : Fin q) : ∑ destination : D, (err g destination) ^ 2 ≤ energy g := by
    let ownerOne : Fin 1 → Fin 4096 → D := fun _ => owner g
    let bitsOne : Fin 1 → Fin 4096 → Bool := fun _ => bits g
    have hsingle := monotoneBits_assignedRankProfiles_aggregate_L2_var_allow_endpoint
      (D := D) (c := 1) (m := 4096) (by norm_num)
      ownerOne bitsOne (by intro i; exact hbits g)
      (fun _ => targetQ g) (fun _ => frac g)
      (by intro i; exact hq g) (by intro i; exact hendpoint g)
      (by intro i; exact hfrac0 g) (by intro i; exact hfrac1 g)
    simp only [ownerOne, bitsOne, Fin.sum_univ_succ] at hsingle
    simp only [Fin.sum_univ_zero, add_zero] at hsingle
    simp only [Nat.cast_one, one_mul] at hsingle
    change (∑ destination : D,
      ((assignedBitCount (owner g) (bits g) destination : Real) -
        ((1 - frac g) * assignedRankCount (owner g)
            (fun z j => decide (4096 - z ≤ j.val)) destination (targetQ g) +
          frac g * assignedRankCount (owner g)
            (fun z j => decide (4096 - z ≤ j.val)) destination (targetQ g + 1))) ^ 2) ≤
      ((boolTrueCount (bits g) : Real) - (targetQ g + frac g)) ^ 2
    simpa only [ownerOne, bitsOne] using hsingle
  have hoverlap' : ∀ destination,
      ((Finset.univ : Finset (Fin q)).filter (fun g => err g destination ≠ 0)).card ≤ k := by
    intro destination
    simpa only [err] using hoverlap destination
  have haggregate := finiteErrorProfiles_aggregate_L2_overlap
    err energy k hoverlap' hwithin
  simpa only [err, energy] using haggregate

set_option maxHeartbeats 1000000
/-- The actual even/odd ranks of a sorted 64-bit profile may be assigned to
arbitrary destinations lane by lane. Their suffix-interpolated destination
errors still sum exactly to the original 64-rank error. -/
theorem oddEvenMerge64_assignedParityProfiles_L1_exact
    {D : Type} [Fintype D] [DecidableEq D]
    (v : Fin 64 → Bool) (hv : Monotone v)
    (owner : Bool → Fin 32 → D) (q : Nat) (frac : Real)
    (hq : q < 64) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ lane : Bool, ∑ destination : D,
      |(assignedBitCount (owner lane)
          (fun i : Fin 32 => if lane then v (oddWire 32 i) else v (evenWire 32 i))
          destination : Real) -
        ((1 - oddEvenMerge64_parityCodeFrac lane q frac) *
            assignedRankCount (owner lane)
              (fun z k => decide (32 - z ≤ k.val)) destination
              (oddEvenMerge64_parityCodeFloor lane q) +
          oddEvenMerge64_parityCodeFrac lane q frac *
            assignedRankCount (owner lane)
              (fun z k => decide (32 - z ≤ k.val)) destination
              (oddEvenMerge64_parityCodeFloor lane q + 1))|) =
      |(boolTrueCount v : Real) - (q + frac)| := by
  let laneBits : Bool → Fin 32 → Bool := fun lane i =>
    if lane then v (oddWire 32 i) else v (evenWire 32 i)
  have hbits (lane : Bool) : Monotone (laneBits lane) := by
    intro i j hij
    cases lane
    · change v (evenWire 32 i) ≤ v (evenWire 32 j)
      apply hv
      apply Fin.le_def.mpr
      simp only [evenWire, Fin.val_mk]
      omega
    · change v (oddWire 32 i) ≤ v (oddWire 32 j)
      apply hv
      apply Fin.le_def.mpr
      simp only [oddWire, Fin.val_mk]
      omega
  have hparity := sorted_bool_parity_counts (m := 32) v hv
  have hprofile (lane : Bool) :
      boolTrueCount (laneBits lane) =
        oddEvenMerge64_parityCount lane (boolTrueCount v) := by
    cases lane <;> simp [laneBits, oddEvenMerge64_parityCount, hparity]
  have hlane (lane : Bool) :
      (∑ destination : D,
        |(assignedBitCount (owner lane) (laneBits lane) destination : Real) -
          ((1 - oddEvenMerge64_parityCodeFrac lane q frac) *
              assignedRankCount (owner lane)
                (fun z k => decide (32 - z ≤ k.val)) destination
                (oddEvenMerge64_parityCodeFloor lane q) +
            oddEvenMerge64_parityCodeFrac lane q frac *
              assignedRankCount (owner lane)
                (fun z k => decide (32 - z ≤ k.val)) destination
                (oddEvenMerge64_parityCodeFloor lane q + 1))|) =
        |(boolTrueCount (laneBits lane) : Real) -
          oddEvenMerge64_parityMean lane q frac| := by
    have hvalid := oddEvenMerge64_parityCode_valid lane q frac hq hfrac0 hfrac1
    have hexact := monotoneBits_assignedRankProfiles_L1_exact
      (owner lane) (laneBits lane) (hbits lane)
      (boolTrueCount (laneBits lane))
      (oddEvenMerge64_parityCodeFloor lane q)
      (oddEvenMerge64_parityCodeFrac lane q frac) rfl
      hvalid.1 hvalid.2.1 hvalid.2.2
    simpa only [oddEvenMerge64_parityMean_eq_code lane q frac hq,
      Nat.cast_add] using hexact
  calc
    _ = ∑ lane : Bool,
        |(boolTrueCount (laneBits lane) : Real) -
          oddEvenMerge64_parityMean lane q frac| := by
      apply Finset.sum_congr rfl
      intro lane hlaneMem
      exact hlane lane
    _ = |(boolTrueCount v : Real) - (q + frac)| := by
      simpa [laneBits] using
        oddEvenMerge64_parity_rebin_L1_exact v hv q frac hq hfrac0 hfrac1

/-- Squaring the destination errors after splitting a sorted 64-wire packet
into its parity lanes costs no extra factor of two: the total squared error is
bounded by the square of the original packet's scalar count error. This is
the energy form needed before matching the parity supports to next-stage
cuts. -/
theorem oddEvenMerge64_assignedParityProfiles_L2_le
    {D : Type} [Fintype D] [DecidableEq D]
    (v : Fin 64 → Bool) (hv : Monotone v)
    (owner : Bool → Fin 32 → D) (q : Nat) (frac : Real)
    (hq : q < 64) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ lane : Bool, ∑ destination : D,
      ((assignedBitCount (owner lane)
          (fun i : Fin 32 => if lane then v (oddWire 32 i) else v (evenWire 32 i))
          destination : Real) -
        ((1 - oddEvenMerge64_parityCodeFrac lane q frac) *
            assignedRankCount (owner lane)
              (fun z k => decide (32 - z ≤ k.val)) destination
              (oddEvenMerge64_parityCodeFloor lane q) +
          oddEvenMerge64_parityCodeFrac lane q frac *
            assignedRankCount (owner lane)
              (fun z k => decide (32 - z ≤ k.val)) destination
              (oddEvenMerge64_parityCodeFloor lane q + 1))) ^ 2) ≤
      ((boolTrueCount v : Real) - (q + frac)) ^ 2 := by
  let err (lane : Bool) (destination : D) : Real :=
    (assignedBitCount (owner lane)
        (fun i : Fin 32 => if lane then v (oddWire 32 i) else v (evenWire 32 i))
        destination : Real) -
      ((1 - oddEvenMerge64_parityCodeFrac lane q frac) *
          assignedRankCount (owner lane)
            (fun z k => decide (32 - z ≤ k.val)) destination
            (oddEvenMerge64_parityCodeFloor lane q) +
        oddEvenMerge64_parityCodeFrac lane q frac *
          assignedRankCount (owner lane)
            (fun z k => decide (32 - z ≤ k.val)) destination
            (oddEvenMerge64_parityCodeFloor lane q + 1))
  have hL1 : (∑ lane : Bool, ∑ destination : D, |err lane destination|) =
      |(boolTrueCount v : Real) - (q + frac)| := by
    simpa only [err] using
      oddEvenMerge64_assignedParityProfiles_L1_exact
        v hv owner q frac hq hfrac0 hfrac1
  have hinner (lane : Bool) :
      (∑ destination : D, (err lane destination) ^ 2) ≤
        (∑ destination : D, |err lane destination|) ^ 2 := by
    simpa using Finset.sum_sq_le_sq_sum_of_nonneg
      (fun destination _ => abs_nonneg (err lane destination))
  have houter :
      (∑ lane : Bool, (∑ destination : D, |err lane destination|) ^ 2) ≤
        (∑ lane : Bool, ∑ destination : D, |err lane destination|) ^ 2 := by
    exact Finset.sum_sq_le_sq_sum_of_nonneg
      (fun lane _ => Finset.sum_nonneg (fun destination _ => abs_nonneg (err lane destination)))
  calc
    (∑ lane : Bool, ∑ destination : D, (err lane destination) ^ 2) ≤
        ∑ lane : Bool, (∑ destination : D, |err lane destination|) ^ 2 :=
      Finset.sum_le_sum (fun lane _ => hinner lane)
    _ ≤ (∑ lane : Bool, ∑ destination : D, |err lane destination|) ^ 2 := houter
    _ = |(boolTrueCount v : Real) - (q + frac)| ^ 2 := by rw [hL1]
    _ = ((boolTrueCount v : Real) - (q + frac)) ^ 2 := by rw [sq_abs]

/-- The two parity lanes partition the parent ranks, so their actual
destination counts recombine exactly for every owner map. -/
theorem oddEvenMerge64_assignedBitCount_parity_split
    {D : Type} [DecidableEq D]
    (v : Fin 64 → Bool) (owner : Fin 64 → D) (destination : D) :
    (∑ lane : Bool,
      assignedBitCount
        (fun i : Fin 32 => owner (if lane then oddWire 32 i else evenWire 32 i))
        (fun i : Fin 32 => if lane then v (oddWire 32 i) else v (evenWire 32 i))
        destination) =
      assignedBitCount owner v destination := by
  let p : Fin 32 ⊕ Fin 32 → Prop
    | Sum.inl i => destination = owner (evenWire 32 i) ∧ v (evenWire 32 i) = true
    | Sum.inr i => destination = owner (oddWire 32 i) ∧ v (oddWire 32 i) = true
  have hp (s : Fin 32 ⊕ Fin 32) :
      p s ↔ destination = owner (parityEquiv 32 s) ∧ v (parityEquiv 32 s) = true := by
    cases s <;> rfl
  let e : {k : Fin 64 // destination = owner k ∧ v k = true} ≃
      ({i : Fin 32 // destination = owner (evenWire 32 i) ∧
        v (evenWire 32 i) = true} ⊕
       {i : Fin 32 // destination = owner (oddWire 32 i) ∧
        v (oddWire 32 i) = true}) :=
    ((parityEquiv 32).subtypeEquiv hp).symm.trans Equiv.subtypeSum
  unfold assignedBitCount
  change
    (∑ lane : Bool, ∑ i : Fin 32,
      if destination = owner (if lane then oddWire 32 i else evenWire 32 i) ∧
          (if lane then v (oddWire 32 i) else v (evenWire 32 i)) = true
      then 1 else 0) =
    ∑ k : Fin 64, if destination = owner k ∧ v k = true then 1 else 0
  rw [Fintype.sum_bool]
  rw [finSum_ite_one_eq_card_subtype, finSum_ite_one_eq_card_subtype]
  rw [finSum_ite_one_eq_card_subtype]
  rw [← Fintype.card_sum]
  exact (Fintype.card_congr (e.trans (Equiv.sumComm _ _))).symm

/-- At every integer parent cut, the two lane suffix profiles assigned to a
destination sum exactly to that destination's parent-rank suffix count. -/
theorem oddEvenMerge64_assignedRankCount_parity_split
    {D : Type} [Fintype D] [DecidableEq D]
    (owner : Fin 64 → D) (destination : D) (z : Nat) (hz : z ≤ 64) :
    (∑ lane : Bool,
      assignedRankCount
        (fun i : Fin 32 => owner (if lane then oddWire 32 i else evenWire 32 i))
        (fun r k => decide (32 - r ≤ k.val)) destination
        (oddEvenMerge64_parityCount lane z)) =
      assignedRankCount owner (fun r k => decide (64 - r ≤ k.val)) destination z := by
  let v : Fin 64 → Bool := fun k => decide (64 - z ≤ k.val)
  have hv : Monotone v := by
    intro i j hij
    change decide (64 - z ≤ i.val) ≤ decide (64 - z ≤ j.val)
    by_cases hi : 64 - z ≤ i.val
    · have hj : 64 - z ≤ j.val := le_trans hi (Fin.le_def.mp hij)
      simp [hi, hj]
    · simp [hi]
  have hvcount : boolTrueCount v = z := by
    simpa [v] using boolTrueCount_countSuffix 64 z hz
  have hlaneCount (lane : Bool) :
      boolTrueCount (fun i : Fin 32 =>
        if lane then v (oddWire 32 i) else v (evenWire 32 i)) =
          oddEvenMerge64_parityCount lane z := by
    have hparity := sorted_bool_parity_counts (m := 32) v hv
    cases lane <;> simp [oddEvenMerge64_parityCount, hvcount, hparity]
  have hprofile (lane : Bool) (i : Fin 32) :
      (if lane then v (oddWire 32 i) else v (evenWire 32 i)) =
        decide (32 - oddEvenMerge64_parityCount lane z ≤ i.val) := by
    rw [monotoneBool_eq_countSuffix (fun i : Fin 32 =>
      if lane then v (oddWire 32 i) else v (evenWire 32 i))]
    · rw [hlaneCount lane]
    · intro i j hij
      cases lane
      · change v (evenWire 32 i) ≤ v (evenWire 32 j)
        apply hv
        apply Fin.le_def.mpr
        simp [evenWire]
        omega
      · change v (oddWire 32 i) ≤ v (oddWire 32 j)
        apply hv
        apply Fin.le_def.mpr
        simp [oddWire]
        omega
  have hsplit := oddEvenMerge64_assignedBitCount_parity_split v owner destination
  have hlane (lane : Bool) :
      assignedBitCount
          (fun i : Fin 32 => owner (if lane then oddWire 32 i else evenWire 32 i))
          (fun i : Fin 32 => if lane then v (oddWire 32 i) else v (evenWire 32 i))
          destination =
        assignedRankCount
          (fun i : Fin 32 => owner (if lane then oddWire 32 i else evenWire 32 i))
          (fun r k => decide (32 - r ≤ k.val)) destination
          (oddEvenMerge64_parityCount lane z) := by
    unfold assignedBitCount assignedRankCount
    apply Finset.sum_congr rfl
    intro i _
    have hi := congrArg (fun b : Bool =>
      if destination = owner (if lane then oddWire 32 i else evenWire 32 i) ∧ b = true
      then (1 : Nat) else 0) (hprofile lane i)
    simpa using hi
  have hparent : assignedBitCount owner v destination =
      assignedRankCount owner (fun r k => decide (64 - r ≤ k.val)) destination z := by
    unfold assignedBitCount assignedRankCount
    apply Finset.sum_congr rfl
    intro k _
    rfl
  simp_rw [hlane] at hsplit
  rw [hparent] at hsplit
  exact hsplit

/-- The encoded integer/fraction pair for one parity lane is precisely the
interpolation of its rank profiles at the parent cuts `q` and `q+1`. -/
theorem oddEvenMerge64_parityAssignedRankInterp_eq
    (lane : Bool) (q : Nat) (frac : Real) (hq : q < 64)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) (C : Nat → Real) :
    (1 - oddEvenMerge64_parityCodeFrac lane q frac) *
        C (oddEvenMerge64_parityCodeFloor lane q) +
      oddEvenMerge64_parityCodeFrac lane q frac *
        C (oddEvenMerge64_parityCodeFloor lane q + 1) =
      (1 - frac) * C (oddEvenMerge64_parityCount lane q) +
        frac * C (oddEvenMerge64_parityCount lane (q + 1)) := by
  have hcount : oddEvenMerge64_parityCount lane q ≤ 32 := by
    cases lane <;> simp [oddEvenMerge64_parityCount] <;> omega
  have hstepLo : oddEvenMerge64_parityCount lane q ≤
      oddEvenMerge64_parityCount lane (q + 1) := by
    cases lane
    · exact Nat.div_le_div_right (Nat.le_succ q)
    · exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.le_succ q) 1)
  have hstepHi : oddEvenMerge64_parityCount lane (q + 1) ≤
      oddEvenMerge64_parityCount lane q + 1 := by
    cases lane <;> simp [oddEvenMerge64_parityCount] <;> omega
  by_cases hfull : oddEvenMerge64_parityCount lane q = 32
  · have hnext : oddEvenMerge64_parityCount lane (q + 1) = 32 := by
      cases lane <;> simp [oddEvenMerge64_parityCount] at hfull ⊢ <;> omega
    simp [oddEvenMerge64_parityCodeFloor, oddEvenMerge64_parityCodeFrac,
      hfull, hnext]
    ring
  · have hbelow : oddEvenMerge64_parityCount lane q ≤ 31 := by omega
    by_cases hrise : oddEvenMerge64_parityCount lane (q + 1) =
        oddEvenMerge64_parityCount lane q + 1
    · simp [oddEvenMerge64_parityCodeFloor, oddEvenMerge64_parityCodeFrac,
        hfull, hrise, Nat.min_eq_right hbelow]
    · have hflat : oddEvenMerge64_parityCount lane (q + 1) =
          oddEvenMerge64_parityCount lane q := by omega
      simp [oddEvenMerge64_parityCodeFloor, oddEvenMerge64_parityCodeFrac,
        hfull, hrise, hflat, Nat.min_eq_right hbelow]
      ring

set_option maxHeartbeats 5000000
/-- For an owner of the original 64 ranks, the two parity-lane errors
recombine with their signs, destination by destination, to the parent error.
This is the cancellation-preserving bridge needed before source aggregation. -/
theorem oddEvenMerge64_assignedParity_signed_error_eq
    {D : Type} [Fintype D] [DecidableEq D]
    (v : Fin 64 → Bool) (owner : Fin 64 → D) (destination : D)
    (q : Nat) (frac : Real) (hq : q < 64)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ lane : Bool,
      ((assignedBitCount
          (fun i : Fin 32 => owner (if lane then oddWire 32 i else evenWire 32 i))
          (fun i : Fin 32 => if lane then v (oddWire 32 i) else v (evenWire 32 i))
          destination : Real) -
        ((1 - oddEvenMerge64_parityCodeFrac lane q frac) *
            assignedRankCount
              (fun i : Fin 32 => owner (if lane then oddWire 32 i else evenWire 32 i))
              (fun z k => decide (32 - z ≤ k.val)) destination
              (oddEvenMerge64_parityCodeFloor lane q) +
          oddEvenMerge64_parityCodeFrac lane q frac *
            assignedRankCount
              (fun i : Fin 32 => owner (if lane then oddWire 32 i else evenWire 32 i))
              (fun z k => decide (32 - z ≤ k.val)) destination
              (oddEvenMerge64_parityCodeFloor lane q + 1)))) =
      (assignedBitCount owner v destination : Real) -
        ((1 - frac) * assignedRankCount owner
            (fun z k => decide (64 - z ≤ k.val)) destination q +
          frac * assignedRankCount owner
            (fun z k => decide (64 - z ≤ k.val)) destination (q + 1)) := by
  let C (lane : Bool) (z : Nat) : Real :=
    assignedRankCount
      (fun i : Fin 32 => owner (if lane then oddWire 32 i else evenWire 32 i))
      (fun r k => decide (32 - r ≤ k.val)) destination z
  let A (lane : Bool) : Real :=
    assignedBitCount
      (fun i : Fin 32 => owner (if lane then oddWire 32 i else evenWire 32 i))
      (fun i : Fin 32 => if lane then v (oddWire 32 i) else v (evenWire 32 i))
      destination
  let T (lane : Bool) : Real :=
    (1 - oddEvenMerge64_parityCodeFrac lane q frac) *
        C lane (oddEvenMerge64_parityCodeFloor lane q) +
      oddEvenMerge64_parityCodeFrac lane q frac *
        C lane (oddEvenMerge64_parityCodeFloor lane q + 1)
  have hactualNat := oddEvenMerge64_assignedBitCount_parity_split v owner destination
  have hactual :
      (∑ lane : Bool, A lane) =
        (assignedBitCount owner v destination : Real) := by
    have hcast := congrArg (fun n : Nat => (n : Real)) hactualNat
    simpa only [A, Nat.cast_sum] using hcast
  have htarget : (∑ lane : Bool, T lane) =
        (1 - frac) * assignedRankCount owner
            (fun z k => decide (64 - z ≤ k.val)) destination q +
          frac * assignedRankCount owner
            (fun z k => decide (64 - z ≤ k.val)) destination (q + 1) := by
    calc
      _ = ∑ lane : Bool,
          ((1 - frac) * C lane (oddEvenMerge64_parityCount lane q) +
            frac * C lane (oddEvenMerge64_parityCount lane (q + 1))) := by
        apply Finset.sum_congr rfl
        intro lane _
        exact oddEvenMerge64_parityAssignedRankInterp_eq lane q frac hq
          hfrac0 hfrac1 (C lane)
      _ = (1 - frac) *
            (∑ lane : Bool, C lane (oddEvenMerge64_parityCount lane q)) +
          frac * (∑ lane : Bool, C lane (oddEvenMerge64_parityCount lane (q + 1))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by
        have hqSplit := oddEvenMerge64_assignedRankCount_parity_split
          owner destination q (by omega)
        have hq1Split := oddEvenMerge64_assignedRankCount_parity_split
          owner destination (q + 1) (by omega)
        have hqR :
            (∑ lane : Bool, C lane (oddEvenMerge64_parityCount lane q)) =
              (assignedRankCount owner
                (fun z k => decide (64 - z ≤ k.val)) destination q : Real) := by
          dsimp [C]
          exact_mod_cast hqSplit
        have hq1R :
            (∑ lane : Bool, C lane (oddEvenMerge64_parityCount lane (q + 1))) =
              (assignedRankCount owner
                (fun z k => decide (64 - z ≤ k.val)) destination (q + 1) : Real) := by
          dsimp [C]
          exact_mod_cast hq1Split
        rw [hqR, hq1R]
  have hsum : (∑ lane : Bool, (A lane - T lane)) =
      (∑ lane : Bool, A lane) - (∑ lane : Bool, T lane) := by
    simp only [Fintype.sum_bool]
    ring
  calc
    _ = (∑ lane : Bool, A lane) - (∑ lane : Bool, T lane) := by
      simpa only [A, T, C] using hsum
    _ = _ := congrArg₂ (· - ·) hactual htarget

/-- One destination's signed error on a parity lane of a parent 64-rank
profile, using the induced fractional lane cut. -/
def oddEvenMerge64_assignedParityLaneError {D : Type} [Fintype D] [DecidableEq D]
    (bits : Fin 64 → Bool) (owner : Fin 64 → D) (destination : D)
    (q : Nat) (frac : Real) (lane : Bool) : Real :=
  (assignedBitCount
      (fun i : Fin 32 => owner (if lane then oddWire 32 i else evenWire 32 i))
      (fun i : Fin 32 => if lane then bits (oddWire 32 i) else bits (evenWire 32 i))
      destination : Real) -
    ((1 - oddEvenMerge64_parityCodeFrac lane q frac) *
        assignedRankCount
          (fun i : Fin 32 => owner (if lane then oddWire 32 i else evenWire 32 i))
          (fun z k => decide (32 - z ≤ k.val)) destination
          (oddEvenMerge64_parityCodeFloor lane q) +
      oddEvenMerge64_parityCodeFrac lane q frac *
        assignedRankCount
          (fun i : Fin 32 => owner (if lane then oddWire 32 i else evenWire 32 i))
          (fun z k => decide (32 - z ≤ k.val)) destination
          (oddEvenMerge64_parityCodeFloor lane q + 1))

/-- Signed parity errors also recombine after summing any finite cohort of
source packets, with no lane multiplicity. -/
theorem oddEvenMerge64_assignedParity_cohort_signed_error_eq
    {D : Type} [Fintype D] [DecidableEq D] {c : Nat}
    (bits : Fin c → Fin 64 → Bool)
    (owner : Fin c → Fin 64 → D)
    (q : Fin c → Nat) (frac : Fin c → Real)
    (hq : ∀ packet, q packet < 64)
    (hfrac0 : ∀ packet, 0 ≤ frac packet)
    (hfrac1 : ∀ packet, frac packet ≤ 1)
    (destination : D) :
    (∑ packet : Fin c, ∑ lane : Bool,
      oddEvenMerge64_assignedParityLaneError (bits packet) (owner packet)
        destination (q packet) (frac packet) lane) =
      ∑ packet : Fin c,
        ((assignedBitCount (owner packet) (bits packet) destination : Real) -
          ((1 - frac packet) * assignedRankCount (owner packet)
              (fun z k => decide (64 - z ≤ k.val)) destination (q packet) +
            frac packet * assignedRankCount (owner packet)
              (fun z k => decide (64 - z ≤ k.val)) destination (q packet + 1))) := by
  apply Finset.sum_congr rfl
  intro packet _
  simpa only [oddEvenMerge64_assignedParityLaneError] using
    oddEvenMerge64_assignedParity_signed_error_eq
      (bits packet) (owner packet) destination (q packet) (frac packet)
      (hq packet) (hfrac0 packet) (hfrac1 packet)

set_option maxHeartbeats 1000000

/-- The signed parity errors can be recombined before squaring across a
cohort: when each parent packet is sorted, the aggregate destination energy
is bounded by the cohort size times the original scalar profile energy. This
avoids the spurious factor of two incurred by bounding the two lanes
separately. -/
theorem oddEvenMerge64_assignedParity_cohort_L2_le
    {D : Type} [Fintype D] [DecidableEq D] {c : Nat}
    (bits : Fin c → Fin 64 → Bool)
    (hbits : ∀ packet, Monotone (bits packet))
    (owner : Fin c → Fin 64 → D)
    (q : Fin c → Nat) (frac : Fin c → Real)
    (hq : ∀ packet, q packet < 64)
    (hfrac0 : ∀ packet, 0 ≤ frac packet)
    (hfrac1 : ∀ packet, frac packet ≤ 1) :
    (∑ destination : D,
      (∑ packet : Fin c, ∑ lane : Bool,
        oddEvenMerge64_assignedParityLaneError (bits packet) (owner packet)
          destination (q packet) (frac packet) lane) ^ 2) ≤
      (c : Real) * (∑ packet : Fin c,
        ((boolTrueCount (bits packet) : Real) -
          (q packet + frac packet)) ^ 2) := by
  classical
  let suffix : Nat → Fin 64 → Bool :=
    fun z k => decide (64 - z ≤ k.val)
  let X : Fin c → Nat := fun packet => boolTrueCount (bits packet)
  have hX : ∀ packet, X packet ≤ 64 := by
    intro packet
    exact Fintype.card_subtype_le (fun k : Fin 64 => bits packet k = true)
  have hsuffix : ∀ z ≤ 64,
      (∑ k : Fin 64, if suffix z k = true then 1 else 0) = z := by
    intro z hz
    calc
      (∑ k : Fin 64, if suffix z k = true then 1 else 0) =
          boolTrueCount (fun k : Fin 64 => decide (64 - z ≤ k.val)) := by
        exact finSum_ite_one_eq_card_subtype _
      _ = z := boolTrueCount_countSuffix 64 z hz
  have hmonoSuffix : ∀ a b, a ≤ b → ∀ k,
      suffix a k = true → suffix b k = true := by
    intro a b hab k ha
    simp only [suffix, decide_eq_true_eq] at ha ⊢
    omega
  have hcount (packet : Fin c) (destination : D) :
      assignedBitCount (owner packet) (bits packet) destination =
        assignedRankCount (owner packet) suffix destination (X packet) := by
    unfold assignedBitCount assignedRankCount
    apply Finset.sum_congr rfl
    intro k hk
    rw [monotoneBool_eq_countSuffix (bits packet) (hbits packet) k]
  have hagg := assignedRankProfiles_aggregate_L2_var
    (owner := owner) (suffix := suffix) (X := X) (q := q) (frac := frac)
    hX hq hfrac0 hfrac1 hsuffix hmonoSuffix
  have hsigned (destination : D) :
      (∑ packet : Fin c, ∑ lane : Bool,
        oddEvenMerge64_assignedParityLaneError (bits packet) (owner packet)
          destination (q packet) (frac packet) lane) =
      ∑ packet : Fin c,
        ((assignedRankCount (owner packet) suffix destination (X packet) : Real) -
          ((1 - frac packet) *
              assignedRankCount (owner packet) suffix destination (q packet) +
            frac packet *
              assignedRankCount (owner packet) suffix destination (q packet + 1))) := by
    rw [oddEvenMerge64_assignedParity_cohort_signed_error_eq
      bits owner q frac hq hfrac0 hfrac1 destination]
    apply Finset.sum_congr rfl
    intro packet _
    rw [hcount packet destination]
  calc
    _ = ∑ destination : D,
        (∑ packet : Fin c,
          ((assignedRankCount (owner packet) suffix destination (X packet) : Real) -
            ((1 - frac packet) *
                assignedRankCount (owner packet) suffix destination (q packet) +
              frac packet *
                assignedRankCount (owner packet) suffix destination (q packet + 1)))) ^ 2 := by
      apply Finset.sum_congr rfl
      intro destination _
      rw [hsigned destination]
    _ ≤ (c : Real) * ∑ packet : Fin c,
        ((X packet : Real) - (q packet + frac packet)) ^ 2 := hagg
    _ = _ := by simp [X]

set_option maxHeartbeats 200000

/-- If each parity lane's destination errors are exactly accounted for by its
own profile error, then the two lane errors sum exactly to the parent error.
`assignedRankProfiles_L1_exact` supplies the lane premise for arbitrary
rank-owner maps. -/
theorem oddEvenMerge64_ownedParityProfile_rebin_L1_exact
    {D : Type} [Fintype D]
    (v : Fin 64 → Bool) (hv : Monotone v)
    (laneBits : Bool → Fin 32 → Bool)
    (hprofile : ∀ lane,
      boolTrueCount (laneBits lane) =
        oddEvenMerge64_parityCount lane (boolTrueCount v))
    (q : Nat) (frac : Real) (hq : q < 64)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (laneError : Bool → D → Real)
    (howner : ∀ lane,
      (∑ destination : D, |laneError lane destination|) =
        |(boolTrueCount (laneBits lane) : Real) -
          oddEvenMerge64_parityMean lane q frac|) :
    (∑ lane : Bool, ∑ destination : D, |laneError lane destination|) =
      |(boolTrueCount v : Real) - (q + frac)| := by
  calc
    _ = ∑ lane : Bool,
        |(boolTrueCount (laneBits lane) : Real) -
          oddEvenMerge64_parityMean lane q frac| := by
      apply Finset.sum_congr rfl
      intro lane _
      exact howner lane
    _ = |(boolTrueCount v : Real) - (q + frac)| := by
      calc
        _ = ∑ lane : Bool,
            |(oddEvenMerge64_parityCount lane (boolTrueCount v) : Real) -
              oddEvenMerge64_parityMean lane q frac| := by
          apply Finset.sum_congr rfl
          intro lane _
          rw [hprofile lane]
        _ = |(boolTrueCount v : Real) - (q + frac)| := by
          have hparity := sorted_bool_parity_counts (m := 32) v hv
          simpa [oddEvenMerge64_parityMean, oddEvenMerge64_parityCount, hparity] using
            oddEvenMerge64_parity_rebin_L1_exact v hv q frac hq hfrac0 hfrac1

/-- Every nontrivial, non-singleton threshold count loses at least eight
units of doubled centered energy in this 64-wire phase. -/
theorem oddEvenMerge64_phase_drop_ge_eight (H : Nat) (hH : H ≤ 64)
    (hlo : 2 ≤ H) (hhi : H ≤ 62) :
    8 ≤ 2 * ((min H (64 - H) : Nat) : ℤ) ^ 2 -
      (if H % 2 = 0 then 0 else 2 : ℤ) := by
  interval_cases H <;> norm_num

/-- The phase has zero energy drop exactly at the empty/full and singleton /
complement-singleton threshold counts. -/
theorem oddEvenMerge64_phase_drop_eq_zero_iff (H : Nat) (hH : H ≤ 64) :
    (2 * ((min H (64 - H) : Nat) : ℤ) ^ 2 -
      (if H % 2 = 0 then 0 else 2 : ℤ) = 0) ↔
      (H = 0 ∨ H = 1 ∨ H = 63 ∨ H = 64) := by
  interval_cases H <;> norm_num

/-- Applied to an actual sorted packet, the sole noncontracting threshold
counts are 0, 1, 63, and 64; all others lose at least eight. -/
theorem oddEvenMerge64_monotone_energy_drop_ge_eight
    (v : Fin 64 → Bool) (hv : Monotone v)
    (hlo : 2 ≤ boolTrueCount v) (hhi : boolTrueCount v ≤ 62) :
    8 ≤ oddEvenMerge64InputEnergy v - oddEvenMerge64ParityEnergy v := by
  rw [oddEvenMerge64_monotone_energy_drop_eq_phase v hv]
  exact oddEvenMerge64_phase_drop_ge_eight (boolTrueCount v)
    (by simpa [boolTrueCount] using
      (Fintype.card_subtype_le (fun i : Fin 64 => v i = true))) hlo hhi

/-- On every active threshold, the merge removes at least three quarters of
the input phase energy. -/
theorem oddEvenMerge64_monotone_energy_drop_ge_three_quarters
    (v : Fin 64 → Bool) (hv : Monotone v)
    (hlo : 2 ≤ boolTrueCount v) (hhi : boolTrueCount v ≤ 62) :
    3 * oddEvenMerge64InputEnergy v ≤
      4 * (oddEvenMerge64InputEnergy v - oddEvenMerge64ParityEnergy v) := by
  conv_lhs => rw [oddEvenMerge64_monotone_input_energy_eq_phase v hv]
  conv_rhs => rw [oddEvenMerge64_monotone_energy_drop_eq_phase v hv]
  have hcount : boolTrueCount v ≤ 64 := by
    simpa [boolTrueCount] using
      (Fintype.card_subtype_le (fun i : Fin 64 => v i = true))
  have hm : 2 ≤ min (boolTrueCount v) (64 - boolTrueCount v) :=
    Nat.le_min.mpr ⟨hlo, by omega⟩
  have hr : 0 ≤ (if boolTrueCount v % 2 = 0 then 0 else 2 : Int) ∧
      (if boolTrueCount v % 2 = 0 then 0 else 2 : Int) ≤ 2 := by
    split <;> norm_num
  rcases hr with ⟨hr0, hr2⟩
  have hmcast : (2 : Int) ≤
      ((min (boolTrueCount v) (64 - boolTrueCount v) : Nat) : Int) := by
    exact_mod_cast hm
  nlinarith [sq_nonneg ((min (boolTrueCount v) (64 - boolTrueCount v) : Int) - 2)]

/-- Exact correction-layer exception bound: the 3/4 drop holds except for
singleton and co-singleton threshold profiles, each of which costs six units
in this scaled inequality. -/
theorem oddEvenMerge64_monotone_energy_drop_with_exception
    (v : Fin 64 → Bool) (hv : Monotone v) :
    3 * oddEvenMerge64InputEnergy v ≤
      4 * (oddEvenMerge64InputEnergy v - oddEvenMerge64ParityEnergy v) +
        (if boolTrueCount v = 1 ∨ boolTrueCount v = 63 then 6 else 0) := by
  by_cases hlo : 2 ≤ boolTrueCount v
  · by_cases hhi : boolTrueCount v ≤ 62
    · have h := oddEvenMerge64_monotone_energy_drop_ge_three_quarters v hv hlo hhi
      by_cases hex : boolTrueCount v = 1 ∨ boolTrueCount v = 63
      · simp [hex]
        linarith [h]
      · simp [hex]
        exact h
    · have hcount : boolTrueCount v ≤ 64 := by
        simpa [boolTrueCount] using
          (Fintype.card_subtype_le (fun i : Fin 64 => v i = true))
      have hgt : 62 < boolTrueCount v := Nat.lt_of_not_ge hhi
      let H := boolTrueCount v
      have hHle : H ≤ 64 := hcount
      have hHgt : 62 < H := hgt
      by_cases hH64 : H = 64
      · have h64 : boolTrueCount v = 64 := by simpa [H] using hH64
        have hI : oddEvenMerge64InputEnergy v = 0 := by
          rw [oddEvenMerge64_monotone_input_energy_eq_phase v hv, h64]
          norm_num
        have hD : oddEvenMerge64InputEnergy v - oddEvenMerge64ParityEnergy v = 0 := by
          rw [oddEvenMerge64_monotone_energy_drop_eq_phase v hv, h64]
          norm_num
        have hP : oddEvenMerge64ParityEnergy v = 0 := by omega
        rw [hI, hP]
        simp [h64]
      · have hHeq : H = 63 := by omega
        have h63 : boolTrueCount v = 63 := by simpa [H] using hHeq
        have hI : oddEvenMerge64InputEnergy v = 2 := by
          rw [oddEvenMerge64_monotone_input_energy_eq_phase v hv, h63]
          norm_num
        have hD : oddEvenMerge64InputEnergy v - oddEvenMerge64ParityEnergy v = 0 := by
          rw [oddEvenMerge64_monotone_energy_drop_eq_phase v hv, h63]
          norm_num
        have hP : oddEvenMerge64ParityEnergy v = 2 := by omega
        rw [hI, hP]
        simp [h63]
  · have hcount : boolTrueCount v ≤ 64 := by
      simpa [boolTrueCount] using
        (Fintype.card_subtype_le (fun i : Fin 64 => v i = true))
    have hsmall : boolTrueCount v = 0 ∨ boolTrueCount v = 1 := by omega
    rcases hsmall with hzero | hone
    · have hI : oddEvenMerge64InputEnergy v = 0 := by
        rw [oddEvenMerge64_monotone_input_energy_eq_phase v hv, hzero]
        norm_num
      have hD : oddEvenMerge64InputEnergy v - oddEvenMerge64ParityEnergy v = 0 := by
        rw [oddEvenMerge64_monotone_energy_drop_eq_phase v hv, hzero]
        norm_num
      have hP : oddEvenMerge64ParityEnergy v = 0 := by omega
      rw [hI, hP]
      simp [hzero]
    · have hI : oddEvenMerge64InputEnergy v = 2 := by
        rw [oddEvenMerge64_monotone_input_energy_eq_phase v hv, hone]
        norm_num
      have hD : oddEvenMerge64InputEnergy v - oddEvenMerge64ParityEnergy v = 0 := by
        rw [oddEvenMerge64_monotone_energy_drop_eq_phase v hv, hone]
        norm_num
      have hP : oddEvenMerge64ParityEnergy v = 2 := by omega
      rw [hI, hP]
      simp [hone]

/-- The local exception inequality sums without loss over any finite family
of sorted Boolean 64-profiles. -/
theorem oddEvenMerge64_family_energy_drop_with_exception
    {I : Type} [Fintype I] [DecidableEq I]
    (bits : I → Fin 64 → Bool) (hsorted : ∀ i, Monotone (bits i)) :
    3 * (Finset.univ.sum (fun i : I => oddEvenMerge64InputEnergy (bits i))) ≤
      4 * (Finset.univ.sum (fun i : I =>
        oddEvenMerge64InputEnergy (bits i) - oddEvenMerge64ParityEnergy (bits i))) +
        6 * (Finset.univ.sum (fun i : I =>
          if boolTrueCount (bits i) = 1 ∨ boolTrueCount (bits i) = 63
          then (1 : ℤ) else 0)) := by
  classical
  have hlocal (i : I) := oddEvenMerge64_monotone_energy_drop_with_exception
    (bits i) (hsorted i)
  calc
    3 * (Finset.univ.sum (fun i : I => oddEvenMerge64InputEnergy (bits i))) =
        Finset.univ.sum (fun i : I => 3 * oddEvenMerge64InputEnergy (bits i)) := by
      rw [Finset.mul_sum]
    _ ≤ Finset.univ.sum (fun i : I =>
        4 * (oddEvenMerge64InputEnergy (bits i) - oddEvenMerge64ParityEnergy (bits i)) +
          if boolTrueCount (bits i) = 1 ∨ boolTrueCount (bits i) = 63 then 6 else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hlocal i
    _ = 4 * (Finset.univ.sum (fun i : I =>
          oddEvenMerge64InputEnergy (bits i) - oddEvenMerge64ParityEnergy (bits i))) +
        6 * (Finset.univ.sum (fun i : I =>
          if boolTrueCount (bits i) = 1 ∨ boolTrueCount (bits i) = 63
          then (1 : ℤ) else 0)) := by
      have hexsum : Finset.univ.sum (fun i : I =>
          if boolTrueCount (bits i) = 1 ∨ boolTrueCount (bits i) = 63
          then (6 : ℤ) else 0) =
          6 * Finset.univ.sum (fun i : I =>
            if boolTrueCount (bits i) = 1 ∨ boolTrueCount (bits i) = 63
            then (1 : ℤ) else 0) := by
        calc
          _ = Finset.univ.sum (fun i : I =>
              6 * (if boolTrueCount (bits i) = 1 ∨ boolTrueCount (bits i) = 63
                then (1 : ℤ) else 0)) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hp : boolTrueCount (bits i) = 1 ∨ boolTrueCount (bits i) = 63
            · simp [hp]
            · simp [hp]
          _ = _ := by rw [Finset.mul_sum]
      calc
        _ = Finset.univ.sum (fun i : I =>
              4 * (oddEvenMerge64InputEnergy (bits i) -
                oddEvenMerge64ParityEnergy (bits i))) +
            Finset.univ.sum (fun i : I =>
              if boolTrueCount (bits i) = 1 ∨ boolTrueCount (bits i) = 63
              then (6 : ℤ) else 0) := by rw [Finset.sum_add_distrib]
        _ = _ := by rw [← Finset.mul_sum, hexsum]

def canonicalPacketThresholdBits {N : Nat} (P : CanonicalPacketFamily N)
    (support : Finset (Fin N)) {A : Type} [LinearOrder A]
    (value : Fin N → A) (threshold : A → Bool)
    (hcontract : CanonicalPacketPortContract P support value)
    (i : Fin P.count) : Fin 64 → Bool := fun j =>
  threshold (value ((P.packet i).orderEmbOfFin (hcontract.2.2.2 i) j))

/-- Actual canonical receiver packets inherit the aggregated phase-drop
inequality, with the exceptional-profile count exposed packetwise. -/
theorem canonicalPacketFamily_energy_drop_with_exception
    {N : Nat} (P : CanonicalPacketFamily N) (support : Finset (Fin N))
    {A : Type} [LinearOrder A] (value : Fin N → A)
    (threshold : A → Bool) (hthreshold : Monotone threshold)
    (hcontract : CanonicalPacketPortContract P support value) :
    3 * (Finset.univ.sum (fun i : Fin P.count => oddEvenMerge64InputEnergy
      (canonicalPacketThresholdBits P support value threshold hcontract i))) ≤
      4 * (Finset.univ.sum (fun i : Fin P.count =>
        oddEvenMerge64InputEnergy
          (canonicalPacketThresholdBits P support value threshold hcontract i) -
        oddEvenMerge64ParityEnergy
          (canonicalPacketThresholdBits P support value threshold hcontract i))) +
        6 * (Finset.univ.sum (fun i : Fin P.count =>
          if boolTrueCount (canonicalPacketThresholdBits P support value threshold hcontract i) = 1 ∨
             boolTrueCount (canonicalPacketThresholdBits P support value threshold hcontract i) = 63
          then (1 : ℤ) else 0)) := by
  let bits : Fin P.count → Fin 64 → Bool := fun i =>
    canonicalPacketThresholdBits P support value threshold hcontract i
  have hsorted (i : Fin P.count) : Monotone (bits i) := by
    intro j k hjk
    apply hthreshold
    exact hcontract.1 i
      (Finset.orderEmbOfFin_mem (P.packet i) (hcontract.2.2.2 i) j)
      (Finset.orderEmbOfFin_mem (P.packet i) (hcontract.2.2.2 i) k)
      (Fin.le_def.mp (((P.packet i).orderEmbOfFin (hcontract.2.2.2 i)).monotone hjk))
  simpa [bits, canonicalPacketThresholdBits] using
    oddEvenMerge64_family_energy_drop_with_exception bits hsorted

/-- The explicit singleton exception budget is available on the actual
repaired receiver packet family produced by `flowA7`. -/
theorem flowA7_receiver_allCases_energy_drop_with_exception
    {d : Nat} {A : Type} [LinearOrder A]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → A)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (threshold : A → Bool) (hthreshold : Monotone threshold) :
    ∃ receiver : CanonicalPacketFamily (64 ^ d),
      ∃ hcontract : CanonicalPacketPortContract receiver
        (wireSets (flowSizes7 d hd) (t + 1) b)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v),
        3 * (Finset.univ.sum (fun i : Fin receiver.count =>
          oddEvenMerge64InputEnergy (canonicalPacketThresholdBits receiver
            (wireSets (flowSizes7 d hd) (t + 1) b)
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
            threshold hcontract i))) ≤
          4 * (Finset.univ.sum (fun i : Fin receiver.count =>
            oddEvenMerge64InputEnergy (canonicalPacketThresholdBits receiver
              (wireSets (flowSizes7 d hd) (t + 1) b)
              ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
              threshold hcontract i) -
            oddEvenMerge64ParityEnergy (canonicalPacketThresholdBits receiver
              (wireSets (flowSizes7 d hd) (t + 1) b)
              ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
              threshold hcontract i))) +
          6 * (Finset.univ.sum (fun i : Fin receiver.count =>
            if boolTrueCount (canonicalPacketThresholdBits receiver
                (wireSets (flowSizes7 d hd) (t + 1) b)
                ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
                threshold hcontract i) = 1 ∨
               boolTrueCount (canonicalPacketThresholdBits receiver
                (wireSets (flowSizes7 d hd) (t + 1) b)
                ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
                threshold hcontract i) = 63
            then (1 : ℤ) else 0)) := by
  obtain ⟨receiver, hcontract⟩ := flowA7_receiver_allCases_canonical
    hd t ht2 ht b hb hchildLevel v hpack
  exact ⟨receiver, hcontract, canonicalPacketFamily_energy_drop_with_exception
    receiver (wireSets (flowSizes7 d hd) (t + 1) b)
    ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
    threshold hthreshold hcontract⟩

/-- In a finite family of sorted profiles, every packet with between two and
62 ones contributes at least eight units of energy drop; all other profiles
still contribute a nonnegative amount. -/
theorem oddEvenMerge64_family_active_drop_lower_bound
    {I : Type} [Fintype I] [DecidableEq I]
    (bits : I -> Fin 64 -> Bool) (hsorted : forall i, Monotone (bits i)) :
    (8 : Int) * (((Finset.univ.filter (fun i : I =>
      2 <= boolTrueCount (bits i) /\ boolTrueCount (bits i) <= 62)).card : Int)) <=
      Finset.univ.sum (fun i : I =>
        oddEvenMerge64InputEnergy (bits i) - oddEvenMerge64ParityEnergy (bits i)) := by
  classical
  let active := Finset.univ.filter (fun i : I =>
    2 <= boolTrueCount (bits i) /\ boolTrueCount (bits i) <= 62)
  have hsubset := Finset.filter_subset (fun i : I => 2 <= boolTrueCount (bits i) /\ boolTrueCount (bits i) <= 62) Finset.univ
  have hnonneg (i : I) :
      0 <= oddEvenMerge64InputEnergy (bits i) - oddEvenMerge64ParityEnergy (bits i) := by
    have h := oddEvenMerge64_monotone_parity_energy_le_input (bits i) (hsorted i)
    omega
  have hactive (i : I) (hi : 2 <= boolTrueCount (bits i) /\
      boolTrueCount (bits i) <= 62) :
      8 <= oddEvenMerge64InputEnergy (bits i) - oddEvenMerge64ParityEnergy (bits i) := by
    exact oddEvenMerge64_monotone_energy_drop_ge_eight (bits i) (hsorted i)
      hi.1 hi.2
  calc
    (8 : Int) * (active.card : Int) = active.sum (fun _ => (8 : Int)) := by
      simp [active, mul_comm]
    _ <= active.sum (fun i =>
        oddEvenMerge64InputEnergy (bits i) - oddEvenMerge64ParityEnergy (bits i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hactive i (Finset.mem_filter.mp hi).2
    _ <= Finset.univ.sum (fun i =>
        oddEvenMerge64InputEnergy (bits i) - oddEvenMerge64ParityEnergy (bits i)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro i hi hnot
        exact hnonneg i)
/-- Summed over a canonical sorted packet family, parity-lane energy is
exactly twice the number of odd threshold counts. -/
theorem canonicalPacketFamily_parity_energy_eq_residual
    {N : Nat} (P : CanonicalPacketFamily N) (support : Finset (Fin N))
    {A : Type} [LinearOrder A] (value : Fin N → A) (threshold : A → Bool)
    (hthreshold : Monotone threshold)
    (hcontract : CanonicalPacketPortContract P support value) :
    (∑ i : Fin P.count, oddEvenMerge64ParityEnergy
      (fun j => threshold
        (value ((P.packet i).orderEmbOfFin (hcontract.2.2.2 i) j)))) =
      ∑ i : Fin P.count,
        if boolTrueCount (fun j => threshold
          (value ((P.packet i).orderEmbOfFin (hcontract.2.2.2 i) j))) % 2 = 0
        then 0 else 2 := by
  apply Finset.sum_congr rfl
  intro i hi
  apply oddEvenMerge64_monotone_parity_energy_eq_residual
  intro j k hjk
  apply hthreshold
  exact hcontract.1 i
    (Finset.orderEmbOfFin_mem (P.packet i) (hcontract.2.2.2 i) j)
    (Finset.orderEmbOfFin_mem (P.packet i) (hcontract.2.2.2 i) k)
    (Fin.le_def.mp (((P.packet i).orderEmbOfFin (hcontract.2.2.2 i)).monotone hjk))

/-- Across an actual canonical receiver packet family, splitting every sorted
64-wire threshold profile into parity lanes preserves the sum of fractional
target L1 errors exactly, packet by packet. -/
theorem canonicalPacketFamily_parity_rebin_L1_exact
    {N : Nat} (P : CanonicalPacketFamily N) (support : Finset (Fin N))
    {A : Type} [LinearOrder A] (value : Fin N → A)
    (threshold : A → Bool) (hthreshold : Monotone threshold)
    (q : Fin P.count → Nat) (frac : Fin P.count → Real)
    (hq : ∀ i, q i < 64) (hfrac0 : ∀ i, 0 ≤ frac i)
    (hfrac1 : ∀ i, frac i ≤ 1)
    (hcontract : CanonicalPacketPortContract P support value) :
    (∑ i : Fin P.count, ∑ lane : Bool,
      |(boolTrueCount (fun j : Fin 32 =>
          threshold (value ((P.packet i).orderEmbOfFin (hcontract.2.2.2 i)
            (if lane then oddWire 32 j else evenWire 32 j)))) : Real) -
        oddEvenMerge64_parityMean lane (q i) (frac i)|) =
      ∑ i : Fin P.count,
        |(boolTrueCount (fun j : Fin 64 =>
          threshold (value ((P.packet i).orderEmbOfFin (hcontract.2.2.2 i) j))) : Real) -
          (q i + frac i)| := by
  apply Finset.sum_congr rfl
  intro i hi
  let bits : Fin 64 → Bool := fun j =>
    threshold (value ((P.packet i).orderEmbOfFin (hcontract.2.2.2 i) j))
  have hbits : Monotone bits := by
    intro j k hjk
    apply hthreshold
    exact hcontract.1 i
      (Finset.orderEmbOfFin_mem (P.packet i) (hcontract.2.2.2 i) j)
      (Finset.orderEmbOfFin_mem (P.packet i) (hcontract.2.2.2 i) k)
      (Fin.le_def.mp (((P.packet i).orderEmbOfFin (hcontract.2.2.2 i)).monotone hjk))
  have hlocal := oddEvenMerge64_parity_rebin_L1_exact bits hbits
    (q i) (frac i) (hq i) (hfrac0 i) (hfrac1 i)
  simpa [bits] using hlocal

/-- The exact parity-lane L1 rebinning identity holds at the actual
`WireFlow` receiver boundary, for the repaired values and any packetwise
fractional target. -/
theorem flowA7_receiver_allCases_parity_rebin_L1_exact
    {d : Nat} {A : Type} [LinearOrder A]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → A)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (threshold : A → Bool) (hthreshold : Monotone threshold)
    (q : Nat → Nat) (frac : Nat → Real)
    (hq : ∀ i : Nat, q i < 64)
    (hfrac0 : ∀ i : Nat, 0 ≤ frac i)
    (hfrac1 : ∀ i : Nat, frac i ≤ 1) :
    ∃ receiver : CanonicalPacketFamily (64 ^ d),
      ∃ hcontract : CanonicalPacketPortContract receiver
        (wireSets (flowSizes7 d hd) (t + 1) b)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v),
        (∑ i : Fin receiver.count, ∑ lane : Bool,
          |(boolTrueCount (fun j : Fin 32 =>
              threshold ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v
                ((receiver.packet i).orderEmbOfFin (hcontract.2.2.2 i)
                  (if lane then oddWire 32 j else evenWire 32 j)))) : Real) -
            oddEvenMerge64_parityMean lane (q i.val) (frac i.val)|) =
        ∑ i : Fin receiver.count,
          |(boolTrueCount (fun j : Fin 64 =>
              threshold ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v
                ((receiver.packet i).orderEmbOfFin (hcontract.2.2.2 i) j))) : Real) -
            (q i.val + frac i.val)| := by
  obtain ⟨receiver, hcontract⟩ := flowA7_receiver_allCases_canonical
    hd t ht2 ht b hb hchildLevel v hpack
  refine ⟨receiver, hcontract, ?_⟩
  exact canonicalPacketFamily_parity_rebin_L1_exact receiver
    (wireSets (flowSizes7 d hd) (t + 1) b)
    ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
    threshold hthreshold (fun i => q i.val) (fun i => frac i.val)
    (fun i => hq i.val) (fun i => hfrac0 i.val) (fun i => hfrac1 i.val) hcontract

/-- Exact actual-receiver parity-energy residual, summed over packets and any
finite family of monotone thresholds. -/
theorem flowA7_receiver_allCases_parityEnergy_exact_multi
    {d : Nat} {A T : Type} [LinearOrder A] [Fintype T] [DecidableEq T]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → A)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (threshold : T → A → Bool)
    (hthreshold : ∀ theta, Monotone (threshold theta)) :
    ∃ receiver : CanonicalPacketFamily (64 ^ d),
      ∃ hcontract : CanonicalPacketPortContract receiver
        (wireSets (flowSizes7 d hd) (t + 1) b)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v),
        (∑ theta : T, ∑ i : Fin receiver.count, oddEvenMerge64ParityEnergy
          (fun j => threshold theta ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v
            ((receiver.packet i).orderEmbOfFin (hcontract.2.2.2 i) j)))) =
        ∑ theta : T, ∑ i : Fin receiver.count,
          if boolTrueCount (fun j => threshold theta
            ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v
              ((receiver.packet i).orderEmbOfFin (hcontract.2.2.2 i) j))) % 2 = 0
          then 0 else 2 := by
  obtain ⟨receiver, hcontract⟩ := flowA7_receiver_allCases_canonical
    hd t ht2 ht b hb hchildLevel v hpack
  refine ⟨receiver, hcontract, ?_⟩
  apply Finset.sum_congr rfl
  intro theta htheta
  exact canonicalPacketFamily_parity_energy_eq_residual receiver
    (wireSets (flowSizes7 d hd) (t + 1) b)
    ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
    (threshold theta) (hthreshold theta) hcontract

/-- Exact doubled centered energy of the two physical 32-rank halves after a
64-wire merge with `H` Boolean ones. -/
theorem oddEvenMerge64_parallel_monotone_parity_energy_le_input
    {I : Type} [Fintype I] [DecidableEq I] (v : I → Fin 64 → Bool)
    (hsorted : ∀ p, Monotone (v p)) :
    (∑ p : I, oddEvenMerge64ParityEnergy (v p)) ≤
      ∑ p : I, oddEvenMerge64InputEnergy (v p) := by
  apply Finset.sum_le_sum
  intro p hp
  exact oddEvenMerge64_monotone_parity_energy_le_input (v p) (hsorted p)

theorem oddEvenMerge64_parallel_dealt_energy_le_input {I : Type}
    [Fintype I] [DecidableEq I] (v : I → Fin 64 → Bool)
    (hA : ∀ p, Monotone (fun i : Fin 32 => v p (Fin.castAdd 32 i)))
    (hB : ∀ p, Monotone (fun i : Fin 32 => v p (Fin.natAdd 32 i))) :
    (∑ p : I, oddEvenMerge64DealtEnergy (v p)) ≤
      ∑ p : I, oddEvenMerge64InputEnergy (v p) := by
  apply Finset.sum_le_sum
  intro p hp
  simpa only [oddEvenMerge64DealtEnergy, oddEvenMerge64InputEnergy] using
    oddEvenMerge64_dealt_energy_le_input (v p) (hA p) (hB p)

theorem oddEvenMerge64_scatteredFamily_dealt_energy_le_input
    {I : Type} [Fintype I] [DecidableEq I] {N : Nat}
    (e : I → Fin 64 ↪o Fin N) (bits : Fin N → Bool)
    (hsorted : ∀ p, Monotone (fun i : Fin 64 => bits (e p i))) :
    (∑ p : I, oddEvenMerge64DealtEnergy (fun i => bits (e p i))) ≤
      ∑ p : I, oddEvenMerge64InputEnergy (fun i => bits (e p i)) := by
  apply oddEvenMerge64_parallel_dealt_energy_le_input
  · intro p
    apply (hsorted p).comp
    intro i j hij
    apply Fin.mk_le_mk.mpr
    exact Fin.mk_le_mk.mp hij
  · intro p
    apply (hsorted p).comp
    intro i j hij
    apply Fin.mk_le_mk.mpr
    have hv := Fin.mk_le_mk.mp hij
    change 32 + i.val ≤ 32 + j.val
    omega

theorem oddEvenMerge64_rankSortedFamily_dealt_energy_le_input
    {I : Type} [Fintype I] [DecidableEq I] {N : Nat} {A : Type}
    [Preorder A] (e : I → Fin 64 ↪o Fin N)
    (support : I → Finset (Fin N)) (value : Fin N → A) (threshold : A → Bool)
    (hthreshold : Monotone threshold)
    (hsorted : ∀ p, RankSortedOn (support p) value)
    (hempty : ∀ p i, e p i ∈ support p) :
    (∑ p : I, oddEvenMerge64DealtEnergy
      (fun i => threshold (value (e p i)))) ≤
      ∑ p : I, oddEvenMerge64InputEnergy
        (fun i => threshold (value (e p i))) := by
  apply oddEvenMerge64_scatteredFamily_dealt_energy_le_input e
    (fun w => threshold (value w))
  intro p i j hij
  apply hthreshold
  exact hsorted p (hempty p i) (hempty p j)
    (Fin.le_def.mp ((e p).monotone hij))

theorem canonicalPacketFamily_dealt_energy_le_input
    {N : Nat} (P : CanonicalPacketFamily N) (support : Finset (Fin N))
    {A : Type} [LinearOrder A] (value : Fin N → A) (threshold : A → Bool)
    (hthreshold : Monotone threshold)
    (hcontract : CanonicalPacketPortContract P support value) :
    (∑ i : Fin P.count, oddEvenMerge64DealtEnergy
      (fun j => threshold
        (value ((P.packet i).orderEmbOfFin (hcontract.2.2.2 i) j)))) ≤
      ∑ i : Fin P.count, oddEvenMerge64InputEnergy
        (fun j => threshold
          (value ((P.packet i).orderEmbOfFin (hcontract.2.2.2 i) j))) := by
  let e : Fin P.count → Fin 64 ↪o Fin N := fun i =>
    (P.packet i).orderEmbOfFin (hcontract.2.2.2 i)
  apply oddEvenMerge64_rankSortedFamily_dealt_energy_le_input
    e P.packet value threshold hthreshold hcontract.1
  intro i j
  exact Finset.orderEmbOfFin_mem (P.packet i) (hcontract.2.2.2 i) j

theorem canonicalPacketFamily_parity_energy_le_input
    {N : Nat} (P : CanonicalPacketFamily N) (support : Finset (Fin N))
    {A : Type} [LinearOrder A] (value : Fin N → A) (threshold : A → Bool)
    (hthreshold : Monotone threshold)
    (hcontract : CanonicalPacketPortContract P support value) :
    (∑ i : Fin P.count, oddEvenMerge64ParityEnergy
      (fun j => threshold
        (value ((P.packet i).orderEmbOfFin (hcontract.2.2.2 i) j)))) ≤
      ∑ i : Fin P.count, oddEvenMerge64InputEnergy
        (fun j => threshold
          (value ((P.packet i).orderEmbOfFin (hcontract.2.2.2 i) j))) := by
  apply Finset.sum_le_sum
  intro i hi
  apply oddEvenMerge64_monotone_parity_energy_le_input
  intro j k hjk
  apply hthreshold
  exact hcontract.1 i
    (Finset.orderEmbOfFin_mem (P.packet i) (hcontract.2.2.2 i) j)
    (Finset.orderEmbOfFin_mem (P.packet i) (hcontract.2.2.2 i) k)
    (Fin.le_def.mp (((P.packet i).orderEmbOfFin (hcontract.2.2.2 i)).monotone hjk))

/-- The local dealt-lane contraction at the actual next WireFlow receiver,
summed over any finite family of monotone Boolean thresholds. -/
theorem flowA7_receiver_allCases_packetEnergy_contraction_multi
    {d : Nat} {A T : Type} [LinearOrder A] [Fintype T] [DecidableEq T]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → A)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (threshold : T → A → Bool)
    (hthreshold : ∀ theta, Monotone (threshold theta)) :
    ∃ receiver : CanonicalPacketFamily (64 ^ d),
      ∃ hcontract : CanonicalPacketPortContract receiver
        (wireSets (flowSizes7 d hd) (t + 1) b)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v),
        (∑ theta : T, ∑ i : Fin receiver.count, oddEvenMerge64DealtEnergy
          (fun j => threshold theta ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v
            ((receiver.packet i).orderEmbOfFin (hcontract.2.2.2 i) j)))) ≤
        ∑ theta : T, ∑ i : Fin receiver.count, oddEvenMerge64InputEnergy
          (fun j => threshold theta ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v
            ((receiver.packet i).orderEmbOfFin (hcontract.2.2.2 i) j))) := by
  obtain ⟨receiver, hcontract⟩ := flowA7_receiver_allCases_canonical
    hd t ht2 ht b hb hchildLevel v hpack
  refine ⟨receiver, hcontract, ?_⟩
  apply Finset.sum_le_sum
  intro theta htheta
  exact canonicalPacketFamily_dealt_energy_le_input receiver
    (wireSets (flowSizes7 d hd) (t + 1) b)
    ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
    (threshold theta) (hthreshold theta) hcontract

/-- Specialization of the receiver contraction to one threshold. -/
theorem flowA7_receiver_allCases_packetEnergy_contraction
    {d : Nat} {A : Type} [LinearOrder A]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → A)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (threshold : A → Bool) (hthreshold : Monotone threshold) :
    ∃ receiver : CanonicalPacketFamily (64 ^ d),
      ∃ hcontract : CanonicalPacketPortContract receiver
        (wireSets (flowSizes7 d hd) (t + 1) b)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v),
        (∑ i : Fin receiver.count, oddEvenMerge64DealtEnergy
          (fun j => threshold ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v
            ((receiver.packet i).orderEmbOfFin (hcontract.2.2.2 i) j)))) ≤
        ∑ i : Fin receiver.count, oddEvenMerge64InputEnergy
          (fun j => threshold ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v
            ((receiver.packet i).orderEmbOfFin (hcontract.2.2.2 i) j))) := by
  obtain ⟨receiver, hcontract⟩ := flowA7_receiver_allCases_canonical
    hd t ht2 ht b hb hchildLevel v hpack
  refine ⟨receiver, hcontract, ?_⟩
  exact canonicalPacketFamily_dealt_energy_le_input receiver
    (wireSets (flowSizes7 d hd) (t + 1) b)
    ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
    threshold hthreshold hcontract

/-- The exact parity residual is bounded by input energy at each receiver,
for any finite threshold family. -/
theorem flowA7_receiver_allCases_parityEnergy_contraction_multi
    {d : Nat} {A T : Type} [LinearOrder A] [Fintype T] [DecidableEq T]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → A)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (threshold : T → A → Bool)
    (hthreshold : ∀ theta, Monotone (threshold theta)) :
    ∃ receiver : CanonicalPacketFamily (64 ^ d),
      ∃ hcontract : CanonicalPacketPortContract receiver
        (wireSets (flowSizes7 d hd) (t + 1) b)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v),
        (∑ theta : T, ∑ i : Fin receiver.count, oddEvenMerge64ParityEnergy
          (fun j => threshold theta ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v
            ((receiver.packet i).orderEmbOfFin (hcontract.2.2.2 i) j)))) ≤
        ∑ theta : T, ∑ i : Fin receiver.count, oddEvenMerge64InputEnergy
          (fun j => threshold theta ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v
            ((receiver.packet i).orderEmbOfFin (hcontract.2.2.2 i) j))) := by
  obtain ⟨receiver, hcontract⟩ := flowA7_receiver_allCases_canonical
    hd t ht2 ht b hb hchildLevel v hpack
  refine ⟨receiver, hcontract, ?_⟩
  apply Finset.sum_le_sum
  intro theta htheta
  exact canonicalPacketFamily_parity_energy_le_input receiver
    (wireSets (flowSizes7 d hd) (t + 1) b)
    ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v)
    (threshold theta) (hthreshold theta) hcontract

/-- The even/odd 32-rank lanes of an actual canonical receiver partition
reindex the next `WireFlow` register's threshold count exactly. This is the
local owner-map bridge from parity supports to scheduled destination counts. -/
theorem flowA7_receiver_allCases_parityOwnerCount
    {d : Nat} {A : Type} [LinearOrder A]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → A)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (threshold : A → Bool) :
    ∃ receiver : CanonicalPacketFamily (64 ^ d),
      ∃ hcontract : CanonicalPacketPortContract receiver
        (wireSets (flowSizes7 d hd) (t + 1) b)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v),
        (∑ z : Fin receiver.count × Bool,
          assignedRankCount
            (wireSetPacketRankOwner (flowSizes7 d hd) (t + 1) (by omega)
              (fun z => canonicalPacketParityEmbedding receiver hcontract.2.2.2 z) z)
            (fun _ i => threshold ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v
              (canonicalPacketParityEmbedding receiver hcontract.2.2.2 z i))) b 0) =
          trueCountOn (wireSets (flowSizes7 d hd) (t + 1) b)
            (fun w => threshold ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v w)) := by
  obtain ⟨receiver, hcontract⟩ := flowA7_receiver_allCases_canonical
    hd t ht2 ht b hb hchildLevel v hpack
  refine ⟨receiver, hcontract, ?_⟩
  let lanes : Fin receiver.count × Bool → Fin 32 ↪ Fin (64 ^ d) :=
    fun z => canonicalPacketParityEmbedding receiver hcontract.2.2.2 z
  have hdis : ∀ {z z' : Fin receiver.count × Bool}, z ≠ z' →
      ∀ i j, lanes z i ≠ lanes z' j := by
    simpa [lanes] using canonicalPacketParityEmbeddings_disjoint receiver
      (wireSets (flowSizes7 d hd) (t + 1) b)
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) hcontract
  have hcover : ∀ w ∈ wireSets (flowSizes7 d hd) (t + 1) b,
      ∃ z i, lanes z i = w := by
    simpa [lanes] using canonicalPacketParityEmbeddings_cover receiver
      (wireSets (flowSizes7 d hd) (t + 1) b)
      ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v) hcontract
  simpa [lanes] using packetRankOwner_trueCountOn_eq_of_local_partition
    (flowSizes7 d hd) (t + 1) (by omega) lanes
    hdis b hcover
    (fun w => threshold ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v w))

/-- The actual even/odd packet lanes assigned to next-time WireFlow registers
recover the threshold count on their intersection with the current receiver.
This is the destination-restricted form needed to turn owner-profile errors
into physical next-register errors. -/
theorem flowA7_receiver_allCases_parityOwnerCount_intersection
    {d : Nat} {A : Type} [LinearOrder A]
    (hd : 7 ≤ d) (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (htnext : t + 1 < tf7 d)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchildLevel : b.l < d)
    (v : Fin (64 ^ d) → A)
    (hpack : ∀ q : KBag 64 d,
      PacketSortedOn (wireSets (flowSizes7 d hd) t q) v)
    (threshold : A → Bool) :
    ∃ receiver : CanonicalPacketFamily (64 ^ d),
      ∃ hcontract : CanonicalPacketPortContract receiver
        (wireSets (flowSizes7 d hd) (t + 1) b)
        ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v),
      ∀ destination : KBag 64 d,
        (∑ z : Fin receiver.count × Bool,
          assignedRankCount
            (wireSetPacketRankOwner (flowSizes7 d hd) (t + 2) (by omega)
              (fun z => canonicalPacketParityEmbedding receiver hcontract.2.2.2 z) z)
            (fun _ i => threshold ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v
              (canonicalPacketParityEmbedding receiver hcontract.2.2.2 z i)))
            destination 0) =
          trueCountOn
            (wireSets (flowSizes7 d hd) (t + 1) b ∩
              wireSets (flowSizes7 d hd) (t + 2) destination)
            (fun w => threshold ((flowA7_sourcePortRepairStage hd t ht2 ht).exec v w)) := by
  obtain ⟨receiver, hcontract⟩ := flowA7_receiver_allCases_canonical
    hd t ht2 ht b hb hchildLevel v hpack
  refine ⟨receiver, hcontract, ?_⟩
  intro destination
  let F := flowSizes7 d hd
  let stageV := (flowA7_sourcePortRepairStage hd t ht2 ht).exec v
  let support := wireSets F (t + 1) b
  let lanes : Fin receiver.count × Bool → Fin 32 ↪ Fin (64 ^ d) :=
    fun z => canonicalPacketParityEmbedding receiver hcontract.2.2.2 z
  have hdis : ∀ {z z' : Fin receiver.count × Bool}, z ≠ z' →
      ∀ i j, lanes z i ≠ lanes z' j := by
    simpa [lanes] using canonicalPacketParityEmbeddings_disjoint receiver
      support stageV hcontract
  have hsubset : ∀ z i, lanes z i ∈ support := by
    intro z i
    have hmem := canonicalPacketParityEmbedding_mem receiver
      hcontract.2.2.2 z i
    change lanes z i ∈ wireSets (flowSizes7 d hd) (t + 1) b
    rw [← hcontract.2.1]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨z.1, hmem⟩
  have hcover : ∀ w ∈ support, ∃ z i, lanes z i = w := by
    simpa [lanes] using canonicalPacketParityEmbeddings_cover receiver
      support stageV hcontract
  have hcount := packetRankOwner_trueCountOn_intersection
    F (t + 2) (by omega) lanes hdis support hsubset hcover destination
    (fun w => threshold (stageV w))
  simpa [F, stageV, support, lanes] using hcount

theorem oddEvenMerge64_physicalHalf_doubledEnergy (H : Nat) (hH : H ≤ 64) :
    let a : ℤ := (min 32 (H - 32) : Nat)
    let b : ℤ := (min 32 H : Nat)
    (2 * a - H) ^ 2 + (2 * b - H) ^ 2 =
      2 * ((min H (64 - H) : Nat) : ℤ) ^ 2 := by
  dsimp
  by_cases h : H ≤ 32
  · have hminA : min 32 (H - 32) = 0 := by omega
    have hminB : min 32 H = H := Nat.min_eq_right h
    have hminH : min H (64 - H) = H := by omega
    rw [hminA, hminB, hminH]
    ring
  · have hlow : 32 ≤ H := by omega
    have hsub_le : H - 32 ≤ 32 := by omega
    have hminA : min 32 (H - 32) = H - 32 := Nat.min_eq_right hsub_le
    have hminB : min 32 H = 32 := Nat.min_eq_left hlow
    have hminH : min H (64 - H) = 64 - H := by omega
    rw [hminA, hminB, hminH]
    rw [Int.natCast_sub hlow, Int.natCast_sub hH]
    ring

/-- Actual values on a `WireFlow` rank block have exactly the ideal sorted
profile count. This connects the abstract profile lemma to concrete `blockOf`
ports without choosing or reordering their physical wire labels. -/
theorem trueCountOn_blockOf_profile {N : Nat} (s : Finset (Fin N))
    (v : Fin N → Bool) (hv : Monotone (v ∘ s.orderEmbOfFin rfl)) (lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ s.card) :
    trueCountOn (blockOf s lo hi) v = profileInterval s.card (trueCountOn s v) lo hi := by
  let e := blockRankEmbedding s lo hi hlo hhi
  have hcount := boolTrueCount_embedding (blockOf s lo hi) e
    (blockRankEmbedding_range s lo hi hlo hhi) v
  have hinterval := sortedBool_rankInterval_trueCount (v ∘ s.orderEmbOfFin rfl) hv lo hi hlo hhi
  have htotal := boolTrueCount_orderEmb s rfl v
  have heq : v ∘ e = fun j : Fin (hi - lo) =>
      (v ∘ s.orderEmbOfFin rfl) ⟨lo + j.val, by
        have hsum := Nat.add_sub_of_le hlo
        calc
          lo + j.val < lo + (hi - lo) := Nat.add_lt_add_left j.isLt _
          _ = hi := hsum
          _ ≤ s.card := hhi⟩ := by
    funext j
    rfl
  rw [← hcount, heq, hinterval, ← htotal]

theorem trueCountOn_eq_card_filter {N : Nat} (s : Finset (Fin N)) (v : Fin N → Bool) :
    trueCountOn s v = (s.filter (fun w => v w = true)).card := by
  classical
  let e : {w : s // v w.val = true} ≃
      {w // w ∈ s.filter (fun x => v x = true)} :=
    { toFun := fun w => ⟨w.val.val, by simp [w.val.property, w.property]⟩
      invFun := fun w => ⟨⟨w.val, (Finset.mem_filter.mp w.property).1⟩,
        (Finset.mem_filter.mp w.property).2⟩
      left_inv := by intro w; cases w; rfl
      right_inv := by intro w; cases w; rfl }
  unfold trueCountOn
  rw [Fintype.card_congr e]
  exact Fintype.card_coe (s.filter (fun x => v x = true))

/-- Injective relabeling preserves the Boolean count. -/
theorem trueCountOn_image {m N : Nat} (s : Finset (Fin m)) (f : Fin m → Fin N)
    (hf : Function.Injective f) (v : Fin N → Bool) :
    trueCountOn (s.image f) v = trueCountOn s (v ∘ f) := by
  let e : Fin s.card ↪ Fin N :=
    ⟨fun i => f (s.orderEmbOfFin rfl i), fun i j hij => by
      apply (s.orderEmbOfFin rfl).injective
      exact hf hij⟩
  have hrange : Set.range e = {w | w ∈ s.image f} := by
    ext w
    simp only [Set.mem_range, Set.mem_setOf_eq, Finset.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨s.orderEmbOfFin rfl i, Finset.orderEmbOfFin_mem _ rfl _, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, rfl⟩ := exists_orderEmb_eq hx
      exact ⟨i, rfl⟩
  calc
    trueCountOn (s.image f) v = boolTrueCount (v ∘ e) :=
      (boolTrueCount_embedding (s.image f) e hrange v).symm
    _ = boolTrueCount ((v ∘ f) ∘ s.orderEmbOfFin rfl) := by rfl
    _ = trueCountOn s (v ∘ f) := boolTrueCount_orderEmb s rfl (v ∘ f)

/-- Threshold counts add across disjoint finite supports. -/
theorem trueCountOn_union_disjoint {N : Nat} (A B : Finset (Fin N))
    (hdis : Disjoint A B) (v : Fin N → Bool) :
    trueCountOn (A ∪ B) v = trueCountOn A v + trueCountOn B v := by
  let p : Fin N → Prop := fun w => v w = true
  have hfilter : (A ∪ B).filter p = A.filter p ∪ B.filter p := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hdis' : Disjoint (A.filter p) (B.filter p) :=
    hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  calc
    trueCountOn (A ∪ B) v = ((A ∪ B).filter p).card := trueCountOn_eq_card_filter _ _
    _ = (A.filter p).card + (B.filter p).card := by
      rw [hfilter, Finset.card_union_of_disjoint hdis']
    _ = trueCountOn A v + trueCountOn B v := by
      rw [← trueCountOn_eq_card_filter A v, ← trueCountOn_eq_card_filter B v]

theorem trueCountOn_biUnion {ι : Type*} {N : Nat} [DecidableEq ι] (I : Finset ι)
    (A : ι → Finset (Fin N))
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j))
    (v : Fin N → Bool) :
    trueCountOn (I.biUnion A) v = ∑ i ∈ I, trueCountOn (A i) v := by
  have hdis' : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint ((A i).filter (fun w => v w = true))
        ((A j).filter (fun w => v w = true)) := by
    intro i hi j hj hij
    exact (hdis i hi j hj hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [trueCountOn_eq_card_filter, Finset.filter_biUnion, Finset.card_biUnion hdis']
  simp_rw [← trueCountOn_eq_card_filter]

theorem sortedWireBags_intervalPartition_L1_exact {c N m p q : Nat} (frac : Real)
    (S : Fin c → Finset (Fin N)) (v : Fin c → Fin N → Bool)
    (hcard : ∀ packet, (S packet).card = m)
    (hsorted : ∀ packet, Monotone (v packet ∘ (S packet).orderEmbOfFin rfl))
    (cuts : Fin c → Nat → Nat) (hstart : ∀ packet, cuts packet 0 = 0)
    (hcuts : ∀ packet, Monotone (cuts packet))
    (hcutBound : ∀ packet i, cuts packet i ≤ m)
    (hend : ∀ packet, cuts packet p = m) (hq : q < m)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ packet : Fin c, ∑ i ∈ range p,
      |(trueCountOn (blockOf (S packet) (cuts packet i) (cuts packet (i + 1)))
          (v packet) : Real) -
        profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))|) =
      ∑ packet : Fin c, |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := by
  let V : Fin c → Fin m → Bool := fun packet i =>
    v packet ((S packet).orderEmbOfFin rfl (Fin.cast (hcard packet).symm i))
  have hV : ∀ packet, Monotone (V packet) := by
    intro packet i j hij
    apply hsorted packet
    apply Fin.le_iff_val_le_val.mpr
    exact Fin.le_iff_val_le_val.mp hij
  have htotal (packet : Fin c) : boolTrueCount (V packet) = trueCountOn (S packet) (v packet) := by
    calc
      boolTrueCount (V packet) = boolTrueCount (v packet ∘ (S packet).orderEmbOfFin rfl) := by
        dsimp [V]
        exact boolTrueCount_finCast (hcard packet).symm (v packet ∘ (S packet).orderEmbOfFin rfl)
      _ = trueCountOn (S packet) (v packet) := boolTrueCount_orderEmb (S packet) rfl (v packet)
  calc
    _ = ∑ packet : Fin c, ∑ i ∈ range p,
        |(boolTrueCount (fun j : Fin (cuts packet (i + 1) - cuts packet i) =>
            V packet ⟨cuts packet i + j.val, by
              have hab : cuts packet i ≤ cuts packet (i + 1) := hcuts packet (Nat.le_succ i)
              have hsum := Nat.add_sub_of_le hab
              calc
                cuts packet i + j.val < cuts packet i + (cuts packet (i + 1) - cuts packet i) :=
                  Nat.add_lt_add_left j.isLt _
                _ = cuts packet (i + 1) := hsum
                _ ≤ m := hcutBound packet (i + 1)⟩) : Real) -
          profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))| := by
      apply Finset.sum_congr rfl
      intro packet _
      apply Finset.sum_congr rfl
      intro i hi
      have hcutCard : cuts packet (i + 1) ≤ (S packet).card := by
        rw [hcard packet]
        exact hcutBound packet (i + 1)
      have hblock := trueCountOn_blockOf_profile (S packet) (v packet)
        (hsorted packet) (cuts packet i) (cuts packet (i + 1))
        (hcuts packet (Nat.le_succ i)) hcutCard
      have hinterval := sortedBool_rankInterval_trueCount (V packet) (hV packet)
        (cuts packet i) (cuts packet (i + 1)) (hcuts packet (Nat.le_succ i))
        (hcutBound packet (i + 1))
      rw [hcard packet] at hblock
      rw [hblock, ← htotal packet, ← hinterval]
    _ = ∑ packet : Fin c, |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := by
      apply Finset.sum_congr rfl
      intro packet _
      have hVbound : boolTrueCount (V packet) ≤ m := by
        simpa [boolTrueCount] using
          (Fintype.card_subtype_le (fun i : Fin m => V packet i = true))
      have hprofile := profileInterval_partition_L1_exact m p
        (boolTrueCount (V packet)) q frac (cuts packet) (hstart packet) (hcuts packet)
        (hend packet) hVbound hq hfrac0 hfrac1
      have hinterval' (i : Nat) (hi : i < p) :
          boolTrueCount (fun j : Fin (cuts packet (i + 1) - cuts packet i) =>
            V packet ⟨cuts packet i + j.val, by
              have hab : cuts packet i ≤ cuts packet (i + 1) := hcuts packet (Nat.le_succ i)
              have hsum := Nat.add_sub_of_le hab
              calc
                cuts packet i + j.val < cuts packet i + (cuts packet (i + 1) - cuts packet i) :=
                  Nat.add_lt_add_left j.isLt _
                _ = cuts packet (i + 1) := hsum
                _ ≤ m := hcutBound packet (i + 1)⟩) =
            profileInterval m (boolTrueCount (V packet)) (cuts packet i) (cuts packet (i + 1)) :=
        sortedBool_rankInterval_trueCount (V packet) (hV packet)
          (cuts packet i) (cuts packet (i + 1)) (hcuts packet (Nat.le_succ i))
          (hcutBound packet (i + 1))
      calc
        _ = ∑ i ∈ range p,
            |(profileInterval m (boolTrueCount (V packet)) (cuts packet i) (cuts packet (i + 1)) : Real) -
              profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hinterval' i (mem_range.mp hi)]
        _ = |(boolTrueCount (V packet) : Real) - (q + frac)| := hprofile
        _ = |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := by
          rw [htotal packet]

/-- The 66 consecutive rank pieces that a sender routes: two separate
halves of its parent fringe and one middle block for each child. -/
def senderRankCut (up down i : Nat) : Nat :=
  if i = 0 then 0 else if i ≤ 65 then up / 2 + (i - 1) * down else up + 64 * down

theorem senderRankCut_le (up down i : Nat) : senderRankCut up down i ≤ up + 64 * down := by
  unfold senderRankCut
  split_ifs with hi0 hi65
  · omega
  · have hmul : (i - 1) * down ≤ 64 * down := Nat.mul_le_mul_right down (by omega)
    omega
  · rfl

theorem senderRankCut_mono (up down : Nat) : Monotone (senderRankCut up down) := by
  intro i j hij
  by_cases hi0 : i = 0
  · simp [senderRankCut, hi0]
  · by_cases hj65 : j ≤ 65
    · have hi65 : i ≤ 65 := le_trans hij hj65
      have hj0 : j ≠ 0 := by
        intro hj
        subst j
        exact hi0 (by omega)
      have hsub : i - 1 ≤ j - 1 := by omega
      have hmul := Nat.mul_le_mul_right down hsub
      simp [senderRankCut, hi0, hi65, hj65, hj0]
      exact hmul
    · have hle := senderRankCut_le up down i
      have hj0 : j ≠ 0 := by
        intro hj
        subst j
        exact hi0 (by omega)
      have hcutj : senderRankCut up down j = up + 64 * down := by
        simp [senderRankCut, hj0, hj65]
      rw [hcutj]
      exact hle

theorem senderRankCut_start (up down : Nat) : senderRankCut up down 0 = 0 := by
  simp [senderRankCut]

theorem senderRankCut_end (up down : Nat) : senderRankCut up down 66 = up + 64 * down := by
  simp [senderRankCut]

/-- The two omitted frontier fringe targets have total mass at most the
sender's up-flow capacity. -/
theorem senderRankCut_fringe_mean_sum_le (up down q : Nat) (frac : Real)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ ({0, 65} : Finset Nat),
      profileIntervalMean (up + 64 * down) q frac
        (senderRankCut up down i) (senderRankCut up down (i + 1))) ≤ up := by
  have hmean (i : Nat) (hi : i ∈ ({0, 65} : Finset Nat)) :
      profileIntervalMean (up + 64 * down) q frac
        (senderRankCut up down i) (senderRankCut up down (i + 1)) ≤
        ((senderRankCut up down (i + 1) - senderRankCut up down i : Nat) : Real) := by
    have hi_lt : i < 66 := by simp at hi; omega
    have hmono := senderRankCut_mono up down (Nat.le_succ i)
    have hbound := senderRankCut_le up down (i + 1)
    exact (profileIntervalMean_bounds (up + 64 * down) q
      (senderRankCut up down i) (senderRankCut up down (i + 1)) frac
      hmono hbound hfrac0 hfrac1).2
  calc
    _ ≤ ∑ i ∈ ({0, 65} : Finset Nat),
        ((senderRankCut up down (i + 1) - senderRankCut up down i : Nat) : Real) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hmean i hi
    _ = up := by
      have hwidth : ∑ i ∈ ({0, 65} : Finset Nat),
          (senderRankCut up down (i + 1) - senderRankCut up down i) = up := by
        norm_num [senderRankCut]
        omega
      exact_mod_cast hwidth

/-- The 64 omitted upper-frontier middle targets have total mass at most
the sender's aggregate down-flow capacity. -/
theorem senderRankCut_middle_mean_sum_le (up down q : Nat) (frac : Real)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
      profileIntervalMean (up + 64 * down) q frac
        (senderRankCut up down i) (senderRankCut up down (i + 1))) ≤ 64 * down := by
  let middle := (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64)
  have hwidth (i : Nat) (hi : i ∈ middle) :
      senderRankCut up down (i + 1) - senderRankCut up down i = down := by
    have hx := (Finset.mem_filter.mp hi).1
    have hb := (Finset.mem_filter.mp hi).2
    have hi0 : i ≠ 0 := by omega
    have hi64 : i ≤ 64 := hb.2
    have hnext : i + 1 ≤ 65 := by omega
    have hcut : senderRankCut up down i = up / 2 + (i - 1) * down := by
      simp [senderRankCut, hi0, show i ≤ 65 by omega]
    have hcutNext : senderRankCut up down (i + 1) = up / 2 + i * down := by
      simp [senderRankCut, hnext]
    rw [hcut, hcutNext]
    have hmul : i * down = (i - 1) * down + down := by
      calc
        i * down = ((i - 1) + 1) * down := by rw [Nat.sub_add_cancel hb.1]
        _ = (i - 1) * down + down := by rw [Nat.add_mul]; simp
    rw [hmul]
    omega
  have hmean (i : Nat) (hi : i ∈ middle) :
      profileIntervalMean (up + 64 * down) q frac
        (senderRankCut up down i) (senderRankCut up down (i + 1)) ≤ down := by
    have hmono := senderRankCut_mono up down (Nat.le_succ i)
    have hbound := senderRankCut_le up down (i + 1)
    have hbounds := profileIntervalMean_bounds (up + 64 * down) q
      (senderRankCut up down i) (senderRankCut up down (i + 1)) frac
      hmono hbound hfrac0 hfrac1
    calc
      profileIntervalMean (up + 64 * down) q frac
          (senderRankCut up down i) (senderRankCut up down (i + 1)) ≤
        ((senderRankCut up down (i + 1) - senderRankCut up down i : Nat) : Real) :=
          hbounds.2
      _ = down := by exact_mod_cast hwidth i hi
  have hcard : middle.card = 64 := by
    have hset : middle = Finset.Icc 1 64 := by
      ext i
      simp [middle, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    simp
  calc
    _ ≤ ∑ i ∈ middle, (down : Real) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hmean i hi
    _ = (64 : Real) * down := by simp [hcard]

def senderOutgoingPiece {N : Nat} (s : Finset (Fin N)) (up down i : Nat) :
    Finset (Fin N) :=
  if i = 0 then blockOf s 0 (up / 2)
  else if i ≤ 64 then downSet s up down (i - 1)
  else blockOf s (s.card - up / 2) s.card

theorem senderOutgoingPiece_eq_blockOf {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up) (i : Nat) (hi : i < 66) :
    senderOutgoingPiece s up down i =
      blockOf s (senderRankCut up down i) (senderRankCut up down (i + 1)) := by
  by_cases hi0 : i = 0
  · subst i
    simp [senderOutgoingPiece, senderRankCut]
  · by_cases hi64 : i ≤ 64
    · have hnext : i + 1 ≤ 65 := by omega
      have hcut : senderRankCut up down i = up / 2 + (i - 1) * down := by
        simp [senderRankCut, hi0, Nat.not_lt.mpr (by omega : i ≤ 65)]
      have hcutNext : senderRankCut up down (i + 1) = up / 2 + i * down := by
        simp [senderRankCut, hnext]
      unfold senderOutgoingPiece
      rw [if_neg hi0, if_pos hi64]
      unfold downSet
      rw [hcut, hcutNext]
      have hiPos : 1 ≤ i := by omega
      rw [Nat.sub_add_cancel hiPos]
    · have hi65 : i = 65 := by omega
      subst i
      have hlast : s.card - up / 2 = up / 2 + 64 * down := by omega
      have hc65 : senderRankCut up down 65 = up / 2 + 64 * down := by
        simp [senderRankCut]
      have hc66 : senderRankCut up down 66 = s.card := by
        rw [senderRankCut_end, hs]
      unfold senderOutgoingPiece
      rw [if_neg (by omega : ¬65 = 0), if_neg (by omega : ¬65 ≤ 64), hlast, hc65, hc66]

/-- A regular 4096-rank group inside a port intersects an outgoing WireFlow
piece in one sender-rank interval, with endpoints given by max/min. This is
the concrete owner-map geometry needed to subdivide receiver targets at macro
boundaries. -/
theorem senderOutgoingPiece_inter_portMacroGroup_eq {N : Nat}
    (s : Finset (Fin N)) (up down i lo hi g : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up)
    (hi66 : i < 66) (hhi : hi ≤ s.card)
    (hg : 4096 * (g + 1) ≤ hi - lo) :
    Chvatal.blockOf (Chvatal.blockOf s lo hi)
        (4096 * g) (4096 * (g + 1)) ∩
      senderOutgoingPiece s up down i =
    Chvatal.blockOf s
      (max (lo + 4096 * g) (senderRankCut up down i))
      (min (lo + 4096 * (g + 1)) (senderRankCut up down (i + 1))) := by
  rw [blockOf_blockOf_eq_shift s lo hi (4096 * g) (4096 * (g + 1))
    (by omega) (by omega)]
  rw [senderOutgoingPiece_eq_blockOf s up down hs hu i hi66]
  exact blockOf_inter_eq s _ _ _ _

theorem senderOutgoingPiece_card_eq_interval {N : Nat}
    (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up) (i : Nat) (hi : i < 66) :
    (senderOutgoingPiece s up down i).card =
      senderRankCut up down (i + 1) - senderRankCut up down i := by
  rw [senderOutgoingPiece_eq_blockOf s up down hs hu i hi]
  exact blockOf_card (by rw [hs]; exact senderRankCut_le up down (i + 1))

/-- A routed piece's actual Boolean count and its ideal mean both lie in the
piece capacity, so their absolute discrepancy is at most that capacity. -/
theorem senderOutgoingPiece_profile_error_le_capacity {N : Nat}
    (s : Finset (Fin N)) (v : Fin N → Bool) (up down q : Nat) (frac : Real)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) (i : Nat) (hi : i < 66) :
    |(trueCountOn (senderOutgoingPiece s up down i) v : Real) -
      profileIntervalMean s.card q frac (senderRankCut up down i)
        (senderRankCut up down (i + 1))| ≤
      (senderRankCut up down (i + 1) - senderRankCut up down i : Nat) := by
  have hcard := senderOutgoingPiece_card_eq_interval s up down hs hu i hi
  have hcount : trueCountOn (senderOutgoingPiece s up down i) v ≤
      (senderOutgoingPiece s up down i).card := by
    rw [trueCountOn_eq_card_filter]
    exact Finset.card_filter_le _ _
  have hcountR : (trueCountOn (senderOutgoingPiece s up down i) v : Real) ≤
      (senderRankCut up down (i + 1) - senderRankCut up down i : Nat) := by
    exact_mod_cast (hcard ▸ hcount)
  have hmono := senderRankCut_mono up down (Nat.le_succ i)
  have hbound : senderRankCut up down (i + 1) ≤ s.card := by
    rw [hs]
    exact senderRankCut_le up down (i + 1)
  have hmean := profileIntervalMean_bounds s.card q
    (senderRankCut up down i) (senderRankCut up down (i + 1)) frac
    hmono hbound hfrac0 hfrac1
  apply abs_le.mpr
  constructor <;> linarith

/-- The combined omitted root/first-level fringe discrepancy of one sender is
bounded by its total up-flow capacity. -/
theorem senderOutgoing_fringe_profile_error_sum_le_up {N : Nat}
    (s : Finset (Fin N)) (v : Fin N → Bool) (up down q : Nat) (frac : Real)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ ({0, 65} : Finset Nat),
      |(trueCountOn (senderOutgoingPiece s up down i) v : Real) -
        profileIntervalMean s.card q frac
          (senderRankCut up down i) (senderRankCut up down (i + 1))|) ≤ up := by
  calc
    _ ≤ ∑ i ∈ ({0, 65} : Finset Nat),
        ((senderRankCut up down (i + 1) - senderRankCut up down i : Nat) : Real) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi_lt : i < 66 := by simp at hi; omega
      exact senderOutgoingPiece_profile_error_le_capacity s v up down q frac
        hs hu hfrac0 hfrac1 i hi_lt
    _ = up := by
      have hwidth : ∑ i ∈ ({0, 65} : Finset Nat),
          (senderRankCut up down (i + 1) - senderRankCut up down i) = up := by
        norm_num [senderRankCut]
        omega
      exact_mod_cast hwidth

/-- The omitted top-frontier middle discrepancy of one sender is bounded by
the combined capacity of its 64 child ports. -/
theorem senderOutgoing_middle_profile_error_sum_le_down {N : Nat}
    (s : Finset (Fin N)) (v : Fin N → Bool) (up down q : Nat) (frac : Real)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
      |(trueCountOn (senderOutgoingPiece s up down i) v : Real) -
        profileIntervalMean s.card q frac
          (senderRankCut up down i) (senderRankCut up down (i + 1))|) ≤ 64 * down := by
  let middle := (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64)
  have hwidth (i : Nat) (hi : i ∈ middle) :
      senderRankCut up down (i + 1) - senderRankCut up down i = down := by
    have hb := (Finset.mem_filter.mp hi).2
    have hi0 : i ≠ 0 := by omega
    have hnext : i + 1 ≤ 65 := by omega
    have hcut : senderRankCut up down i = up / 2 + (i - 1) * down := by
      simp [senderRankCut, hi0, show i ≤ 65 by omega]
    have hcutNext : senderRankCut up down (i + 1) = up / 2 + i * down := by
      simp [senderRankCut, hnext]
    rw [hcut, hcutNext]
    have hmul : i * down = (i - 1) * down + down := by
      calc
        i * down = ((i - 1) + 1) * down := by rw [Nat.sub_add_cancel hb.1]
        _ = (i - 1) * down + down := by rw [Nat.add_mul]; simp
    rw [hmul]
    omega
  have hcard : middle.card = 64 := by
    have hset : middle = Finset.Icc 1 64 := by
      ext i
      simp [middle, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    simp
  calc
    _ ≤ ∑ i ∈ middle, (down : Real) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi_lt : i < 66 := by
        have := (Finset.mem_filter.mp hi).1
        simp at this
        omega
      have hpiece := senderOutgoingPiece_profile_error_le_capacity s v up down q frac
        hs hu hfrac0 hfrac1 i hi_lt
      rw [hwidth i hi] at hpiece
      exact hpiece
    _ = (64 : Real) * down := by simp [hcard]

theorem senderOutgoingPieces_are_WireFlow_ports {N : Nat} (s : Finset (Fin N))
    (up down : Nat) :
    senderOutgoingPiece s up down 0 ∪ senderOutgoingPiece s up down 65 = upSet s up ∧
      ∀ j < 64, senderOutgoingPiece s up down (j + 1) = downSet s up down j := by
  constructor
  · simp [senderOutgoingPiece, upSet]
  · intro j hj
    have hj1 : j + 1 ≤ 64 := by omega
    simp [senderOutgoingPiece, show j + 1 ≠ 0 by omega, hj1, Nat.succ_sub_one]

theorem sortedSenderOutgoing_profile_error_exact {c N m q : Nat} (frac : Real)
    (S : Fin c → Finset (Fin N)) (v : Fin c → Fin N → Bool)
    (up down : Fin c → Nat)
    (hcard : ∀ packet, (S packet).card = m)
    (hsize : ∀ packet, (S packet).card = up packet + 64 * down packet)
    (hu : ∀ packet, 2 ∣ up packet)
    (hsorted : ∀ packet, Monotone (v packet ∘ (S packet).orderEmbOfFin rfl))
    (hq : q < m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ packet : Fin c, ∑ i ∈ range 66,
      |(trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
          (v packet) : Real) -
        profileIntervalMean m q frac
          (senderRankCut (up packet) (down packet) i)
          (senderRankCut (up packet) (down packet) (i + 1))|) =
      ∑ packet : Fin c, |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := by
  let cuts : Fin c → Nat → Nat := fun packet i => senderRankCut (up packet) (down packet) i
  have hstart : ∀ packet, cuts packet 0 = 0 := by intro packet; exact senderRankCut_start _ _
  have hcuts : ∀ packet, Monotone (cuts packet) := by intro packet; exact senderRankCut_mono _ _
  have hcutBound : ∀ packet i, cuts packet i ≤ m := by
    intro packet i
    calc
      cuts packet i ≤ up packet + 64 * down packet := senderRankCut_le _ _ _
      _ = m := by rw [← hsize packet, hcard packet]
  have hend : ∀ packet, cuts packet 66 = m := by
    intro packet
    change senderRankCut (up packet) (down packet) 66 = m
    rw [senderRankCut_end, ← hsize packet, hcard packet]
  have hgeneric := sortedWireBags_intervalPartition_L1_exact frac S v hcard hsorted
    cuts hstart hcuts hcutBound hend hq hfrac0 hfrac1
  calc
    _ = ∑ packet : Fin c, ∑ i ∈ range 66,
        |(trueCountOn (blockOf (S packet) (cuts packet i) (cuts packet (i + 1)))
            (v packet) : Real) -
          profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))| := by
      apply Finset.sum_congr rfl
      intro packet _
      apply Finset.sum_congr rfl
      intro i hi
      rw [senderOutgoingPiece_eq_blockOf (S packet) (up packet) (down packet)
        (hsize packet) (hu packet) i (mem_range.mp hi)]
    _ = ∑ packet : Fin c, |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := hgeneric

noncomputable def senderOutgoingProfileError {c N : Nat} (S : Fin c → Finset (Fin N))
    (v : Fin c → Fin N → Bool) (up down : Fin c → Nat)
    (q : Nat) (frac : Real) (packet : Fin c) (i : Nat) : Real :=
  |(trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
      (v packet) : Real) -
    profileIntervalMean (S packet).card q frac
      (senderRankCut (up packet) (down packet) i)
      (senderRankCut (up packet) (down packet) (i + 1))|

/-- Selecting any subset of the routed pieces for a receiver cannot amplify
the aggregate profile error: it is bounded by the sender cohort's original
coarse count error, independently of how many pieces are selected. -/
theorem selectedSenderOutgoing_profile_error_le {c N m q : Nat} (frac : Real)
    (S : Fin c → Finset (Fin N)) (v : Fin c → Fin N → Bool)
    (up down : Fin c → Nat)
    (hcard : ∀ packet, (S packet).card = m)
    (hsize : ∀ packet, (S packet).card = up packet + 64 * down packet)
    (hu : ∀ packet, 2 ∣ up packet)
    (hsorted : ∀ packet, Monotone (v packet ∘ (S packet).orderEmbOfFin rfl))
    (hq : q < m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (selected : Fin c → Finset Nat)
    (hselected : ∀ packet, selected packet ⊆ range 66) :
    (∑ packet : Fin c, ∑ i ∈ selected packet,
      senderOutgoingProfileError S v up down q frac packet i) ≤
      ∑ packet : Fin c, |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := by
  have hfull := sortedSenderOutgoing_profile_error_exact frac S v up down
    hcard hsize hu hsorted hq hfrac0 hfrac1
  calc
    _ ≤ ∑ packet : Fin c, ∑ i ∈ range 66,
        senderOutgoingProfileError S v up down q frac packet i := by
      apply Finset.sum_le_sum
      intro packet _
      exact Finset.sum_le_sum_of_subset_of_nonneg (hselected packet) (by
        intro i hi hnot
        exact abs_nonneg _)
    _ = ∑ packet : Fin c,
        |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := by
      simpa [senderOutgoingProfileError, hcard] using hfull

noncomputable def senderOutgoingProfileErrorVar {Source : Type} {N : Nat}
    (S : Source → Finset (Fin N)) (v : Source → Fin N → Bool)
    (up down q : Source → Nat) (frac : Source → Real)
    (packet : Source) (i : Nat) : Real :=
  |(trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
      (v packet) : Real) -
    profileIntervalMean (S packet).card (q packet) (frac packet)
      (senderRankCut (up packet) (down packet) i)
      (senderRankCut (up packet) (down packet) (i + 1))|

/-- The no-loss sender partition identity also holds for unequal source bag
sizes and a separate fractional ideal count for each sender. This is the
shape needed when a receiver combines its larger parent bag with smaller child
bags. -/
theorem sortedSenderOutgoing_profile_error_exact_var
    {Source : Type} [Fintype Source] [DecidableEq Source] {N : Nat}
    (S : Source → Finset (Fin N)) (v : Source → Fin N → Bool)
    (up down q : Source → Nat) (frac : Source → Real)
    (hsize : ∀ packet, (S packet).card = up packet + 64 * down packet)
    (hu : ∀ packet, 2 ∣ up packet)
    (hsorted : ∀ packet, Monotone (v packet ∘ (S packet).orderEmbOfFin rfl))
    (hq : ∀ packet, q packet ≤ (S packet).card)
    (hfrac0 : ∀ packet, 0 ≤ frac packet)
    (hfrac1 : ∀ packet, frac packet ≤ 1)
    (hendpoint : ∀ packet, q packet = (S packet).card → frac packet = 0) :
    (∑ packet : Source, ∑ i ∈ range 66,
      senderOutgoingProfileErrorVar S v up down q frac packet i) =
      ∑ packet : Source,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
  have hlocal (packet : Source) :
      (∑ i ∈ range 66,
        senderOutgoingProfileErrorVar S v up down q frac packet i) =
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
    let cuts : Nat → Nat := senderRankCut (up packet) (down packet)
    have hstart : cuts 0 = 0 := senderRankCut_start _ _
    have hcuts : Monotone cuts := senderRankCut_mono _ _
    have hbound : ∀ i, cuts i ≤ (S packet).card := by
      intro i
      calc
        cuts i ≤ up packet + 64 * down packet := senderRankCut_le _ _ _
        _ = (S packet).card := (hsize packet).symm
    have hend : cuts 66 = (S packet).card := by
      change senderRankCut (up packet) (down packet) 66 = _
      rw [senderRankCut_end, hsize packet]
    have hcount (i : Nat) (hi : i < 66) :
        trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
            (v packet) =
          profileInterval (S packet).card (trueCountOn (S packet) (v packet))
            (cuts i) (cuts (i + 1)) := by
      rw [senderOutgoingPiece_eq_blockOf (S packet) (up packet) (down packet)
        (hsize packet) (hu packet) i hi]
      exact trueCountOn_blockOf_profile (S packet) (v packet) (hsorted packet)
        (cuts i) (cuts (i + 1)) (hcuts (Nat.le_succ i)) (hbound (i + 1))
    have hX : trueCountOn (S packet) (v packet) ≤ (S packet).card := by
      unfold trueCountOn
      simpa using (Fintype.card_subtype_le
        (fun w : S packet => v packet w.val = true))
    have hprofile := profileInterval_partition_L1_exact_allow_endpoint
      (S packet).card 66 (trueCountOn (S packet) (v packet)) (q packet)
      (frac packet) cuts hstart hcuts hend hX
      (hq packet) (hfrac0 packet) (hfrac1 packet) (hendpoint packet)
    calc
      (∑ i ∈ range 66,
          senderOutgoingProfileErrorVar S v up down q frac packet i) =
        ∑ i ∈ range 66,
          |(profileInterval (S packet).card (trueCountOn (S packet) (v packet))
              (cuts i) (cuts (i + 1)) : Real) -
            profileIntervalMean (S packet).card (q packet) (frac packet)
              (cuts i) (cuts (i + 1))| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [senderOutgoingProfileErrorVar, hcount i (mem_range.mp hi)]
      _ = |(trueCountOn (S packet) (v packet) : Real) -
            (q packet + frac packet)| := hprofile
  calc
    (∑ packet : Source, ∑ i ∈ range 66,
        senderOutgoingProfileErrorVar S v up down q frac packet i) =
      ∑ packet : Source,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
      apply Finset.sum_congr rfl
      intro packet _
      exact hlocal packet

/-- For a sorted Boolean source, all 66 outgoing profile-error pieces have
the same sign as the source's total threshold-count error. -/
theorem sortedSenderOutgoing_profile_error_piecewise_sign {N : Nat}
    (S : Finset (Fin N)) (v : Fin N → Bool) (up down q : Nat) (frac : Real)
    (hsize : S.card = up + 64 * down) (hu : 2 ∣ up)
    (hsorted : Monotone (v ∘ S.orderEmbOfFin rfl))
    (hq : q ≤ S.card) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (hendpoint : q = S.card → frac = 0) :
    ((trueCountOn S v ≤ q → ∀ i ∈ range 66,
      (trueCountOn (senderOutgoingPiece S up down i) v : Real) ≤
        profileIntervalMean S.card q frac
          (senderRankCut up down i) (senderRankCut up down (i + 1))) ∧
     (q + 1 ≤ trueCountOn S v → ∀ i ∈ range 66,
      profileIntervalMean S.card q frac
          (senderRankCut up down i) (senderRankCut up down (i + 1)) ≤
        (trueCountOn (senderOutgoingPiece S up down i) v : Real))) := by
  have hX : trueCountOn S v ≤ S.card := by
    unfold trueCountOn
    simpa using (Fintype.card_subtype_le (fun w : S => v w.val = true))
  have hcount (i : Nat) (hi : i < 66) :
      trueCountOn (senderOutgoingPiece S up down i) v =
        profileInterval S.card (trueCountOn S v)
          (senderRankCut up down i) (senderRankCut up down (i + 1)) := by
    rw [senderOutgoingPiece_eq_blockOf S up down hsize hu i hi]
    exact trueCountOn_blockOf_profile S v hsorted
      (senderRankCut up down i) (senderRankCut up down (i + 1))
      (senderRankCut_mono up down (Nat.le_succ i))
      (by calc
        senderRankCut up down (i + 1) ≤ up + 64 * down :=
          senderRankCut_le up down (i + 1)
        _ = S.card := hsize.symm)
  constructor
  · intro hXq i hi
    rw [hcount i (mem_range.mp hi)]
    exact profileInterval_error_nonpos_of_X_le_target S.card
      (trueCountOn S v) q (senderRankCut up down i)
      (senderRankCut up down (i + 1)) frac
      (senderRankCut_mono up down (Nat.le_succ i))
      (by calc
        senderRankCut up down (i + 1) ≤ up + 64 * down :=
          senderRankCut_le up down (i + 1)
        _ = S.card := hsize.symm) hXq
      hfrac0 hfrac1
  · intro hqX i hi
    rw [hcount i (mem_range.mp hi)]
    exact profileInterval_error_nonneg_of_target_le_X S.card
      (trueCountOn S v) q (senderRankCut up down i)
      (senderRankCut up down (i + 1)) frac
      (senderRankCut_mono up down (Nat.le_succ i))
      (by calc
        senderRankCut up down (i + 1) ≤ up + 64 * down :=
          senderRankCut_le up down (i + 1)
        _ = S.card := hsize.symm) hqX
      hfrac0 hfrac1

/-- The sender's 66-piece L1 identity, stated for one source packet so it can
be charged after receiver selections are regrouped source-by-source. -/
theorem sortedSenderOutgoing_profile_error_exact_one {N : Nat}
    (S : Finset (Fin N)) (v : Fin N → Bool) (up down q : Nat) (frac : Real)
    (hsize : S.card = up + 64 * down) (hu : 2 ∣ up)
    (hsorted : Monotone (v ∘ S.orderEmbOfFin rfl))
    (hq : q ≤ S.card) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (hendpoint : q = S.card → frac = 0) :
    (∑ i ∈ range 66,
      |(trueCountOn (senderOutgoingPiece S up down i) v : Real) -
        profileIntervalMean S.card q frac
          (senderRankCut up down i) (senderRankCut up down (i + 1))|) =
      |(trueCountOn S v : Real) - (q + frac)| := by
  let cuts : Nat → Nat := senderRankCut up down
  have hstart : cuts 0 = 0 := senderRankCut_start _ _
  have hcuts : Monotone cuts := senderRankCut_mono _ _
  have hbound : ∀ i, cuts i ≤ S.card := by
    intro i
    calc
      cuts i ≤ up + 64 * down := senderRankCut_le _ _ _
      _ = S.card := hsize.symm
  have hend : cuts 66 = S.card := by
    change senderRankCut up down 66 = _
    rw [senderRankCut_end, hsize]
  have hcount (i : Nat) (hi : i < 66) :
      trueCountOn (senderOutgoingPiece S up down i) v =
        profileInterval S.card (trueCountOn S v) (cuts i) (cuts (i + 1)) := by
    rw [senderOutgoingPiece_eq_blockOf S up down hsize hu i hi]
    exact trueCountOn_blockOf_profile S v hsorted (cuts i) (cuts (i + 1))
      (hcuts (Nat.le_succ i)) (hbound (i + 1))
  have hX : trueCountOn S v ≤ S.card := by
    unfold trueCountOn
    simpa using (Fintype.card_subtype_le (fun w : S => v w.val = true))
  have hprofile := profileInterval_partition_L1_exact_allow_endpoint
    S.card 66 (trueCountOn S v) q frac cuts hstart hcuts hend hX hq
    hfrac0 hfrac1 hendpoint
  calc
    _ = ∑ i ∈ range 66,
        |(profileInterval S.card (trueCountOn S v) (cuts i) (cuts (i + 1)) : Real) -
          profileIntervalMean S.card q frac (cuts i) (cuts (i + 1))| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcount i (mem_range.mp hi)]
    _ = |(trueCountOn S v : Real) - (q + frac)| := hprofile

/-- Selecting any actual sender pieces still cannot amplify error when the
source bags have different sizes and ideal means. -/
theorem selectedSenderOutgoing_profile_error_le_var {c N : Nat}
    (S : Fin c → Finset (Fin N)) (v : Fin c → Fin N → Bool)
    (up down q : Fin c → Nat) (frac : Fin c → Real)
    (hsize : ∀ packet, (S packet).card = up packet + 64 * down packet)
    (hu : ∀ packet, 2 ∣ up packet)
    (hsorted : ∀ packet, Monotone (v packet ∘ (S packet).orderEmbOfFin rfl))
    (hq : ∀ packet, q packet ≤ (S packet).card)
    (hfrac0 : ∀ packet, 0 ≤ frac packet)
    (hfrac1 : ∀ packet, frac packet ≤ 1)
    (hendpoint : ∀ packet, q packet = (S packet).card → frac packet = 0)
    (selected : Fin c → Finset Nat)
    (hselected : ∀ packet, selected packet ⊆ range 66) :
    (∑ packet : Fin c, ∑ i ∈ selected packet,
      senderOutgoingProfileErrorVar S v up down q frac packet i) ≤
      ∑ packet : Fin c,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
  have hfull := sortedSenderOutgoing_profile_error_exact_var S v up
    down q frac hsize hu hsorted hq hfrac0 hfrac1 hendpoint
  calc
    _ ≤ ∑ packet : Fin c, ∑ i ∈ range 66,
        senderOutgoingProfileErrorVar S v up down q frac packet i := by
      apply Finset.sum_le_sum
      intro packet _
      exact Finset.sum_le_sum_of_subset_of_nonneg (hselected packet) (by
        intro i hi hnot
        exact abs_nonneg _)
    _ = ∑ packet : Fin c,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := hfull

/-- The combined threshold count entering a receiver differs from the sum of
its selected source-ideal interval counts by at most the senders' total coarse
count error. This is the aggregate form consumed by a later merge/deal bound. -/
theorem selectedSenderOutgoing_count_error_le_var {c N : Nat}
    (S : Fin c → Finset (Fin N)) (v : Fin c → Fin N → Bool)
    (up down q : Fin c → Nat) (frac : Fin c → Real)
    (hsize : ∀ packet, (S packet).card = up packet + 64 * down packet)
    (hu : ∀ packet, 2 ∣ up packet)
    (hsorted : ∀ packet, Monotone (v packet ∘ (S packet).orderEmbOfFin rfl))
    (hq : ∀ packet, q packet ≤ (S packet).card)
    (hfrac0 : ∀ packet, 0 ≤ frac packet)
    (hfrac1 : ∀ packet, frac packet ≤ 1)
    (hendpoint : ∀ packet, q packet = (S packet).card → frac packet = 0)
    (selected : Fin c → Finset Nat)
    (hselected : ∀ packet, selected packet ⊆ range 66) :
    |(∑ packet : Fin c, ∑ i ∈ selected packet,
        (trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
          (v packet) : Real)) -
      ∑ packet : Fin c, ∑ i ∈ selected packet,
        profileIntervalMean (S packet).card (q packet) (frac packet)
          (senderRankCut (up packet) (down packet) i)
          (senderRankCut (up packet) (down packet) (i + 1))| ≤
      ∑ packet : Fin c,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
  let err : Fin c → Nat → Real := fun packet i =>
    (trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
      (v packet) : Real) -
      profileIntervalMean (S packet).card (q packet) (frac packet)
        (senderRankCut (up packet) (down packet) i)
        (senderRankCut (up packet) (down packet) (i + 1))
  have hdiff :
      (∑ packet : Fin c, ∑ i ∈ selected packet,
        (trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
          (v packet) : Real)) -
        ∑ packet : Fin c, ∑ i ∈ selected packet,
          profileIntervalMean (S packet).card (q packet) (frac packet)
            (senderRankCut (up packet) (down packet) i)
            (senderRankCut (up packet) (down packet) (i + 1)) =
      ∑ packet : Fin c, ∑ i ∈ selected packet, err packet i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro packet _
    rw [← Finset.sum_sub_distrib]
  have hinner (packet : Fin c) :
      |∑ i ∈ selected packet, err packet i| ≤
        ∑ i ∈ selected packet, |err packet i| :=
    Finset.abs_sum_le_sum_abs _ _
  have hselectedError := selectedSenderOutgoing_profile_error_le_var
    S v up down q frac hsize hu hsorted hq hfrac0 hfrac1 hendpoint selected hselected
  calc
    |(∑ packet : Fin c, ∑ i ∈ selected packet,
        (trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
          (v packet) : Real)) -
      ∑ packet : Fin c, ∑ i ∈ selected packet,
        profileIntervalMean (S packet).card (q packet) (frac packet)
          (senderRankCut (up packet) (down packet) i)
          (senderRankCut (up packet) (down packet) (i + 1))| =
      |∑ packet : Fin c, ∑ i ∈ selected packet, err packet i| := by rw [hdiff]
    _ ≤ ∑ packet : Fin c, |∑ i ∈ selected packet, err packet i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ packet : Fin c, ∑ i ∈ selected packet, |err packet i| := by
      apply Finset.sum_le_sum
      intro packet _
      exact hinner packet
    _ ≤ ∑ packet : Fin c,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
      simpa [err, senderOutgoingProfileErrorVar] using hselectedError

/-- Selection pattern matching one `WireFlow` receiver when its sources are
indexed by the parent followed by its 64 children: take the receiver's one
down block from the parent, and both up-fringe halves from each child. -/
def receiverOutgoingSelection (parentPort : Nat) : Fin 65 → Finset Nat :=
  fun source => if source.val = 0 then {parentPort + 1} else {0, 65}

theorem receiverOutgoingSelection_subset (parentPort : Nat) (hport : parentPort < 64)
    (source : Fin 65) : receiverOutgoingSelection parentPort source ⊆ range 66 := by
  by_cases hsource : source.val = 0
  · simp [receiverOutgoingSelection, hsource]
    omega
  · rw [Finset.subset_iff]
    intro i hi
    simp [receiverOutgoingSelection, hsource] at hi
    rcases hi with rfl | rfl <;> simp
/-- The parent-plus-children-shaped selection has the same no-amplification
count bound. Instantiating its source data with actual `execPlacement` sets is
still a separate adapter obligation. -/
theorem wireFlowReceiver_count_error_le {N : Nat}
    (S : Fin 65 → Finset (Fin N)) (v : Fin 65 → Fin N → Bool)
    (up down q : Fin 65 → Nat) (frac : Fin 65 → Real)
    (hsize : ∀ source, (S source).card = up source + 64 * down source)
    (hu : ∀ source, 2 ∣ up source)
    (hsorted : ∀ source, Monotone (v source ∘ (S source).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤ (S source).card)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source, q source = (S source).card → frac source = 0)
    (parentPort : Nat) (hport : parentPort < 64) :
    |(∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection parentPort source,
        (trueCountOn (senderOutgoingPiece (S source) (up source) (down source) i)
          (v source) : Real)) -
      ∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection parentPort source,
        profileIntervalMean (S source).card (q source) (frac source)
          (senderRankCut (up source) (down source) i)
          (senderRankCut (up source) (down source) (i + 1))| ≤
      ∑ source : Fin 65,
        |(trueCountOn (S source) (v source) : Real) - (q source + frac source)| := by
  exact selectedSenderOutgoing_count_error_le_var S v up down q frac hsize hu hsorted
    hq hfrac0 hfrac1 hendpoint (receiverOutgoingSelection parentPort)
    (fun source => receiverOutgoingSelection_subset parentPort hport source)

/-- If one source's piece errors all have the same sign and its pieces are
partitioned among receivers, then routing preserves its absolute error mass
exactly (before different sources can cancel at a receiver). -/
theorem sum_receiver_selected_errors_eq_source_pieces_of_common_sign
    {Receiver : Type} [Fintype Receiver] [DecidableEq Receiver]
    (receivers : Finset Receiver) (err : Nat → Real)
    (selected : Receiver → Finset Nat)
    (hselected : ∀ receiver ∈ receivers, selected receiver ⊆ range 66)
    (hdisjoint : ∀ receiver₁ ∈ receivers, ∀ receiver₂ ∈ receivers,
      receiver₁ ≠ receiver₂ →
      Disjoint (selected receiver₁) (selected receiver₂))
    (hunion : receivers.biUnion selected = range 66)
    (hsign : (∀ i ∈ range 66, 0 ≤ err i) ∨
      (∀ i ∈ range 66, err i ≤ 0)) :
    (∑ receiver ∈ receivers, |∑ i ∈ selected receiver, err i|) =
      ∑ i ∈ range 66, |err i| := by
  classical
  have hpair : Set.PairwiseDisjoint (↑receivers : Set Receiver) selected := by
    intro receiver hreceiver receiver' hreceiver' hne
    exact hdisjoint receiver hreceiver receiver' hreceiver' hne
  have hsame (receiver : Receiver) (hmem : receiver ∈ receivers) :
      |∑ i ∈ selected receiver, err i| =
        ∑ i ∈ selected receiver, |err i| := by
    rcases hsign with hnonneg | hnonpos
    · have hs : 0 ≤ ∑ i ∈ selected receiver, err i :=
        Finset.sum_nonneg (fun i hi => hnonneg i (hselected receiver hmem hi))
      rw [abs_of_nonneg hs]
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_of_nonneg (hnonneg i (hselected receiver hmem hi))]
    · have hs : ∑ i ∈ selected receiver, err i ≤ 0 :=
        Finset.sum_nonpos (fun i hi => hnonpos i (hselected receiver hmem hi))
      rw [abs_of_nonpos hs]
      calc
        -∑ i ∈ selected receiver, err i =
            ∑ i ∈ selected receiver, -err i := by rw [Finset.sum_neg_distrib]
        _ = ∑ i ∈ selected receiver, |err i| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [abs_of_nonpos (hnonpos i (hselected receiver hmem hi))]
  calc
    (∑ receiver ∈ receivers, |∑ i ∈ selected receiver, err i|) =
        ∑ receiver ∈ receivers, ∑ i ∈ selected receiver, |err i| := by
      apply Finset.sum_congr rfl
      intro receiver hmem
      exact hsame receiver hmem
    _ = ∑ i ∈ receivers.biUnion selected, |err i| :=
      (Finset.sum_biUnion hpair).symm
    _ = ∑ i ∈ range 66, |err i| := by rw [hunion]

/-- Layerwise sum of receiver discrepancies charges each source rank piece at
most once when routed selections are pairwise disjoint. -/
theorem sum_receiver_selected_errors_le_source_pieces
    {Receiver Source : Type} [Fintype Receiver] [Fintype Source]
    [DecidableEq Receiver] [DecidableEq Source]
    (err : Source → Nat → Real) (selected : Receiver → Source → Finset Nat)
    (hselected : ∀ receiver source, selected receiver source ⊆ range 66)
    (hdisjoint : ∀ source receiver₁ receiver₂, receiver₁ ≠ receiver₂ →
      Disjoint (selected receiver₁ source) (selected receiver₂ source)) :
    (∑ receiver : Receiver,
      |∑ source : Source, ∑ i ∈ selected receiver source, err source i|) ≤
      ∑ source : Source, ∑ i ∈ range 66, |err source i| := by
  classical
  have htriangle (receiver : Receiver) :
      |∑ source : Source, ∑ i ∈ selected receiver source, err source i| ≤
        ∑ source : Source, ∑ i ∈ selected receiver source, |err source i| := by
    calc
      |∑ source : Source, ∑ i ∈ selected receiver source, err source i| ≤
          ∑ source : Source, |∑ i ∈ selected receiver source, err source i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ source : Source, ∑ i ∈ selected receiver source, |err source i| := by
        apply Finset.sum_le_sum
        intro source _
        exact Finset.abs_sum_le_sum_abs _ _
  calc
    _ ≤ ∑ receiver : Receiver,
        ∑ source : Source, ∑ i ∈ selected receiver source, |err source i| := by
      apply Finset.sum_le_sum
      intro receiver _
      exact htriangle receiver
    _ = ∑ source : Source,
        ∑ receiver : Receiver, ∑ i ∈ selected receiver source, |err source i| := by
      rw [Finset.sum_comm]
    _ ≤ ∑ source : Source, ∑ i ∈ range 66, |err source i| := by
      apply Finset.sum_le_sum
      intro source _
      let pieces := Finset.univ.biUnion (fun receiver : Receiver => selected receiver source)
      have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Receiver)))
          (fun receiver => selected receiver source) := by
        intro receiver _ receiver' _ hne
        exact hdisjoint source receiver receiver' hne
      have hpieces :
          (∑ receiver : Receiver, ∑ i ∈ selected receiver source, |err source i|) =
            ∑ i ∈ pieces, |err source i| := by
        dsimp [pieces]
        rw [← Finset.sum_biUnion hpair]
      have hsub : pieces ⊆ range 66 := by
        intro i hi
        obtain ⟨receiver, _, hi⟩ := Finset.mem_biUnion.mp hi
        exact hselected receiver source hi
      rw [hpieces]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro i _ _
        exact abs_nonneg _)

/-- Squared routed discrepancy is controlled by the square of the complete
source-piece L1 error whenever each piece is routed to at most one receiver. -/
theorem sum_receiver_selected_error_sq_le_source_pieces
    {Receiver : Type} [Fintype Receiver] [DecidableEq Receiver]
    (err : Nat → Real) (selected : Receiver → Finset Nat)
    (hselected : ∀ receiver, selected receiver ⊆ range 66)
    (hdisjoint : ∀ receiver₁ receiver₂, receiver₁ ≠ receiver₂ →
      Disjoint (selected receiver₁) (selected receiver₂)) :
    (∑ receiver : Receiver,
      (∑ i ∈ selected receiver, err i) ^ 2) ≤
      (∑ i ∈ range 66, |err i|) ^ 2 := by
  classical
  let magnitude (receiver : Receiver) : Real :=
    ∑ i ∈ selected receiver, |err i|
  have hmag_nonneg (receiver : Receiver) : 0 ≤ magnitude receiver := by
    dsimp [magnitude]
    exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hpiece (receiver : Receiver) :
      (∑ i ∈ selected receiver, err i) ^ 2 ≤ magnitude receiver ^ 2 := by
    have habs : |∑ i ∈ selected receiver, err i| ≤ magnitude receiver := by
      simpa [magnitude] using Finset.abs_sum_le_sum_abs err
        (selected receiver)
    have hleft : 0 ≤ |∑ i ∈ selected receiver, err i| := abs_nonneg _
    calc
      (∑ i ∈ selected receiver, err i) ^ 2 =
          |∑ i ∈ selected receiver, err i| ^ 2 := (sq_abs _).symm
      _ ≤ magnitude receiver ^ 2 := by nlinarith [habs, hleft, hmag_nonneg receiver]
  let pieces := Finset.univ.biUnion selected
  have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset Receiver)) selected := by
    intro receiver hreceiver other hother hne
    exact hdisjoint receiver other hne
  have hsum :
      (∑ receiver : Receiver, magnitude receiver) =
        ∑ i ∈ pieces, |err i| := by
    dsimp [magnitude, pieces]
    rw [Finset.sum_biUnion hpair]
  have hsub : pieces ⊆ range 66 := by
    intro i hi
    obtain ⟨receiver, _, hmem⟩ := Finset.mem_biUnion.mp hi
    exact hselected receiver hmem
  have hfull : 0 ≤ ∑ i ∈ range 66, |err i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hpieces_nonneg : 0 ≤ ∑ i ∈ pieces, |err i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hpieces_le :
      (∑ i ∈ pieces, |err i|) ≤ ∑ i ∈ range 66, |err i| :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro i _ _
      exact abs_nonneg _)
  calc
    _ ≤ ∑ receiver : Receiver, magnitude receiver ^ 2 :=
      Finset.sum_le_sum (fun receiver _ => hpiece receiver)
    _ ≤ (∑ receiver : Receiver, magnitude receiver) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun receiver _ => hmag_nonneg receiver)
    _ = (∑ i ∈ pieces, |err i|) ^ 2 := by rw [hsum]
    _ ≤ (∑ i ∈ range 66, |err i|) ^ 2 :=
      (sq_le_sq₀ hpieces_nonneg hfull).2 hpieces_le

/-- If receivers partition each sender's 66 outgoing rank pieces, the sum of
their absolute profile discrepancies is bounded by one coarse count error per
sender, regardless of how the pieces are grouped into receivers. -/
theorem sum_receiver_profile_errors_le_source_count_errors
    {Receiver Source : Type} [Fintype Receiver] [Fintype Source]
    [DecidableEq Receiver] [DecidableEq Source] {N : Nat}
    (S : Source → Finset (Fin N)) (v : Source → Fin N → Bool)
    (up down q : Source → Nat) (frac : Source → Real)
    (hsize : ∀ source, (S source).card = up source + 64 * down source)
    (hu : ∀ source, 2 ∣ up source)
    (hsorted : ∀ source, Monotone (v source ∘ (S source).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤ (S source).card)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source, q source = (S source).card → frac source = 0)
    (selected : Receiver → Source → Finset Nat)
    (hselected : ∀ receiver source, selected receiver source ⊆ range 66)
    (hdisjoint : ∀ source receiver₁ receiver₂, receiver₁ ≠ receiver₂ →
      Disjoint (selected receiver₁ source) (selected receiver₂ source)) :
    (∑ receiver : Receiver,
      |∑ source : Source,
        ∑ i ∈ selected receiver source,
          ((trueCountOn
            (senderOutgoingPiece (S source) (up source) (down source) i)
            (v source) : Real) -
          profileIntervalMean (S source).card (q source) (frac source)
            (senderRankCut (up source) (down source) i)
            (senderRankCut (up source) (down source) (i + 1)))|) ≤
      ∑ source : Source,
        |(trueCountOn (S source) (v source) : Real) - (q source + frac source)| := by
  let err : Source → Nat → Real := fun source i =>
    (trueCountOn (senderOutgoingPiece (S source) (up source) (down source) i)
      (v source) : Real) -
      profileIntervalMean (S source).card (q source) (frac source)
        (senderRankCut (up source) (down source) i)
        (senderRankCut (up source) (down source) (i + 1))
  calc
    _ ≤ ∑ source : Source, ∑ i ∈ range 66, |err source i| :=
      sum_receiver_selected_errors_le_source_pieces err selected hselected hdisjoint
    _ = ∑ source : Source,
        |(trueCountOn (S source) (v source) : Real) - (q source + frac source)| := by
      simpa [err, senderOutgoingProfileErrorVar] using
        (sortedSenderOutgoing_profile_error_exact_var S v up down q frac
          hsize hu hsorted hq hfrac0 hfrac1 hendpoint)

/-- Packetized version of the layer energy bound. Each source cohort may
produce many sorted output packets, and each packet's discrepancy may be
split arbitrarily among destination registers. If the total routed L1 error
from a cohort is bounded by its coarse error, then summing over `k` source
cohorts costs only the Cauchy factor `k`. -/
theorem packetized_source_errors_sq_sum_le
    {Source Packet Receiver : Type}
    [Fintype Source] [Fintype Packet] [Fintype Receiver]
    (err : Source → Packet → Receiver → Real)
    (batchError : Source → Real)
    (hbatch : ∀ source,
      (∑ packet : Packet, ∑ receiver : Receiver,
        |err source packet receiver|) ≤ batchError source) :
    (∑ receiver : Receiver,
      (∑ source : Source, ∑ packet : Packet,
        err source packet receiver) ^ 2) ≤
      (Fintype.card Source : Real) *
        ∑ source : Source, (batchError source) ^ 2 := by
  classical
  let agg (receiver : Receiver) : Real :=
    ∑ source : Source, ∑ packet : Packet, err source packet receiver
  have htriangle (receiver : Receiver) :
      |agg receiver| ≤
        ∑ source : Source, ∑ packet : Packet,
          |err source packet receiver| := by
    unfold agg
    calc
      |∑ source : Source, ∑ packet : Packet,
          err source packet receiver| ≤
        ∑ source : Source,
          |∑ packet : Packet, err source packet receiver| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ source : Source, ∑ packet : Packet,
          |err source packet receiver| := by
        apply Finset.sum_le_sum
        intro source _
        exact Finset.abs_sum_le_sum_abs _ _
  have htotal :
      (∑ receiver : Receiver, |agg receiver|) ≤
        ∑ source : Source, batchError source := by
    calc
      _ ≤ ∑ receiver : Receiver,
          ∑ source : Source, ∑ packet : Packet,
            |err source packet receiver| := by
        apply Finset.sum_le_sum
        intro receiver _
        exact htriangle receiver
      _ = ∑ source : Source,
          ∑ packet : Packet, ∑ receiver : Receiver,
            |err source packet receiver| := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro source _
        rw [Finset.sum_comm]
      _ ≤ ∑ source : Source, batchError source := by
        apply Finset.sum_le_sum
        intro source _
        exact hbatch source
  have htotal_nonneg : 0 ≤ ∑ source : Source, batchError source := by
    calc
      0 ≤ ∑ receiver : Receiver, |agg receiver| :=
        Finset.sum_nonneg (fun receiver _ => abs_nonneg _)
      _ ≤ ∑ source : Source, batchError source := htotal
  have hagg_nonneg : 0 ≤ ∑ receiver : Receiver, |agg receiver| :=
    Finset.sum_nonneg (fun receiver _ => abs_nonneg _)
  calc
    _ = ∑ receiver : Receiver, |agg receiver| ^ 2 := by
      apply Finset.sum_congr rfl
      intro receiver _
      rw [sq_abs]
    _ ≤ (∑ receiver : Receiver, |agg receiver|) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg
        (fun receiver _ => abs_nonneg _)
    _ ≤ (∑ source : Source, batchError source) ^ 2 := by
      nlinarith [htotal, hagg_nonneg, htotal_nonneg]
    _ ≤ (Fintype.card Source : Real) *
          ∑ source : Source, (batchError source) ^ 2 := by
      exact _root_.sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset Source)) (f := batchError)
    _ = _ := by simp

/-- Compose local merge/reassembly with arbitrary scattered packet ownership.
The merge bounds each cohort's aggregate output-cell L1 error; ownership
redistributes each cell's error across destinations with exact L1
conservation. The next-register squared error then costs only one factor for
the number of incoming cohorts. -/
theorem packetized_merge_owner_errors_sq_sum_le
    {Source Packet Receiver : Type}
    [Fintype Source] [Fintype Packet] [Fintype Receiver]
    (ownerError : Source → Packet → Receiver → Real)
    (cellError : Source → Packet → Real)
    (batchError : Source → Real)
    (howner : ∀ source packet,
      (∑ receiver : Receiver,
        |ownerError source packet receiver|) =
          |cellError source packet|)
    (hmerge : ∀ source,
      (∑ packet : Packet, |cellError source packet|) ≤ batchError source) :
    (∑ receiver : Receiver,
      (∑ source : Source, ∑ packet : Packet,
        ownerError source packet receiver) ^ 2) ≤
      (Fintype.card Source : Real) *
        ∑ source : Source, (batchError source) ^ 2 := by
  apply packetized_source_errors_sq_sum_le ownerError batchError
  intro source
  calc
    _ = ∑ packet : Packet, |cellError source packet| := by
      apply Finset.sum_congr rfl
      intro packet _
      exact howner source packet
    _ ≤ batchError source := hmerge source

/-- Global version of the packetized layer bound. A destination may receive
errors from only `k` source cohorts, while each source's routed L1 error is
charged at most once across all destinations. This incidence form avoids a
factor equal to the total number of registers; for `WireFlow`, `k = 65`. -/
theorem packetized_source_errors_sq_sum_le_of_degree
    {Source Packet Receiver : Type}
    [Fintype Source] [Fintype Packet] [Fintype Receiver]
    [DecidableEq Source]
    (err : Source → Packet → Receiver → Real)
    (batchError : Source → Real) (incident : Source → Receiver → Prop)
    [DecidableRel incident]
    (k : Nat)
    (hdegree : ∀ receiver,
      ((Finset.univ : Finset Source).filter
        (fun source => incident source receiver)).card ≤ k)
    (hzero : ∀ source receiver, ¬ incident source receiver →
      ∀ packet, err source packet receiver = 0)
    (hbatch : ∀ source,
      (∑ receiver : Receiver, ∑ packet : Packet,
        |err source packet receiver|) ≤ batchError source) :
    (∑ receiver : Receiver,
      (∑ source : Source, ∑ packet : Packet,
        err source packet receiver) ^ 2) ≤
      (k : Real) * ∑ source : Source, (batchError source) ^ 2 := by
  classical
  let mass (source : Source) (receiver : Receiver) : Real :=
    ∑ packet : Packet, |err source packet receiver|
  let Incident (receiver : Receiver) : Finset Source :=
    (Finset.univ : Finset Source).filter (fun source => incident source receiver)
  have hmass_nonneg (source : Source) (receiver : Receiver) :
      0 ≤ mass source receiver := by
    dsimp [mass]
    exact Finset.sum_nonneg (fun packet _ => abs_nonneg _)
  have hmass_zero (source : Source) (receiver : Receiver)
      (hnot : ¬ incident source receiver) : mass source receiver = 0 := by
    apply Finset.sum_eq_zero
    intro packet _
    rw [hzero source receiver hnot packet]
    simp
  have hmass_total (source : Source) :
      (∑ receiver : Receiver, mass source receiver) ≤ batchError source := by
    simpa [mass] using hbatch source
  have hbatch_nonneg (source : Source) : 0 ≤ batchError source := by
    calc
      0 ≤ ∑ receiver : Receiver, mass source receiver :=
        Finset.sum_nonneg (fun receiver _ => hmass_nonneg source receiver)
      _ ≤ batchError source := hmass_total source
  have hmass_support (receiver : Receiver) :
      (∑ source : Source, mass source receiver) =
        ∑ source ∈ Incident receiver, mass source receiver := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro source _
    by_cases h : incident source receiver
    · simp [h]
    · simp [h, hmass_zero source receiver h]
  have hmass_sq (receiver : Receiver) :
      (∑ source : Source, mass source receiver) ^ 2 ≤
        (k : Real) * ∑ source : Source, (mass source receiver) ^ 2 := by
    rw [hmass_support]
    have hc := _root_.sq_sum_le_card_mul_sum_sq
      (s := Incident receiver) (f := fun source => mass source receiver)
    have hcard : (Incident receiver).card ≤ k := hdegree receiver
    have hsub :
        (∑ source ∈ Incident receiver, (mass source receiver) ^ 2) ≤
          ∑ source : Source, (mass source receiver) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro source hs
        simp
      · intro source _ _
        positivity
    have hfilter_nonneg :
        0 ≤ ∑ source ∈ Incident receiver, (mass source receiver) ^ 2 :=
      Finset.sum_nonneg (fun source _ => sq_nonneg _)
    have hsum_nonneg :
        0 ≤ ∑ source : Source, (mass source receiver) ^ 2 :=
      Finset.sum_nonneg (fun source _ => sq_nonneg _)
    have hcardR : ((Incident receiver).card : Real) ≤ k := by exact_mod_cast hcard
    calc
      _ ≤ ((Incident receiver).card : Real) *
            ∑ source ∈ Incident receiver, (mass source receiver) ^ 2 := by
        simpa using hc
      _ ≤ (k : Real) * ∑ source : Source, (mass source receiver) ^ 2 := by
        exact mul_le_mul hcardR hsub hfilter_nonneg (by positivity)
  have hreceiver (receiver : Receiver) :
      (∑ source : Source, ∑ packet : Packet,
        err source packet receiver) ^ 2 ≤
        (k : Real) * ∑ source : Source, (mass source receiver) ^ 2 := by
    have htriangle :
        |∑ source : Source, ∑ packet : Packet,
          err source packet receiver| ≤ ∑ source : Source, mass source receiver := by
      calc
        _ ≤ ∑ source : Source,
            |∑ packet : Packet, err source packet receiver| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ source : Source, mass source receiver := by
          apply Finset.sum_le_sum
          intro source _
          dsimp [mass]
          exact Finset.abs_sum_le_sum_abs _ _
    have hsum_nonneg : 0 ≤ ∑ source : Source, mass source receiver :=
      Finset.sum_nonneg (fun source _ => hmass_nonneg source receiver)
    have hsq := hmass_sq receiver
    have habs_nonneg := abs_nonneg
      (∑ source : Source, ∑ packet : Packet, err source packet receiver)
    have hsqAbs :
        |∑ source : Source, ∑ packet : Packet,
          err source packet receiver| ^ 2 ≤
          (∑ source : Source, mass source receiver) ^ 2 :=
      (sq_le_sq₀ habs_nonneg hsum_nonneg).2 htriangle
    calc
      (∑ source : Source, ∑ packet : Packet,
        err source packet receiver) ^ 2 =
          |∑ source : Source, ∑ packet : Packet,
            err source packet receiver| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ source : Source, mass source receiver) ^ 2 := hsqAbs
      _ ≤ (k : Real) * ∑ source : Source,
          (mass source receiver) ^ 2 := hsq
  calc
    _ ≤ ∑ receiver : Receiver,
          (k : Real) * ∑ source : Source,
            (mass source receiver) ^ 2 := by
      apply Finset.sum_le_sum
      intro receiver _
      exact hreceiver receiver
    _ = (k : Real) *
          ∑ source : Source, ∑ receiver : Receiver,
            (mass source receiver) ^ 2 := by
      calc
        _ = ∑ receiver : Receiver, ∑ source : Source,
              (k : Real) * (mass source receiver) ^ 2 := by
          apply Finset.sum_congr rfl
          intro receiver _
          rw [Finset.mul_sum]
        _ = ∑ source : Source, ∑ receiver : Receiver,
              (k : Real) * (mass source receiver) ^ 2 := by
          rw [Finset.sum_comm]
        _ = ∑ source : Source,
              (k : Real) * ∑ receiver : Receiver,
                (mass source receiver) ^ 2 := by
          apply Finset.sum_congr rfl
          intro source _
          rw [← Finset.mul_sum]
        _ = _ := by rw [← Finset.mul_sum]
    _ ≤ (k : Real) *
          ∑ source : Source, (batchError source) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro source _
      have hsum_sq := Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset Receiver))
        (f := mass source)
        (fun receiver _ => hmass_nonneg source receiver)
      have hmassSum_nonneg : 0 ≤ ∑ receiver : Receiver, mass source receiver :=
        Finset.sum_nonneg (fun receiver _ => hmass_nonneg source receiver)
      have hmass2 :
          (∑ receiver : Receiver, (mass source receiver) ^ 2) ≤
            (batchError source) ^ 2 := by
        calc
          _ ≤ (∑ receiver : Receiver, mass source receiver) ^ 2 := hsum_sq
          _ ≤ (batchError source) ^ 2 := by
            nlinarith [hmass_total source, hbatch_nonneg source, hmassSum_nonneg]
      exact hmass2

/-- Degree-sensitive composition of the local merge estimate and exact
rank-piece ownership. This is the interface needed by the fixed 65-port
WireFlow scheduler: one must still prove the incidence and zero-support
premises for the concrete layer. -/
theorem packetized_merge_owner_errors_sq_sum_le_of_degree
    {Source Packet Receiver : Type}
    [Fintype Source] [Fintype Packet] [Fintype Receiver]
    [DecidableEq Source]
    (ownerError : Source → Packet → Receiver → Real)
    (cellError : Source → Packet → Real)
    (batchError : Source → Real)
    (incident : Source → Receiver → Prop) [DecidableRel incident]
    (k : Nat)
    (hdegree : ∀ receiver,
      ((Finset.univ : Finset Source).filter
        (fun source => incident source receiver)).card ≤ k)
    (hzero : ∀ source receiver, ¬ incident source receiver →
      ∀ packet, ownerError source packet receiver = 0)
    (howner : ∀ source packet,
      (∑ receiver : Receiver, |ownerError source packet receiver|) =
        |cellError source packet|)
    (hmerge : ∀ source,
      (∑ packet : Packet, |cellError source packet|) ≤ batchError source) :
    (∑ receiver : Receiver,
      (∑ source : Source, ∑ packet : Packet,
        ownerError source packet receiver) ^ 2) ≤
      (k : Real) * ∑ source : Source, (batchError source) ^ 2 := by
  apply packetized_source_errors_sq_sum_le_of_degree
    ownerError batchError incident k hdegree hzero
  intro source
  calc
    _ = ∑ packet : Packet,
          ∑ receiver : Receiver, |ownerError source packet receiver| := by
      rw [Finset.sum_comm]
    _ = ∑ packet : Packet, |cellError source packet| := by
      apply Finset.sum_congr rfl
      intro packet _
      exact howner source packet
    _ ≤ batchError source := hmerge source

/-- Rank pieces sent from `source` to `receiver`: child receivers get the
middle piece indexed by their child digit, and the parent gets both fringes. -/
def wireFlowLayerSelection {d : Nat} (receiver source : KBag 64 d) : Finset Nat :=
  (range 66).filter (fun i =>
    (1 ≤ receiver.l ∧ source = receiver.parent ∧ i = receiver.x % 64 + 1) ∨
    (1 ≤ source.l ∧ receiver = source.parent ∧ (i = 0 ∨ i = 65)))

theorem wireFlowLayerSelection_mem {d : Nat} (receiver source : KBag 64 d)
    (i : Nat) :
    i ∈ wireFlowLayerSelection receiver source ↔
      i ∈ range 66 ∧
        ((1 ≤ receiver.l ∧ source = receiver.parent ∧ i = receiver.x % 64 + 1) ∨
          (1 ≤ source.l ∧ receiver = source.parent ∧ (i = 0 ∨ i = 65))) := by
  simp only [wireFlowLayerSelection, Finset.mem_filter]

/-- Every selected sender rank piece, after the stage permutation, lies in
its designated physical receiver register. This is the set-level routing
fact behind `wireFlowReceiver_selected_count_eq_register`. -/
theorem wireFlowLayer_selectedPiece_image_subset_register {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (receiver source : KBag 64 d) (hb : 1 ≤ receiver.l) (hchild : receiver.l < d)
    (i : Nat) (hi : i ∈ wireFlowLayerSelection receiver source) :
    (senderOutgoingPiece (wireSets F t source) (F.up source.l t)
      (F.down source.l t) i).image (X F nets input (t + 1)) ⊆
      (execPlacement F nets input (t + 1) (by omega)).regs receiver := by
  classical
  rw [wireFlowLayerSelection_mem] at hi
  rcases hi.2 with ⟨hlev, hsource, hindex⟩ | ⟨hsourcelev, hreceiver, hfringe⟩
  · have hport : receiver.x % 64 < 64 := Nat.mod_lt _ (by omega)
    have hpiece := (senderOutgoingPieces_are_WireFlow_ports
      (wireSets F t receiver.parent) (F.up receiver.parent.l t)
      (F.down receiver.parent.l t)).2 (receiver.x % 64) hport
    rw [execPlacement_succ_regs F nets input t ht receiver hlev]
    apply Finset.Subset.trans ?_ Finset.subset_union_left
    simp only [fromParentK]
    rw [hsource, hindex, hpiece]
    exact Finset.Subset.rfl
  · subst receiver
    have hparentlt : source.parent.l < d := hchild
    have hparentSucc : source.parent.l + 1 = source.l := by
      rw [KBag.parent_l]
      omega
    have jlt : source.x % 64 < 64 := Nat.mod_lt _ (by omega)
    let j : Fin 64 := ⟨source.x % 64, jlt⟩
    have hsourceChild : source.parent.child j.val j.isLt hparentlt = source :=
      KBag.parent_child source hsourcelev (by norm_num) hparentlt
    have hports := senderOutgoingPieces_are_WireFlow_ports
      (wireSets F t source) (F.up source.l t) (F.down source.l t)
    have hpieceUp : senderOutgoingPiece (wireSets F t source)
        (F.up source.l t) (F.down source.l t) i ⊆
        upSet (wireSets F t source) (F.up source.l t) := by
      rw [← hports.1]
      rcases hfringe with hzero | hlast
      · rw [hzero]
        exact Finset.subset_union_left
      · rw [hlast]
        exact Finset.subset_union_right
    have himage :
        (senderOutgoingPiece (wireSets F t source) (F.up source.l t)
          (F.down source.l t) i).image (X F nets input (t + 1)) ⊆
          (upSet (wireSets F t source) (F.up source.l t)).image
            (X F nets input (t + 1)) :=
      Finset.image_subset_image hpieceUp
    rw [execPlacement_succ_regs F nets input t ht source.parent
      hb]
    apply Finset.Subset.trans ?_ Finset.subset_union_right
    unfold fromChildrenK
    rw [dif_pos hparentlt]
    intro w hw
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨j, ?_⟩
    rw [hsourceChild]
    simpa [hparentSucc] using himage hw

/-- Pulling back through the stage permutation, a selected sender piece is a
subset of the receiver's next static WireFlow wire set. Thus every rank in
that interval has the designated next-stage owner. -/
theorem wireFlowLayer_selectedPiece_subset_nextWireSet {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (receiver source : KBag 64 d) (hb : 1 ≤ receiver.l) (hchild : receiver.l < d)
    (i : Nat) (hi : i ∈ wireFlowLayerSelection receiver source) :
    senderOutgoingPiece (wireSets F t source) (F.up source.l t)
      (F.down source.l t) i ⊆ wireSets F (t + 1) receiver := by
  intro w hw
  have himage := wireFlowLayer_selectedPiece_image_subset_register
    F nets input t ht receiver source hb hchild i hi
    (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  change X F nets input (t + 1) w ∈
    (wireSets F (t + 1) receiver).image (X F nets input (t + 1)) at himage
  rcases Finset.mem_image.mp himage with ⟨w', hw', heq⟩
  have heqw : w' = w := X_injective F nets input (t + 1) heq
  simpa [heqw] using hw'

theorem wireFlowLayerSelection_subset {d : Nat} (receiver source : KBag 64 d) :
    wireFlowLayerSelection receiver source ⊆ range 66 := by
  intro i hi
  rw [wireFlowLayerSelection_mem] at hi
  exact hi.1

/-- Distinct receivers select disjoint rank-piece indices from a fixed
source bag. Child digits are unique; the parent's fringe indices are outside
the child-index range. -/
theorem wireFlowLayerSelection_pairwise_disjoint {d : Nat}
    (source receiver₁ receiver₂ : KBag 64 d) (hne : receiver₁ ≠ receiver₂) :
    Disjoint (wireFlowLayerSelection receiver₁ source)
      (wireFlowLayerSelection receiver₂ source) := by
  classical
  apply Finset.disjoint_left.2
  intro i hi₁ hi₂
  rw [wireFlowLayerSelection_mem] at hi₁ hi₂
  rcases hi₁.2 with hp₁ | hc₁ <;> rcases hi₂.2 with hp₂ | hc₂
  · have hparent : receiver₁.parent = receiver₂.parent :=
      hp₁.2.1.symm.trans hp₂.2.1
    have hport : receiver₁.x % 64 = receiver₂.x % 64 := by omega
    have hpX₁ : source.x = receiver₁.x / 64 := by
      have h := congrArg KBag.x hp₁.2.1
      simpa [KBag.parent] using h
    have hpX₂ : source.x = receiver₂.x / 64 := by
      have h := congrArg KBag.x hp₂.2.1
      simpa [KBag.parent] using h
    have hx₁ : receiver₁.x = 64 * source.x + receiver₁.x % 64 := by
      have h := Nat.mod_add_div receiver₁.x 64
      omega
    have hx₂ : receiver₂.x = 64 * source.x + receiver₂.x % 64 := by
      have h := Nat.mod_add_div receiver₂.x 64
      omega
    have hl : receiver₁.l = receiver₂.l := by
      have h := congrArg KBag.l hparent
      rw [KBag.parent_l, KBag.parent_l] at h
      omega
    apply hne
    exact KBag.ext hl (by rw [hx₁, hx₂, hport])
  · have hport : 0 < receiver₁.x % 64 + 1 ∧ receiver₁.x % 64 + 1 ≤ 64 := by
      have hmod := Nat.mod_lt receiver₁.x (by norm_num : 0 < 64)
      omega
    rcases hc₂.2.2 with hiZero | hiLast <;> omega
  · have hport : 0 < receiver₂.x % 64 + 1 ∧ receiver₂.x % 64 + 1 ≤ 64 := by
      have hmod := Nat.mod_lt receiver₂.x (by norm_num : 0 < 64)
      omega
    rcases hc₁.2.2 with hiZero | hiLast <;> omega
  · exact hne (hc₁.2.1.trans hc₂.2.1.symm)

/-- Every piece of an interior source bag is routed to exactly one active
receiver: pieces 1 through 64 go to its children, and the two fringe pieces
go to its parent. The two level restrictions exclude the root and top frontier. -/
theorem wireFlowLayerSelection_active_cover {d : Nat}
    (source : KBag 64 d) (hlo : 2 ≤ source.l)
    (hhi : source.l + 2 ≤ d) (i : Nat) (hi : i ∈ range 66) :
    ∃ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      i ∈ wireFlowLayerSelection receiver source := by
  rw [mem_range] at hi
  rcases eq_or_lt_of_le (show i ≤ 65 by omega) with hlast | hlt
  · subst i
    refine ⟨source.parent, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simp [KBag.parent_l]
      omega
    · rw [wireFlowLayerSelection_mem]
      refine ⟨mem_range.mpr (by omega), Or.inr ⟨by omega, rfl, Or.inr rfl⟩⟩
  · by_cases hzero : i = 0
    · subst i
      refine ⟨source.parent, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simp [KBag.parent_l]
        omega
      · rw [wireFlowLayerSelection_mem]
        refine ⟨mem_range.mpr (by omega), Or.inr ⟨by omega, rfl, Or.inl rfl⟩⟩
    · have hidx : 1 ≤ i ∧ i ≤ 64 := by omega
      let receiver := source.child (i - 1) (by omega) (by omega)
      refine ⟨receiver, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · change 1 ≤ source.l + 1 ∧ source.l + 1 < d
        omega
      · rw [wireFlowLayerSelection_mem]
        have hlevel : 1 ≤ receiver.l := by
          simp [receiver, KBag.child_l]
        have hparent : source = receiver.parent := by
          dsimp [receiver]
          exact (KBag.child_parent source (i - 1) (by omega) (by omega)
            (by norm_num)).symm
        have hmod : receiver.x % 64 = i - 1 := by
          change (64 * source.x + (i - 1)) % 64 = i - 1
          omega
        have hindex : i = receiver.x % 64 + 1 := by omega
        refine ⟨mem_range.mpr (by omega), Or.inl ⟨hlevel, hparent, hindex⟩⟩

/-- The active receiver assigned to each of an interior sender's 66 rank
pieces. The active-cover theorem supplies existence, and selector disjointness
makes this owner unique. -/
noncomputable def wireFlowLayerPieceOwner {d : Nat}
    (source : KBag 64 d) (hlo : 2 ≤ source.l)
    (hhi : source.l + 2 ≤ d) (i : Fin 66) : KBag 64 d :=
  Classical.choose
    (wireFlowLayerSelection_active_cover source hlo hhi i.val
      (Finset.mem_range.mpr i.isLt))

theorem wireFlowLayerPieceOwner_spec {d : Nat}
    (source : KBag 64 d) (hlo : 2 ≤ source.l)
    (hhi : source.l + 2 ≤ d) (i : Fin 66) :
    wireFlowLayerPieceOwner source hlo hhi i ∈
        (Finset.univ : Finset (KBag 64 d)).filter
          (fun b => 1 ≤ b.l ∧ b.l < d) ∧
      i.val ∈ wireFlowLayerSelection
        (wireFlowLayerPieceOwner source hlo hhi i) source :=
  Classical.choose_spec
    (wireFlowLayerSelection_active_cover source hlo hhi i.val
      (Finset.mem_range.mpr i.isLt))

/-- The chosen interval owner equals a receiver exactly when that receiver
selects the interval. This is the finite owner map needed by the abstract
owner-count interpolation lemma. -/
theorem wireFlowLayerPieceOwner_eq_iff_selected {d : Nat}
    (source receiver : KBag 64 d) (hlo : 2 ≤ source.l)
    (hhi : source.l + 2 ≤ d) (i : Fin 66) :
    wireFlowLayerPieceOwner source hlo hhi i = receiver ↔
      i.val ∈ wireFlowLayerSelection receiver source := by
  constructor
  · intro heq
    subst receiver
    exact (wireFlowLayerPieceOwner_spec source hlo hhi i).2
  · intro hselected
    by_contra hne
    have hdis := wireFlowLayerSelection_pairwise_disjoint source
      (wireFlowLayerPieceOwner source hlo hhi i) receiver hne
    exact (Finset.disjoint_left.mp hdis)
      (wireFlowLayerPieceOwner_spec source hlo hhi i).2 hselected

/-- The integer count profile induced by the chosen interval-owner map is
exactly the profile of the intervals selected for that receiver. -/
theorem wireFlowLayerPieceOwner_profileCount_eq_selected {d m : Nat}
    (source receiver : KBag 64 d) (hlo : 2 ≤ source.l)
    (hhi : source.l + 2 ≤ d) (cuts : Nat → Nat) (X : Nat) :
    profileIntervalOwnerCount (m := m) cuts
        (wireFlowLayerPieceOwner source hlo hhi) receiver X =
      profileIntervalSelectedCount (m := m) cuts
        (wireFlowLayerSelection receiver source) X := by
  classical
  unfold profileIntervalOwnerCount profileIntervalSelectedCount
  let f : Nat → Nat := fun i => if hi : i < 66 then
    if wireFlowLayerPieceOwner source hlo hhi ⟨i, hi⟩ = receiver then
      profileInterval m X (cuts i) (cuts (i + 1)) else 0 else 0
  change (∑ i : Fin 66, f i.val) =
    ∑ i ∈ wireFlowLayerSelection receiver source,
      profileInterval m X (cuts i) (cuts (i + 1))
  rw [Fin.sum_univ_eq_sum_range f 66]
  change (∑ i ∈ range 66, f i) =
    ∑ i ∈ (range 66).filter (fun i =>
      (1 ≤ receiver.l ∧ source = receiver.parent ∧ i = receiver.x % 64 + 1) ∨
      (1 ≤ source.l ∧ receiver = source.parent ∧ (i = 0 ∨ i = 65))),
      profileInterval m X (cuts i) (cuts (i + 1))
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  have hi66 : i < 66 := Finset.mem_range.mp hi
  have howner := wireFlowLayerPieceOwner_eq_iff_selected
    source receiver hlo hhi ⟨i, hi66⟩
  simp [f, hi66, howner, wireFlowLayerSelection, Fin.val_mk]

/-- The interpolated owner target for the 66 sender intervals is exactly the
selected-interval target. This is the target equality needed by the cohort
parity L2 estimate. -/
theorem wireFlowLayerPieceOwner_profileMean_eq_selected {d m : Nat}
    (source receiver : KBag 64 d) (hlo : 2 ≤ source.l)
    (hhi : source.l + 2 ≤ d) (cuts : Nat → Nat) (q : Nat) (frac : Real) :
    (∑ i : Fin 66,
      if wireFlowLayerPieceOwner source hlo hhi i = receiver then
        profileIntervalMean m q frac (cuts i.val) (cuts (i.val + 1)) else 0) =
      (∑ i ∈ wireFlowLayerSelection receiver source,
        profileIntervalMean m q frac (cuts i) (cuts (i + 1))) := by
  rw [profileIntervalOwnerMean_eq_interp
    (m := m) (p := 66) cuts (wireFlowLayerPieceOwner source hlo hhi)
    receiver q frac]
  rw [profileIntervalSelectedMean_eq_interp cuts
    (wireFlowLayerSelection receiver source) q frac]
  unfold natProfileInterp
  rw [wireFlowLayerPieceOwner_profileCount_eq_selected
      source receiver hlo hhi cuts q,
    wireFlowLayerPieceOwner_profileCount_eq_selected
      source receiver hlo hhi cuts (q + 1)]

/-- On an interior sender, a rank wire belongs to receiver `b` at the next
WireFlow time exactly when its unique outgoing rank piece is selected by
`b`. This is the pointwise owner/cut alignment needed to identify the
parity-rebinned target with the selected-interval target. -/
theorem wireFlowLayer_pieceOwner_iff_selected {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (source receiver : KBag 64 d) (hsourceLo : 2 ≤ source.l)
    (hsourceHi : source.l + 2 ≤ d)
    (hb : 1 ≤ receiver.l) (hreceiverChild : receiver.l < d)
    (i : Nat) (hi : i ∈ range 66) (w : Fin (64 ^ d))
    (hw : w ∈ senderOutgoingPiece (wireSets F t source)
      (F.up source.l t) (F.down source.l t) i) :
    wireSetOwner F (t + 1) (by omega) w = receiver ↔
      i ∈ wireFlowLayerSelection receiver source := by
  constructor
  · intro howner
    have hnext : t + 1 ≤ tf := by omega
    have hmem : w ∈ wireSets F (t + 1) receiver :=
      (wireSetOwner_eq_iff_mem F (t + 1) hnext w receiver).1 howner
    have hrExist : ∃ r : KBag 64 d,
        r ∈ (Finset.univ : Finset (KBag 64 d)).filter
          (fun b => 1 ≤ b.l ∧ b.l < d) ∧
          i ∈ wireFlowLayerSelection r source :=
      wireFlowLayerSelection_active_cover source hsourceLo hsourceHi i hi
    obtain ⟨r, hractive, hrsel⟩ := hrExist
    have hrlevel := (Finset.mem_filter.mp hractive).2
    have hmemr := wireFlowLayer_selectedPiece_subset_nextWireSet
      F nets input t ht r source hrlevel.1 hrlevel.2 i hrsel hw
    have hrEq : r = receiver := by
      by_contra hne
      have hdis := wireSets_disjoint F hnext r receiver hne
      exact (Finset.disjoint_left.mp hdis) hmemr hmem
    simpa [hrEq] using hrsel
  · intro hsel
    have hnext : t + 1 ≤ tf := by omega
    have hmem := wireFlowLayer_selectedPiece_subset_nextWireSet
      F nets input t ht receiver source hb hreceiverChild i hsel hw
    exact (wireSetOwner_eq_iff_mem F (t + 1) hnext w receiver).2 hmem

/-- On every wire of an interior sender piece, the physical next-stage owner
is exactly the receiver selected by the finite piece-owner map. -/
theorem wireFlowLayer_selectedPiece_owner_eq_pieceOwner {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (source : KBag 64 d) (hsourceLo : 2 ≤ source.l)
    (hsourceHi : source.l + 2 ≤ d) (i : Fin 66)
    (w : Fin (64 ^ d))
    (hw : w ∈ senderOutgoingPiece (wireSets F t source)
      (F.up source.l t) (F.down source.l t) i.val) :
    wireSetOwner F (t + 1) (by omega) w =
      wireFlowLayerPieceOwner source hsourceLo hsourceHi i := by
  have hspec := wireFlowLayerPieceOwner_spec source hsourceLo hsourceHi i
  have hactive := (Finset.mem_filter.mp hspec.1).2
  have hselected := hspec.2
  have hi : i.val ∈ range 66 := Finset.mem_range.mpr i.isLt
  exact (wireFlowLayer_pieceOwner_iff_selected F nets input t ht source
    (wireFlowLayerPieceOwner source hsourceLo hsourceHi i)
    hsourceLo hsourceHi hactive.1 hactive.2 i.val hi w hw).2 hselected

/-- On interior source levels, the active receiver selectors partition the
whole 66-piece sender profile, not merely a subset of it. -/

theorem wireFlowLayerSelection_active_union_eq_range {d : Nat}
    (source : KBag 64 d) (hlo : 2 ≤ source.l) (hhi : source.l + 2 ≤ d) :
    (Finset.univ.filter (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
      (fun receiver => wireFlowLayerSelection receiver source) = range 66 := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨receiver, hreceiver, hpiece⟩ := Finset.mem_biUnion.mp hi
    exact wireFlowLayerSelection_subset receiver source hpiece
  · intro hi
    obtain ⟨receiver, hreceiver, hpiece⟩ :=
      wireFlowLayerSelection_active_cover source hlo hhi i hi
    exact Finset.mem_biUnion.mpr ⟨receiver, hreceiver, hpiece⟩

/-- A low-frontier source (root or first level) sends exactly its middle 64
pieces to active children; its parent fringe receiver is inactive. -/
theorem wireFlowLayerSelection_active_union_low {d : Nat}
    (source : KBag 64 d) (hlow : source.l ≤ 1)
    (hchild : source.l + 1 < d) :
    (Finset.univ.filter (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
      (fun receiver => wireFlowLayerSelection receiver source) =
      (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64) := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨receiver, hreceiver, hpiece⟩ := Finset.mem_biUnion.mp hi
    rw [wireFlowLayerSelection_mem] at hpiece
    rcases hpiece.2 with hfromChild | hfromParent
    · exact Finset.mem_filter.mpr ⟨hpiece.1, by
        have hmod := Nat.mod_lt receiver.x (by norm_num : 0 < 64)
        omega⟩
    · have hreceiverParent := congrArg KBag.l hfromParent.2.1
      rw [KBag.parent_l] at hreceiverParent
      have : receiver.l = 0 := by omega
      have hactive := (Finset.mem_filter.mp hreceiver).2.1
      omega
  · intro hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hindex := (Finset.mem_filter.mp hi).1
    let receiver := source.child (i - 1) (by omega) (by omega)
    have hreceiverLevel : 1 ≤ receiver.l ∧ receiver.l < d := by
      change 1 ≤ source.l + 1 ∧ source.l + 1 < d
      omega
    have hparent : source = receiver.parent := by
      dsimp [receiver]
      exact (KBag.child_parent source (i - 1) (by omega) (by omega)
        (by norm_num)).symm
    have hmod : receiver.x % 64 = i - 1 := by
      change (64 * source.x + (i - 1)) % 64 = i - 1
      omega
    have hpiece : i ∈ wireFlowLayerSelection receiver source := by
      rw [wireFlowLayerSelection_mem]
      refine ⟨hindex, Or.inl ⟨hreceiverLevel.1, hparent, ?_⟩⟩
      omega
    exact Finset.mem_biUnion.mpr ⟨receiver,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreceiverLevel⟩, hpiece⟩

/-- At the upper frontier, an active source reaches only its two parent-fringe
pieces; no active receiver exists below those pieces. -/
theorem wireFlowLayerSelection_active_union_high {d : Nat}
    (source : KBag 64 d) (hlo : 2 ≤ source.l)
    (hhigh : d ≤ source.l + 1) :
    (Finset.univ.filter (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
      (fun receiver => wireFlowLayerSelection receiver source) = {0, 65} := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨receiver, hreceiver, hpiece⟩ := Finset.mem_biUnion.mp hi
    rw [wireFlowLayerSelection_mem] at hpiece
    rcases hpiece.2 with hfromChild | hfromParent
    · have hlevel := congrArg KBag.l hfromChild.2.1
      rw [KBag.parent_l] at hlevel
      have hactive := (Finset.mem_filter.mp hreceiver).2.2
      have hsourced : source.l ≤ d := source.hl
      omega
    · rcases hfromParent.2.2 with hzero | hlast
      · simp [hzero]
      · simp [hlast]
  · intro hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hzero | hlast
    · subst i
      let receiver := source.parent
      have hreceiverLevel : 1 ≤ receiver.l ∧ receiver.l < d := by
        change 1 ≤ source.l - 1 ∧ source.l - 1 < d
        have hsourced : source.l ≤ d := source.hl
        omega
      have hpiece : 0 ∈ wireFlowLayerSelection receiver source := by
        rw [wireFlowLayerSelection_mem]
        exact ⟨mem_range.mpr (by omega), Or.inr ⟨by omega, rfl, Or.inl rfl⟩⟩
      exact Finset.mem_biUnion.mpr ⟨receiver,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreceiverLevel⟩, hpiece⟩
    · subst i
      let receiver := source.parent
      have hreceiverLevel : 1 ≤ receiver.l ∧ receiver.l < d := by
        change 1 ≤ source.l - 1 ∧ source.l - 1 < d
        have hsourced : source.l ≤ d := source.hl
        omega
      have hpiece : 65 ∈ wireFlowLayerSelection receiver source := by
        rw [wireFlowLayerSelection_mem]
        exact ⟨mem_range.mpr (by omega), Or.inr ⟨by omega, rfl, Or.inr rfl⟩⟩
      exact Finset.mem_biUnion.mpr ⟨receiver,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreceiverLevel⟩, hpiece⟩

/-- Complete selector geometry for every source bag once the tree has height
at least three: low sources send the 64 middle pieces, interior sources send
all 66, and top-frontier sources send only the two fringes. -/
theorem wireFlowLayerSelection_active_union_complete {d : Nat}
    (hd : 3 ≤ d) (source : KBag 64 d) :
    (source.l ≤ 1 ∧
      (Finset.univ.filter (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
        (fun receiver => wireFlowLayerSelection receiver source) =
          (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64)) ∨
    (2 ≤ source.l ∧ source.l + 2 ≤ d ∧
      (Finset.univ.filter (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
        (fun receiver => wireFlowLayerSelection receiver source) = range 66) ∨
    (2 ≤ source.l ∧ d ≤ source.l + 1 ∧
      (Finset.univ.filter (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
        (fun receiver => wireFlowLayerSelection receiver source) = {0, 65}) := by
  by_cases hlow : source.l ≤ 1
  · exact Or.inl ⟨hlow,
      wireFlowLayerSelection_active_union_low source hlow (by omega)⟩
  · have hsource : 2 ≤ source.l := by omega
    by_cases hmid : source.l + 2 ≤ d
    · exact Or.inr (Or.inl ⟨hsource, hmid,
        wireFlowLayerSelection_active_union_eq_range source hsource hmid⟩)
    · exact Or.inr (Or.inr ⟨hsource, by omega,
        wireFlowLayerSelection_active_union_high source hsource (by omega)⟩)

/-- Any exact active-selector union identity immediately gives the matching
additive conservation identity, since selectors for distinct receivers are
pairwise disjoint. -/
theorem wireFlowLayerSelection_active_sum_eq_union {d : Nat}
    {M : Type*} [AddCommMonoid M] (source : KBag 64 d) (pieces : Finset Nat)
    (hunion : (Finset.univ.filter
      (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
        (fun receiver => wireFlowLayerSelection receiver source) = pieces)
    (f : Nat → M) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      ∑ i ∈ wireFlowLayerSelection receiver source, f i) =
      ∑ i ∈ pieces, f i := by
  classical
  let active := (Finset.univ : Finset (KBag 64 d)).filter
    (fun b => 1 ≤ b.l ∧ b.l < d)
  have hdis : Set.PairwiseDisjoint (↑active : Set (KBag 64 d))
      (fun receiver => wireFlowLayerSelection receiver source) := by
    intro receiver hreceiver other hother hne
    exact wireFlowLayerSelection_pairwise_disjoint source receiver other hne
  calc
    (∑ receiver ∈ active,
      ∑ i ∈ wireFlowLayerSelection receiver source, f i) =
        ∑ i ∈ active.biUnion (fun receiver => wireFlowLayerSelection receiver source),
          f i := (Finset.sum_biUnion hdis).symm
    _ = ∑ i ∈ pieces, f i := by rw [hunion]

theorem wireFlowLayerSelection_active_sum_eq_low {d : Nat}
    {M : Type*} [AddCommMonoid M] (source : KBag 64 d)
    (hlow : source.l ≤ 1) (hchild : source.l + 1 < d) (f : Nat → M) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      ∑ i ∈ wireFlowLayerSelection receiver source, f i) =
      ∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64), f i :=
  wireFlowLayerSelection_active_sum_eq_union source _
    (wireFlowLayerSelection_active_union_low source hlow hchild) f

theorem wireFlowLayerSelection_active_sum_eq_high {d : Nat}
    {M : Type*} [AddCommMonoid M] (source : KBag 64 d)
    (hlo : 2 ≤ source.l) (hhigh : d ≤ source.l + 1) (f : Nat → M) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      ∑ i ∈ wireFlowLayerSelection receiver source, f i) =
      f 0 + f 65 := by
  rw [wireFlowLayerSelection_active_sum_eq_union source {0, 65}
    (wireFlowLayerSelection_active_union_high source hlo hhigh) f]
  simp

/-- Consequently, summing any additive piece quantity over the active
receivers preserves the exact full source total on interior bag levels. -/
theorem wireFlowLayerSelection_active_sum_eq_range {d : Nat}
    {M : Type*} [AddCommMonoid M] (source : KBag 64 d)
    (hlo : 2 ≤ source.l) (hhi : source.l + 2 ≤ d) (f : Nat → M) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      ∑ i ∈ wireFlowLayerSelection receiver source, f i) =
      ∑ i ∈ range 66, f i := by
  classical
  let active := (Finset.univ : Finset (KBag 64 d)).filter
    (fun b => 1 ≤ b.l ∧ b.l < d)
  have hdis : Set.PairwiseDisjoint (↑active : Set (KBag 64 d))
      (fun receiver => wireFlowLayerSelection receiver source) := by
    intro receiver hreceiver other hother hne
    exact wireFlowLayerSelection_pairwise_disjoint source receiver other hne
  calc
    (∑ receiver ∈ active,
      ∑ i ∈ wireFlowLayerSelection receiver source, f i) =
        ∑ i ∈ active.biUnion (fun receiver => wireFlowLayerSelection receiver source),
          f i := (Finset.sum_biUnion hdis).symm
    _ = ∑ i ∈ range 66, f i := by
      rw [wireFlowLayerSelection_active_union_eq_range source hlo hhi]

/-- Actual bag-indexed incidence bound: summing the absolute routed-profile
errors over every receiver in the 64-ary tree charges each sender's coarse
count error only once. The hypotheses carry the source sorting and ideal-count
invariants; the routing disjointness itself is proved above. -/
theorem wireFlowLayer_profile_error_sum_le {d N : Nat}
    (S : KBag 64 d → Finset (Fin N)) (v : KBag 64 d → Fin N → Bool)
    (up down q : KBag 64 d → Nat) (frac : KBag 64 d → Real)
    (hsize : ∀ source, (S source).card = up source + 64 * down source)
    (hu : ∀ source, 2 ∣ up source)
    (hsorted : ∀ source,
      Monotone (v source ∘ (S source).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤ (S source).card)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source, q source = (S source).card → frac source = 0) :
    (∑ receiver : KBag 64 d,
      |∑ source : KBag 64 d,
        ∑ i ∈ wireFlowLayerSelection receiver source,
          ((trueCountOn
            (senderOutgoingPiece (S source) (up source) (down source) i)
            (v source) : Real) -
          profileIntervalMean (S source).card (q source) (frac source)
            (senderRankCut (up source) (down source) i)
            (senderRankCut (up source) (down source) (i + 1)))|) ≤
      ∑ source : KBag 64 d,
        |(trueCountOn (S source) (v source) : Real) - (q source + frac source)| := by
  classical
  exact sum_receiver_profile_errors_le_source_count_errors
    S v up down q frac hsize hu hsorted hq hfrac0 hfrac1
    hendpoint
    wireFlowLayerSelection
    (fun receiver source => wireFlowLayerSelection_subset receiver source)
    (fun source receiver₁ receiver₂ hne =>
      wireFlowLayerSelection_pairwise_disjoint source receiver₁ receiver₂ hne)

def wireFlowReceiverSource {d : Nat} (b : KBag 64 d) (hchild : b.l < d)
    (source : Fin 65) : KBag 64 d :=
  if h : source.val = 0 then b.parent
  else b.child (source.val - 1) (by have hs := source.isLt; omega) hchild

def wireFlowReceiverChildSource (j : Fin 64) : Fin 65 :=
  ⟨j.val + 1, by have hj := j.isLt; omega⟩

theorem wireFlowReceiverSource_parent {d : Nat} (b : KBag 64 d) (hchild : b.l < d) :
    wireFlowReceiverSource b hchild ⟨0, by omega⟩ = b.parent := by
  simp [wireFlowReceiverSource]

theorem wireFlowReceiverSource_child {d : Nat} (b : KBag 64 d) (hchild : b.l < d)
    (j : Fin 64) :
    wireFlowReceiverSource b hchild (wireFlowReceiverChildSource j) =
      b.child j.val j.isLt hchild := by
  simp [wireFlowReceiverSource, wireFlowReceiverChildSource]

/-- For each receiver, the global bag selector agrees on its 65 actual
neighbors with the local parent-plus-children selector used by the register
identity. -/
theorem wireFlowLayerSelection_receiverSource {d : Nat}
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d) (source : Fin 65) :
    wireFlowLayerSelection b (wireFlowReceiverSource b hchild source) =
      receiverOutgoingSelection (b.x % 64) source := by
  classical
  rcases source with ⟨s, hslt⟩
  by_cases hs : s = 0
  · subst s
    have hnotParentParent : b ≠ b.parent.parent := by
      intro h
      have hl := congrArg KBag.l h
      rw [KBag.parent_l, KBag.parent_l] at hl
      omega
    ext i
    rw [wireFlowLayerSelection_mem, wireFlowReceiverSource_parent]
    simp [receiverOutgoingSelection, Fin.val_mk]
    constructor
    · intro h
      rcases h.2 with hp | hc
      · exact hp.2
      · exact False.elim (hnotParentParent hc.2.1)
    · intro h
      refine ⟨?_, Or.inl ⟨hb, h⟩⟩
      have hmod := Nat.mod_lt b.x (by norm_num : 0 < 64)
      change i < 66
      omega
  · have hj : s - 1 < 64 := by omega
    let j : Fin 64 := ⟨s - 1, hj⟩
    have hsource : (⟨s, hslt⟩ : Fin 65) = wireFlowReceiverChildSource j := by
      apply Fin.ext
      simp [j, wireFlowReceiverChildSource]
      omega
    rw [hsource]
    have hbag := wireFlowReceiverSource_child b hchild j
    have hchildParent : (b.child j.val j.isLt hchild).parent = b :=
      KBag.child_parent b j.val j.isLt hchild (by omega)
    ext i
    rw [wireFlowLayerSelection_mem, hbag]
    simp only [receiverOutgoingSelection, wireFlowReceiverChildSource,
      Fin.val_mk]
    have hjnz : ¬(j.val + 1 = 0) := by omega
    rw [if_neg hjnz]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      rcases h.2 with hp | hc
      · have hl := congrArg KBag.l hp.2.1
        rw [KBag.child_l, KBag.parent_l] at hl
        omega
      · exact hc.2.2
    · intro h
      have hmod := Nat.mod_lt b.x (by norm_num : 0 < 64)
      rcases h with h | h
      · refine ⟨?_, Or.inr ⟨by simp [KBag.child_l], hchildParent.symm, Or.inl h⟩⟩
        exact mem_range.mpr (by omega)
      · refine ⟨?_, Or.inr ⟨by simp [KBag.child_l], hchildParent.symm, Or.inr h⟩⟩
        exact mem_range.mpr (by omega)

/-- The source bags incident to an active receiver: its parent followed by its
64 children (when present). -/
def wireFlowReceiverNeighborBags {d : Nat} (b : KBag 64 d) (hchild : b.l < d) :
    Finset (KBag 64 d) :=
  insert (b.parent (by omega))
    (Finset.univ.image (fun j : Fin 64 => b.child j.val j.isLt hchild))

theorem wireFlowReceiverNeighborBags_mem {d : Nat}
    (b : KBag 64 d) (hchild : b.l < d) (source : KBag 64 d) :
    source ∈ wireFlowReceiverNeighborBags b hchild ↔
      source = b.parent ∨ ∃ j : Fin 64, source = b.child j.val j.isLt hchild := by
  simp [wireFlowReceiverNeighborBags, eq_comm]

/-- The global selector vanishes outside the actual parent/children source
bags of an active receiver. -/
theorem wireFlowLayerSelection_eq_empty_of_not_neighbor {d : Nat}
    (b source : KBag 64 d) (hchild : b.l < d)
    (hnot : source ∉ wireFlowReceiverNeighborBags b hchild) :
    wireFlowLayerSelection b source = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  rw [wireFlowLayerSelection_mem] at hi
  rcases hi.2 with hp | hc
  · exact hnot ((wireFlowReceiverNeighborBags_mem b hchild source).2 (Or.inl hp.2.1))
  · have hparent_lt : (source.parent).l < d := by simpa [hc.2.1] using hchild
    have hpc := KBag.parent_child source hc.1 (by omega) hparent_lt
    have hsrc : source = b.child (source.x % 64)
        (Nat.mod_lt _ (by omega)) hchild := by
      simpa [← hc.2.1] using hpc.symm
    exact hnot ((wireFlowReceiverNeighborBags_mem b hchild source).2
      (Or.inr ⟨⟨source.x % 64, Nat.mod_lt _ (by omega)⟩, hsrc⟩))

theorem fin65_sum_parent_children {α : Type*} [AddCommMonoid α]
    (f : Fin 65 → α) :
    (∑ source : Fin 65, f source) =
      f ⟨0, by omega⟩ + ∑ j : Fin 64, f (wireFlowReceiverChildSource j) := by
  rw [Fin.sum_univ_succ]
  congr 1

/-- Reindex the global source sum for one active receiver onto its actual
parent-plus-children `Fin 65` source map. -/
theorem wireFlowLayerSelection_receiverSum_eq {d : Nat}
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (f : KBag 64 d → Nat → Real) :
    (∑ source : KBag 64 d,
      ∑ i ∈ wireFlowLayerSelection b source, f source i) =
    (∑ source : Fin 65,
      ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
        f (wireFlowReceiverSource b hchild source) i) := by
  classical
  let g : KBag 64 d → Real := fun source =>
    ∑ i ∈ wireFlowLayerSelection b source, f source i
  let neighbors := wireFlowReceiverNeighborBags b hchild
  have hzero (source : KBag 64 d) (hnot : source ∉ neighbors) : g source = 0 := by
    simp [g, wireFlowLayerSelection_eq_empty_of_not_neighbor b source hchild hnot]
  have hparentNotChild :
      b.parent ∉ Finset.univ.image (fun j : Fin 64 => b.child j.val j.isLt hchild) := by
    intro h
    obtain ⟨j, _, hEq⟩ := Finset.mem_image.mp h
    have hl := congrArg KBag.l hEq
    rw [KBag.parent_l, KBag.child_l] at hl
    omega
  have hchildInj : Function.Injective (fun j : Fin 64 => b.child j.val j.isLt hchild) := by
    intro j k hEq
    apply Fin.ext
    exact KBag.child_inj b j.val k.val j.isLt k.isLt hchild hEq
  calc
    (∑ source : KBag 64 d, g source) =
        ∑ source ∈ Finset.univ, g source := by simp
    _ = ∑ source ∈ neighbors, g source := by
      symm
      exact Finset.sum_subset (Finset.subset_univ neighbors) (by
        intro source _ hnot
        exact hzero source hnot)
    _ = g b.parent + ∑ j : Fin 64, g (b.child j.val j.isLt hchild) := by
      simp only [neighbors, wireFlowReceiverNeighborBags]
      rw [Finset.sum_insert hparentNotChild]
      rw [Finset.sum_image]
      exact hchildInj.injOn
    _ = ∑ source : Fin 65, g (wireFlowReceiverSource b hchild source) := by
      rw [fin65_sum_parent_children]
      rw [wireFlowReceiverSource_parent]
      simp_rw [wireFlowReceiverSource_child]
    _ = ∑ source : Fin 65,
        ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
          f (wireFlowReceiverSource b hchild source) i := by
      apply Finset.sum_congr rfl
      intro source _
      simp only [g]
      rw [wireFlowLayerSelection_receiverSource b hb hchild source]

/-- Reindex any source-bag quantity supported on a receiver's neighbors to
the receiver's canonical parent-plus-children `Fin 65` family. -/
theorem wireFlowReceiverNeighborSum_eq {d : Nat}
    (b : KBag 64 d) (hchild : b.l < d)
    (f : KBag 64 d → Real)
    (hzero : ∀ source, source ∉ wireFlowReceiverNeighborBags b hchild → f source = 0) :
    (∑ source : KBag 64 d, f source) =
      ∑ source : Fin 65, f (wireFlowReceiverSource b hchild source) := by
  classical
  let neighbors := wireFlowReceiverNeighborBags b hchild
  have hparentNotChild :
      b.parent ∉ Finset.univ.image (fun j : Fin 64 => b.child j.val j.isLt hchild) := by
    intro h
    obtain ⟨j, _, hEq⟩ := Finset.mem_image.mp h
    have hl := congrArg KBag.l hEq
    rw [KBag.parent_l, KBag.child_l] at hl
    omega
  have hchildInj : Function.Injective (fun j : Fin 64 => b.child j.val j.isLt hchild) := by
    intro j k hEq
    apply Fin.ext
    exact KBag.child_inj b j.val k.val j.isLt k.isLt hchild hEq
  calc
    (∑ source : KBag 64 d, f source) = ∑ source ∈ Finset.univ, f source := by simp
    _ = ∑ source ∈ neighbors, f source := by
      symm
      exact Finset.sum_subset (Finset.subset_univ neighbors) (by
        intro source _ hnot
        exact hzero source hnot)
    _ = f b.parent + ∑ j : Fin 64, f (b.child j.val j.isLt hchild) := by
      simp only [neighbors, wireFlowReceiverNeighborBags]
      rw [Finset.sum_insert hparentNotChild]
      rw [Finset.sum_image]
      exact hchildInj.injOn
    _ = ∑ source : Fin 65, f (wireFlowReceiverSource b hchild source) := by
      rw [fin65_sum_parent_children]
      rw [wireFlowReceiverSource_parent]
      simp_rw [wireFlowReceiverSource_child]



theorem receiverOutgoingSelection_sum (parentPort : Nat)
    (source : Fin 65) (f : Nat → Nat) :
    (∑ i ∈ receiverOutgoingSelection parentPort source, f i) =
      if source.val = 0 then f (parentPort + 1) else f 0 + f 65 := by
  by_cases hs : source.val = 0
  · simp [receiverOutgoingSelection, hs]
  · simp [receiverOutgoingSelection, hs]

/-- Instantiate the parent/children profile estimate on the actual source
wire sets and flow sizes from `WireFlow`. The sortedness premise says each
sender's post-stage Boolean values are in rank order. The theorem bounds the
sum of selected incoming-piece counts; identifying that sum with a count on
`execPlacement.regs` still requires the disjoint-image adapter. -/
theorem wireFlowReceiver_count_error_actual {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (predicate : Fin (64 ^ d) → Bool)
    (q : Fin 65 → Nat) (frac : Fin 65 → Real)
    (hsorted : ∀ source, Monotone
      ((fun w => predicate (X F nets input (t + 1) w)) ∘
        (wireSets F t (wireFlowReceiverSource b hchild source)).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤
      (wireSets F t (wireFlowReceiverSource b hchild source)).card)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source,
      q source = (wireSets F t (wireFlowReceiverSource b hchild source)).card →
        frac source = 0) :
    |(∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
        ((trueCountOn
          (senderOutgoingPiece (wireSets F t (wireFlowReceiverSource b hchild source))
            (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) i)
          (fun w => predicate (X F nets input (t + 1) w))) : Real) -
      ∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
        profileIntervalMean
          (wireSets F t (wireFlowReceiverSource b hchild source)).card
          (q source) (frac source)
          (senderRankCut (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) i)
          (senderRankCut (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) (i + 1)))| ≤
      ∑ source : Fin 65,
        |(trueCountOn (wireSets F t (wireFlowReceiverSource b hchild source))
          (fun w => predicate (X F nets input (t + 1) w)) : Real) -
          (q source + frac source)| := by
  let S : Fin 65 → Finset (Fin (64 ^ d)) :=
    fun source => wireSets F t (wireFlowReceiverSource b hchild source)
  let val : Fin 65 → Fin (64 ^ d) → Bool :=
    fun _ w => predicate (X F nets input (t + 1) w)
  let up : Fin 65 → Nat := fun source =>
    F.up (wireFlowReceiverSource b hchild source).l t
  let down : Fin 65 → Nat := fun source =>
    F.down (wireFlowReceiverSource b hchild source).l t
  have hinv := wireSets_inv F t (Nat.le_of_lt ht)
  have hsize : ∀ source, (S source).card = up source + 64 * down source := by
    intro source
    change (wireSets F t (wireFlowReceiverSource b hchild source)).card = _
    rw [hinv.1 (wireFlowReceiverSource b hchild source)]
    exact F.hsplit _ _ (wireFlowReceiverSource b hchild source).hl ht
  have hu : ∀ source, 2 ∣ up source := by
    intro source
    exact F.hup_even _ _ ht
  have hsorted' : ∀ source, Monotone (val source ∘ (S source).orderEmbOfFin rfl) := by
    intro source
    exact hsorted source
  have hq' : ∀ source, q source ≤ (S source).card := hq
  have hendpoint' : ∀ source, q source = (S source).card → frac source = 0 := hendpoint
  have hfrac0' : ∀ source, 0 ≤ frac source := hfrac0
  have hfrac1' : ∀ source, frac source ≤ 1 := hfrac1
  have hparentPort : b.x % 64 < 64 := Nat.mod_lt _ (by omega)
  simpa [S, val, up, down] using
    (wireFlowReceiver_count_error_le S val up down q frac hsize hu hsorted'
      hq' hfrac0' hfrac1' hendpoint' (b.x % 64) hparentPort)

/-- The selected interval counts in the previous theorem are exactly the
threshold count on the receiver's actual `execPlacement` register. This uses
the parent/child port decomposition, injectivity of execution, and disjoint
source bags; it removes the selected-sum versus receiver-count gap. -/
theorem wireFlowReceiver_selected_count_eq_register {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (predicate : Fin (64 ^ d) → Bool) :
    (∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
      trueCountOn
        (senderOutgoingPiece (wireSets F t (wireFlowReceiverSource b hchild source))
          (F.up (wireFlowReceiverSource b hchild source).l t)
          (F.down (wireFlowReceiverSource b hchild source).l t) i)
        (fun w => predicate (X F nets input (t + 1) w))) =
       trueCountOn ((execPlacement F nets input (t + 1) (by omega)).regs b) predicate := by
  let Xout := X F nets input (t + 1)
  let sourceBag := wireFlowReceiverSource b hchild
  let senderSet (source : Fin 65) := wireSets F t (sourceBag source)
  let senderUp (source : Fin 65) := F.up (sourceBag source).l t
  let senderDown (source : Fin 65) := F.down (sourceBag source).l t
  let value (w : Fin (64 ^ d)) := predicate (Xout w)
  let source0 : Fin 65 := ⟨0, by omega⟩
  have hsource0 : sourceBag source0 = b.parent := by
    exact wireFlowReceiverSource_parent b hchild
  have hXinj : Function.Injective Xout := X_injective F nets input (t + 1)
  have hinv := wireSets_inv F t (Nat.le_of_lt ht)
  have hparentPort : b.x % 64 < 64 := Nat.mod_lt _ (by omega)
  have hparentPiece :
      senderOutgoingPiece (wireSets F t b.parent) (F.up b.parent.l t)
          (F.down b.parent.l t) (b.x % 64 + 1) =
        downSet (wireSets F t b.parent) (F.up b.parent.l t)
          (F.down b.parent.l t) (b.x % 64) :=
    (senderOutgoingPieces_are_WireFlow_ports (wireSets F t b.parent)
      (F.up b.parent.l t) (F.down b.parent.l t)).2 _ hparentPort
  have hparentSelected :
      (∑ i ∈ receiverOutgoingSelection (b.x % 64) source0,
        trueCountOn (senderOutgoingPiece (senderSet source0) (senderUp source0)
          (senderDown source0) i) value) =
        trueCountOn (fromParentK F nets input t b) predicate := by
    have hsourceZero : wireFlowReceiverSource b hchild 0 = b.parent := by
      simpa [source0] using hsource0
    simp only [receiverOutgoingSelection, source0, Fin.val_mk, if_pos rfl,
      Finset.sum_singleton]
    dsimp [senderSet, senderUp, senderDown, sourceBag]
    simp only [Finset.sum_singleton]
    rw [hsourceZero, hparentPiece]
    symm
    simp [fromParentK, hb, KBag.parent_l, Xout]
    rw [trueCountOn_image _ Xout hXinj predicate]
    rfl
  have hsourceSize (source : Fin 65) :
      (senderSet source).card = senderUp source + 64 * senderDown source := by
    calc
      (senderSet source).card = F.a (sourceBag source).l t := hinv.1 (sourceBag source)
      _ = senderUp source + 64 * senderDown source :=
        F.hsplit _ _ (sourceBag source).hl ht
  have hchildPieceDisjoint (j : Fin 64) :
      Disjoint
        (senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
          (F.up (b.l + 1) t) (F.down (b.l + 1) t) 0)
        (senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
          (F.up (b.l + 1) t) (F.down (b.l + 1) t) 65) := by
    let s := wireSets F t (b.child j.val j.isLt hchild)
    let up := F.up (b.l + 1) t
    let down := F.down (b.l + 1) t
    have hsize : s.card = up + 64 * down := by
      simpa [s, up, down, KBag.child_l] using
        (hinv.1 (b.child j.val j.isLt hchild)).trans
          (F.hsplit (b.l + 1) t (by omega) ht)
    have heven : 2 ∣ up := F.hup_even _ _ ht
    rw [senderOutgoingPiece_eq_blockOf s up down hsize heven 0 (by omega),
      senderOutgoingPiece_eq_blockOf s up down hsize heven 65 (by omega)]
    have hcut : senderRankCut up down 1 ≤ senderRankCut up down 65 := by
      simp [senderRankCut]
    exact disjoint_blockOf hcut
  have hchildCount (j : Fin 64) :
      (∑ i ∈ receiverOutgoingSelection (b.x % 64)
          (wireFlowReceiverChildSource j),
        trueCountOn
          (senderOutgoingPiece (senderSet (wireFlowReceiverChildSource j))
            (senderUp (wireFlowReceiverChildSource j))
            (senderDown (wireFlowReceiverChildSource j)) i) value) =
        trueCountOn
          ((upSet (wireSets F t (b.child j.val j.isLt hchild))
              (F.up (b.l + 1) t)).image Xout) predicate := by
    let childSource := wireFlowReceiverChildSource j
    have hchildSourceNe : childSource ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp [childSource, wireFlowReceiverChildSource] at hv
    have hbag : sourceBag childSource = b.child j.val j.isLt hchild :=
      wireFlowReceiverSource_child b hchild j
    have hports := senderOutgoingPieces_are_WireFlow_ports
      (wireSets F t (b.child j.val j.isLt hchild)) (F.up (b.l + 1) t)
      (F.down (b.l + 1) t)
    have hdisImage : Disjoint
        ((senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
          (F.up (b.l + 1) t) (F.down (b.l + 1) t) 0).image Xout)
        ((senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
          (F.up (b.l + 1) t) (F.down (b.l + 1) t) 65).image Xout) := by
      rw [Finset.disjoint_image hXinj]
      exact hchildPieceDisjoint j
    calc
      _ = trueCountOn
          (senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
            (F.up (b.l + 1) t) (F.down (b.l + 1) t) 0) value +
          trueCountOn
          (senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
            (F.up (b.l + 1) t) (F.down (b.l + 1) t) 65) value := by
        simp [receiverOutgoingSelection, childSource, hchildSourceNe,
          wireFlowReceiverSource_child, sourceBag, senderSet, senderUp, senderDown,
          value, KBag.child_l]
      _ = trueCountOn
          ((senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
              (F.up (b.l + 1) t) (F.down (b.l + 1) t) 0 ∪
            senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
              (F.up (b.l + 1) t) (F.down (b.l + 1) t) 65).image Xout) predicate := by
        rw [Finset.image_union,
          trueCountOn_union_disjoint _ _ hdisImage predicate]
        rw [trueCountOn_image _ Xout hXinj, trueCountOn_image _ Xout hXinj]
        rfl
      _ = trueCountOn
          ((upSet (wireSets F t (b.child j.val j.isLt hchild))
              (F.up (b.l + 1) t)).image Xout) predicate := by
        rw [hports.1]
  have hchildPairDisjoint (j k : Fin 64) (hjk : j ≠ k) :
      Disjoint
        ((upSet (wireSets F t (b.child j.val j.isLt hchild))
          (F.up (b.l + 1) t)).image Xout)
        ((upSet (wireSets F t (b.child k.val k.isLt hchild))
          (F.up (b.l + 1) t)).image Xout) := by
    rw [Finset.disjoint_image hXinj]
    apply Disjoint.mono upSet_subset upSet_subset
    apply hinv.2.1
    intro he
    apply hjk
    exact Fin.ext (KBag.child_inj b j.val k.val j.isLt k.isLt hchild he)
  have hchildrenCount :
      trueCountOn (fromChildrenK F nets input t b) predicate =
        ∑ j : Fin 64,
          trueCountOn
            ((upSet (wireSets F t (b.child j.val j.isLt hchild))
                (F.up (b.l + 1) t)).image Xout) predicate := by
    unfold fromChildrenK
    rw [dif_pos hchild]
    rw [trueCountOn_biUnion Finset.univ
      (fun j : Fin 64 =>
        (upSet (wireSets F t (b.child j.val j.isLt hchild))
          (F.up (b.l + 1) t)).image Xout)
      (by
        intro j _ k _ hjk
        exact hchildPairDisjoint j k hjk) predicate]
  have hparentChildDisjoint :
      Disjoint (fromParentK F nets input t b) (fromChildrenK F nets input t b) := by
    unfold fromParentK fromChildrenK
    rw [dif_pos hchild, Finset.disjoint_biUnion_right]
    intro j hj
    rw [Finset.disjoint_image hXinj]
    apply Disjoint.mono downSet_subset upSet_subset
    apply hinv.2.1
    intro he
    have hl := congrArg KBag.l he
    rw [KBag.parent_l, KBag.child_l] at hl
    omega
  have hregisterCount :
      trueCountOn ((execPlacement F nets input (t + 1) (by omega)).regs b) predicate =
        trueCountOn (fromParentK F nets input t b) predicate +
          trueCountOn (fromChildrenK F nets input t b) predicate := by
    rw [execPlacement_succ_regs F nets input t ht b hb]
    exact trueCountOn_union_disjoint _ _ hparentChildDisjoint predicate
  let pieceCount (source : Fin 65) :=
    ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
      trueCountOn (senderOutgoingPiece (senderSet source) (senderUp source)
        (senderDown source) i) value
  have hsum := fin65_sum_parent_children pieceCount
  calc
    (∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
        trueCountOn
          (senderOutgoingPiece (senderSet source) (senderUp source) (senderDown source) i)
          value) =
      trueCountOn (fromParentK F nets input t b) predicate +
        trueCountOn (fromChildrenK F nets input t b) predicate := by
      rw [hsum]
      change pieceCount source0 + ∑ j : Fin 64, pieceCount (wireFlowReceiverChildSource j) = _
      rw [show pieceCount source0 =
        trueCountOn (fromParentK F nets input t b) predicate from hparentSelected]
      simp_rw [show ∀ j : Fin 64,
        pieceCount (wireFlowReceiverChildSource j) =
          trueCountOn ((upSet (wireSets F t (b.child j.val j.isLt hchild))
            (F.up (b.l + 1) t)).image Xout) predicate from hchildCount]
      rw [← hchildrenCount]
    _ = trueCountOn ((execPlacement F nets input (t + 1) (by omega)).regs b) predicate :=
      hregisterCount.symm

/-- Actual threshold count in one sender's outgoing rank piece. -/
noncomputable def wireFlowLayerSenderPieceCount {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat)
    (predicate : Fin (64 ^ d) → Bool) (source : KBag 64 d) (i : Nat) : Nat :=
  trueCountOn
    (senderOutgoingPiece (wireSets F t source)
      (F.up source.l t) (F.down source.l t) i)
    (fun w => predicate (X F nets input (t + 1) w))

/-- Ideal profile mean assigned to one sender rank piece. -/
def wireFlowLayerSenderPieceMean {d tf : Nat}
    (F : FlowSizes d tf) (t : Nat) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real) (source : KBag 64 d) (i : Nat) : Real :=
  profileIntervalMean (wireSets F t source).card (q source) (frac source)
    (senderRankCut (F.up source.l t) (F.down source.l t) i)
    (senderRankCut (F.up source.l t) (F.down source.l t) (i + 1))

/-- For every interior source bag, summing its ideal rank-piece means over
the active destinations recovers the entire source mean profile. This exact
conservation law is stronger than the one-sided no-amplification estimate. -/
theorem wireFlowLayerSenderPieceMean_active_sum_eq {d tf : Nat}
    (F : FlowSizes d tf) (t : Nat) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real) (source : KBag 64 d)
    (hlo : 2 ≤ source.l) (hhi : source.l + 2 ≤ d) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      ∑ i ∈ wireFlowLayerSelection receiver source,
        wireFlowLayerSenderPieceMean F t q frac source i) =
      ∑ i ∈ range 66, wireFlowLayerSenderPieceMean F t q frac source i := by
  exact wireFlowLayerSelection_active_sum_eq_range source hlo hhi
    (wireFlowLayerSenderPieceMean F t q frac source)

/-- The active destinations receive exactly the source's fractional target
mass, once all source rank pieces are accounted for. -/
theorem wireFlowLayerSenderPieceMean_active_sum_eq_target {d tf : Nat}
    (F : FlowSizes d tf) (t : Nat) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real) (source : KBag 64 d)
    (hsize : (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t)
    (hq : q source ≤ (wireSets F t source).card)
    (hfrac0 : 0 ≤ frac source) (hfrac1 : frac source ≤ 1)
    (hendpoint : q source = (wireSets F t source).card → frac source = 0)
    (hlo : 2 ≤ source.l) (hhi : source.l + 2 ≤ d) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      ∑ i ∈ wireFlowLayerSelection receiver source,
        wireFlowLayerSenderPieceMean F t q frac source i) =
      (q source : Real) + frac source := by
  rw [wireFlowLayerSenderPieceMean_active_sum_eq F t q frac source hlo hhi]
  have hstart := senderRankCut_start (F.up source.l t) (F.down source.l t)
  have hcuts := senderRankCut_mono (F.up source.l t) (F.down source.l t)
  have hend : senderRankCut (F.up source.l t) (F.down source.l t) 66 =
      (wireSets F t source).card := by
    rw [senderRankCut_end, hsize]
  simpa [wireFlowLayerSenderPieceMean] using
    (profileIntervalMean_partition_sum (wireSets F t source).card 66
      (q source) (frac source)
      (senderRankCut (F.up source.l t) (F.down source.l t))
      hstart hcuts hend hq hfrac0 hfrac1 hendpoint)

/-- Signed discrepancy contributed by one routed sender piece. -/
noncomputable def wireFlowLayerSenderPieceError {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real) (source : KBag 64 d) (i : Nat) : Real :=
  (wireFlowLayerSenderPieceCount F nets input t predicate source i : Real) -
    wireFlowLayerSenderPieceMean F t q frac source i

/-- For an interior source bag, the absolute threshold-error mass is routed
across its active receiver pieces exactly once. Cancellation between distinct
sources is deliberately left to the receiver-side recurrence. -/
theorem wireFlowLayer_interior_source_error_mass_conserved {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (source : KBag 64 d) (hlo : 2 ≤ source.l) (hhi : source.l + 2 ≤ d)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real)
    (hsorted : Monotone
      ((fun w => predicate (X F nets input (t + 1) w)) ∘
        (wireSets F t source).orderEmbOfFin rfl))
    (hq : q source ≤ (wireSets F t source).card)
    (hfrac0 : 0 ≤ frac source) (hfrac1 : frac source ≤ 1)
    (hendpoint : q source = (wireSets F t source).card → frac source = 0) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      |∑ i ∈ wireFlowLayerSelection receiver source,
        wireFlowLayerSenderPieceError F nets input t predicate q frac source i|) =
      |(trueCountOn (wireSets F t source)
          (fun w => predicate (X F nets input (t + 1) w)) : Real) -
        (q source + frac source)| := by
  classical
  let receivers := (Finset.univ : Finset (KBag 64 d)).filter
    (fun b => 1 ≤ b.l ∧ b.l < d)
  let v : Fin (64 ^ d) → Bool :=
    fun w => predicate (X F nets input (t + 1) w)
  let err (i : Nat) : Real :=
    wireFlowLayerSenderPieceError F nets input t predicate q frac source i
  have hsize : (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t := by
    rw [wireSets_card _ (Nat.le_of_lt ht)]
    exact F.hsplit source.l t source.hl ht
  have hu : 2 ∣ F.up source.l t := F.hup_even source.l t ht
  have hsign : (∀ i ∈ range 66, 0 ≤ err i) ∨
      (∀ i ∈ range 66, err i ≤ 0) := by
    by_cases hleft : trueCountOn (wireSets F t source) v ≤ q source
    · right
      intro i hi
      have hpiece := (sortedSenderOutgoing_profile_error_piecewise_sign
        (wireSets F t source) v (F.up source.l t) (F.down source.l t)
        (q source) (frac source) hsize hu hsorted hq hfrac0 hfrac1
        hendpoint).1 hleft i hi
      dsimp [err, wireFlowLayerSenderPieceError, v,
        wireFlowLayerSenderPieceCount, wireFlowLayerSenderPieceMean]
      linarith
    · left
      have hright' : q source + 1 ≤ trueCountOn (wireSets F t source) v := by omega
      intro i hi
      have hpiece := (sortedSenderOutgoing_profile_error_piecewise_sign
        (wireSets F t source) v (F.up source.l t) (F.down source.l t)
        (q source) (frac source) hsize hu hsorted hq hfrac0 hfrac1
        hendpoint).2 hright' i hi
      dsimp [err, wireFlowLayerSenderPieceError, v,
        wireFlowLayerSenderPieceCount, wireFlowLayerSenderPieceMean]
      linarith
  have hselected : ∀ receiver ∈ receivers,
      wireFlowLayerSelection receiver source ⊆ range 66 := by
    intro receiver hreceiver
    exact wireFlowLayerSelection_subset receiver source
  have hdisjoint : ∀ receiver₁ ∈ receivers, ∀ receiver₂ ∈ receivers,
      receiver₁ ≠ receiver₂ →
        Disjoint (wireFlowLayerSelection receiver₁ source)
          (wireFlowLayerSelection receiver₂ source) := by
    intro receiver₁ _ receiver₂ _ hne
    exact wireFlowLayerSelection_pairwise_disjoint source receiver₁ receiver₂ hne
  have hunion : receivers.biUnion (fun receiver =>
      wireFlowLayerSelection receiver source) = range 66 := by
    exact wireFlowLayerSelection_active_union_eq_range source hlo hhi
  calc
    (∑ receiver ∈ receivers,
        |∑ i ∈ wireFlowLayerSelection receiver source, err i|) =
      ∑ i ∈ range 66, |err i| :=
        sum_receiver_selected_errors_eq_source_pieces_of_common_sign
          receivers err (fun receiver => wireFlowLayerSelection receiver source)
          hselected hdisjoint hunion hsign
    _ = |(trueCountOn (wireSets F t source) v : Real) -
        (q source + frac source)| := by
      simpa [err, wireFlowLayerSenderPieceError, wireFlowLayerSenderPieceCount,
        wireFlowLayerSenderPieceMean, v] using
        (sortedSenderOutgoing_profile_error_exact_one
          (wireSets F t source) v (F.up source.l t) (F.down source.l t)
          (q source) (frac source) hsize hu hsorted hq hfrac0 hfrac1 hendpoint)

/-- Across all root/first-level source bags, the profile error in the omitted
fringes is bounded by their total up-flow capacity. -/
theorem wireFlowLayer_low_frontier_error_sum_le_up {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1) :
    (∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => b.l ≤ 1 ∧ b.l + 1 < d),
      ∑ i ∈ ({0, 65} : Finset Nat),
        |wireFlowLayerSenderPieceError F nets input t predicate q frac source i|) ≤
      ∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
        (fun b => b.l ≤ 1 ∧ b.l + 1 < d),
        (F.up source.l t : Real) := by
  classical
  apply Finset.sum_le_sum
  intro source hsource
  have hsize : (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t := by
    rw [wireSets_card _ (Nat.le_of_lt ht)]
    exact F.hsplit source.l t source.hl ht
  simpa [wireFlowLayerSenderPieceError, wireFlowLayerSenderPieceCount,
    wireFlowLayerSenderPieceMean] using
    (senderOutgoing_fringe_profile_error_sum_le_up
      (wireSets F t source)
      (fun w => predicate (X F nets input (t + 1) w))
      (F.up source.l t) (F.down source.l t) (q source) (frac source)
      hsize (F.hup_even source.l t ht) (hfrac0 source) (hfrac1 source))

/-- Across all top-frontier source bags, the profile error in the omitted
middle pieces is bounded by their aggregate down-flow capacity. -/
theorem wireFlowLayer_high_frontier_error_sum_le_down {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1) :
    (∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 2 ≤ b.l ∧ d ≤ b.l + 1),
      ∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
        |wireFlowLayerSenderPieceError F nets input t predicate q frac source i|) ≤
      ∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
        (fun b => 2 ≤ b.l ∧ d ≤ b.l + 1),
        (64 * F.down source.l t : Real) := by
  classical
  apply Finset.sum_le_sum
  intro source hsource
  have hsize : (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t := by
    rw [wireSets_card _ (Nat.le_of_lt ht)]
    exact F.hsplit source.l t source.hl ht
  simpa [wireFlowLayerSenderPieceError, wireFlowLayerSenderPieceCount,
    wireFlowLayerSenderPieceMean] using
    (senderOutgoing_middle_profile_error_sum_le_down
      (wireSets F t source)
      (fun w => predicate (X F nets input (t + 1) w))
      (F.up source.l t) (F.down source.l t) (q source) (frac source)
      hsize (F.hup_even source.l t ht) (hfrac0 source) (hfrac1 source))

/-- The root's omitted fringe error vanishes: its up-flow is identically zero. -/
theorem wireFlowLayer_root_fringe_error_eq_zero {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (source : KBag 64 d) (hroot : source.l = 0)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real)
    (hfrac0 : 0 ≤ frac source) (hfrac1 : frac source ≤ 1) :
    (∑ i ∈ ({0, 65} : Finset Nat),
      |wireFlowLayerSenderPieceError F nets input t predicate q frac source i|) = 0 := by
  have hsize : (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t := by
    rw [wireSets_card _ (Nat.le_of_lt ht)]
    exact F.hsplit source.l t source.hl ht
  have hup : F.up source.l t = 0 := by
    rw [hroot]
    exact F.hup_root t ht
  have hle := senderOutgoing_fringe_profile_error_sum_le_up
    (wireSets F t source) (fun w => predicate (X F nets input (t + 1) w))
    (F.up source.l t) (F.down source.l t) (q source) (frac source)
    hsize (F.hup_even source.l t ht) hfrac0 hfrac1
  have hnonneg : 0 ≤ ∑ i ∈ ({0, 65} : Finset Nat),
      |(trueCountOn (senderOutgoingPiece (wireSets F t source)
          (F.up source.l t) (F.down source.l t) i)
          (fun w => predicate (X F nets input (t + 1) w)) : Real) -
        profileIntervalMean (wireSets F t source).card (q source) (frac source)
          (senderRankCut (F.up source.l t) (F.down source.l t) i)
          (senderRankCut (F.up source.l t) (F.down source.l t) (i + 1))| := by
    apply Finset.sum_nonneg
    intro i hi
    exact abs_nonneg _
  have hle0 := by simpa [hup] using hle
  have hnonneg0 := by simpa [hup] using hnonneg
  have hsum := le_antisymm hle0 hnonneg0
  simpa [hup, wireFlowLayerSenderPieceError, wireFlowLayerSenderPieceCount,
    wireFlowLayerSenderPieceMean] using hsum

/-- The bottom leaf's omitted middle error vanishes: it sends no down-flow. -/
theorem wireFlowLayer_leaf_middle_error_eq_zero {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (source : KBag 64 d) (hleaf : source.l = d)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real)
    (hfrac0 : 0 ≤ frac source) (hfrac1 : frac source ≤ 1) :
    (∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
      |wireFlowLayerSenderPieceError F nets input t predicate q frac source i|) = 0 := by
  have hsize : (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t := by
    rw [wireSets_card _ (Nat.le_of_lt ht)]
    exact F.hsplit source.l t source.hl ht
  have hdown : F.down source.l t = 0 := by
    rw [hleaf]
    exact F.hdown_leaf t ht
  have hle := senderOutgoing_middle_profile_error_sum_le_down
    (wireSets F t source) (fun w => predicate (X F nets input (t + 1) w))
    (F.up source.l t) (F.down source.l t) (q source) (frac source)
    hsize (F.hup_even source.l t ht) hfrac0 hfrac1
  have hnonneg : 0 ≤ ∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
      |(trueCountOn (senderOutgoingPiece (wireSets F t source)
          (F.up source.l t) (F.down source.l t) i)
          (fun w => predicate (X F nets input (t + 1) w)) : Real) -
        profileIntervalMean (wireSets F t source).card (q source) (frac source)
          (senderRankCut (F.up source.l t) (F.down source.l t) i)
          (senderRankCut (F.up source.l t) (F.down source.l t) (i + 1))| := by
    apply Finset.sum_nonneg
    intro i hi
    exact abs_nonneg _
  have hle0 := by simpa [hdown] using hle
  have hnonneg0 := by simpa [hdown] using hnonneg
  have hsum := le_antisymm hle0 hnonneg0
  simpa [hdown, wireFlowLayerSenderPieceError, wireFlowLayerSenderPieceCount,
    wireFlowLayerSenderPieceMean] using hsum

private theorem omega7_lt_d_sub_one (d : Nat) (hd : 7 ≤ d)
    (t : Nat) (ht : t < tf7 d) : omega7 d t < d - 1 := by
  by_cases ht0 : t = 0
  · simp [omega7, ht0]
    omega
  · by_cases ht1 : t = 1
    · simp [omega7, ht0, ht1]
      omega
    · have ht2 : 2 ≤ t := by omega
      have hbound := omega7_bounds d t ht2
      unfold tf7 at ht
      omega

/-- In the §7 schedule, level d−1 is already outside the active band at all
ordinary stages, so it sends no down-flow to the leaves. -/
theorem flowDown7_d_sub_one_eq_zero (d : Nat) (hd : 7 ≤ d)
    (t : Nat) (ht : t < tf7 d) : flowDown7 d hd (d - 1) t = 0 := by
  by_cases ht0 : t = 0
  · simp [flowDown7, ht0]
    omega
  · by_cases ht1 : t = 1
    · simp [flowDown7, ht0, ht1]
      omega
    · have ht2 : 2 ≤ t := by omega
      have hnot : ¬Active d (d - 1) t := by
        intro ha
        have hle := ha.2.2.1
        have hstrict := omega7_lt_d_sub_one d hd t ht
        omega
      have hrat := flowDown_inactive d hnot
      have hcast := cast_flowDown7 d hd (d - 1) t ht2 ht
      have hzero : ((flowDown7 d hd (d - 1) t : Nat) : Rat) = 0 := by
        rw [hcast, hrat]
      exact_mod_cast hzero

/-- The level-1 parent send at an ordinary stage is at most its capacity
divided by `4096^2`; this is the geometric envelope for the low-frontier tail. -/
theorem flowUp7_level_one_le_capacity_scale (d : Nat) (hd : 7 ≤ d)
    (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    ((flowUp7 d hd 1 t : Nat) : Rat) ≤ capacity d 1 t / (4096 : Rat) ^ 2 := by
  have hcast := cast_flowUp7 d hd 1 t ht2 ht
  by_cases ha : Active d 1 t
  · have hω := omega7_bounds d t ht2
    have hneω : 1 ≠ omega7 d t := by omega
    by_cases hα : 1 = alpha7 d t
    · by_cases hstep : alpha7 d t < alpha7 d (t + 1)
      · have hup := flowUp_top_desc d ha hα hstep
        rw [hcast.1, hup]
        exact div_nonneg (capacity_nonneg d 1 t) (by positivity)
      · have hup := flowUp_top_rise d ha hα hstep
        rw [hcast.1, hup]
        have hratio : (1 / 64 : Rat) * capacity d 1 t / (4096 * 64) =
            capacity d 1 t / (4096 : Rat) ^ 2 := by
          field_simp
          ring
        rw [hratio]
    · have hup := flowUp_mid d ha hα (fun heq => (hneω heq).elim)
      rw [hcast.1, hup]
      have hcoeff : (4095 : Rat) / capacityRatio ≤
          1 / (4096 : Rat) ^ 2 := by
        rw [capacityRatio_eq]
        norm_num
      have hcap := capacity_nonneg d 1 t
      calc
        (4095 : Rat) * capacity d 1 t / capacityRatio =
            ((4095 : Rat) / capacityRatio) * capacity d 1 t := by ring
        _ ≤ (1 / (4096 : Rat) ^ 2) * capacity d 1 t :=
          mul_le_mul_of_nonneg_right hcoeff hcap
        _ = capacity d 1 t / (4096 : Rat) ^ 2 := by ring
  · have hup := flowUp_inactive d ha
    rw [hcast.1, hup]
    exact div_nonneg (capacity_nonneg d 1 t) (by positivity)

private theorem capacity_level_one_geometric_sum (d n : Nat) :
    (∑ k ∈ range n, capacity d 1 (k + 1)) =
      (64 / 63 : Rat) * (capacity d 1 1 - capacity d 1 (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep := capacity_succ_stage d 1 (n + 1)
      rw [hstep]
      ring

theorem wireFlowLayer_level_one_bags_card_le_64 (d : Nat) :
    ((Finset.univ : Finset (KBag 64 d)).filter (fun b => b.l = 1)).card ≤ 64 := by
  calc
    _ ≤ (Finset.range 64).card := by
      apply Finset.card_le_card_of_injOn
        (fun b : KBag 64 d => b.x)
      · intro b hb
        have hl := (Finset.mem_filter.mp hb).2
        simp only [Finset.mem_range]
        simpa [hl] using b.hx
      · intro a ha b hb hab
        apply KBag.ext
        · have ha' := (Finset.mem_filter.mp ha).2
          have hb' := (Finset.mem_filter.mp hb).2
          omega
        · exact hab
    _ = 64 := by simp

/-- Summed over every ordinary stage starting at t=1, the level-1 up-flow is
bounded by a geometric tail with ratio 1/64. -/
theorem flowUp7_level_one_time_sum_le (d : Nat) (hd : 7 ≤ d) :
    (∑ k ∈ range (tf7 d - 1),
      (flowUp7 d hd 1 (k + 1) : Rat)) ≤
      (64 / 63 : Rat) * (capacity d 1 1 / (4096 : Rat) ^ 2) := by
  have hterm (k : Nat) (hk : k ∈ range (tf7 d - 1)) :
      (flowUp7 d hd 1 (k + 1) : Rat) ≤
        capacity d 1 (k + 1) / (4096 : Rat) ^ 2 := by
    have ht : k + 1 < tf7 d := by
      have hk' := mem_range.mp hk
      unfold tf7 at *
      omega
    by_cases ht1 : k + 1 = 1
    · have hspecial : flowUp7 d hd 1 1 = 64 ^ (d - 5) := by
        simp [flowUp7]
      have hcap := capacity_eq_pow d 1 1 (d - 1) (by omega)
      rw [ht1, hspecial, hcap]
      have hratio : ((64 ^ (d - 5) : Nat) : Rat) =
          (64 : Rat) ^ (d - 1) / (4096 : Rat) ^ 2 := by
        have hexp : d - 1 = (d - 5) + 4 := by omega
        rw [hexp, pow_add]
        norm_num
      rw [hratio, Nat.cast_pow]
      norm_num
    · have ht2 : 2 ≤ k + 1 := by omega
      exact flowUp7_level_one_le_capacity_scale d hd (k + 1) ht2 ht
  calc
    _ ≤ ∑ k ∈ range (tf7 d - 1),
        capacity d 1 (k + 1) / (4096 : Rat) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact hterm k hk
    _ = (∑ k ∈ range (tf7 d - 1), capacity d 1 (k + 1)) /
          (4096 : Rat) ^ 2 := by
      calc
        _ = ∑ k ∈ range (tf7 d - 1),
            capacity d 1 (k + 1) * ((4096 : Rat) ^ 2)⁻¹ := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = (∑ k ∈ range (tf7 d - 1), capacity d 1 (k + 1)) *
            ((4096 : Rat) ^ 2)⁻¹ := by rw [Finset.sum_mul]
        _ = _ := by ring
    _ ≤ (64 / 63 : Rat) * capacity d 1 1 / (4096 : Rat) ^ 2 := by
      have hgeom := capacity_level_one_geometric_sum d (tf7 d - 1)
      rw [hgeom]
      have htfpos : 1 ≤ tf7 d := by unfold tf7; omega
      rw [Nat.sub_add_cancel htfpos]
      have hcap := capacity_nonneg d 1 (tf7 d)
      have hbound : (64 / 63 : Rat) *
          (capacity d 1 1 - capacity d 1 (tf7 d)) ≤
          (64 / 63 : Rat) * capacity d 1 1 := by
        nlinarith [hcap]
      have hden : 0 < (4096 : Rat) ^ 2 := by positivity
      rw [div_le_div_iff_of_pos_right hden]
      field_simp
      nlinarith [hbound]
    _ = (64 / 63 : Rat) *
        (capacity d 1 1 / (4096 : Rat) ^ 2) := by ring

/-- The level-1 up-flow capacity, summed over all its bags and ordinary
stages, is at most 64 copies of the per-bag geometric tail. -/
theorem flowUp7_level_one_aggregate_time_sum_le (d : Nat) (hd : 7 ≤ d) :
    (∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
        (fun b => b.l = 1),
      ∑ k ∈ range (tf7 d - 1),
        (flowUp7 d hd source.l (k + 1) : Rat)) ≤
      64 * ((64 / 63 : Rat) *
        (capacity d 1 1 / (4096 : Rat) ^ 2)) := by
  let sources := (Finset.univ : Finset (KBag 64 d)).filter (fun b => b.l = 1)
  have hlevel (source : KBag 64 d) (hs : source ∈ sources) : source.l = 1 := by
    exact (Finset.mem_filter.mp hs).2
  have hrewrite :
      (∑ source ∈ sources,
        ∑ k ∈ range (tf7 d - 1),
          (flowUp7 d hd source.l (k + 1) : Rat)) =
      (sources.card : Rat) *
        (∑ k ∈ range (tf7 d - 1),
          (flowUp7 d hd 1 (k + 1) : Rat)) := by
    calc
      _ = ∑ source ∈ sources,
          (∑ k ∈ range (tf7 d - 1),
            (flowUp7 d hd 1 (k + 1) : Rat)) := by
        apply Finset.sum_congr rfl
        intro source hs
        apply Finset.sum_congr rfl
        intro k hk
        rw [hlevel source hs]
      _ = (sources.card : Rat) *
          (∑ k ∈ range (tf7 d - 1),
            (flowUp7 d hd 1 (k + 1) : Rat)) := by
        simp [Finset.sum_const]
  have hcard : (sources.card : Rat) ≤ 64 := by
    have h := wireFlowLayer_level_one_bags_card_le_64 d
    exact_mod_cast h
  have htime := flowUp7_level_one_time_sum_le d hd
  have htime_nonneg : 0 ≤
      (∑ k ∈ range (tf7 d - 1),
        (flowUp7 d hd 1 (k + 1) : Rat)) := by
    apply Finset.sum_nonneg
    intro k hk
    positivity
  rw [hrewrite]
  calc
    (sources.card : Rat) *
        (∑ k ∈ range (tf7 d - 1),
          (flowUp7 d hd 1 (k + 1) : Rat)) ≤
        64 * (∑ k ∈ range (tf7 d - 1),
          (flowUp7 d hd 1 (k + 1) : Rat)) :=
      mul_le_mul_of_nonneg_right hcard htime_nonneg
    _ ≤ 64 * ((64 / 63 : Rat) *
          (capacity d 1 1 / (4096 : Rat) ^ 2)) :=
      mul_le_mul_of_nonneg_left htime (by norm_num)

/-- All high-frontier omitted-middle error vanishes in the actual §7 flow:
level d−1 is inactive, and level d has zero down-flow by construction. -/
theorem wireFlowLayer_high_frontier_error_sum_eq_zero {d : Nat}
    (hd : 7 ≤ d) (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf7 d)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1) :
    (∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 2 ≤ b.l ∧ d ≤ b.l + 1),
      ∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
        |wireFlowLayerSenderPieceError (flowSizes7 d hd) nets input t
          predicate q frac source i|) = 0 := by
  let F := flowSizes7 d hd
  have hle := wireFlowLayer_high_frontier_error_sum_le_down
    F nets input t ht predicate q frac hfrac0 hfrac1
  have hdown (source : KBag 64 d)
      (hsource : source ∈ (Finset.univ : Finset (KBag 64 d)).filter
        (fun b => 2 ≤ b.l ∧ d ≤ b.l + 1)) : F.down source.l t = 0 := by
    have hmem := (Finset.mem_filter.mp hsource).2
    have hlevel : source.l = d - 1 ∨ source.l = d := by
      have hsourced : source.l ≤ d := source.hl
      omega
    change flowDown7 d hd source.l t = 0
    rcases hlevel with hlevel | hlevel
    · rw [hlevel]
      exact flowDown7_d_sub_one_eq_zero d hd t ht
    · rw [hlevel]
      exact flowSizes7_down_leaf d hd t ht
  have hrhs : (∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 2 ≤ b.l ∧ d ≤ b.l + 1),
      (64 * F.down source.l t : Real)) = 0 := by
    apply Finset.sum_eq_zero
    intro source hsource
    rw [hdown source hsource]
    simp
  have hnonneg : 0 ≤ (∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b : KBag 64 d => 2 ≤ b.l ∧ d ≤ b.l + 1),
      ∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
        |wireFlowLayerSenderPieceError F nets input t predicate q frac source i|) := by
    apply Finset.sum_nonneg
    intro source hsource
    apply Finset.sum_nonneg
    intro i hi
    exact abs_nonneg _
  have hsum := le_antisymm (by simpa [hrhs] using hle) hnonneg
  simpa [F] using hsum

/-- Sum of the selected ideal means for an active receiver. -/
noncomputable def wireFlowReceiverSelectedIdealMean {d tf : Nat}
    (F : FlowSizes d tf) (t : Nat) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real) (receiver : KBag 64 d) : Real :=
  if hchild : receiver.l < d then
    ∑ source : Fin 65,
      ∑ i ∈ receiverOutgoingSelection (receiver.x % 64) source,
        wireFlowLayerSenderPieceMean F t q frac
          (wireFlowReceiverSource receiver hchild source) i
  else 0

/-- The actual selected target of a receiver is a sum of interpolated integer
counts of the sender rank pieces routed to it. This expresses the existing
WireFlow target in the same count-profile language as packet ownership. -/
theorem wireFlowReceiverSelectedIdealMean_eq_intervalProfile {d tf : Nat}
    (F : FlowSizes d tf) (t : Nat)
    (q : KBag 64 d → Nat) (frac : KBag 64 d → Real)
    (receiver : KBag 64 d) (hchild : receiver.l < d) :
    wireFlowReceiverSelectedIdealMean F t q frac receiver =
      ∑ source : Fin 65,
        natProfileInterp
          (profileIntervalSelectedCount
            (m := (wireSets F t
              (wireFlowReceiverSource receiver hchild source)).card)
            (fun i => senderRankCut
              (F.up (wireFlowReceiverSource receiver hchild source).l t)
              (F.down (wireFlowReceiverSource receiver hchild source).l t) i)
            (receiverOutgoingSelection (receiver.x % 64) source))
          (q (wireFlowReceiverSource receiver hchild source))
          (frac (wireFlowReceiverSource receiver hchild source)) := by
  unfold wireFlowReceiverSelectedIdealMean
  rw [dif_pos hchild]
  apply Finset.sum_congr rfl
  intro source hsource
  simpa [wireFlowLayerSenderPieceMean] using
    (profileIntervalSelectedMean_eq_interp
      (m := (wireSets F t
        (wireFlowReceiverSource receiver hchild source)).card)
      (cuts := fun i => senderRankCut
        (F.up (wireFlowReceiverSource receiver hchild source).l t)
        (F.down (wireFlowReceiverSource receiver hchild source).l t) i)
      (selected := receiverOutgoingSelection (receiver.x % 64) source)
      (q := q (wireFlowReceiverSource receiver hchild source))
      (frac := frac (wireFlowReceiverSource receiver hchild source)))

set_option maxHeartbeats 1000000
/-- The signed all-bag routed discrepancy at an active receiver equals its
actual register threshold count minus the selected ideal means. -/
theorem wireFlowLayer_receiver_signed_error_eq_register {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (receiver : KBag 64 d) (hb : 1 ≤ receiver.l) (hchild : receiver.l < d)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real) :
    (∑ source : KBag 64 d,
      ∑ i ∈ wireFlowLayerSelection receiver source,
        wireFlowLayerSenderPieceError F nets input t predicate q frac source i) =
      (trueCountOn
          ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
          predicate : Real) -
        (wireFlowReceiverSelectedIdealMean F t q frac receiver) := by
  let pieceCount (source : KBag 64 d) (i : Nat) : Real :=
    wireFlowLayerSenderPieceCount F nets input t predicate source i
  let pieceMean (source : KBag 64 d) (i : Nat) : Real :=
    wireFlowLayerSenderPieceMean F t q frac source i
  have hcountsNat := wireFlowReceiver_selected_count_eq_register
    F nets input t ht receiver hb hchild predicate
  have hcounts :
      (∑ source : Fin 65,
        ∑ i ∈ receiverOutgoingSelection (receiver.x % 64) source,
          pieceCount (wireFlowReceiverSource receiver hchild source) i) =
        (trueCountOn
          ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
          predicate : Real) := by
    simpa only [pieceCount, Nat.cast_sum] using
      congrArg (fun n : Nat => (n : Real)) hcountsNat
  have hpieceSum := wireFlowLayerSelection_receiverSum_eq receiver hb hchild
    (fun source i => pieceCount source i - pieceMean source i)
  calc
    _ = ∑ source : Fin 65,
        ∑ i ∈ receiverOutgoingSelection (receiver.x % 64) source,
          (pieceCount (wireFlowReceiverSource receiver hchild source) i -
            pieceMean (wireFlowReceiverSource receiver hchild source) i) := by
      simpa [wireFlowLayerSenderPieceError, pieceCount, pieceMean] using hpieceSum
    _ = (∑ source : Fin 65,
          ∑ i ∈ receiverOutgoingSelection (receiver.x % 64) source,
            pieceCount (wireFlowReceiverSource receiver hchild source) i) -
        ∑ source : Fin 65,
          ∑ i ∈ receiverOutgoingSelection (receiver.x % 64) source,
            pieceMean (wireFlowReceiverSource receiver hchild source) i := by
      simp_rw [Finset.sum_sub_distrib]
    _ = _ := by
      rw [hcounts]
      simp only [pieceMean, wireFlowReceiverSelectedIdealMean, dif_pos hchild]
set_option maxHeartbeats 200000

/-- Aggregate square-error recurrence for the actual active `WireFlow`
receivers. Each receiver combines at most 65 source bags; across receivers,
the source's selected rank pieces are disjoint, so the sum of their squared
contributions is charged once to that source's exact 66-piece L1 error. -/
theorem wireFlowLayer_profile_error_sq_sum_le_source_energy {d N : Nat}
    (S : KBag 64 d → Finset (Fin N)) (v : KBag 64 d → Fin N → Bool)
    (up down q : KBag 64 d → Nat) (frac : KBag 64 d → Real)
    (hsize : ∀ source, (S source).card = up source + 64 * down source)
    (hu : ∀ source, 2 ∣ up source)
    (hsorted : ∀ source, Monotone (v source ∘ (S source).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤ (S source).card)
    (hfrac0 : ∀ source, 0 ≤ frac source) (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source, q source = (S source).card → frac source = 0) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      (∑ source : KBag 64 d,
        ∑ i ∈ wireFlowLayerSelection receiver source,
          ((trueCountOn
            (senderOutgoingPiece (S source) (up source) (down source) i)
            (v source) : Real) -
            profileIntervalMean (S source).card (q source) (frac source)
              (senderRankCut (up source) (down source) i)
              (senderRankCut (up source) (down source) (i + 1)))) ^ 2) ≤
      65 * ∑ source : KBag 64 d,
        |(trueCountOn (S source) (v source) : Real) -
          (q source + frac source)| ^ 2 := by
  classical
  let active := (Finset.univ : Finset (KBag 64 d)).filter
    (fun b => 1 ≤ b.l ∧ b.l < d)
  let err (source : KBag 64 d) (i : Nat) : Real :=
    (trueCountOn (senderOutgoingPiece (S source) (up source) (down source) i)
      (v source) : Real) -
      profileIntervalMean (S source).card (q source) (frac source)
        (senderRankCut (up source) (down source) i)
        (senderRankCut (up source) (down source) (i + 1))
  let sourceError (receiver source : KBag 64 d) : Real :=
    ∑ i ∈ wireFlowLayerSelection receiver source, err source i
  have hfull (source : KBag 64 d) :
      (∑ i ∈ range 66, |err source i|) =
        |(trueCountOn (S source) (v source) : Real) -
          (q source + frac source)| := by
    simpa [err] using sortedSenderOutgoing_profile_error_exact_one
      (S source) (v source) (up source) (down source) (q source) (frac source)
      (hsize source) (hu source) (hsorted source) (hq source)
      (hfrac0 source) (hfrac1 source) (hendpoint source)
  have hlocal (receiver : KBag 64 d) (hb : 1 ≤ receiver.l)
      (hchild : receiver.l < d) :
      (∑ source : KBag 64 d, sourceError receiver source) =
        ∑ source : Fin 65,
          ∑ i ∈ receiverOutgoingSelection (receiver.x % 64) source,
            err (wireFlowReceiverSource receiver hchild source) i := by
    simpa only [sourceError] using
      wireFlowLayerSelection_receiverSum_eq receiver hb hchild
        (fun source i => err source i)
  have hneighborSq (receiver : KBag 64 d) (hb : 1 ≤ receiver.l)
      (hchild : receiver.l < d) :
      (∑ source : KBag 64 d, sourceError receiver source ^ 2) =
        ∑ source : Fin 65,
          (∑ i ∈ receiverOutgoingSelection (receiver.x % 64) source,
            err (wireFlowReceiverSource receiver hchild source) i) ^ 2 := by
    calc
      _ = ∑ source : Fin 65,
          sourceError receiver (wireFlowReceiverSource receiver hchild source) ^ 2 := by
        apply wireFlowReceiverNeighborSum_eq receiver hchild
        intro source hsource
        simp [sourceError, wireFlowLayerSelection_eq_empty_of_not_neighbor
          receiver source hchild hsource]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro source _
        simp only [sourceError]
        rw [wireFlowLayerSelection_receiverSource receiver hb hchild source]
  have hreceiverCS (receiver : KBag 64 d) (hb : 1 ≤ receiver.l)
      (hchild : receiver.l < d) :
      (∑ source : KBag 64 d, sourceError receiver source) ^ 2 ≤
        65 * ∑ source : KBag 64 d, sourceError receiver source ^ 2 := by
    rw [hlocal receiver hb hchild, hneighborSq receiver hb hchild]
    have hcs := _root_.sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin 65)))
      (f := fun source =>
        ∑ i ∈ receiverOutgoingSelection (receiver.x % 64) source,
          err (wireFlowReceiverSource receiver hchild source) i)
    simpa using hcs
  have hsourcePieces (source : KBag 64 d) :
      (∑ receiver : KBag 64 d,
        (∑ i ∈ wireFlowLayerSelection receiver source, err source i) ^ 2) ≤
        (∑ i ∈ range 66, |err source i|) ^ 2 := by
    exact sum_receiver_selected_error_sq_le_source_pieces
      (err source) (fun receiver => wireFlowLayerSelection receiver source)
      (fun receiver => wireFlowLayerSelection_subset receiver source)
      (fun receiver₁ receiver₂ hne =>
        wireFlowLayerSelection_pairwise_disjoint source receiver₁ receiver₂ hne)
  calc
    _ ≤ ∑ receiver ∈ active, 65 *
        ∑ source : KBag 64 d, sourceError receiver source ^ 2 := by
      apply Finset.sum_le_sum
      intro receiver hreceiver
      have hactive := (Finset.mem_filter.mp hreceiver).2
      exact hreceiverCS receiver hactive.1 hactive.2
    _ = 65 * ∑ receiver ∈ active,
        ∑ source : KBag 64 d, sourceError receiver source ^ 2 := by
      rw [← Finset.mul_sum]
    _ = 65 * ∑ source : KBag 64 d,
        ∑ receiver ∈ active, sourceError receiver source ^ 2 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ 65 * ∑ source : KBag 64 d,
        (∑ receiver : KBag 64 d, sourceError receiver source ^ 2) := by
      have h65 : (0 : Real) ≤ 65 := by norm_num
      apply mul_le_mul_of_nonneg_left _ h65
      apply Finset.sum_le_sum
      intro source _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ active) (by
        intro receiver _ _
        exact sq_nonneg _)
    _ ≤ 65 * ∑ source : KBag 64 d,
        (∑ i ∈ range 66, |err source i|) ^ 2 := by
      have h65 : (0 : Real) ≤ 65 := by norm_num
      apply mul_le_mul_of_nonneg_left _ h65
      apply Finset.sum_le_sum
      intro source _
      exact hsourcePieces source
    _ = 65 * ∑ source : KBag 64 d,
        |(trueCountOn (S source) (v source) : Real) -
          (q source + frac source)| ^ 2 := by
      apply congrArg (fun z : Real => 65 * z)
      apply Finset.sum_congr rfl
      intro source _
      rw [hfull source]

/-- Register-level form of the layer square-error recurrence: the abstract
piece sums are exactly the threshold-count discrepancies on the scheduled
receiver registers. -/
theorem wireFlowLayer_register_error_sq_sum_le_source_energy {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (predicate : Fin (64 ^ d) → Bool)
    (q : KBag 64 d → Nat) (frac : KBag 64 d → Real)
    (hsize : ∀ source, (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t)
    (hu : ∀ source : KBag 64 d, 2 ∣ F.up source.l t)
    (hsorted : ∀ source, Monotone
      ((fun w => predicate (X F nets input (t + 1) w)) ∘
        (wireSets F t source).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤ (wireSets F t source).card)
    (hfrac0 : ∀ source, 0 ≤ frac source) (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source, q source = (wireSets F t source).card → frac source = 0) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      ((trueCountOn
          ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
          predicate : Real) -
        wireFlowReceiverSelectedIdealMean F t q frac receiver) ^ 2) ≤
      65 * ∑ source : KBag 64 d,
        |((trueCountOn (wireSets F t source)
            (fun w => predicate (X F nets input (t + 1) w))) : Real) -
          (q source + frac source)| ^ 2 := by
  let S : KBag 64 d → Finset (Fin (64 ^ d)) := wireSets F t
  let v : KBag 64 d → Fin (64 ^ d) → Bool := fun source w =>
    predicate (X F nets input (t + 1) w)
  have hprofile := wireFlowLayer_profile_error_sq_sum_le_source_energy
    S v (fun source => F.up source.l t) (fun source => F.down source.l t)
    q frac hsize hu hsorted hq hfrac0 hfrac1 hendpoint
  have hprofile_eq :
      (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
        (fun b => 1 ≤ b.l ∧ b.l < d),
        (∑ source : KBag 64 d,
          ∑ i ∈ wireFlowLayerSelection receiver source,
            ((trueCountOn
              (senderOutgoingPiece (wireSets F t source)
                (F.up source.l t) (F.down source.l t) i)
              (fun w => predicate (X F nets input (t + 1) w)) : Real) -
              profileIntervalMean (wireSets F t source).card (q source) (frac source)
                (senderRankCut (F.up source.l t) (F.down source.l t) i)
                (senderRankCut (F.up source.l t) (F.down source.l t) (i + 1)))) ^ 2) =
      (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
        (fun b => 1 ≤ b.l ∧ b.l < d),
        ((trueCountOn
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
            predicate : Real) -
          wireFlowReceiverSelectedIdealMean F t q frac receiver) ^ 2) := by
    apply Finset.sum_congr rfl
    intro receiver hreceiver
    have hactive := (Finset.mem_filter.mp hreceiver).2
    rw [← wireFlowLayer_receiver_signed_error_eq_register F nets input t ht
      receiver hactive.1 hactive.2 predicate q frac]
    simp only [wireFlowLayerSenderPieceError, wireFlowLayerSenderPieceCount,
      wireFlowLayerSenderPieceMean, S, v]
  calc
    _ = _ := hprofile_eq.symm
    _ ≤ 65 * ∑ source : KBag 64 d,
        |(trueCountOn (S source) (v source) : Real) -
          (q source + frac source)| ^ 2 := hprofile
    _ = _ := by simp [S, v]

/-- Simultaneous threshold form: summing over all Boolean rank thresholds and
all active receiver levels preserves the same factor-65 energy charge. -/
theorem wireFlowLayer_register_error_sq_sum_le_source_energy_multi
    {d tf : Nat} {Θ : Type} [Fintype Θ] [DecidableEq Θ]
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (predicate : Θ → Fin (64 ^ d) → Bool)
    (q : Θ → KBag 64 d → Nat) (frac : Θ → KBag 64 d → Real)
    (hsize : ∀ source, (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t)
    (hu : ∀ source : KBag 64 d, 2 ∣ F.up source.l t)
    (hsorted : ∀ θ source, Monotone
      ((fun w => predicate θ (X F nets input (t + 1) w)) ∘
        (wireSets F t source).orderEmbOfFin rfl))
    (hq : ∀ θ source, q θ source ≤ (wireSets F t source).card)
    (hfrac0 : ∀ θ source, 0 ≤ frac θ source)
    (hfrac1 : ∀ θ source, frac θ source ≤ 1)
    (hendpoint : ∀ θ source,
      q θ source = (wireSets F t source).card → frac θ source = 0) :
    (∑ θ : Θ,
      ∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
        (fun b => 1 ≤ b.l ∧ b.l < d),
        ((trueCountOn
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
            (predicate θ) : Real) -
          wireFlowReceiverSelectedIdealMean F t (q θ) (frac θ) receiver) ^ 2) ≤
      65 * ∑ θ : Θ, ∑ source : KBag 64 d,
        |((trueCountOn (wireSets F t source)
            (fun w => predicate θ (X F nets input (t + 1) w))) : Real) -
          (q θ source + frac θ source)| ^ 2 := by
  calc
    _ ≤ ∑ θ : Θ,
        65 * ∑ source : KBag 64 d,
          |((trueCountOn (wireSets F t source)
              (fun w => predicate θ (X F nets input (t + 1) w))) : Real) -
            (q θ source + frac θ source)| ^ 2 := by
      apply Finset.sum_le_sum
      intro θ _
      exact wireFlowLayer_register_error_sq_sum_le_source_energy
        F nets input t ht (predicate θ) (q θ) (frac θ) hsize hu
        (hsorted θ) (hq θ) (hfrac0 θ) (hfrac1 θ) (hendpoint θ)
    _ = 65 * ∑ θ : Θ, ∑ source : KBag 64 d,
        |((trueCountOn (wireSets F t source)
            (fun w => predicate θ (X F nets input (t + 1) w))) : Real) -
          (q θ source + frac θ source)| ^ 2 := by
      rw [Finset.mul_sum]

/-- The selected ideal means form a valid Boolean threshold target for the
receiver: they lie between zero and the receiver register capacity. -/
theorem wireFlowReceiverSelectedIdealMean_bounds {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (receiver : KBag 64 d) (hb : 1 ≤ receiver.l) (hchild : receiver.l < d)
    (q : KBag 64 d → Nat) (frac : KBag 64 d → Real)
    (hfrac0 : ∀ source : Fin 65,
      0 ≤ frac (wireFlowReceiverSource receiver hchild source))
    (hfrac1 : ∀ source : Fin 65,
      frac (wireFlowReceiverSource receiver hchild source) ≤ 1) :
    0 ≤ wireFlowReceiverSelectedIdealMean F t q frac receiver ∧
      wireFlowReceiverSelectedIdealMean F t q frac receiver ≤
        ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card := by
  classical
  let sourceBag := wireFlowReceiverSource receiver hchild
  let selection := receiverOutgoingSelection (receiver.x % 64)
  have hinv := wireSets_inv F t (Nat.le_of_lt ht)
  have hsize (source : Fin 65) :
      (wireSets F t (sourceBag source)).card =
        F.up (sourceBag source).l t + 64 * F.down (sourceBag source).l t := by
    rw [hinv.1]
    exact F.hsplit (sourceBag source).l t (sourceBag source).hl ht
  have hpieceCard (source : Fin 65) (i : Nat) (hi : i < 66) :
      (senderOutgoingPiece (wireSets F t (sourceBag source))
        (F.up (sourceBag source).l t) (F.down (sourceBag source).l t) i).card =
        senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) (i + 1) -
        senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) i := by
    rw [senderOutgoingPiece_eq_blockOf _ _ _ (hsize source)
      (F.hup_even _ _ ht) i hi]
    apply blockOf_card
    rw [hsize source]
    exact senderRankCut_le _ _ _
  have hcountNat := wireFlowReceiver_selected_count_eq_register
    F nets input t ht receiver hb hchild (fun _ => true)
  have hcountCard :
      (∑ source : Fin 65, ∑ i ∈ selection source,
        (senderOutgoingPiece (wireSets F t (sourceBag source))
          (F.up (sourceBag source).l t) (F.down (sourceBag source).l t) i).card) =
        ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card := by
    simpa [trueCountOn_eq_card_filter] using hcountNat
  have hwidthNat :
      (∑ source : Fin 65, ∑ i ∈ selection source,
        (senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) (i + 1) -
        senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) i)) =
        ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card := by
    calc
      _ = ∑ source : Fin 65, ∑ i ∈ selection source,
          (senderOutgoingPiece (wireSets F t (sourceBag source))
            (F.up (sourceBag source).l t) (F.down (sourceBag source).l t) i).card := by
        apply Finset.sum_congr rfl
        intro source _
        apply Finset.sum_congr rfl
        intro i hi
        symm
        exact hpieceCard source i (by
          have hlt := receiverOutgoingSelection_subset (receiver.x % 64)
            (Nat.mod_lt _ (by omega)) source hi
          exact Finset.mem_range.mp hlt)
      _ = _ := hcountCard
  have hwidthReal :
      (∑ source : Fin 65, ∑ i ∈ selection source,
        ((senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) (i + 1) -
        senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) i : Nat) : Real)) =
        (((execPlacement F nets input (t + 1) (by omega)).regs receiver).card : Real) := by
    simpa only [Nat.cast_sum] using
      congrArg (fun n : Nat => (n : Real)) hwidthNat
  have hpieceBounds (source : Fin 65) (i : Nat) (hi : i ∈ selection source) :
      0 ≤ wireFlowLayerSenderPieceMean F t q frac (sourceBag source) i ∧
        wireFlowLayerSenderPieceMean F t q frac (sourceBag source) i ≤
          ((senderRankCut (F.up (sourceBag source).l t)
            (F.down (sourceBag source).l t) (i + 1) -
          senderRankCut (F.up (sourceBag source).l t)
            (F.down (sourceBag source).l t) i : Nat) : Real) := by
    have hmono := senderRankCut_mono
      (F.up (sourceBag source).l t) (F.down (sourceBag source).l t)
    have hcut := hmono (Nat.le_succ i)
    have hcutEnd := senderRankCut_le (F.up (sourceBag source).l t)
      (F.down (sourceBag source).l t) (i + 1)
    rw [← hsize source] at hcutEnd
    simpa [sourceBag, wireFlowLayerSenderPieceMean] using profileIntervalMean_bounds _ (q (sourceBag source))
      (senderRankCut (F.up (sourceBag source).l t) (F.down (sourceBag source).l t) i)
      (senderRankCut (F.up (sourceBag source).l t) (F.down (sourceBag source).l t) (i + 1))
      (frac (sourceBag source)) hcut hcutEnd (hfrac0 source) (hfrac1 source)
  constructor
  · unfold wireFlowReceiverSelectedIdealMean
    rw [dif_pos hchild]
    apply Finset.sum_nonneg
    intro source _
    apply Finset.sum_nonneg
    intro i hi
    exact (hpieceBounds source i hi).1
  · unfold wireFlowReceiverSelectedIdealMean
    rw [dif_pos hchild]
    calc
      _ ≤ ∑ source : Fin 65, ∑ i ∈ selection source,
          ((senderRankCut (F.up (sourceBag source).l t)
            (F.down (sourceBag source).l t) (i + 1) -
          senderRankCut (F.up (sourceBag source).l t)
            (F.down (sourceBag source).l t) i : Nat) : Real) := by
        apply Finset.sum_le_sum
        intro source _
        apply Finset.sum_le_sum
        intro i hi
        exact (hpieceBounds source i hi).2
      _ = _ := hwidthReal

/-- The receiver's selected ideal mean can be installed as a legal next-stage
`q + frac` target, including the zero-capacity endpoint case. -/
theorem wireFlowReceiverSelectedIdealMean_has_code {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (receiver : KBag 64 d) (hb : 1 ≤ receiver.l) (hchild : receiver.l < d)
    (q : KBag 64 d → Nat) (frac : KBag 64 d → Real)
    (hfrac0 : ∀ source : Fin 65,
      0 ≤ frac (wireFlowReceiverSource receiver hchild source))
    (hfrac1 : ∀ source : Fin 65,
      frac (wireFlowReceiverSource receiver hchild source) ≤ 1) :
    ∃ nextQ : Nat, nextQ ≤
        ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card ∧
      ∃ nextFrac : Real, 0 ≤ nextFrac ∧ nextFrac ≤ 1 ∧
        (nextQ : Real) + nextFrac =
          wireFlowReceiverSelectedIdealMean F t q frac receiver ∧
        (nextQ = ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card →
          nextFrac = 0) := by
  let m := ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card
  let μ := wireFlowReceiverSelectedIdealMean F t q frac receiver
  have hbnds := wireFlowReceiverSelectedIdealMean_bounds F nets input t ht
    receiver hb hchild q frac hfrac0 hfrac1
  by_cases hm : m = 0
  · have hμ : μ = 0 := by
      have hμm : μ ≤ 0 := by simpa [μ, m, hm] using hbnds.2
      exact le_antisymm hμm (by simpa [μ] using hbnds.1)
    refine ⟨0, by simp [m, hm], 0, by norm_num, by norm_num, ?_, ?_⟩
    · simpa [μ] using hμ.symm
    · intro _
      rfl
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    obtain ⟨nextQ, hq, nextFrac, hf0, hf1, hmean⟩ :=
      realTarget_has_integer_fraction m μ hmpos (by simpa [μ] using hbnds.1)
        (by simpa [m, μ] using hbnds.2)
    refine ⟨nextQ, by omega, nextFrac, hf0, hf1, ?_, ?_⟩
    · simpa [μ] using hmean
    · intro htop
      omega

/-- Choose coherent next-stage target codes simultaneously for every value
threshold and every active receiver. -/
theorem wireFlowLayer_selected_means_have_codes {d tf : Nat} {Θ : Type}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (q : Θ → KBag 64 d → Nat) (frac : Θ → KBag 64 d → Real)
    (hfrac0 : ∀ θ source, 0 ≤ frac θ source)
    (hfrac1 : ∀ θ source, frac θ source ≤ 1) :
    ∃ qNext : Θ → KBag 64 d → Nat, ∃ fracNext : Θ → KBag 64 d → Real,
      ∀ θ receiver, 1 ≤ receiver.l → receiver.l < d →
        qNext θ receiver ≤
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card ∧
          0 ≤ fracNext θ receiver ∧ fracNext θ receiver ≤ 1 ∧
          (qNext θ receiver : Real) + fracNext θ receiver =
            wireFlowReceiverSelectedIdealMean F t (q θ) (frac θ) receiver ∧
          (qNext θ receiver =
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card →
              fracNext θ receiver = 0) := by
  classical
  let Active : KBag 64 d → Prop := fun receiver => 1 ≤ receiver.l ∧ receiver.l < d
  have hcodes : ∀ θ receiver, Active receiver →
      ∃ nextQ : Nat, nextQ ≤
          ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card ∧
        ∃ nextFrac : Real, 0 ≤ nextFrac ∧ nextFrac ≤ 1 ∧
          (nextQ : Real) + nextFrac =
            wireFlowReceiverSelectedIdealMean F t (q θ) (frac θ) receiver ∧
          (nextQ =
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card →
              nextFrac = 0) := by
    intro θ receiver hactive
    exact wireFlowReceiverSelectedIdealMean_has_code F nets input t ht receiver
      hactive.1 hactive.2 (q θ) (frac θ)
      (fun source => hfrac0 θ (wireFlowReceiverSource receiver hactive.2 source))
      (fun source => hfrac1 θ (wireFlowReceiverSource receiver hactive.2 source))
  choose qCode hqCode fracCode hfracCode0 hfracCode1 hcode hendpointCode using hcodes
  refine ⟨fun θ receiver => if h : Active receiver then qCode θ receiver h else 0,
    fun θ receiver => if h : Active receiver then fracCode θ receiver h else 0, ?_⟩
  intro θ receiver hb hchild
  have hactive : Active receiver := ⟨hb, hchild⟩
  simpa [Active, hactive] using
    ⟨hqCode θ receiver hactive, hfracCode0 θ receiver hactive,
      hfracCode1 θ receiver hactive, hcode θ receiver hactive,
      hendpointCode θ receiver hactive⟩

/-- If every source bag's real threshold target is monotone between two value
thresholds, then the receiver's selected ideal target is monotone as well.
Thus the port rule preserves coherence of the target profile. -/
theorem wireFlowReceiverSelectedIdealMean_mono {d tf : Nat} {Θ : Type}
    (F : FlowSizes d tf) (t : Nat) (ht : t < tf)
    (receiver : KBag 64 d) (hchild : receiver.l < d)
    (q : Θ → KBag 64 d → Nat) (frac : Θ → KBag 64 d → Real)
    (θ₁ θ₂ : Θ)
    (hfrac₁0 : ∀ source : Fin 65,
      0 ≤ frac θ₁ (wireFlowReceiverSource receiver hchild source))
    (hfrac₁1 : ∀ source : Fin 65,
      frac θ₁ (wireFlowReceiverSource receiver hchild source) ≤ 1)
    (hfrac₂0 : ∀ source : Fin 65,
      0 ≤ frac θ₂ (wireFlowReceiverSource receiver hchild source))
    (hfrac₂1 : ∀ source : Fin 65,
      frac θ₂ (wireFlowReceiverSource receiver hchild source) ≤ 1)
    (hmean : ∀ source : Fin 65,
      (q θ₁ (wireFlowReceiverSource receiver hchild source) : Real) +
          frac θ₁ (wireFlowReceiverSource receiver hchild source) ≤
        (q θ₂ (wireFlowReceiverSource receiver hchild source) : Real) +
          frac θ₂ (wireFlowReceiverSource receiver hchild source)) :
    wireFlowReceiverSelectedIdealMean F t (q θ₁) (frac θ₁) receiver ≤
      wireFlowReceiverSelectedIdealMean F t (q θ₂) (frac θ₂) receiver := by
  classical
  let sourceBag := wireFlowReceiverSource receiver hchild
  let selection := receiverOutgoingSelection (receiver.x % 64)
  have hinv := wireSets_inv F t (Nat.le_of_lt ht)
  have hsize (source : Fin 65) :
      (wireSets F t (sourceBag source)).card =
        F.up (sourceBag source).l t + 64 * F.down (sourceBag source).l t := by
    rw [hinv.1]
    exact F.hsplit (sourceBag source).l t (sourceBag source).hl ht
  have hpiece (source : Fin 65) (i : Nat) :
      wireFlowLayerSenderPieceMean F t (q θ₁) (frac θ₁) (sourceBag source) i ≤
        wireFlowLayerSenderPieceMean F t (q θ₂) (frac θ₂) (sourceBag source) i := by
    have hcuts := senderRankCut_mono
      (F.up (sourceBag source).l t) (F.down (sourceBag source).l t)
    have hcut := hcuts (Nat.le_succ i)
    have hcutEnd := senderRankCut_le (F.up (sourceBag source).l t)
      (F.down (sourceBag source).l t) (i + 1)
    rw [← hsize source] at hcutEnd
    simpa [sourceBag, wireFlowLayerSenderPieceMean] using
      (profileIntervalMean_mono_mean (wireSets F t (sourceBag source)).card
        (q θ₁ (sourceBag source)) (q θ₂ (sourceBag source))
        (senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) i)
        (senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) (i + 1))
        (frac θ₁ (sourceBag source)) (frac θ₂ (sourceBag source))
        hcut hcutEnd (hfrac₁0 source) (hfrac₁1 source)
        (hfrac₂0 source) (hfrac₂1 source) (hmean source))
  unfold wireFlowReceiverSelectedIdealMean
  simp only [dif_pos hchild]
  apply Finset.sum_le_sum
  intro source _
  apply Finset.sum_le_sum
  intro i _
  exact hpiece source i

/-- Summed over every interior receiver of a WireFlow layer, the actual
register discrepancy from its selected ideal port mean is bounded by the
coarse count error of each sender, once. This is the concrete layerwise
incidence estimate needed by the bag-mean recurrence. The selected means form
valid monotone receiver targets under the corresponding source-profile
hypotheses; contraction of the resulting profile under merge/deal is still
separate. -/
theorem wireFlowLayer_register_error_sum_le_source_count_error {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real)
    (hsorted : ∀ source, Monotone
      ((fun w => predicate (X F nets input (t + 1) w)) ∘
        (wireSets F t source).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤ (wireSets F t source).card)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source, q source = (wireSets F t source).card → frac source = 0) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      |(trueCountOn
          ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
          predicate : Real) -
        wireFlowReceiverSelectedIdealMean F t q frac receiver|) ≤
      ∑ source : KBag 64 d,
        |(trueCountOn (wireSets F t source)
          (fun w => predicate (X F nets input (t + 1) w)) : Real) -
          (q source + frac source)| := by
  classical
  let active : Finset (KBag 64 d) :=
    (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d)
  let v : KBag 64 d → Fin (64 ^ d) → Bool :=
    fun _ w => predicate (X F nets input (t + 1) w)
  have hinv := wireSets_inv F t (Nat.le_of_lt ht)
  have hsize : ∀ source,
      (wireSets F t source).card = F.up source.l t + 64 * F.down source.l t := by
    intro source
    rw [hinv.1 source]
    exact F.hsplit source.l t source.hl ht
  have hu : ∀ source : KBag 64 d, 2 ∣ F.up source.l t := by
    intro source
    exact F.hup_even source.l t ht
  have hbound := wireFlowLayer_profile_error_sum_le
    (fun source => wireSets F t source) v (fun source => F.up source.l t)
    (fun source => F.down source.l t) q frac hsize hu hsorted hq hfrac0 hfrac1 hendpoint
  have hsubset : active ⊆ Finset.univ := Finset.filter_subset _ _
  calc
    (∑ receiver ∈ active,
        |(trueCountOn
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
            predicate : Real) -
          wireFlowReceiverSelectedIdealMean F t q frac receiver|) =
      ∑ receiver ∈ active,
        |∑ source : KBag 64 d,
          ∑ i ∈ wireFlowLayerSelection receiver source,
            wireFlowLayerSenderPieceError F nets input t predicate q frac source i| := by
      apply Finset.sum_congr rfl
      intro receiver hreceiver
      have hactive := (Finset.mem_filter.mp hreceiver).2
      rw [← wireFlowLayer_receiver_signed_error_eq_register F nets input t ht
        receiver hactive.1 hactive.2 predicate q frac]
    _ ≤ ∑ receiver : KBag 64 d,
        |∑ source : KBag 64 d,
          ∑ i ∈ wireFlowLayerSelection receiver source,
            wireFlowLayerSenderPieceError F nets input t predicate q frac source i| :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro receiver _ _
        exact abs_nonneg _)
    _ ≤ ∑ source : KBag 64 d,
        |(trueCountOn (wireSets F t source)
          (fun w => predicate (X F nets input (t + 1) w)) : Real) -
          (q source + frac source)| := by
      simpa [v, wireFlowLayerSenderPieceError, wireFlowLayerSenderPieceCount,
        wireFlowLayerSenderPieceMean, profileIntervalMean] using hbound

/-- If the incoming real threshold targets are monotone, the simultaneously
chosen next-stage codes remain monotone after re-encoding. -/
theorem wireFlowLayer_selected_means_have_monotone_codes {d tf : Nat} {Θ : Type}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (q : Θ → KBag 64 d → Nat) (frac : Θ → KBag 64 d → Real)
    (hfrac0 : ∀ θ source, 0 ≤ frac θ source)
    (hfrac1 : ∀ θ source, frac θ source ≤ 1)
    (hmono : ∀ θ₁ θ₂ source,
      (q θ₁ source : Real) + frac θ₁ source ≤
        (q θ₂ source : Real) + frac θ₂ source) :
    ∃ qNext : Θ → KBag 64 d → Nat, ∃ fracNext : Θ → KBag 64 d → Real,
      (∀ θ receiver, 1 ≤ receiver.l → receiver.l < d →
        qNext θ receiver ≤
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card ∧
          0 ≤ fracNext θ receiver ∧ fracNext θ receiver ≤ 1 ∧
          (qNext θ receiver : Real) + fracNext θ receiver =
            wireFlowReceiverSelectedIdealMean F t (q θ) (frac θ) receiver ∧
          (qNext θ receiver =
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card →
              fracNext θ receiver = 0)) ∧
      (∀ θ₁ θ₂ receiver, 1 ≤ receiver.l → receiver.l < d →
        (qNext θ₁ receiver : Real) + fracNext θ₁ receiver ≤
          (qNext θ₂ receiver : Real) + fracNext θ₂ receiver) := by
  obtain ⟨qNext, fracNext, hcodes⟩ :=
    wireFlowLayer_selected_means_have_codes F nets input t ht q frac hfrac0 hfrac1
  refine ⟨qNext, fracNext, hcodes, ?_⟩
  intro θ₁ θ₂ receiver hb hchild
  have hmean := wireFlowReceiverSelectedIdealMean_mono F t ht receiver hchild
    q frac θ₁ θ₂
    (fun source => hfrac0 θ₁ (wireFlowReceiverSource receiver hchild source))
    (fun source => hfrac1 θ₁ (wireFlowReceiverSource receiver hchild source))
    (fun source => hfrac0 θ₂ (wireFlowReceiverSource receiver hchild source))
    (fun source => hfrac1 θ₂ (wireFlowReceiverSource receiver hchild source))
    (fun source => hmono θ₁ θ₂ (wireFlowReceiverSource receiver hchild source))
  have hcode₁ := (hcodes θ₁ receiver hb hchild).2.2.2.1
  have hcode₂ := (hcodes θ₂ receiver hb hchild).2.2.2.1
  rw [hcode₁, hcode₂]
  exact hmean

/-- The no-amplification estimate holds simultaneously for any finite family
of value thresholds. Summing over all active receivers and thresholds charges
each source bag's coarse error once per threshold, with no factor for the
number of receiver levels or routed ports. -/
theorem wireFlowLayer_register_error_sum_le_source_count_error_multi
    {d tf : Nat} {Θ : Type} [Fintype Θ] [DecidableEq Θ]
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (predicate : Θ → Fin (64 ^ d) → Bool)
    (q : Θ → KBag 64 d → Nat) (frac : Θ → KBag 64 d → Real)
    (hsorted : ∀ θ source, Monotone
      ((fun w => predicate θ (X F nets input (t + 1) w)) ∘
        (wireSets F t source).orderEmbOfFin rfl))
    (hq : ∀ θ source, q θ source ≤ (wireSets F t source).card)
    (hfrac0 : ∀ θ source, 0 ≤ frac θ source)
    (hfrac1 : ∀ θ source, frac θ source ≤ 1)
    (hendpoint : ∀ θ source,
      q θ source = (wireSets F t source).card → frac θ source = 0) :
    (∑ θ : Θ, ∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      |(trueCountOn
          ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
          (predicate θ) : Real) -
        wireFlowReceiverSelectedIdealMean F t (q θ) (frac θ) receiver|) ≤
      ∑ θ : Θ, ∑ source : KBag 64 d,
        |(trueCountOn (wireSets F t source)
          (fun w => predicate θ (X F nets input (t + 1) w)) : Real) -
          (q θ source + frac θ source)| := by
  classical
  apply Finset.sum_le_sum
  intro θ _
  exact wireFlowLayer_register_error_sum_le_source_count_error
    F nets input t ht (predicate θ) (q θ) (frac θ)
    (hsorted θ) (hq θ) (hfrac0 θ) (hfrac1 θ) (hendpoint θ)

/-- One complete layer interface: choose a monotone next threshold profile on
every active receiver, and bound its total register discrepancy by the prior
source-profile error with no port or receiver-level multiplicity. -/
theorem wireFlowLayer_reencoded_profile_recurrence {d tf : Nat} {Θ : Type}
    [Fintype Θ] [DecidableEq Θ]
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (predicate : Θ → Fin (64 ^ d) → Bool)
    (q : Θ → KBag 64 d → Nat) (frac : Θ → KBag 64 d → Real)
    (hsorted : ∀ θ source, Monotone
      ((fun w => predicate θ (X F nets input (t + 1) w)) ∘
        (wireSets F t source).orderEmbOfFin rfl))
    (hq : ∀ θ source, q θ source ≤ (wireSets F t source).card)
    (hfrac0 : ∀ θ source, 0 ≤ frac θ source)
    (hfrac1 : ∀ θ source, frac θ source ≤ 1)
    (hendpoint : ∀ θ source,
      q θ source = (wireSets F t source).card → frac θ source = 0)
    (hmono : ∀ θ₁ θ₂ source,
      (q θ₁ source : Real) + frac θ₁ source ≤
        (q θ₂ source : Real) + frac θ₂ source) :
    ∃ qNext : Θ → KBag 64 d → Nat, ∃ fracNext : Θ → KBag 64 d → Real,
      (∀ θ receiver, 1 ≤ receiver.l → receiver.l < d →
        qNext θ receiver ≤
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card ∧
          0 ≤ fracNext θ receiver ∧ fracNext θ receiver ≤ 1 ∧
          (qNext θ receiver : Real) + fracNext θ receiver =
            wireFlowReceiverSelectedIdealMean F t (q θ) (frac θ) receiver ∧
          (qNext θ receiver =
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card →
              fracNext θ receiver = 0)) ∧
      (∀ θ₁ θ₂ receiver, 1 ≤ receiver.l → receiver.l < d →
        (qNext θ₁ receiver : Real) + fracNext θ₁ receiver ≤
          (qNext θ₂ receiver : Real) + fracNext θ₂ receiver) ∧
      (∑ θ : Θ, ∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
          (fun b => 1 ≤ b.l ∧ b.l < d),
        |(trueCountOn
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
            (predicate θ) : Real) -
          ((qNext θ receiver : Real) + fracNext θ receiver)|) ≤
        ∑ θ : Θ, ∑ source : KBag 64 d,
          |(trueCountOn (wireSets F t source)
              (fun w => predicate θ (X F nets input (t + 1) w)) : Real) -
            (q θ source + frac θ source)| := by
  obtain ⟨qNext, fracNext, hcodes, hmonoNext⟩ :=
    wireFlowLayer_selected_means_have_monotone_codes F nets input t ht q frac
      hfrac0 hfrac1 hmono
  have herror := wireFlowLayer_register_error_sum_le_source_count_error_multi
    F nets input t ht predicate q frac hsorted hq hfrac0 hfrac1 hendpoint
  have heq :
      (∑ θ : Θ, ∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
          (fun b => 1 ≤ b.l ∧ b.l < d),
        |(trueCountOn
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
            (predicate θ) : Real) -
          ((qNext θ receiver : Real) + fracNext θ receiver)|) =
      ∑ θ : Θ, ∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
          (fun b => 1 ≤ b.l ∧ b.l < d),
        |(trueCountOn
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
            (predicate θ) : Real) -
          wireFlowReceiverSelectedIdealMean F t (q θ) (frac θ) receiver| := by
    apply Finset.sum_congr rfl
    intro θ _
    apply Finset.sum_congr rfl
    intro receiver hreceiver
    have hactive := (Finset.mem_filter.mp hreceiver).2
    have hcode := (hcodes θ receiver hactive.1 hactive.2).2.2.2.1
    rw [hcode]
  refine ⟨qNext, fracNext, hcodes, hmonoNext, ?_⟩
  rw [heq]
  exact herror

/-- The re-encoded profile recurrence also holds in squared error across all
thresholds and active receiver levels, with the same factor-65 source-energy
charge. -/
theorem wireFlowLayer_reencoded_profile_energy_recurrence {d tf : Nat} {Θ : Type}
    [Fintype Θ] [DecidableEq Θ]
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (predicate : Θ → Fin (64 ^ d) → Bool)
    (q : Θ → KBag 64 d → Nat) (frac : Θ → KBag 64 d → Real)
    (hsize : ∀ source, (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t)
    (hu : ∀ source : KBag 64 d, 2 ∣ F.up source.l t)
    (hsorted : ∀ θ source, Monotone
      ((fun w => predicate θ (X F nets input (t + 1) w)) ∘
        (wireSets F t source).orderEmbOfFin rfl))
    (hq : ∀ θ source, q θ source ≤ (wireSets F t source).card)
    (hfrac0 : ∀ θ source, 0 ≤ frac θ source)
    (hfrac1 : ∀ θ source, frac θ source ≤ 1)
    (hendpoint : ∀ θ source,
      q θ source = (wireSets F t source).card → frac θ source = 0)
    (hmono : ∀ θ₁ θ₂ source,
      (q θ₁ source : Real) + frac θ₁ source ≤
        (q θ₂ source : Real) + frac θ₂ source) :
    ∃ qNext : Θ → KBag 64 d → Nat, ∃ fracNext : Θ → KBag 64 d → Real,
      (∀ θ receiver, 1 ≤ receiver.l → receiver.l < d →
        qNext θ receiver ≤
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card ∧
          0 ≤ fracNext θ receiver ∧ fracNext θ receiver ≤ 1 ∧
          (qNext θ receiver : Real) + fracNext θ receiver =
            wireFlowReceiverSelectedIdealMean F t (q θ) (frac θ) receiver ∧
          (qNext θ receiver =
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card →
              fracNext θ receiver = 0)) ∧
      (∀ θ₁ θ₂ receiver, 1 ≤ receiver.l → receiver.l < d →
        (qNext θ₁ receiver : Real) + fracNext θ₁ receiver ≤
          (qNext θ₂ receiver : Real) + fracNext θ₂ receiver) ∧
      (∑ θ : Θ, ∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
          (fun b => 1 ≤ b.l ∧ b.l < d),
        ((trueCountOn
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
            (predicate θ) : Real) -
          ((qNext θ receiver : Real) + fracNext θ receiver)) ^ 2) ≤
        65 * ∑ θ : Θ, ∑ source : KBag 64 d,
          |((trueCountOn (wireSets F t source)
              (fun w => predicate θ (X F nets input (t + 1) w))) : Real) -
            (q θ source + frac θ source)| ^ 2 := by
  obtain ⟨qNext, fracNext, hcodes, hmonoNext⟩ :=
    wireFlowLayer_selected_means_have_monotone_codes F nets input t ht q frac
      hfrac0 hfrac1 hmono
  have henergy := wireFlowLayer_register_error_sq_sum_le_source_energy_multi
    F nets input t ht predicate q frac hsize hu hsorted hq hfrac0 hfrac1 hendpoint
  have heq :
      (∑ θ : Θ, ∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
          (fun b => 1 ≤ b.l ∧ b.l < d),
        ((trueCountOn
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
            (predicate θ) : Real) -
          ((qNext θ receiver : Real) + fracNext θ receiver)) ^ 2) =
      (∑ θ : Θ, ∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
          (fun b => 1 ≤ b.l ∧ b.l < d),
        ((trueCountOn
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
            (predicate θ) : Real) -
          wireFlowReceiverSelectedIdealMean F t (q θ) (frac θ) receiver) ^ 2) := by
    apply Finset.sum_congr rfl
    intro θ _
    apply Finset.sum_congr rfl
    intro receiver hreceiver
    have hactive := (Finset.mem_filter.mp hreceiver).2
    have hcode := (hcodes θ receiver hactive.1 hactive.2).2.2.2.1
    rw [hcode]
  refine ⟨qNext, fracNext, hcodes, hmonoNext, ?_⟩
  rw [heq]
  exact henergy

/-- The source-profile error bound applies directly to the actual receiver
register: the selected parent/child piece counts are exactly its Boolean
threshold count. This packages the source-side discrepancy at the receiver
boundary; matching the selected profile means to a common downstream target
is still a separate recurrence obligation. -/
theorem wireFlowReceiver_register_count_error_actual {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (predicate : Fin (64 ^ d) → Bool)
    (q : Fin 65 → Nat) (frac : Fin 65 → Real)
    (hsorted : ∀ source, Monotone
      ((fun w => predicate (X F nets input (t + 1) w)) ∘
        (wireSets F t (wireFlowReceiverSource b hchild source)).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤
      (wireSets F t (wireFlowReceiverSource b hchild source)).card)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source,
      q source = (wireSets F t (wireFlowReceiverSource b hchild source)).card →
        frac source = 0) :
    |(trueCountOn ((execPlacement F nets input (t + 1) (by omega)).regs b)
        predicate : Real) -
      ∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
        profileIntervalMean
          (wireSets F t (wireFlowReceiverSource b hchild source)).card
          (q source) (frac source)
          (senderRankCut (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) i)
          (senderRankCut (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) (i + 1))| ≤
      ∑ source : Fin 65,
        |(trueCountOn (wireSets F t (wireFlowReceiverSource b hchild source))
          (fun w => predicate (X F nets input (t + 1) w)) : Real) -
          (q source + frac source)| := by
  have hcount := (wireFlowReceiver_selected_count_eq_register
    F nets input t ht b hb hchild predicate).symm
  calc
    |(trueCountOn ((execPlacement F nets input (t + 1) (by omega)).regs b)
        predicate : Real) - _| =
      |((∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
          trueCountOn
            (senderOutgoingPiece
              (wireSets F t (wireFlowReceiverSource b hchild source))
              (F.up (wireFlowReceiverSource b hchild source).l t)
              (F.down (wireFlowReceiverSource b hchild source).l t) i)
            (fun w => predicate (X F nets input (t + 1) w)) : Nat) : Real) - _| := by
        rw [hcount]
    _ ≤ _ := by
      simpa only [Nat.cast_sum] using
        (wireFlowReceiver_count_error_actual F nets input t ht b hb hchild predicate
          q frac hsorted hq hfrac0 hfrac1 hendpoint)

/-- The receiver discrepancy is directly against a valid re-encoded next-stage
target, with the same source-error charge as the selected-mean interface. -/
theorem wireFlowReceiver_register_count_error_reencoded {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (predicate : Fin (64 ^ d) → Bool)
    (q : KBag 64 d → Nat) (frac : KBag 64 d → Real)
    (hsorted : ∀ source : Fin 65, Monotone
      ((fun w => predicate (X F nets input (t + 1) w)) ∘
        (wireSets F t (wireFlowReceiverSource b hchild source)).orderEmbOfFin rfl))
    (hq : ∀ source : Fin 65, q (wireFlowReceiverSource b hchild source) ≤
      (wireSets F t (wireFlowReceiverSource b hchild source)).card)
    (hfrac0 : ∀ source : Fin 65,
      0 ≤ frac (wireFlowReceiverSource b hchild source))
    (hfrac1 : ∀ source : Fin 65,
      frac (wireFlowReceiverSource b hchild source) ≤ 1)
    (hendpoint : ∀ source : Fin 65,
      q (wireFlowReceiverSource b hchild source) =
        (wireSets F t (wireFlowReceiverSource b hchild source)).card →
      frac (wireFlowReceiverSource b hchild source) = 0) :
    ∃ nextQ : Nat, nextQ ≤
        ((execPlacement F nets input (t + 1) (by omega)).regs b).card ∧
      ∃ nextFrac : Real, 0 ≤ nextFrac ∧ nextFrac ≤ 1 ∧
        (nextQ : Real) + nextFrac =
          wireFlowReceiverSelectedIdealMean F t q frac b ∧
        (nextQ = ((execPlacement F nets input (t + 1) (by omega)).regs b).card →
          nextFrac = 0) ∧
        |(trueCountOn ((execPlacement F nets input (t + 1) (by omega)).regs b)
            predicate : Real) - ((nextQ : Real) + nextFrac)| ≤
          ∑ source : Fin 65,
            |((trueCountOn (wireSets F t (wireFlowReceiverSource b hchild source))
                (fun w => predicate (X F nets input (t + 1) w)) : Nat) : Real) -
              ((q (wireFlowReceiverSource b hchild source) : Real) +
                frac (wireFlowReceiverSource b hchild source))| := by
  rcases wireFlowReceiverSelectedIdealMean_has_code F nets input t ht b hb hchild
      q frac hfrac0 hfrac1 with ⟨nextQ, hnextQ, nextFrac, hnextFrac0,
        hnextFrac1, hcode, hendpointNext⟩
  have hmean :
      (∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
        profileIntervalMean
          (wireSets F t (wireFlowReceiverSource b hchild source)).card
          (q (wireFlowReceiverSource b hchild source))
          (frac (wireFlowReceiverSource b hchild source))
          (senderRankCut (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) i)
          (senderRankCut (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) (i + 1))) =
        wireFlowReceiverSelectedIdealMean F t q frac b := by
    simp [wireFlowReceiverSelectedIdealMean, wireFlowLayerSenderPieceMean, hchild]
  have herror := wireFlowReceiver_register_count_error_actual F nets input t ht b hb hchild
    predicate (fun source => q (wireFlowReceiverSource b hchild source))
    (fun source => frac (wireFlowReceiverSource b hchild source)) hsorted hq hfrac0 hfrac1
    hendpoint
  rw [hmean] at herror
  refine ⟨nextQ, hnextQ, nextFrac, hnextFrac0, hnextFrac1, hcode, hendpointNext, ?_⟩
  rw [hcode]
  simpa using herror

theorem sortedPackets_intervalPartition_L1_exact {c m p q : Nat} (frac : Real)
    (V : Fin c → Fin m → Bool) (hV : ∀ i, Monotone (V i))
    (cuts : Nat → Nat) (hstart : cuts 0 = 0) (hcuts : Monotone cuts)
    (hcutBound : ∀ i, cuts i ≤ m)
    (hend : cuts p = m) (hq : q < m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ packet : Fin c, ∑ i ∈ range p,
      |(boolTrueCount (fun j : Fin (cuts (i + 1) - cuts i) =>
          V packet ⟨cuts i + j.val, by
            have hab : cuts i ≤ cuts (i + 1) := hcuts (Nat.le_succ i)
            have hsum := Nat.add_sub_of_le hab
            calc
              cuts i + j.val < cuts i + (cuts (i + 1) - cuts i) := Nat.add_lt_add_left j.isLt _
              _ = cuts (i + 1) := hsum
              _ ≤ m := hcutBound (i + 1)⟩) : Real) -
        profileIntervalMean m q frac (cuts i) (cuts (i + 1))|) =
      ∑ packet : Fin c, |(boolTrueCount (V packet) : Real) - (q + frac)| := by
  apply Finset.sum_congr rfl
  intro packet _
  have hpacket (i : Nat) (hi : i < p) :
      boolTrueCount (fun j : Fin (cuts (i + 1) - cuts i) =>
        V packet ⟨cuts i + j.val, by
          have hab : cuts i ≤ cuts (i + 1) := hcuts (Nat.le_succ i)
          have hsum := Nat.add_sub_of_le hab
          calc
            cuts i + j.val < cuts i + (cuts (i + 1) - cuts i) := Nat.add_lt_add_left j.isLt _
            _ = cuts (i + 1) := hsum
            _ ≤ m := hcutBound (i + 1)⟩) =
        profileInterval m (boolTrueCount (V packet)) (cuts i) (cuts (i + 1)) := by
    apply sortedBool_rankInterval_trueCount (V packet) (hV packet)
    · exact hcuts (Nat.le_succ i)
    · exact hcutBound (i + 1)
  have hprofile := profileInterval_partition_L1_exact m p
    (boolTrueCount (V packet)) q frac cuts hstart hcuts hend
    (by
      simpa [boolTrueCount] using
        (Fintype.card_subtype_le (fun k : Fin m => V packet k = true))) hq hfrac0 hfrac1
  calc
    _ = ∑ i ∈ range p,
      |(profileInterval m (boolTrueCount (V packet)) (cuts i) (cuts (i + 1)) : Real) -
          profileIntervalMean m q frac (cuts i) (cuts (i + 1))| := by
      apply sum_congr rfl
      intro i hi
      rw [hpacket i (mem_range.mp hi)]
    _ = |(boolTrueCount (V packet) : Real) - (q + frac)| := hprofile

theorem sortedPackets_intervalPartition_L1_sq {c m p q : Nat} (frac : Real)
    (V : Fin c → Fin m → Bool) (hV : ∀ i, Monotone (V i))
    (cuts : Nat → Nat) (hstart : cuts 0 = 0) (hcuts : Monotone cuts)
    (hcutBound : ∀ i, cuts i ≤ m) (hend : cuts p = m) (hq : q < m)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    ((∑ packet : Fin c, ∑ i ∈ range p,
      |(boolTrueCount (fun j : Fin (cuts (i + 1) - cuts i) =>
          V packet ⟨cuts i + j.val, by
            have hab : cuts i ≤ cuts (i + 1) := hcuts (Nat.le_succ i)
            have hsum := Nat.add_sub_of_le hab
            calc
              cuts i + j.val < cuts i + (cuts (i + 1) - cuts i) := Nat.add_lt_add_left j.isLt _
              _ = cuts (i + 1) := hsum
              _ ≤ m := hcutBound (i + 1)⟩) : Real) -
        profileIntervalMean m q frac (cuts i) (cuts (i + 1))|)^2) ≤
      (c : Real) * ∑ packet : Fin c,
        ((boolTrueCount (V packet) : Real) - (q + frac))^2 := by
  rw [sortedPackets_intervalPartition_L1_exact frac V hV cuts hstart hcuts
    hcutBound hend hq hfrac0 hfrac1]
  simpa [sq_abs, mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun packet : Fin c => |(boolTrueCount (V packet) : Real) - (q + frac)|)
      (fun _ => (1 : Real)))

theorem sortedPackets_individualIntervalPartitions_L1_exact {c m p q : Nat}
    (frac : Real) (V : Fin c → Fin m → Bool) (hV : ∀ packet, Monotone (V packet))
    (cuts : Fin c → Nat → Nat) (hstart : ∀ packet, cuts packet 0 = 0)
    (hcuts : ∀ packet, Monotone (cuts packet))
    (hcutBound : ∀ packet i, cuts packet i ≤ m)
    (hend : ∀ packet, cuts packet p = m) (hq : q < m)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ packet : Fin c, ∑ i ∈ range p,
      |(boolTrueCount (fun j : Fin (cuts packet (i + 1) - cuts packet i) =>
          V packet ⟨cuts packet i + j.val, by
            have hab : cuts packet i ≤ cuts packet (i + 1) := hcuts packet (Nat.le_succ i)
            have hsum := Nat.add_sub_of_le hab
            calc
              cuts packet i + j.val < cuts packet i + (cuts packet (i + 1) - cuts packet i) :=
                Nat.add_lt_add_left j.isLt _
              _ = cuts packet (i + 1) := hsum
              _ ≤ m := hcutBound packet (i + 1)⟩) : Real) -
        profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))|) =
      ∑ packet : Fin c, |(boolTrueCount (V packet) : Real) - (q + frac)| := by
  apply Finset.sum_congr rfl
  intro packet _
  have hpacket (i : Nat) (hi : i < p) :
      boolTrueCount (fun j : Fin (cuts packet (i + 1) - cuts packet i) =>
        V packet ⟨cuts packet i + j.val, by
          have hab : cuts packet i ≤ cuts packet (i + 1) := hcuts packet (Nat.le_succ i)
          have hsum := Nat.add_sub_of_le hab
          calc
            cuts packet i + j.val < cuts packet i + (cuts packet (i + 1) - cuts packet i) :=
              Nat.add_lt_add_left j.isLt _
            _ = cuts packet (i + 1) := hsum
            _ ≤ m := hcutBound packet (i + 1)⟩) =
        profileInterval m (boolTrueCount (V packet)) (cuts packet i) (cuts packet (i + 1)) := by
    apply sortedBool_rankInterval_trueCount (V packet) (hV packet)
    · exact hcuts packet (Nat.le_succ i)
    · exact hcutBound packet (i + 1)
  have hprofile := profileInterval_partition_L1_exact m p
    (boolTrueCount (V packet)) q frac (cuts packet) (hstart packet) (hcuts packet)
    (hend packet) (by
      simpa [boolTrueCount] using
        (Fintype.card_subtype_le (fun k : Fin m => V packet k = true))) hq hfrac0 hfrac1
  calc
    _ = ∑ i ∈ range p,
        |(profileInterval m (boolTrueCount (V packet)) (cuts packet i) (cuts packet (i + 1)) : Real) -
          profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))| := by
      apply sum_congr rfl
      intro i hi
      rw [hpacket i (mem_range.mp hi)]
    _ = |(boolTrueCount (V packet) : Real) - (q + frac)| := hprofile

theorem sortedPackets_individualIntervalPartitions_L1_sq {c m p q : Nat}
    (frac : Real) (V : Fin c → Fin m → Bool) (hV : ∀ packet, Monotone (V packet))
    (cuts : Fin c → Nat → Nat) (hstart : ∀ packet, cuts packet 0 = 0)
    (hcuts : ∀ packet, Monotone (cuts packet))
    (hcutBound : ∀ packet i, cuts packet i ≤ m)
    (hend : ∀ packet, cuts packet p = m) (hq : q < m)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    ((∑ packet : Fin c, ∑ i ∈ range p,
      |(boolTrueCount (fun j : Fin (cuts packet (i + 1) - cuts packet i) =>
          V packet ⟨cuts packet i + j.val, by
            have hab : cuts packet i ≤ cuts packet (i + 1) := hcuts packet (Nat.le_succ i)
            have hsum := Nat.add_sub_of_le hab
            calc
              cuts packet i + j.val < cuts packet i + (cuts packet (i + 1) - cuts packet i) :=
                Nat.add_lt_add_left j.isLt _
              _ = cuts packet (i + 1) := hsum
              _ ≤ m := hcutBound packet (i + 1)⟩) : Real) -
        profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))|)^2) ≤
      (c : Real) * ∑ packet : Fin c,
        ((boolTrueCount (V packet) : Real) - (q + frac))^2 := by
  rw [sortedPackets_individualIntervalPartitions_L1_exact frac V hV cuts hstart
    hcuts hcutBound hend hq hfrac0 hfrac1]
  simpa [sq_abs, mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun packet : Fin c => |(boolTrueCount (V packet) : Real) - (q + frac)|)
      (fun _ => (1 : Real)))


private theorem sum_profileTail32_differences (m K X : Nat) (hK : 32 * K ≤ m) :
    (∑ i ∈ range K,
      (profileTail m X (32 * (i + 1)) - profileTail m X (32 * i))) =
      profileTail m X (32 * K) - profileTail m X 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [sum_range_succ, ih (by omega)]
      simp only [profileTail]
      omega

theorem profileHalf_formula (K X i : Nat) (hi : i < K) :
    profileHalf K X i = min 32 (X - (32 * K - 32 * (i + 1))) := by
  have hab : 32 * i ≤ 32 * (i + 1) := by omega
  have hb : 32 * (i + 1) ≤ 32 * K := by omega
  unfold profileHalf
  rw [profileTail_interval_count32 (32 * K) X (32 * i) (32 * (i + 1)) hab hb]
  simp [Nat.mul_add]

private theorem profileHalf_mono_X (K X Y i : Nat) (hXY : Y ≤ X)
    (hi : i < K) : profileHalf K Y i ≤ profileHalf K X i := by
  rw [profileHalf_formula K Y i hi, profileHalf_formula K X i hi]
  exact min_le_min le_rfl (Nat.sub_le_sub_right hXY _)

theorem sum_profileHalf_eq_total (K X : Nat) (hX : X ≤ 32 * K) :
    (∑ i ∈ range K, profileHalf K X i) = X := by
  simp only [profileHalf]
  rw [sum_profileTail32_differences (32 * K) K X (by omega)]
  simp only [profileTail]
  omega

def profileHalfMean (K q : Nat) (frac : Real) (i : Nat) : Real :=
  (1 - frac) * profileHalf K q i + frac * profileHalf K (q + 1) i

theorem profileHalfMean_sum (K q : Nat) (frac : Real) (hq : q < 32 * K) :
    (∑ i ∈ range K, profileHalfMean K q frac i) = q + frac := by
  have hqsum : (∑ i ∈ range K, (profileHalf K q i : Real)) = q := by
    exact_mod_cast sum_profileHalf_eq_total K q (by omega)
  have hq1sum : (∑ i ∈ range K, (profileHalf K (q + 1) i : Real)) = q + 1 := by
    exact_mod_cast sum_profileHalf_eq_total K (q + 1) (by omega)
  unfold profileHalfMean
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hqsum, hq1sum]
  ring

theorem profileHalfMean_L1_exact (K X q : Nat) (frac : Real) (hq : q < 32 * K)
    (hXbound : X ≤ 32 * K) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ range K,
      |(profileHalf K X i : Real) - profileHalfMean K q frac i|) =
        |(X : Real) - (q + frac)| := by
  have hmean := profileHalfMean_sum K q frac hq
  have hxsum : (∑ i ∈ range K, (profileHalf K X i : Real)) = X := by
    exact_mod_cast sum_profileHalf_eq_total K X hXbound
  by_cases hX : X ≤ q
  · have hpoint : ∀ i ∈ range K,
        (profileHalf K X i : Real) ≤ profileHalfMean K q frac i := by
      intro i hi
      have hbase := profileHalf_mono_X K q X i (by omega) (mem_range.mp hi)
      have hnext := profileHalf_mono_X K (q + 1) q i (by omega) (mem_range.mp hi)
      unfold profileHalfMean
      have hn : (profileHalf K q i : Real) ≤ profileHalf K (q + 1) i := by exact_mod_cast hnext
      have hb : (profileHalf K X i : Real) ≤ profileHalf K q i := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range K,
          |(profileHalf K X i : Real) - profileHalfMean K q frac i|) =
          ∑ i ∈ range K, (profileHalfMean K q frac i - (profileHalf K X i : Real)) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonpos (by linarith [hpoint i hi])]
        ring
      _ = (∑ i ∈ range K, profileHalfMean K q frac i) -
          (∑ i ∈ range K, (profileHalf K X i : Real)) := by rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        rw [hmean, hxsum]
        have hXR : (X : Real) ≤ (q : Real) := by exact_mod_cast hX
        rw [abs_of_nonpos (by linarith [hfrac0])]
        ring
  · have hX' : q + 1 ≤ X := by omega
    have hpoint : ∀ i ∈ range K,
        profileHalfMean K q frac i ≤ (profileHalf K X i : Real) := by
      intro i hi
      have hbase := profileHalf_mono_X K X (q + 1) i (by omega) (mem_range.mp hi)
      have hnext := profileHalf_mono_X K (q + 1) q i (by omega) (mem_range.mp hi)
      unfold profileHalfMean
      have hn : (profileHalf K q i : Real) ≤ profileHalf K (q + 1) i := by exact_mod_cast hnext
      have hb : (profileHalf K (q + 1) i : Real) ≤ profileHalf K X i := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range K,
          |(profileHalf K X i : Real) - profileHalfMean K q frac i|) =
          ∑ i ∈ range K, ((profileHalf K X i : Real) - profileHalfMean K q frac i) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonneg (by linarith [hpoint i hi])]
      _ = (∑ i ∈ range K, (profileHalf K X i : Real)) -
          (∑ i ∈ range K, profileHalfMean K q frac i) := by rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        rw [hxsum, hmean]
        have hXR : (q : Real) + 1 ≤ (X : Real) := by exact_mod_cast hX'
        rw [abs_of_nonneg (by linarith [hfrac1])]

theorem sortedBool_profileHalf_trueCount {K : Nat} (v : Fin (32 * K) → Bool)
    (hv : Monotone v) (X : Nat) (hX : boolTrueCount v = X) (i : Nat) (hi : i < K) :
    boolTrueCount (fun j : Fin 32 => v ⟨32 * i + j,
      by have hj := j.isLt; omega⟩) = profileHalf K X i := by
  let m := 32 * K
  let a := 32 * i
  let b := 32 * (i + 1)
  have ha : a ≤ m := by dsimp [a, m]; omega
  have hb : b ≤ m := by dsimp [b, m]; omega
  have hab : a + 32 = b := by dsimp [a, b]; omega
  let Plo : Fin a → Bool := fun j =>
    v (Fin.cast (Nat.add_sub_of_le ha) (Fin.castAdd (m - a) j))
  let Phi : Fin b → Bool := fun j =>
    v (Fin.cast (Nat.add_sub_of_le hb) (Fin.castAdd (m - b) j))
  let C : Fin 32 → Bool := fun j => v ⟨a + j, by dsimp [a, m]; have hj := j.isLt; omega⟩
  have he : Fin.append Plo C = Phi ∘ Fin.cast hab := by
    funext k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [Fin.append_left, Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [Plo, Phi, Fin.val_cast, Fin.val_castAdd, Fin.val_mk]
    · simp only [Fin.append_right, Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [C, Phi, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_mk]
  have hcounts : boolTrueCount Phi = boolTrueCount Plo + boolTrueCount C := by
    calc
      boolTrueCount Phi = boolTrueCount (Phi ∘ Fin.cast hab) :=
        (boolTrueCount_finCast hab Phi).symm
      _ = boolTrueCount (Fin.append Plo C) := congrArg boolTrueCount he.symm
      _ = boolTrueCount Plo + boolTrueCount C := boolTrueCount_append_general Plo C
  have hlo := sortedBool_prefix_trueCount v hv ha
  have hhi := sortedBool_prefix_trueCount v hv hb
  rw [hX] at hlo hhi
  change boolTrueCount C = profileHalf K X i
  have hC : boolTrueCount C = boolTrueCount Phi - boolTrueCount Plo := by omega
  unfold profileHalf profileTail
  rw [hC, hhi, hlo]

theorem sortedPackets_halfProfile_L1_exact {c K : Nat}
    (V : Fin c → Fin (32 * K) → Bool) (hV : ∀ i, Monotone (V i))
    (q : Nat) (frac : Real) (hq : q < 32 * K)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i : Fin c, ∑ j : Fin K,
      |(boolTrueCount (fun k : Fin 32 => V i ⟨32 * j.val + k,
        by have hj := j.isLt; have hk := k.isLt; omega⟩) : Real) -
          profileHalfMean K q frac j.val|) =
      ∑ i : Fin c, |(boolTrueCount (V i) : Real) - (q + frac)| := by
  let X : Fin c → Nat := fun i => boolTrueCount (V i)
  have hcell (i : Fin c) (j : Fin K) :
      boolTrueCount (fun k : Fin 32 => V i ⟨32 * j.val + k,
        by have hk := k.isLt; omega⟩) = profileHalf K (X i) j.val := by
    exact sortedBool_profileHalf_trueCount (V i) (hV i) (X i) rfl j.val j.isLt
  have hprofiles : (∑ i : Fin c, ∑ j : Fin K,
      |(boolTrueCount (fun k : Fin 32 => V i ⟨32 * j.val + k,
        by have hj := j.isLt; have hk := k.isLt; omega⟩) : Real) -
          profileHalfMean K q frac j.val|) =
      ∑ i : Fin c, ∑ j : Fin K,
        |(profileHalf K (X i) j.val : Real) - profileHalfMean K q frac j.val| := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hcell i j]
  calc
    _ = ∑ i : Fin c, ∑ j : Fin K,
        |(profileHalf K (X i) j.val : Real) - profileHalfMean K q frac j.val| := hprofiles
    _ = ∑ i : Fin c, |(X i : Real) - (q + frac)| := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ j : Fin K,
            |(profileHalf K (X i) j.val : Real) - profileHalfMean K q frac j.val|) =
            ∑ j ∈ range K,
              |(profileHalf K (X i) j : Real) - profileHalfMean K q frac j| :=
          Fin.sum_univ_eq_sum_range (fun j : Nat =>
            |(profileHalf K (X i) j : Real) - profileHalfMean K q frac j|) K
        _ = |(X i : Real) - (q + frac)| :=
          profileHalfMean_L1_exact K (X i) q frac hq (by
            dsimp [X]
            unfold boolTrueCount
            simpa using Fintype.card_subtype_le (fun k : Fin (32 * K) => V i k = true)) hfrac0 hfrac1

theorem sortedPackets_halfProfile_L1_sq {c K : Nat}
    (V : Fin c → Fin (32 * K) → Bool) (hV : ∀ i, Monotone (V i))
    (q : Nat) (frac : Real) (hq : q < 32 * K)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    ((∑ i : Fin c, ∑ j : Fin K,
      |(boolTrueCount (fun k : Fin 32 => V i ⟨32 * j.val + k,
        by have hj := j.isLt; have hk := k.isLt; omega⟩) : Real) -
          profileHalfMean K q frac j.val|)^2) ≤
      (c : Real) * ∑ i : Fin c,
        ((boolTrueCount (V i) : Real) - (q + frac))^2 := by
  rw [sortedPackets_halfProfile_L1_exact V hV q frac hq hfrac0 hfrac1]
  simpa [sq_abs, mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin c => |(boolTrueCount (V i) : Real) - (q + frac)|)
      (fun _ => (1 : Real)))

/-- Routing the ranks of several sorted blocks to arbitrary destination labels
does not increase their aggregate L1 count-profile error, provided each
destination target is the sum of the blocks' suffix-interpolated targets.
This separates the easy reblocking inequality from the still-open problem of
controlling cohort mean errors under the repeated scheduler. -/
theorem monotoneBlocks_assignedRankProfiles_L1_nonincrease
    {D : Type} [Fintype D] [DecidableEq D] {c m : Nat}
    (owner : Fin c → Fin m → D) (bits : Fin c → Fin m → Bool)
    (hbits : ∀ g, Monotone (bits g))
    (q : Fin c → Nat) (frac : Fin c → Real)
    (hq : ∀ g, q g < m) (hfrac0 : ∀ g, 0 ≤ frac g)
    (hfrac1 : ∀ g, frac g ≤ 1) :
    (∑ destination : D,
      |∑ g : Fin c,
        ((assignedBitCount (owner g) (bits g) destination : Real) -
          ((1 - frac g) * assignedRankCount (owner g)
              (fun z k => decide (m - z ≤ k.val)) destination (q g) +
            frac g * assignedRankCount (owner g)
              (fun z k => decide (m - z ≤ k.val)) destination (q g + 1)))|) ≤
      ∑ g : Fin c,
        |(boolTrueCount (bits g) : Real) - ((q g : Real) + frac g)| := by
  classical
  let err (g : Fin c) (destination : D) : Real :=
    (assignedBitCount (owner g) (bits g) destination : Real) -
      ((1 - frac g) * assignedRankCount (owner g)
          (fun z k => decide (m - z ≤ k.val)) destination (q g) +
        frac g * assignedRankCount (owner g)
          (fun z k => decide (m - z ≤ k.val)) destination (q g + 1))
  have hlocal (g : Fin c) :
      (∑ destination : D, |err g destination|) =
        |(boolTrueCount (bits g) : Real) - ((q g : Real) + frac g)| := by
    simpa [err] using
      (monotoneBits_assignedRankProfiles_L1_exact
        (owner g) (bits g) (hbits g) (boolTrueCount (bits g)) (q g)
        (frac g) rfl (hq g) (hfrac0 g) (hfrac1 g))
  calc
    (∑ destination : D, |∑ g : Fin c, err g destination|) ≤
        ∑ destination : D, ∑ g : Fin c, |err g destination| := by
      apply Finset.sum_le_sum
      intro destination _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ g : Fin c, ∑ destination : D, |err g destination| := by
      exact Finset.sum_comm
    _ = ∑ g : Fin c,
        |(boolTrueCount (bits g) : Real) - ((q g : Real) + frac g)| := by
      apply Finset.sum_congr rfl
      intro g _
      exact hlocal g
