import PacketMergeTree
import PacketGenMerge

/-! Scatter checked merge trees to arbitrary injective packet supports. -/

namespace Chvatal.PacketAlignment

open Untangle

def genScatterMergeTree {α : Type} [LinearOrder α] {M N : Nat}
    (tree : PacketMergeTree α M) (e : Fin M ↪ Fin N) : GenNetwork N :=
  genScatter tree.network e

theorem genScatterMergeTree_sorts {α : Type} [LinearOrder α] {M N : Nat}
    (tree : PacketMergeTree α M) (e : Fin M ↪ Fin N) (v : Fin N → α)
    (hv : tree.RunsSorted (fun i => v (e i))) :
    Monotone (fun i => (genScatterMergeTree tree e).exec v (e i)) := by
  have hs := PacketMergeTree.network_sorts tree (fun i => v (e i)) hv
  simpa only [genScatterMergeTree, genScatter_exec_inside] using hs

theorem genScatterMergeTree_depth_eq {α : Type} [LinearOrder α] {M N : Nat}
    (tree : PacketMergeTree α M) (e : Fin M ↪ Fin N) :
    (genScatterMergeTree tree e).depth = tree.network.depth :=
  genScatter_depth tree.network e

theorem genScatterMergeTree_depth_le {α : Type} [LinearOrder α] {M N C : Nat}
    (tree : PacketMergeTree α M) (e : Fin M ↪ Fin N)
    (hdepth : tree.network.depth ≤ C) :
    (genScatterMergeTree tree e).depth ≤ C := by
  rw [genScatterMergeTree_depth_eq]
  exact hdepth

private def packetTreeCellIndex (j : Fin 63) (i : Fin 64) : Fin 4032 :=
  ⟨j.val * 64 + i.val, by have hj := j.isLt; have hi := i.isLt; omega⟩

private def packetTreeBlockCoordinates (i : Fin 4032) : Fin 63 × Fin 64 :=
  (⟨i.val / 64, by
      have hi := i.isLt
      have hd := Nat.div_mul_le_self i.val 64
      omega⟩,
   ⟨i.val % 64, Nat.mod_lt _ (by omega)⟩)

private theorem packetTreeCellIndex_blockCoordinates (i : Fin 4032) :
    packetTreeCellIndex (packetTreeBlockCoordinates i).1
      (packetTreeBlockCoordinates i).2 = i := by
  apply Fin.ext
  change (i.val / 64) * 64 + i.val % 64 = i.val
  omega

private theorem packetTreeBlockCoordinates_cellIndex (j : Fin 63) (i : Fin 64) :
    packetTreeBlockCoordinates (packetTreeCellIndex j i) = (j, i) := by
  apply Prod.ext
  · apply Fin.ext
    change (j.val * 64 + i.val) / 64 = j.val
    omega
  · apply Fin.ext
    change (j.val * 64 + i.val) % 64 = i.val
    omega

private theorem packetTreeCellIndex_mono (j : Fin 63) :
    Monotone (packetTreeCellIndex j) := by
  intro i k hik
  apply Fin.mk_le_mk.mpr
  have hik' := Fin.mk_le_mk.mp hik
  exact Nat.add_le_add_left hik' (j.val * 64)

def genScatterMergeTreeOutputEmbedding {α : Type} [LinearOrder α] {M N : Nat}
    (tree : PacketMergeTree α M) (e : Fin M ↪ Fin N)
    (j : Fin tree.leafCount) : Fin 64 ↪ Fin N :=
  ⟨fun i => e (PacketMergeTree.chunkIndex tree j i), by
    intro i k hik
    apply Fin.ext
    have h := congrArg Fin.val (e.injective hik)
    rw [PacketMergeTree.chunkIndex_val, PacketMergeTree.chunkIndex_val] at h
    omega⟩

theorem genScatterMergeTreeOutputEmbedding_disjoint {α : Type} [LinearOrder α]
    {M N : Nat} (tree : PacketMergeTree α M) (e : Fin M ↪ Fin N)
    {j k : Fin tree.leafCount} (hjk : j ≠ k) (i q : Fin 64) :
    genScatterMergeTreeOutputEmbedding tree e j i ≠
      genScatterMergeTreeOutputEmbedding tree e k q := by
  intro h
  have hidx := e.injective h
  have hv := congrArg Fin.val hidx
  rw [PacketMergeTree.chunkIndex_val, PacketMergeTree.chunkIndex_val] at hv
  apply hjk
  apply Fin.ext
  omega

theorem genScatterMergeTreeOutputEmbedding_covers {α : Type} [LinearOrder α]
    {M N : Nat} (tree : PacketMergeTree α M) (e : Fin M ↪ Fin N)
    (i : Fin M) :
    ∃ (j : Fin tree.leafCount) (q : Fin 64),
      genScatterMergeTreeOutputEmbedding tree e j q = e i := by
  let j : Fin tree.leafCount := ⟨i.val / 64, by
    have hi := i.isLt
    have hs := PacketMergeTree.leafCount_size tree
    have hd := Nat.div_mul_le_self i.val 64
    omega⟩
  let q : Fin 64 := ⟨i.val % 64, Nat.mod_lt _ (by omega)⟩
  have hidx : PacketMergeTree.chunkIndex tree j q = i := by
    apply Fin.ext
    rw [PacketMergeTree.chunkIndex_val]
    dsimp [j, q]
    omega
  exact ⟨j, q, by simp [genScatterMergeTreeOutputEmbedding, hidx]⟩

def genPacketGroup63Embedding {N : Nat} (packets : Fin 63 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 63}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q) : Fin 4032 ↪ Fin N :=
  ⟨fun x => packets (packetTreeBlockCoordinates x).1
      (packetTreeBlockCoordinates x).2, by
    intro x y hxy
    let cx := packetTreeBlockCoordinates x
    let cy := packetTreeBlockCoordinates y
    change packets cx.1 cx.2 = packets cy.1 cy.2 at hxy
    have hcoords : cx.1 = cy.1 := by
      by_contra hne
      exact hdisjoint hne cx.2 cy.2 hxy
    rw [hcoords] at hxy
    have hinner : cx.2 = cy.2 := (packets cy.1).injective hxy
    have hprod : cx = cy := Prod.ext hcoords hinner
    calc
      x = packetTreeCellIndex cx.1 cx.2 := (packetTreeCellIndex_blockCoordinates x).symm
      _ = packetTreeCellIndex cy.1 cy.2 := congrArg (fun p : Fin 63 × Fin 64 =>
        packetTreeCellIndex p.1 p.2) hprod
      _ = y := packetTreeCellIndex_blockCoordinates y⟩

theorem genPacketGroup63Embedding_mem_packets {N : Nat}
    (packets : Fin 63 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 63}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q) (x : Fin 4032) :
    ∃ (j : Fin 63) (i : Fin 64),
      genPacketGroup63Embedding packets hdisjoint x = packets j i := by
  exact ⟨(packetTreeBlockCoordinates x).1, (packetTreeBlockCoordinates x).2, rfl⟩

theorem genPacketGroup63Embedding_covers_packets {N : Nat}
    (packets : Fin 63 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 63}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q) (j : Fin 63) (i : Fin 64) :
    ∃ x : Fin 4032, genPacketGroup63Embedding packets hdisjoint x = packets j i := by
  refine ⟨packetTreeCellIndex j i, ?_⟩
  simp [genPacketGroup63Embedding, packetTreeBlockCoordinates_cellIndex]

private def packetTreeCellIndex64 (j i : Fin 64) : Fin 4096 :=
  ⟨j.val * 64 + i.val, by have hj := j.isLt; have hi := i.isLt; omega⟩

private def packetTreeBlockCoordinates64 (i : Fin 4096) : Fin 64 × Fin 64 :=
  (⟨i.val / 64, by
      have hi := i.isLt
      have hd := Nat.div_mul_le_self i.val 64
      omega⟩,
   ⟨i.val % 64, Nat.mod_lt _ (by omega)⟩)

private theorem packetTreeCellIndex64_blockCoordinates (i : Fin 4096) :
    packetTreeCellIndex64 (packetTreeBlockCoordinates64 i).1
      (packetTreeBlockCoordinates64 i).2 = i := by
  apply Fin.ext
  change (i.val / 64) * 64 + i.val % 64 = i.val
  omega

private theorem packetTreeBlockCoordinates64_cellIndex (j i : Fin 64) :
    packetTreeBlockCoordinates64 (packetTreeCellIndex64 j i) = (j, i) := by
  apply Prod.ext
  · apply Fin.ext
    change (j.val * 64 + i.val) / 64 = j.val
    omega
  · apply Fin.ext
    change (j.val * 64 + i.val) % 64 = i.val
    omega

def genPacketGroup64Embedding {N : Nat} (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q) : Fin 4096 ↪ Fin N :=
  ⟨fun x => packets (packetTreeBlockCoordinates64 x).1
      (packetTreeBlockCoordinates64 x).2, by
    intro x y hxy
    let cx := packetTreeBlockCoordinates64 x
    let cy := packetTreeBlockCoordinates64 y
    change packets cx.1 cx.2 = packets cy.1 cy.2 at hxy
    have hcoords : cx.1 = cy.1 := by
      by_contra hne
      exact hdisjoint hne cx.2 cy.2 hxy
    rw [hcoords] at hxy
    have hinner : cx.2 = cy.2 := (packets cy.1).injective hxy
    have hprod : cx = cy := Prod.ext hcoords hinner
    calc
      x = packetTreeCellIndex64 cx.1 cx.2 :=
        (packetTreeCellIndex64_blockCoordinates x).symm
      _ = packetTreeCellIndex64 cy.1 cy.2 := congrArg
        (fun p : Fin 64 × Fin 64 => packetTreeCellIndex64 p.1 p.2) hprod
      _ = y := packetTreeCellIndex64_blockCoordinates y⟩

theorem genPacketGroup64Embedding_mem_packets {N : Nat}
    (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q) (x : Fin 4096) :
    ∃ (j : Fin 64) (i : Fin 64),
      genPacketGroup64Embedding packets hdisjoint x = packets j i := by
  exact ⟨(packetTreeBlockCoordinates64 x).1,
    (packetTreeBlockCoordinates64 x).2, rfl⟩

theorem genPacketGroup64Embedding_covers_packets {N : Nat}
    (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q) (j i : Fin 64) :
    ∃ x : Fin 4096, genPacketGroup64Embedding packets hdisjoint x = packets j i := by
  refine ⟨packetTreeCellIndex64 j i, ?_⟩
  simp [genPacketGroup64Embedding, packetTreeBlockCoordinates64_cellIndex]

theorem packetOddTree6_leafCount {α : Type} [LinearOrder α] :
    (packetOddTree6 (α := α)).leafCount = 63 := by
  simp [packetOddTree6, packetOddTree5, packetOddTree4, packetOddTree3,
    packetOddTree2, packetOddTree1, packetPowerTree5, packetPowerTree4,
    packetPowerTree3, packetPowerTree2, packetPowerTree1, packetPowerTree0,
    PacketMergeTree.leafCount]

theorem packetOddTree6_runsSorted_of_packets {N : Nat} {α : Type}
    [LinearOrder α] (packets : Fin 63 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 63}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q)
    (v : Fin N → α)
    (hpackets : ∀ j : Fin 63, Monotone (fun i => v (packets j i))) :
    (packetOddTree6 (α := α)).RunsSorted
      (fun i => v (genPacketGroup63Embedding packets hdisjoint i)) := by
  let tree := packetOddTree6 (α := α)
  have hcount : tree.leafCount = 63 := packetOddTree6_leafCount
  apply PacketMergeTree.runsSorted_of_chunks tree
  intro j
  let jp : Fin 63 := Fin.cast hcount j
  have heq : ∀ i : Fin 64,
      genPacketGroup63Embedding packets hdisjoint (PacketMergeTree.chunkIndex tree j i) =
        packets jp i := by
    intro i
    have hindex : PacketMergeTree.chunkIndex tree j i = packetTreeCellIndex jp i := by
      apply Fin.ext
      rw [PacketMergeTree.chunkIndex_val]
      simp [packetTreeCellIndex, jp]
    rw [hindex]
    simp [genPacketGroup63Embedding, packetTreeBlockCoordinates_cellIndex]
  simpa only [heq] using hpackets jp

theorem packetPowerTree6_leafCount {α : Type} [LinearOrder α] :
    (packetPowerTree6 (α := α)).leafCount = 64 := by
  simp [packetPowerTree6, packetPowerTree5, packetPowerTree4, packetPowerTree3,
    packetPowerTree2, packetPowerTree1, packetPowerTree0, PacketMergeTree.leafCount]

theorem packetPowerTree6_runsSorted_of_packets {N : Nat} {α : Type}
    [LinearOrder α] (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q)
    (v : Fin N → α)
    (hpackets : ∀ j : Fin 64, Monotone (fun i => v (packets j i))) :
    (packetPowerTree6 (α := α)).RunsSorted
      (fun i => v (genPacketGroup64Embedding packets hdisjoint i)) := by
  let tree := packetPowerTree6 (α := α)
  have hcount : tree.leafCount = 64 := packetPowerTree6_leafCount
  apply PacketMergeTree.runsSorted_of_chunks tree
  intro j
  let jp : Fin 64 := Fin.cast hcount j
  have heq : ∀ i : Fin 64,
      genPacketGroup64Embedding packets hdisjoint (PacketMergeTree.chunkIndex tree j i) =
        packets jp i := by
    intro i
    have hindex : PacketMergeTree.chunkIndex tree j i = packetTreeCellIndex64 jp i := by
      apply Fin.ext
      rw [PacketMergeTree.chunkIndex_val]
      simp [packetTreeCellIndex64, jp]
    rw [hindex]
    simp [genPacketGroup64Embedding, packetTreeBlockCoordinates64_cellIndex]
  simpa only [heq] using hpackets jp

def packetOddTree6GroupNet {N : Nat} {α : Type} [LinearOrder α]
    (packets : Fin 63 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 63}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q) : GenNetwork N :=
  genScatterMergeTree (packetOddTree6 (α := α))
    (genPacketGroup63Embedding packets hdisjoint)

theorem packetOddTree6GroupNet_sorts {N : Nat} {α : Type} [LinearOrder α]
    (packets : Fin 63 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 63}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q)
    (v : Fin N → α)
    (hpackets : ∀ j : Fin 63, Monotone (fun i => v (packets j i))) :
    Monotone (fun i =>
      (packetOddTree6GroupNet (α := α) packets hdisjoint).exec v
        (genPacketGroup63Embedding packets hdisjoint i)) := by
  have hRuns := packetOddTree6_runsSorted_of_packets packets hdisjoint v hpackets
  exact genScatterMergeTree_sorts (packetOddTree6 (α := α))
    (genPacketGroup63Embedding packets hdisjoint) v hRuns

theorem packetOddTree6GroupNet_depth_le {N : Nat} {α : Type} [LinearOrder α]
    (packets : Fin 63 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 63}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q) :
    (packetOddTree6GroupNet (α := α) packets hdisjoint).depth ≤ 57 := by
  exact genScatterMergeTree_depth_le (packetOddTree6 (α := α))
    (genPacketGroup63Embedding packets hdisjoint) packetOddTree6_depth_le

def packetPowerTree6GroupNet {N : Nat} {α : Type} [LinearOrder α]
    (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q) : GenNetwork N :=
  genScatterMergeTree (packetPowerTree6 (α := α))
    (genPacketGroup64Embedding packets hdisjoint)

theorem packetPowerTree6GroupNet_sorts {N : Nat} {α : Type} [LinearOrder α]
    (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q)
    (v : Fin N → α)
    (hpackets : ∀ j : Fin 64, Monotone (fun i => v (packets j i))) :
    Monotone (fun i =>
      (packetPowerTree6GroupNet (α := α) packets hdisjoint).exec v
        (genPacketGroup64Embedding packets hdisjoint i)) := by
  have hRuns := packetPowerTree6_runsSorted_of_packets packets hdisjoint v hpackets
  exact genScatterMergeTree_sorts (packetPowerTree6 (α := α))
    (genPacketGroup64Embedding packets hdisjoint) v hRuns

theorem packetPowerTree6GroupNet_depth_le {N : Nat} {α : Type} [LinearOrder α]
    (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q) :
    (packetPowerTree6GroupNet (α := α) packets hdisjoint).depth ≤ 57 := by
  exact genScatterMergeTree_depth_le (packetPowerTree6 (α := α))
    (genPacketGroup64Embedding packets hdisjoint) packetPowerTree6_depth_le

theorem genScatterMergeTree_outputPacket_sorted {M N : Nat} {α : Type}
    [LinearOrder α] (tree : PacketMergeTree α M)
    (e : Fin M ↪ Fin N)
    (v : Fin N → α)
    (hRuns : tree.RunsSorted (fun i => v (e i)))
    (j : Fin tree.leafCount) :
    Monotone (fun i =>
      (genScatterMergeTree tree e).exec v
        (genScatterMergeTreeOutputEmbedding tree e j i)) := by
  have hsorted := genScatterMergeTree_sorts tree e v hRuns
  have hmono := hsorted.comp (PacketMergeTree.chunkIndex_mono tree j)
  simpa only [genScatterMergeTreeOutputEmbedding] using hmono

theorem packetPowerTree6GroupNet_outputPacket_sorted {N : Nat} {α : Type}
    [LinearOrder α] (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q)
    (v : Fin N → α)
    (hpackets : ∀ j : Fin 64, Monotone (fun i => v (packets j i)))
    (j : Fin (packetPowerTree6 (α := α)).leafCount) :
    Monotone (fun i =>
      (packetPowerTree6GroupNet (α := α) packets hdisjoint).exec v
        (genScatterMergeTreeOutputEmbedding
          (packetPowerTree6 (α := α))
          (genPacketGroup64Embedding packets hdisjoint) j i)) := by
  have hRuns := packetPowerTree6_runsSorted_of_packets packets hdisjoint v hpackets
  exact genScatterMergeTree_outputPacket_sorted (packetPowerTree6 (α := α))
    (genPacketGroup64Embedding packets hdisjoint) v hRuns j

theorem packetOddTree6GroupNet_outputPacket_sorted {N : Nat} {α : Type}
    [LinearOrder α] (packets : Fin 63 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 63}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q)
    (v : Fin N → α)
    (hpackets : ∀ j : Fin 63, Monotone (fun i => v (packets j i)))
    (j : Fin (packetOddTree6 (α := α)).leafCount) :
    Monotone (fun i =>
      (packetOddTree6GroupNet (α := α) packets hdisjoint).exec v
        (genScatterMergeTreeOutputEmbedding
          (packetOddTree6 (α := α))
          (genPacketGroup63Embedding packets hdisjoint) j i)) := by
  have hRuns := packetOddTree6_runsSorted_of_packets packets hdisjoint v hpackets
  exact genScatterMergeTree_outputPacket_sorted (packetOddTree6 (α := α))
    (genPacketGroup63Embedding packets hdisjoint) v hRuns j

/-- Run the same fixed merge tree independently over a finite disjoint family
of logical supports. -/
def genScatterMergeTreeBatch {α : Type} [LinearOrder α] {M N : Nat}
    (tree : PacketMergeTree α M) (supports : List (Fin M ↪ Fin N)) : GenNetwork N :=
  genScatterBatch tree.network supports

theorem genScatterMergeTreeBatch_depth_le {α : Type} [LinearOrder α]
    {M N : Nat} (tree : PacketMergeTree α M)
    (supports : List (Fin M ↪ Fin N)) (hnd : supports.Nodup)
    (hdis : ∀ e ∈ supports, ∀ f ∈ supports, e ≠ f → ∀ i j, e i ≠ f j)
    (D : Nat) (hdepth : tree.network.depth ≤ D) :
    (genScatterMergeTreeBatch tree supports).depth ≤ D := by
  exact (genScatterBatch_depth_le tree.network supports hnd hdis).trans hdepth

/-- Every block in a parallel merge-tree batch exits as sorted 64-wire
packets, with the same execution as its individual scattered tree. -/
theorem genScatterMergeTreeBatch_outputPacket_sorted {α : Type}
    [LinearOrder α] {M N : Nat} (tree : PacketMergeTree α M)
    (supports : List (Fin M ↪ Fin N)) (hnd : supports.Nodup)
    (hdis : ∀ e ∈ supports, ∀ f ∈ supports, e ≠ f → ∀ i j, e i ≠ f j)
    (v : Fin N → α)
    (hRuns : ∀ e ∈ supports, tree.RunsSorted (fun i => v (e i)))
    (e : Fin M ↪ Fin N) (he : e ∈ supports)
    (j : Fin tree.leafCount) :
    Monotone (fun i =>
      (genScatterMergeTreeBatch tree supports).exec v
        (genScatterMergeTreeOutputEmbedding tree e j i)) := by
  have hlocal := genScatterMergeTree_outputPacket_sorted tree e v (hRuns e he) j
  intro i k hik
  change (genScatterMergeTreeBatch tree supports).exec v
      (e (PacketMergeTree.chunkIndex tree j i)) ≤
    (genScatterMergeTreeBatch tree supports).exec v
      (e (PacketMergeTree.chunkIndex tree j k))
  change (genScatterBatch tree.network supports).exec v
      (e (PacketMergeTree.chunkIndex tree j i)) ≤
    (genScatterBatch tree.network supports).exec v
      (e (PacketMergeTree.chunkIndex tree j k))
  rw [genScatterBatch_exec_inside tree.network supports hnd hdis v e he
    (PacketMergeTree.chunkIndex tree j i),
    genScatterBatch_exec_inside tree.network supports hnd hdis v e he
    (PacketMergeTree.chunkIndex tree j k)]
  exact hlocal hik

end Chvatal.PacketAlignment
