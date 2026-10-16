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

/-- The output chunks of a merge tree partition exactly the wires in its
input embedding. -/
theorem genScatterMergeTreeOutputEmbedding_support_iff {α : Type}
    [LinearOrder α] {M N : Nat} (tree : PacketMergeTree α M)
    (e : Fin M ↪ Fin N) (w : Fin N) :
    (∃ j : Fin tree.leafCount,
      w ∈ Set.range (genScatterMergeTreeOutputEmbedding tree e j)) ↔
      w ∈ Set.range e := by
  constructor
  · rintro ⟨j, q, hq⟩
    exact ⟨PacketMergeTree.chunkIndex tree j q, hq⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, q, hq⟩ := genScatterMergeTreeOutputEmbedding_covers tree e i
    exact ⟨j, q, hq⟩

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

/-- The Boolean threshold count of a logical 64-packet group is the sum of
the 64 source-packet counts. This makes the grouped merge's scalar target
equal to the sum of heterogeneous packet targets. -/
theorem boolTrueCount_genPacketGroup64Embedding_sum {N : Nat}
    (packets : Fin 64 → Fin 64 ↪ Fin N)
    (hdisjoint : ∀ {j k : Fin 64}, j ≠ k → ∀ (i q : Fin 64),
      packets j i ≠ packets k q) (v : Fin N → Bool) :
    boolTrueCount (fun x : Fin 4096 =>
      v (genPacketGroup64Embedding packets hdisjoint x)) =
      ∑ j : Fin 64, boolTrueCount (fun i : Fin 64 => v (packets j i)) := by
  let source := {x : Fin 4096 //
    v (genPacketGroup64Embedding packets hdisjoint x) = true}
  let pairPred : Fin 64 × Fin 64 → Prop := fun p =>
    v (packets p.1 p.2) = true
  let coordEquiv : Fin 4096 ≃ Fin 64 × Fin 64 := {
    toFun := packetTreeBlockCoordinates64
    invFun := fun p => packetTreeCellIndex64 p.1 p.2
    left_inv := packetTreeCellIndex64_blockCoordinates
    right_inv := by
      rintro ⟨j, i⟩
      exact packetTreeBlockCoordinates64_cellIndex j i
  }
  have hsource : ∀ x : Fin 4096,
      v (genPacketGroup64Embedding packets hdisjoint x) = true ↔
        pairPred (coordEquiv x) := by
    intro x
    change v (packets (packetTreeBlockCoordinates64 x).1
      (packetTreeBlockCoordinates64 x).2) = true ↔ _
    rfl
  let e1 := Equiv.subtypeEquiv coordEquiv hsource
  let e2 : {p : Fin 64 × Fin 64 // pairPred p} ≃
      (Σ j : Fin 64, {i : Fin 64 // v (packets j i) = true}) := {
    toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
    invFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
    left_inv := by intro p; apply Subtype.ext; rfl
    right_inv := by
      rintro ⟨j, ⟨i, hi⟩⟩
      apply Sigma.ext
      · rfl
      · exact HEq.rfl
  }
  let e : source ≃ (Σ j : Fin 64, {i : Fin 64 // v (packets j i) = true}) :=
    e1.trans e2
  unfold boolTrueCount
  calc
    Fintype.card source =
        Fintype.card (Σ j : Fin 64, {i : Fin 64 // v (packets j i) = true}) :=
      Fintype.card_congr e
    _ = ∑ j : Fin 64, Fintype.card {i : Fin 64 // v (packets j i) = true} :=
      Fintype.card_sigma
    _ = ∑ j : Fin 64, boolTrueCount (fun i : Fin 64 => v (packets j i)) := rfl

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

/-- The packet at offset `i` inside the `j`th consecutive 64-packet block of
a cohort whose packet count is `64*q`. -/
def packetFamily64BlockIndex {q : Nat} (j : Fin q) (i : Fin 64) : Fin (q * 64) :=
  ⟨j.val * 64 + i.val, by have hj := j.isLt; have hi := i.isLt; omega⟩

theorem packetFamily64BlockIndex_injective {q : Nat} (j : Fin q) :
    Function.Injective (packetFamily64BlockIndex j) := by
  intro i k h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [packetFamily64BlockIndex, Fin.val_mk] at hv
  omega

/-- Assemble 64 consecutive packets into the 4096-wire support expected by
the proved 64-run merge tree. -/
def packetFamily64BlockEmbedding {q N : Nat}
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (j : Fin q) : Fin 4096 ↪ Fin N :=
  genPacketGroup64Embedding (fun i => packets (packetFamily64BlockIndex j i))
    (by
      intro i k hik x y heq
      apply hdis (packetFamily64BlockIndex j i) (packetFamily64BlockIndex j k)
      · intro h
        apply hik
        exact packetFamily64BlockIndex_injective j h
      · exact heq)

theorem packetFamily64BlockEmbedding_disjoint {q N : Nat}
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    {j k : Fin q} (hjk : j ≠ k) (x y : Fin 4096) :
    packetFamily64BlockEmbedding packets hdis j x ≠
      packetFamily64BlockEmbedding packets hdis k y := by
  let localPackets := fun (g : Fin q) (i : Fin 64) =>
    packets (packetFamily64BlockIndex g i)
  have hinner : ∀ (g : Fin q) (a b : Fin 64), a ≠ b →
      ∀ u v, localPackets g a u ≠ localPackets g b v := by
    intro g a b hab u v heq
    apply hdis (packetFamily64BlockIndex g a) (packetFamily64BlockIndex g b)
    · intro h
      apply hab
      exact packetFamily64BlockIndex_injective g h
    · exact heq
  obtain ⟨a, u, hx⟩ := genPacketGroup64Embedding_mem_packets
    (localPackets j) (by
      intro a b hab u v
      exact hinner j a b hab u v) x
  obtain ⟨b, v, hy⟩ := genPacketGroup64Embedding_mem_packets
    (localPackets k) (by
      intro a b hab u v
      exact hinner k a b hab u v) y
  have hidx : packetFamily64BlockIndex j a ≠ packetFamily64BlockIndex k b := by
    intro hidx
    apply hjk
    apply Fin.ext
    have hv := congrArg Fin.val hidx
    simp only [packetFamily64BlockIndex, Fin.val_mk] at hv
    omega
  intro heq
  have hval : packets (packetFamily64BlockIndex j a) u =
      packets (packetFamily64BlockIndex k b) v := by
    calc
      packets (packetFamily64BlockIndex j a) u =
          packetFamily64BlockEmbedding packets hdis j x := hx.symm
      _ = packetFamily64BlockEmbedding packets hdis k y := heq
      _ = packets (packetFamily64BlockIndex k b) v := hy
  exact (hdis _ _ hidx u v) hval

/-- Enumerate all full 64-packet blocks of a cohort whose packet count is
divisible by 64. -/
def packetFamily64BlockList {q N : Nat}
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y) :
    List (Fin 4096 ↪ Fin N) :=
  List.ofFn (packetFamily64BlockEmbedding packets hdis)

/-- The grouped full blocks cover exactly the wires of the packets in their
cohort. This makes the parallel merge output a full-support packet family. -/
theorem packetFamily64BlockList_support {q N : Nat}
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (w : Fin N) :
    (∃ e ∈ packetFamily64BlockList packets hdis, w ∈ Set.range e) ↔
      (∃ a : Fin (q * 64), ∃ i : Fin 64, packets a i = w) := by
  constructor
  · rintro ⟨e, he, x, hx⟩
    simp only [packetFamily64BlockList, List.mem_ofFn] at he
    obtain ⟨j, rfl⟩ := he
    obtain ⟨a, i, hxi⟩ := genPacketGroup64Embedding_mem_packets
      (packets := fun k => packets (packetFamily64BlockIndex j k))
      (hdisjoint := by
        intro k l hkl u v huv
        apply hdis (packetFamily64BlockIndex j k) (packetFamily64BlockIndex j l)
        · intro h
          apply hkl
          exact packetFamily64BlockIndex_injective j h
        · exact huv)
      (x := x)
    exact ⟨packetFamily64BlockIndex j a, i, hxi.symm.trans hx⟩
  · rintro ⟨a, i, rfl⟩
    have hquot : a.val / 64 < q := by
      apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 64)).2
      simpa [Nat.mul_comm] using a.isLt
    let j : Fin q := ⟨a.val / 64, hquot⟩
    let k : Fin 64 := ⟨a.val % 64, Nat.mod_lt _ (by norm_num)⟩
    have hidx : packetFamily64BlockIndex j k = a := by
      apply Fin.ext
      simp only [packetFamily64BlockIndex, Fin.val_mk]
      simpa [j, k, Nat.mul_comm] using Nat.div_add_mod a.val 64
    obtain ⟨x, hx⟩ := genPacketGroup64Embedding_covers_packets
      (packets := fun l => packets (packetFamily64BlockIndex j l))
      (hdisjoint := by
        intro l m hlm u v huv
        apply hdis (packetFamily64BlockIndex j l) (packetFamily64BlockIndex j m)
        · intro h
          apply hlm
          exact packetFamily64BlockIndex_injective j h
        · exact huv)
      (j := k) (i := i)
    refine ⟨packetFamily64BlockEmbedding packets hdis j, ?_, x, ?_⟩
    · simp [packetFamily64BlockList]
    · change genPacketGroup64Embedding
        (fun l => packets (packetFamily64BlockIndex j l)) _ x = packets a i
      rw [← hidx]
      exact hx

/-- The output chunks of all grouped 64-run merges cover exactly the wires
in the original packet cohort. Thus the merge simultaneously preserves the
cohort support while redistributing it into sorted rank packets. -/
theorem packetFamily64BlockList_output_support {q N : Nat}
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    {α : Type} [LinearOrder α]
    (tree : PacketMergeTree α 4096)
    (w : Fin N) :
    (∃ e ∈ packetFamily64BlockList packets hdis,
      ∃ j : Fin tree.leafCount,
        w ∈ Set.range (genScatterMergeTreeOutputEmbedding tree e j)) ↔
      (∃ a : Fin (q * 64), ∃ i : Fin 64, packets a i = w) := by
  constructor
  · rintro ⟨e, he, j, hw⟩
    apply (packetFamily64BlockList_support packets hdis w).mp
    exact ⟨e, he,
      (genScatterMergeTreeOutputEmbedding_support_iff tree e w).mp
        ⟨j, hw⟩⟩
  · intro hw
    obtain ⟨e, he, hw⟩ :=
      (packetFamily64BlockList_support packets hdis w).mpr hw
    obtain ⟨j, hj⟩ :=
      (genScatterMergeTreeOutputEmbedding_support_iff tree e w).mpr hw
    exact ⟨e, he, j, hj⟩

/-- A cohort with 63 packets beyond a multiple of 64 is covered exactly by
its merged full blocks and its one 63-packet tail. -/
theorem packetFamily64BlockList_residue63_support {q N : Nat}
    (packets : Fin (q * 64 + 63) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (w : Fin N) :
    (∃ e ∈ packetFamily64BlockList
        (fun i : Fin (q * 64) => packets ⟨i.val, by have hi := i.isLt; omega⟩)
        (by
          intro a b hab x y heq
          exact hdis ⟨a.val, by have ha := a.isLt; omega⟩
            ⟨b.val, by have hb := b.isLt; omega⟩
            (by
              intro h
              apply hab
              apply Fin.ext
              have hv := congrArg Fin.val h
              simpa using hv) x y heq),
      w ∈ Set.range e) ∨
      w ∈ Set.range (genPacketGroup63Embedding
        (fun i : Fin 63 => packets ⟨q * 64 + i.val, by have hi := i.isLt; omega⟩)
        (by
          intro a b hab x y heq
          exact hdis ⟨q * 64 + a.val, by have ha := a.isLt; omega⟩
            ⟨q * 64 + b.val, by have hb := b.isLt; omega⟩
            (by
              intro h
              apply hab
              apply Fin.ext
              have hv := congrArg Fin.val h
              simp only [Fin.val_mk] at hv
              omega) x y heq)) ↔
      (∃ a : Fin (q * 64 + 63), ∃ i : Fin 64, packets a i = w) := by
  let prefixIndex : Fin (q * 64) → Fin (q * 64 + 63) :=
    fun i => ⟨i.val, by have hi := i.isLt; omega⟩
  let tailIndex : Fin 63 → Fin (q * 64 + 63) :=
    fun i => ⟨q * 64 + i.val, by have hi := i.isLt; omega⟩
  let prefixPackets : Fin (q * 64) → Fin 64 ↪ Fin N :=
    fun i => packets (prefixIndex i)
  let tailPackets : Fin 63 → Fin 64 ↪ Fin N := fun i => packets (tailIndex i)
  have hprefixInj : Function.Injective prefixIndex := by
    intro i j h
    apply Fin.ext
    simpa [prefixIndex] using congrArg Fin.val h
  have htailInj : Function.Injective tailIndex := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [tailIndex, Fin.val_mk] at hv
    omega
  have hprefixDis : ∀ a b, a ≠ b → ∀ x y, prefixPackets a x ≠ prefixPackets b y := by
    intro a b hab x y heq
    exact hdis (prefixIndex a) (prefixIndex b)
      (fun h => hab (hprefixInj h)) x y heq
  have htailDis : ∀ {a b : Fin 63}, a ≠ b → ∀ x y,
      tailPackets a x ≠ tailPackets b y := by
    intro a b hab x y heq
    exact hdis (tailIndex a) (tailIndex b)
      (fun h => hab (htailInj h)) x y heq
  change (∃ e ∈ packetFamily64BlockList prefixPackets hprefixDis,
      w ∈ Set.range e) ∨
      w ∈ Set.range (genPacketGroup63Embedding tailPackets htailDis) ↔ _
  constructor
  · rintro (⟨e, he, hw⟩ | ⟨x, hx⟩)
    · obtain ⟨a, i, hai⟩ :=
        (packetFamily64BlockList_support prefixPackets hprefixDis w).mp
          ⟨e, he, hw⟩
      exact ⟨prefixIndex a, i, hai⟩
    · obtain ⟨a, i, hai⟩ :=
        genPacketGroup63Embedding_mem_packets tailPackets htailDis x
      exact ⟨tailIndex a, i, hai.symm.trans hx⟩
  · rintro ⟨a, i, hai⟩
    by_cases hprefix : a.val < q * 64
    · let j : Fin (q * 64) := ⟨a.val, hprefix⟩
      have hj : prefixIndex j = a := by
        apply Fin.ext
        rfl
      left
      apply (packetFamily64BlockList_support prefixPackets hprefixDis w).mpr
      exact ⟨j, i, by simpa [prefixPackets, hj] using hai⟩
    · have htailBound : q * 64 ≤ a.val := by omega
      let j : Fin 63 := ⟨a.val - q * 64, by have ha := a.isLt; omega⟩
      have hj : tailIndex j = a := by
        apply Fin.ext
        simp [tailIndex, j]
        omega
      right
      obtain ⟨x, hx⟩ := genPacketGroup63Embedding_covers_packets
        tailPackets htailDis j i
      refine ⟨x, ?_⟩
      calc
        genPacketGroup63Embedding tailPackets htailDis x = tailPackets j i := hx
        _ = packets a i := by simp [tailPackets, hj]
        _ = w := hai

theorem packetFamily64BlockList_nodup {q N : Nat}
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y) :
    (packetFamily64BlockList packets hdis).Nodup := by
  apply List.nodup_ofFn_ofInjective
  intro j k hEq
  apply Fin.ext
  by_contra hne
  have hjk : j ≠ k := by
    intro h
    apply hne
    exact congrArg Fin.val h
  have hwire := congrArg (fun e : Fin 4096 ↪ Fin N => e 0) hEq
  exact (packetFamily64BlockEmbedding_disjoint packets hdis hjk 0 0) hwire

theorem packetFamily64BlockList_disjoint {q N : Nat}
    (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (e : Fin 4096 ↪ Fin N) (he : e ∈ packetFamily64BlockList packets hdis)
    (f : Fin 4096 ↪ Fin N) (hf : f ∈ packetFamily64BlockList packets hdis)
    (hne : e ≠ f) (x y : Fin 4096) : e x ≠ f y := by
  simp only [packetFamily64BlockList, List.mem_ofFn] at he hf
  obtain ⟨j, rfl⟩ := he
  obtain ⟨k, rfl⟩ := hf
  have hjkVal : j.val ≠ k.val := by
    intro h
    apply hne
    exact congrArg (packetFamily64BlockEmbedding packets hdis) (Fin.ext h)
  have hjk : j ≠ k := by
    intro h
    apply hjkVal
    exact congrArg Fin.val h
  exact packetFamily64BlockEmbedding_disjoint packets hdis hjk x y

/-- All full blocks in a divisible cohort can be merged simultaneously in 57
layers. -/
theorem packetFamily64BlockList_merge_depth_le {q N : Nat} {α : Type}
    [LinearOrder α] (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y) :
    (genScatterMergeTreeBatch (packetPowerTree6 (α := α))
      (packetFamily64BlockList packets hdis)).depth ≤ 57 := by
  have hnd := packetFamily64BlockList_nodup packets hdis
  have hdisBlocks := packetFamily64BlockList_disjoint packets hdis
  exact genScatterMergeTreeBatch_depth_le (packetPowerTree6 (α := α))
    (packetFamily64BlockList packets hdis) hnd hdisBlocks 57
    packetPowerTree6_depth_le

/-- If each input packet in a divisible cohort is sorted, every output packet
from every parallel full-block merge is sorted. -/
theorem packetFamily64BlockList_merge_output_sorted {q N : Nat} {α : Type}
    [LinearOrder α] (packets : Fin (q * 64) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (v : Fin N → α)
    (hpackets : ∀ a, Monotone (fun i => v (packets a i))) :
    ∀ e ∈ packetFamily64BlockList packets hdis,
      ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α))
            (packetFamily64BlockList packets hdis)).exec v
              (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α))
                e j i)) := by
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
  exact genScatterMergeTreeBatch_outputPacket_sorted
    (packetPowerTree6 (α := α)) (packetFamily64BlockList packets hdis)
    hnd hdisBlocks v hRuns e he j

/-- For any pairwise-disjoint sorted packet family whose cardinality is a
multiple of 64, expose its consecutive full-block decomposition and the
parallel 57-layer merge result. -/
theorem packetFamily_divisible64_merge {m N : Nat} {α : Type}
    [LinearOrder α] (packets : Fin m → Fin 64 ↪ Fin N)
    (hdiv : 64 ∣ m)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (v : Fin N → α)
    (hpackets : ∀ a, Monotone (fun i => v (packets a i))) :
    ∃ blocks : List (Fin 4096 ↪ Fin N),
      blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).depth ≤ 57 ∧
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genScatterMergeTreeBatch (packetPowerTree6 (α := α)) blocks).exec v
            (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) := by
  let q := m / 64
  have hq : q * 64 = m := by
    dsimp [q]
    exact Nat.div_mul_cancel hdiv
  let castPackets : Fin (q * 64) → Fin 64 ↪ Fin N :=
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
  refine ⟨blocks, ?_, ?_, ?_, ?_⟩
  · exact packetFamily64BlockList_nodup castPackets hdis'
  · exact packetFamily64BlockList_disjoint castPackets hdis'
  · exact packetFamily64BlockList_merge_depth_le castPackets hdis'
  · exact packetFamily64BlockList_merge_output_sorted castPackets hdis' v
      (fun a => hpackets (Fin.cast hq a))

/-- Concatenate a parallel family of full-block merge trees with one unequal
tail merge tree on a disjoint support. -/
def genMergeTreeFullTailBatch {α : Type} [LinearOrder α] {M K N : Nat}
    (fullTree : PacketMergeTree α M) (tailTree : PacketMergeTree α K)
    (fullBlocks : List (Fin M ↪ Fin N)) (tail : Fin K ↪ Fin N) : GenNetwork N :=
  ⟨(genScatterMergeTreeBatch fullTree fullBlocks).comparators ++
    (genScatterMergeTree tailTree tail).comparators⟩

theorem genMergeTreeFullTailBatch_depth_le {α : Type} [LinearOrder α]
    {M K N : Nat} (fullTree : PacketMergeTree α M) (tailTree : PacketMergeTree α K)
    (fullBlocks : List (Fin M ↪ Fin N)) (tail : Fin K ↪ Fin N)
    (hnd : fullBlocks.Nodup)
    (hdis : ∀ e ∈ fullBlocks, ∀ f ∈ fullBlocks, e ≠ f → ∀ i j, e i ≠ f j)
    (hsep : ∀ e ∈ fullBlocks, ∀ i j, e i ≠ tail j)
    (D : Nat) (hfullDepth : fullTree.network.depth ≤ D)
    (htailDepth : tailTree.network.depth ≤ D) :
    (genMergeTreeFullTailBatch fullTree tailTree fullBlocks tail).depth ≤ D := by
  apply genDisjointAppend_depth_le
    (genScatterMergeTreeBatch fullTree fullBlocks)
    (genScatterMergeTree tailTree tail) D
  · exact genScatterMergeTreeBatch_depth_le fullTree fullBlocks hnd hdis D hfullDepth
  · exact genScatterMergeTree_depth_le tailTree tail htailDepth
  · exact genScatterBatch_genScatter_comparators_disjoint
      fullTree.network fullBlocks tailTree.network tail hsep
/-- A disjoint 63-run tail and every full block retain their independent
sorted outputs when their merge trees are concatenated. -/
theorem genMergeTreeFullTailBatch_outputPacket_sorted {α : Type}
    [LinearOrder α] {M K N : Nat} (fullTree : PacketMergeTree α M)
    (tailTree : PacketMergeTree α K) (fullBlocks : List (Fin M ↪ Fin N))
    (tail : Fin K ↪ Fin N) (hnd : fullBlocks.Nodup)
    (hdis : ∀ e ∈ fullBlocks, ∀ f ∈ fullBlocks, e ≠ f → ∀ i j, e i ≠ f j)
    (hsep : ∀ e ∈ fullBlocks, ∀ i j, e i ≠ tail j)
    (v : Fin N → α)
    (hfullRuns : ∀ e ∈ fullBlocks, fullTree.RunsSorted (fun i => v (e i)))
    (htailRuns : tailTree.RunsSorted (fun i => v (tail i))) :
    (∀ e ∈ fullBlocks, ∀ j : Fin fullTree.leafCount,
      Monotone (fun i =>
        (genMergeTreeFullTailBatch fullTree tailTree fullBlocks tail).exec v
          (genScatterMergeTreeOutputEmbedding fullTree e j i))) ∧
    (∀ j : Fin tailTree.leafCount,
      Monotone (fun i =>
        (genMergeTreeFullTailBatch fullTree tailTree fullBlocks tail).exec v
          (genScatterMergeTreeOutputEmbedding tailTree tail j i))) := by
  let G := genScatterMergeTreeBatch fullTree fullBlocks
  let H := genScatterMergeTree tailTree tail
  have hexec :
      (genMergeTreeFullTailBatch fullTree tailTree fullBlocks tail).exec v =
        H.exec (G.exec v) := by
    simp [genMergeTreeFullTailBatch, G, H, GenNetwork.exec, List.foldl_append]
  have htailOutside (w : Fin N) (hw : ∀ e ∈ fullBlocks, w ∉ Set.range e) :
      G.exec v w = v w := by
    exact genScatterBatch_exec_outside fullTree.network fullBlocks w hw v
  have htailInput : G.exec v ∘ tail = v ∘ tail := by
    funext i
    exact htailOutside (tail i) (by
      intro e he heRange
      obtain ⟨j, hj⟩ := heRange
      exact (hsep e he j i) hj)
  have htailRunsAfter : tailTree.RunsSorted (fun i => G.exec v (tail i)) := by
    change tailTree.RunsSorted ((G.exec v) ∘ tail)
    rw [htailInput]
    exact htailRuns
  constructor
  · intro e he j
    have hlocal := genScatterMergeTreeBatch_outputPacket_sorted
      fullTree fullBlocks hnd hdis v hfullRuns e he j
    intro i k hik
    rw [hexec]
    change (genScatter tailTree.network tail).exec (G.exec v)
        (e (PacketMergeTree.chunkIndex fullTree j i)) ≤
      (genScatter tailTree.network tail).exec (G.exec v)
        (e (PacketMergeTree.chunkIndex fullTree j k))
    rw [genScatter_exec_outside tailTree.network tail (G.exec v)
      (e (PacketMergeTree.chunkIndex fullTree j i)) (by
        rintro ⟨q, hq⟩
        exact (hsep e he (PacketMergeTree.chunkIndex fullTree j i) q) hq.symm),
      genScatter_exec_outside tailTree.network tail (G.exec v)
      (e (PacketMergeTree.chunkIndex fullTree j k)) (by
        rintro ⟨q, hq⟩
        exact (hsep e he (PacketMergeTree.chunkIndex fullTree j k) q) hq.symm)]
    exact hlocal hik
  · intro j
    intro i k hik
    rw [hexec]
    change (genScatterMergeTree tailTree tail).exec (G.exec v)
        (tail (PacketMergeTree.chunkIndex tailTree j i)) ≤
      (genScatterMergeTree tailTree tail).exec (G.exec v)
        (tail (PacketMergeTree.chunkIndex tailTree j k))
    have hsortedAfter := genScatterMergeTree_outputPacket_sorted
      tailTree tail (G.exec v) htailRunsAfter j
    exact hsortedAfter hik

/-- The full-block and tail output packets form an exact disjoint
repartition of the supports consumed by a full-plus-tail batch. -/
theorem genMergeTreeFullTailBatch_output_support {α : Type}
    [LinearOrder α] {M K N : Nat} (fullTree : PacketMergeTree α M)
    (tailTree : PacketMergeTree α K) (fullBlocks : List (Fin M ↪ Fin N))
    (tail : Fin K ↪ Fin N)
    (hdis : ∀ e ∈ fullBlocks, ∀ f ∈ fullBlocks, e ≠ f →
      ∀ i j, e i ≠ f j)
    (hsep : ∀ e ∈ fullBlocks, ∀ i j, e i ≠ tail j) :
    (∀ e ∈ fullBlocks, ∀ j k : Fin fullTree.leafCount, j ≠ k →
      ∀ x y : Fin 64,
        genScatterMergeTreeOutputEmbedding fullTree e j x ≠
          genScatterMergeTreeOutputEmbedding fullTree e k y) ∧
    (∀ e f, e ∈ fullBlocks → f ∈ fullBlocks → e ≠ f →
      ∀ j k x y,
        genScatterMergeTreeOutputEmbedding fullTree e j x ≠
          genScatterMergeTreeOutputEmbedding fullTree f k y) ∧
    (∀ e ∈ fullBlocks, ∀ j k x y,
      genScatterMergeTreeOutputEmbedding fullTree e j x ≠
        genScatterMergeTreeOutputEmbedding tailTree tail k y) ∧
    (∀ j k : Fin tailTree.leafCount, j ≠ k → ∀ x y : Fin 64,
      genScatterMergeTreeOutputEmbedding tailTree tail j x ≠
        genScatterMergeTreeOutputEmbedding tailTree tail k y) ∧
    (∀ w : Fin N,
      ((∃ e, ∃ he : e ∈ fullBlocks, ∃ j,
          w ∈ Set.range (genScatterMergeTreeOutputEmbedding fullTree e j)) ∨
        ∃ j, w ∈ Set.range (genScatterMergeTreeOutputEmbedding tailTree tail j)) ↔
      ((∃ e, ∃ he : e ∈ fullBlocks, w ∈ Set.range e) ∨
        w ∈ Set.range tail)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e he j k hjk x y
    exact genScatterMergeTreeOutputEmbedding_disjoint fullTree e hjk x y
  · intro e f he hf hef j k x y heq
    have hne := hdis e he f hf hef
      (PacketMergeTree.chunkIndex fullTree j x)
      (PacketMergeTree.chunkIndex fullTree k y)
    exact hne (by simpa [genScatterMergeTreeOutputEmbedding] using heq)
  · intro e he j k x y heq
    exact hsep e he (PacketMergeTree.chunkIndex fullTree j x)
      (PacketMergeTree.chunkIndex tailTree k y)
      (by simpa [genScatterMergeTreeOutputEmbedding] using heq)
  · intro j k hjk x y
    exact genScatterMergeTreeOutputEmbedding_disjoint tailTree tail hjk x y
  · intro w
    constructor
    · rintro (⟨e, he, j, hw⟩ | ⟨j, hw⟩)
      · exact Or.inl ⟨e, he, (genScatterMergeTreeOutputEmbedding_support_iff
          fullTree e w).mp ⟨j, hw⟩⟩
      · exact Or.inr ((genScatterMergeTreeOutputEmbedding_support_iff
          tailTree tail w).mp ⟨j, hw⟩)
    · rintro (⟨e, he, hw⟩ | hw)
      · exact Or.inl ⟨e, he, (genScatterMergeTreeOutputEmbedding_support_iff
          fullTree e w).mpr hw⟩
      · exact Or.inr ((genScatterMergeTreeOutputEmbedding_support_iff
          tailTree tail w).mpr hw)

/-- Split a cohort with `64*q + 63` sorted packets into consecutive full
blocks and its final 63-packet tail, then merge both parts in parallel at
depth at most 57. -/
theorem packetFamily_residue63_merge {q N : Nat} {α : Type} [LinearOrder α]
    (packets : Fin (q * 64 + 63) → Fin 64 ↪ Fin N)
    (hdis : ∀ a b, a ≠ b → ∀ x y, packets a x ≠ packets b y)
    (v : Fin N → α)
    (hpackets : ∀ a, Monotone (fun i => v (packets a i))) :
    ∃ blocks : List (Fin 4096 ↪ Fin N), ∃ tail : Fin 4032 ↪ Fin N,
      blocks.Nodup ∧
      (∀ e ∈ blocks, ∀ f ∈ blocks, e ≠ f → ∀ x y, e x ≠ f y) ∧
      (∀ e ∈ blocks, ∀ i j, e i ≠ tail j) ∧
      (genMergeTreeFullTailBatch (packetPowerTree6 (α := α))
        (packetOddTree6 (α := α)) blocks tail).depth ≤ 57 ∧
      (∀ e ∈ blocks,
        (packetPowerTree6 (α := α)).RunsSorted (fun i => v (e i))) ∧
      (packetOddTree6 (α := α)).RunsSorted (fun i => v (tail i)) ∧
      (∀ e ∈ blocks, ∀ j : Fin (packetPowerTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genMergeTreeFullTailBatch (packetPowerTree6 (α := α))
            (packetOddTree6 (α := α)) blocks tail).exec v
              (genScatterMergeTreeOutputEmbedding (packetPowerTree6 (α := α)) e j i))) ∧
      (∀ j : Fin (packetOddTree6 (α := α)).leafCount,
        Monotone (fun i =>
          (genMergeTreeFullTailBatch (packetPowerTree6 (α := α))
            (packetOddTree6 (α := α)) blocks tail).exec v
              (genScatterMergeTreeOutputEmbedding (packetOddTree6 (α := α)) tail j i))) := by
  let prefixIndex : Fin (q * 64) → Fin (q * 64 + 63) :=
    fun i => ⟨i.val, by have hi := i.isLt; omega⟩
  let tailIndex : Fin 63 → Fin (q * 64 + 63) :=
    fun i => ⟨q * 64 + i.val, by have hi := i.isLt; omega⟩
  let prefixPackets : Fin (q * 64) → Fin 64 ↪ Fin N :=
    fun i => packets (prefixIndex i)
  let tailPackets : Fin 63 → Fin 64 ↪ Fin N := fun i => packets (tailIndex i)
  have hprefixIndexInjective : Function.Injective prefixIndex := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa [prefixIndex] using hv
  have htailIndexInjective : Function.Injective tailIndex := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [tailIndex, Fin.val_mk] at hv
    omega
  have hdisPrefix : ∀ a b, a ≠ b → ∀ x y,
      prefixPackets a x ≠ prefixPackets b y := by
    intro a b hab x y heq
    apply hdis (prefixIndex a) (prefixIndex b)
    · intro h
      apply hab
      exact hprefixIndexInjective h
    · exact heq
  have hdisTail : ∀ {a b : Fin 63}, a ≠ b → ∀ x y,
      tailPackets a x ≠ tailPackets b y := by
    intro a b hab x y heq
    apply hdis (tailIndex a) (tailIndex b)
    · intro h
      apply hab
      exact htailIndexInjective h
    · exact heq
  let blocks := packetFamily64BlockList prefixPackets hdisPrefix
  let tail := genPacketGroup63Embedding tailPackets hdisTail
  have hsep : ∀ e ∈ blocks, ∀ i j, e i ≠ tail j := by
    intro e he i j
    simp only [blocks, packetFamily64BlockList, List.mem_ofFn] at he
    obtain ⟨g, rfl⟩ := he
    obtain ⟨a, x, hx⟩ := genPacketGroup64Embedding_mem_packets
      (fun a => prefixPackets (packetFamily64BlockIndex g a))
      (by
        intro a' b' hab x y
        have hidx : packetFamily64BlockIndex g a' ≠
            packetFamily64BlockIndex g b' := by
          intro h
          apply hab
          exact packetFamily64BlockIndex_injective g h
        exact hdisPrefix _ _ hidx x y) i
    obtain ⟨b, y, hy⟩ := genPacketGroup63Embedding_mem_packets
      tailPackets hdisTail j
    have hidx : prefixIndex (packetFamily64BlockIndex g a) ≠ tailIndex b := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [prefixIndex, tailIndex, packetFamily64BlockIndex, Fin.val_mk] at hv
      omega
    intro heq
    have hval : packets (prefixIndex (packetFamily64BlockIndex g a)) x =
        packets (tailIndex b) y := by
      calc
        packets (prefixIndex (packetFamily64BlockIndex g a)) x =
            packetFamily64BlockEmbedding prefixPackets hdisPrefix g i := hx.symm
        _ = genPacketGroup63Embedding tailPackets hdisTail j := heq
        _ = packets (tailIndex b) y := hy
    exact (hdis _ _ hidx x y) hval
  have hnd := packetFamily64BlockList_nodup prefixPackets hdisPrefix
  have hdisBlocks := packetFamily64BlockList_disjoint prefixPackets hdisPrefix
  have hRunsFull : ∀ e ∈ blocks,
      (packetPowerTree6 (α := α)).RunsSorted (fun i => v (e i)) := by
    intro e he
    simp only [blocks, packetFamily64BlockList, List.mem_ofFn] at he
    obtain ⟨g, rfl⟩ := he
    have hinner : ∀ {a b : Fin 64}, a ≠ b → ∀ x y,
        prefixPackets (packetFamily64BlockIndex g a) x ≠
          prefixPackets (packetFamily64BlockIndex g b) y := by
      intro a b hab x y
      apply hdisPrefix _ _ ?_ x y
      intro h
      apply hab
      exact packetFamily64BlockIndex_injective g h
    have hlocal := packetPowerTree6_runsSorted_of_packets
      (fun a => prefixPackets (packetFamily64BlockIndex g a)) hinner v
      (fun a => hpackets (prefixIndex (packetFamily64BlockIndex g a)))
    simpa [packetFamily64BlockEmbedding] using hlocal
  have hRunsTail := packetOddTree6_runsSorted_of_packets tailPackets hdisTail v
    (fun i => hpackets (tailIndex i))
  have hdepth := genMergeTreeFullTailBatch_depth_le
    (packetPowerTree6 (α := α)) (packetOddTree6 (α := α)) blocks tail
    hnd hdisBlocks hsep 57 packetPowerTree6_depth_le packetOddTree6_depth_le
  have hsorted := genMergeTreeFullTailBatch_outputPacket_sorted
    (packetPowerTree6 (α := α)) (packetOddTree6 (α := α)) blocks tail
    hnd hdisBlocks hsep v hRunsFull hRunsTail
  exact ⟨blocks, tail, hnd, hdisBlocks, hsep, hdepth,
    hRunsFull, hRunsTail, hsorted.1, hsorted.2⟩


end Chvatal.PacketAlignment
