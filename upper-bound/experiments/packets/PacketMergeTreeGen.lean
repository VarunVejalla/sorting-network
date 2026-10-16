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

private theorem packetTreeCellIndex_mono (j : Fin 63) :
    Monotone (packetTreeCellIndex j) := by
  intro i k hik
  apply Fin.mk_le_mk.mpr
  have hik' := Fin.mk_le_mk.mp hik
  exact Nat.add_le_add_left hik' (j.val * 64)

def genScatterMergeTreeOutputEmbedding {α : Type} [LinearOrder α] {N : Nat}
    (tree : PacketMergeTree α 4032) (e : Fin 4032 ↪ Fin N)
    (j : Fin 63) : Fin 64 ↪ Fin N :=
  ⟨fun i => e (packetTreeCellIndex j i), by
    intro i k hik
    apply Fin.ext
    have h := congrArg Fin.val (e.injective hik)
    simp only [packetTreeCellIndex] at h
    omega⟩

theorem genScatterMergeTreeOutputEmbedding_disjoint {α : Type} [LinearOrder α]
    {N : Nat} (tree : PacketMergeTree α 4032) (e : Fin 4032 ↪ Fin N)
    {j k : Fin 63} (hjk : j ≠ k) (i q : Fin 64) :
    genScatterMergeTreeOutputEmbedding tree e j i ≠
      genScatterMergeTreeOutputEmbedding tree e k q := by
  intro h
  have hidx := e.injective h
  have hv := congrArg Fin.val hidx
  simp only [packetTreeCellIndex] at hv
  apply hjk
  apply Fin.ext
  omega

theorem genScatterMergeTreeOutputEmbedding_covers {α : Type} [LinearOrder α]
    {N : Nat} (tree : PacketMergeTree α 4032) (e : Fin 4032 ↪ Fin N)
    (i : Fin 4032) :
    ∃ (j : Fin 63) (q : Fin 64),
      genScatterMergeTreeOutputEmbedding tree e j q = e i := by
  let j : Fin 63 := ⟨i.val / 64, by
    have hi := i.isLt
    have hd := Nat.div_mul_le_self i.val 64
    omega⟩
  let q : Fin 64 := ⟨i.val % 64, Nat.mod_lt _ (by omega)⟩
  have hidx : packetTreeCellIndex j q = i := by
    apply Fin.ext
    change j.val * 64 + q.val = i.val
    dsimp [j, q]
    omega
  exact ⟨j, q, by simp [genScatterMergeTreeOutputEmbedding, hidx]⟩

theorem genScatterMergeTree_outputPacket_sorted {N : Nat} {α : Type}
    [LinearOrder α] (tree : PacketMergeTree α 4032)
    (e : Fin 4032 ↪ Fin N)
    (v : Fin N → α)
    (hRuns : tree.RunsSorted (fun i => v (e i)))
    (j : Fin 63) :
    Monotone (fun i =>
      (genScatterMergeTree tree e).exec v
        (genScatterMergeTreeOutputEmbedding tree e j i)) := by
  have hsorted := genScatterMergeTree_sorts tree e v hRuns
  have hmono := hsorted.comp (packetTreeCellIndex_mono j)
  simpa only [genScatterMergeTreeOutputEmbedding] using hmono

end Chvatal.PacketAlignment
