import D2VariableTilePhysicalFlowTransfer

namespace Chvatal.D2AlignedPortReceiverCells

open Chvatal
open Chvatal.D2OrdinaryRankRouting
open Chvatal.D2StaticWireSets
open Chvatal.D2VariableTilePhysicalFlowTransfer

theorem blockOf_rank_interval_subset {n : Nat} (s : Finset (Fin n))
    {lo hi lo' hi' : Nat} (hlo : lo' <= lo) (hhi : hi <= hi') :
    Chvatal.blockOf s lo hi ⊆ Chvatal.blockOf s lo' hi' := by
  intro w hw
  have hw' := Chvatal.mem_blockOf.mp hw
  exact Chvatal.mem_blockOf.mpr
    ⟨hw'.1, le_trans hlo hw'.2.1, lt_of_lt_of_le hw'.2.2 hhi⟩

/-- If the sender's static gaps and an ordinary child's rank port are
4096-aligned, every 4096-rank fragment in that port is one physical cell
entirely assigned to that child by the ordinary routing. This is the exact
cell-level receiver-label fact needed to instantiate a uniform port tag. -/
theorem ordinary_child_rank_port_cells_are_receiver
    {n cursor stop left rightStart start finish q : Nat}
    (holes : List (Nat × Nat)) (boundary : Nat → Nat) (child : Fin 8)
    (hfit : StaticHolesFit cursor holes stop)
    (hn : 4096 ∣ n) (hcursor : 4096 ∣ cursor) (hstop : 4096 ∣ stop)
    (hstopBound : stop ≤ n)
    (hholes : ∀ hole, hole ∈ holes → 4096 ∣ hole.1 ∧ 4096 ∣ hole.2)
    (hstart : 4096 ∣ start) (hfinish : 4096 ∣ finish)
    (hlen : finish = start + q * 4096)
    (hbound : finish ≤
      (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes).card)
    (hportStart : start = left + boundary child.val)
    (hportFinish : finish = left + boundary (child.val + 1)) :
    ∀ k : Fin q, ∃ cellLo, 4096 ∣ cellLo ∧ cellLo + 4096 ≤ n ∧
      Chvatal.blockOf
        (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes)
        (start + k.val * 4096) (start + (k.val + 1) * 4096) =
          staticWireInterval cellLo (cellLo + 4096) ∧
      staticWireInterval cellLo (cellLo + 4096) ⊆
        destinationPiece (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes)
          boundary left rightStart (some child) := by
  intro k
  have hcells := staticGapRankPort_cells holes q hn hfit hcursor hstop
    hstopBound hholes hstart hfinish hlen hbound
  obtain ⟨cellLo, hcellGrid, hcellBound, hfragment⟩ := hcells k
  have hkq : k.val + 1 ≤ q := Nat.succ_le_of_lt k.isLt
  have hlow : left + boundary child.val ≤ start + k.val * 4096 := by
    rw [hportStart]
    exact Nat.le_add_right _ _
  have hhigh : start + (k.val + 1) * 4096 ≤
      left + boundary (child.val + 1) := by
    rw [← hportFinish, hlen]
    have := Nat.mul_le_mul_right 4096 hkq
    omega
  refine ⟨cellLo, hcellGrid, hcellBound, hfragment, ?_⟩
  calc
    staticWireInterval cellLo (cellLo + 4096) =
        Chvatal.blockOf
          (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes)
          (start + k.val * 4096) (start + (k.val + 1) * 4096) := hfragment.symm
    _ ⊆ Chvatal.blockOf
        (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes)
        (left + boundary child.val) (left + boundary (child.val + 1)) :=
      blockOf_rank_interval_subset _ hlow hhigh
    _ = destinationPiece
        (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes)
        boundary left rightStart (some child) := by
      rfl

/-- The cell count need not be supplied separately: aligned port endpoints
and their order determine an integer number of 4096-rank cells. -/
theorem ordinary_child_rank_port_cells_are_receiver_of_aligned_endpoints
    {n cursor stop left rightStart start finish : Nat}
    (holes : List (Nat × Nat)) (boundary : Nat → Nat) (child : Fin 8)
    (hfit : StaticHolesFit cursor holes stop)
    (hn : 4096 ∣ n) (hcursor : 4096 ∣ cursor) (hstop : 4096 ∣ stop)
    (hstopBound : stop ≤ n)
    (hholes : ∀ hole, hole ∈ holes → 4096 ∣ hole.1 ∧ 4096 ∣ hole.2)
    (hstart : 4096 ∣ start) (hfinish : 4096 ∣ finish)
    (horder : start ≤ finish)
    (hbound : finish ≤
      (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes).card)
    (hportStart : start = left + boundary child.val)
    (hportFinish : finish = left + boundary (child.val + 1)) :
    ∃ q : Nat, ∀ k : Fin q, ∃ cellLo, 4096 ∣ cellLo ∧
      cellLo + 4096 ≤ n ∧
      Chvatal.blockOf
        (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes)
        (start + k.val * 4096) (start + (k.val + 1) * 4096) =
          staticWireInterval cellLo (cellLo + 4096) ∧
      staticWireInterval cellLo (cellLo + 4096) ⊆
        destinationPiece (staticWireInterval (n := n) cursor stop \ staticHoleUnion holes)
          boundary left rightStart (some child) := by
  rcases hfinish with ⟨f, rfl⟩
  rcases hstart with ⟨s, rfl⟩
  have hsf : s ≤ f := by omega
  refine ⟨f - s, ?_⟩
  have hlen : 4096 * f = 4096 * s + (f - s) * 4096 := by
    rw [Nat.mul_comm (f - s) 4096]
    rw [Nat.mul_sub_left_distrib]
    omega
  exact ordinary_child_rank_port_cells_are_receiver
    (rightStart := rightStart) holes boundary child hfit hn hcursor hstop hstopBound hholes
    (show 4096 ∣ 4096 * s from ⟨s, rfl⟩)
    (show 4096 ∣ 4096 * f from ⟨f, rfl⟩)
    (by simpa using hlen) hbound hportStart hportFinish

end Chvatal.D2AlignedPortReceiverCells
