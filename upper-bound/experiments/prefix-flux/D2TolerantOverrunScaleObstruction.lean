import D2CandidateTwoFrontBridge
import D2StaticWireSets

open scoped BigOperators

namespace Chvatal.D2TolerantOverrunScaleObstruction

open Chvatal.D2RankAlignment
open Chvatal.D2Reserve
open Chvatal.D2StaticWireSets

private def children : Fin 8 -> D2FlowTree 0 :=
  fun _ => .leaf 131072 0 0

private def sizes : Fin 8 -> Nat := fun _ => 131072

private def active : Nat -> Bool := fun _ => true
private def role : Nat -> D2Role := fun _ => .mid
private def quota : Nat -> D2Role -> Nat := fun _ _ => 3840
private def capacity : Nat -> Nat := fun _ => 1048576

private def root : D2FlowTree 1 := .node 5888 0 5888 children

/-- The tolerant recursive stage-input predicate permits a sender of capacity
four physical core tiles with deficit 5888 and quota 3840. -/
theorem tolerant_inputs_allow_four_tile_witness :
    d2FlowStageInvInputsTolerant 8192 active role quota capacity 0 root := by
  norm_num [d2FlowStageInvInputsTolerant, active, role, quota, capacity,
    root, children, d2FlowTreeRootDeficit, d2FlowTotal]

private def firstChild : Fin 8 := ⟨0, by omega⟩

/-- In this legal local flow state, the ideal prefix of mass `G` exceeds the
first child's two-front reserve by 3968. The sender has four physical core
tiles, so this is 992 per core tile, while only 64 per tile remains after
charging the fixed core's 448 error. This refutes the tolerant local gate as a
proof of the desired 512-per-tile doubling step; it is not a reachable-run
counterexample. -/
theorem tolerant_witness_first_child_overrun :
    prefixIntervalMass 5888
        (d2FlowRankBoundary sizes firstChild.val)
        (d2FlowRankBoundary sizes (firstChild.val + 1)) -
      d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage active role quota 1 0 root) firstChild) = 3968 := by
  have hchild := d2FlowStage_regular_child_deficit_eq_rank_mass
    (active := active) (role := role) (quota := quota)
    (h := 0) (i := 0) (G := 5888) (low := 0) (high := 5888)
    children (by decide) (by simp [role]) firstChild
  have hchild' :
      d2FlowTreeRootDeficit
        (d2FlowTreeChild (d2FlowStage active role quota 1 0 root) firstChild) =
      d2FlowTwoFrontMass sizes 1920 1040768 firstChild := by
    simpa [root, children, sizes, role, quota, d2FlowTotal,
      d2FlowTreeRootDeficit] using hchild
  have hzero : d2FlowRankBoundary sizes 0 = 0 := by
    exact d2FlowRankBoundary_zero sizes
  have hone : d2FlowRankBoundary sizes 1 = 131072 := by
    simpa [sizes] using
      d2FlowRankBoundary_const 131072 1 (by omega)
  rw [hchild', d2FlowTwoFrontMass]
  simp only [firstChild, hzero, hone]
  norm_num [prefixIntervalMass, suffixIntervalMass]

/-- The local allowance plus the fixed-core transfer exceeds the doubled
512-per-core-tile budget in this state. -/
theorem tolerant_local_budget_fails_at_core_tile_scale :
    3968 + 448 * 4 > 512 * (2 * 4) := by
  norm_num

end Chvatal.D2TolerantOverrunScaleObstruction
