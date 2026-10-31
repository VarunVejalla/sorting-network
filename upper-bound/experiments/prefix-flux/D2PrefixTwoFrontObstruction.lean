import D2FlowRankBridge
import D2StaticWireSets

open Chvatal.D2RankAlignment
open Chvatal.D2Reserve
open Chvatal.D2StaticWireSets

namespace Chvatal.D2PrefixTwoFrontObstruction

open Chvatal.D2Reserve

private def uniformSizes : Fin 8 -> Nat := fun _ => 10
private def uniformChildren : Fin 8 -> D2FlowTree 0 :=
  fun _ => .leaf 10 0 0

/-- This is an actual ordinary `mid` flow step with valid endpoint cuts.
Its first and last child deficits are the two-front values 5 and 4. -/
theorem uniform_sender_stage_end_deficits :
    d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (fun _ => true) (fun _ => .mid)
            (fun _ _ => 4) 1 0 (.node 5 3 2 uniformChildren))
          (Fin.mk 0 (by omega))) = 5 /\
    d2FlowTreeRootDeficit
        (d2FlowTreeChild
          (d2FlowStage (fun _ => true) (fun _ => .mid)
            (fun _ _ => 4) 1 0 (.node 5 3 2 uniformChildren))
          (Fin.mk 7 (by omega))) = 4 := by
  have hr : (fun _ : Nat => D2Role.mid) 0 = .topRise \/
      (fun _ : Nat => D2Role.mid) 0 = .mid \/
      (fun _ : Nat => D2Role.mid) 0 = .botDesc := Or.inr (Or.inl rfl)
  have hsizes : (fun j : Fin 8 =>
      d2FlowTreeRootDeficit (uniformChildren j)) = uniformSizes := by
    funext j
    simp [uniformChildren, uniformSizes, d2FlowTreeRootDeficit]
  have hp0 : d2FlowPosition uniformSizes (Fin.mk 0 (by omega)) = 0 := by
    simpa [uniformSizes] using
      d2FlowPosition_uniform 10 (Fin.mk 0 (by omega))
  have hp7 : d2FlowPosition uniformSizes (Fin.mk 7 (by omega)) = 70 := by
    simpa [uniformSizes] using
      d2FlowPosition_uniform 10 (Fin.mk 7 (by omega))
  have htotal : d2FlowTotal uniformSizes = 80 := by
    norm_num [d2FlowTotal, uniformSizes]
  have hfirst := d2FlowStage_regular_child_deficit (h := 0) (i := 0)
    (G := 5) (low := 3) (high := 2)
    (active := fun _ : Nat => true) (role := fun _ : Nat => .mid)
    (quota := fun _ _ => 4) uniformChildren (by decide) hr
    (Fin.mk 0 (by omega))
  have hlast := d2FlowStage_regular_child_deficit (h := 0) (i := 0)
    (G := 5) (low := 3) (high := 2)
    (active := fun _ : Nat => true) (role := fun _ : Nat => .mid)
    (quota := fun _ _ => 4) uniformChildren (by decide) hr
    (Fin.mk 7 (by omega))
  have hfirstVal : d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage (fun _ => true) (fun _ => .mid)
          (fun _ _ => 4) 1 0 (.node 5 3 2 uniformChildren))
        (Fin.mk 0 (by omega))) = 5 := by
    rw [hfirst, hsizes, hp0]
    norm_num [d2FlowCutChild, d2LeftCut, d2RightCut, htotal,
      uniformChildren, uniformSizes, d2FlowTreeRootDeficit]
  have hlastVal : d2FlowTreeRootDeficit
      (d2FlowTreeChild
        (d2FlowStage (fun _ => true) (fun _ => .mid)
          (fun _ _ => 4) 1 0 (.node 5 3 2 uniformChildren))
        (Fin.mk 7 (by omega))) = 4 := by
    rw [hlast, hsizes, hp7]
    norm_num [d2FlowCutChild, d2LeftCut, d2RightCut, htotal,
      uniformChildren, uniformSizes, d2FlowTreeRootDeficit]
  exact And.intro hfirstVal hlastVal

/-- For a balanced ordinary sender, its first and last child deficits are
two-front masses. A single exact-rank prefix of the same total mass instead
places all mass in the first child. -/
theorem first_and_last_child_mass_mismatch :
    d2FlowTwoFrontMass uniformSizes 5 76 (Fin.mk 0 (by omega)) = 5 /\
    d2FlowTwoFrontMass uniformSizes 5 76 (Fin.mk 7 (by omega)) = 4 /\
    prefixIntervalMass 5
      (d2FlowRankBoundary uniformSizes 0)
      (d2FlowRankBoundary uniformSizes 1) = 5 /\
    prefixIntervalMass 5
      (d2FlowRankBoundary uniformSizes 7)
      (d2FlowRankBoundary uniformSizes 8) = 0 /\
    prefixIntervalMass 9
      (d2FlowRankBoundary uniformSizes 0)
      (d2FlowRankBoundary uniformSizes 1) = 9 /\
    prefixIntervalMass 9
      (d2FlowRankBoundary uniformSizes 7)
      (d2FlowRankBoundary uniformSizes 8) = 0 := by
  have hb (i : Nat) (hi : i <= 8) :
      d2FlowRankBoundary uniformSizes i = i * 10 := by
    simpa [uniformSizes] using
      d2FlowRankBoundary_const 10 i hi
  change
    (prefixIntervalMass 5 (d2FlowRankBoundary uniformSizes 0)
        (d2FlowRankBoundary uniformSizes 1) +
      suffixIntervalMass 76 (d2FlowRankBoundary uniformSizes 0)
        (d2FlowRankBoundary uniformSizes 1) = 5) /\
    (prefixIntervalMass 5 (d2FlowRankBoundary uniformSizes 7)
        (d2FlowRankBoundary uniformSizes 8) +
      suffixIntervalMass 76 (d2FlowRankBoundary uniformSizes 7)
        (d2FlowRankBoundary uniformSizes 8) = 4) /\
    prefixIntervalMass 5 (d2FlowRankBoundary uniformSizes 0)
      (d2FlowRankBoundary uniformSizes 1) = 5 /\
    prefixIntervalMass 5 (d2FlowRankBoundary uniformSizes 7)
      (d2FlowRankBoundary uniformSizes 8) = 0 /\
    prefixIntervalMass 9 (d2FlowRankBoundary uniformSizes 0)
      (d2FlowRankBoundary uniformSizes 1) = 9 /\
    prefixIntervalMass 9 (d2FlowRankBoundary uniformSizes 7)
      (d2FlowRankBoundary uniformSizes 8) = 0
  rw [hb 0 (by omega), hb 1 (by omega), hb 7 (by omega),
    hb 8 (by omega)]
  norm_num [prefixIntervalMass, suffixIntervalMass]

end Chvatal.D2PrefixTwoFrontObstruction
