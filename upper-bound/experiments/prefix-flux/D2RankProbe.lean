import D2ReflectedPhysicalPack
import AKS.Sort.Monotone

open Chvatal.D2ReflectedPhysicalPack

namespace Chvatal.D2RankProbe

abbrev Wire := Fin (4096 * 64)
noncomputable def stageNet : ComparatorNetwork (4096 * 64) :=
  Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet reflectedSigma35 reflectedSigma25
noncomputable def rankMap : Wire -> Wire := stageNet.exec fun w => w
def highThreshold (k : Nat) (w : Wire) : Bool := decide (k <= w.val)

theorem highThreshold_monotone (k : Nat) : Monotone (highThreshold k) := by
  intro x y hxy
  have hval : x.val <= y.val := Fin.le_iff_val_le_val.mp hxy
  by_cases hx : k <= x.val <;> by_cases hy : k <= y.val
  · simp [highThreshold, hx, hy]
  · have hfalse : False := by omega
    exact hfalse.elim
  · simp [highThreshold, hx, hy]
  · simp [highThreshold, hx, hy]

theorem threshold_output_eq_rankMap (k : Nat) :
    stageNet.exec (highThreshold k) = Function.comp (highThreshold k) rankMap := by
  have h := ComparatorNetwork.exec_comp_monotone stageNet
    (highThreshold_monotone k) (fun w : Wire => w)
  simpa [rankMap, Function.comp] using h.symm

end Chvatal.D2RankProbe
