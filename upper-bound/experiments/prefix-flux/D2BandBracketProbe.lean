import D2ReflectedPhysicalPack
import AKS.Sort.Monotone
import AKS.Misc.Fin

open Chvatal.D2ReflectedPhysicalPack

namespace Chvatal.D2BandBracketProbe

abbrev Wire := Fin (4096 * 64)
abbrev Col := Fin 64
abbrev N := 4096 * 64
noncomputable def stageNet : ComparatorNetwork N :=
  Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet reflectedSigma35 reflectedSigma25
noncomputable def rankMap : Wire -> Wire := stageNet.exec fun w => w
def highThreshold (k : Nat) (w : Wire) : Bool := decide (k <= w.val)
def thresholdHeight (k : Nat) (c : Col) : Nat :=
  matrixColumnTrueCount c (highThreshold k)

theorem threshold_band_brackets (k : Nat) (hk : k <= N) :
    exists a b, 64 * (b - a) <= 832 /\ a <= b /\
      64 * a <= N /\ 64 * b <= N /\ 64 * a <= k /\ k <= 64 * b /\
      (forall q : Wire, q.val < 64 * a -> stageNet.exec (highThreshold k) q = false) /\
      (forall q : Wire, 64 * b <= q.val -> stageNet.exec (highThreshold k) q = true) := by
  let v : Wire -> Bool := highThreshold k
  let h : Col -> Nat := thresholdHeight k
  have hcount : forall c, matrixColumnTrueCount c v = h c := by
    intro c
    rfl
  have hbound : forall c, h c <= 4096 := by
    intro c
    exact matrixColumnTrueCount_le c v
  obtain ⟨a, b, hwidth, hab, haN, hbN, hfalse, htrue⟩ :=
    reflectedPhysicalPackTwoGrid_common_band v h hcount hbound
  exact ⟨a, b, hwidth, hab, haN, hbN, by omega, by omega, hfalse, htrue⟩

end Chvatal.D2BandBracketProbe
