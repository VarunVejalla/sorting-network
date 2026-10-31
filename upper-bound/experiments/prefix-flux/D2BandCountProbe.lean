import D2ReflectedPhysicalPack
import AKS.Sort.Monotone
import AKS.Misc.Fin

open Chvatal.D2ReflectedPhysicalPack

namespace Chvatal.D2BandCountProbe

abbrev Wire := Fin (4096 * 64)
abbrev Col := Fin 64
abbrev N := 4096 * 64
noncomputable def stageNet : ComparatorNetwork N :=
  Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet reflectedSigma35 reflectedSigma25
noncomputable def rankMap : Wire -> Wire := stageNet.exec fun w => w
def highThreshold (k : Nat) (w : Wire) : Bool := decide (k <= w.val)
def thresholdHeight (k : Nat) (c : Col) : Nat :=
  matrixColumnTrueCount c (highThreshold k)

theorem threshold_total (k : Nat) (hk : k <= N) :
    (Finset.univ.filter fun q : Wire => highThreshold k (rankMap q) = true).card = N-k := by
  have hinputTrue :
      (Finset.univ.filter fun q : Wire => highThreshold k q = true).card = N-k := by
    simpa only [highThreshold, decide_eq_true_eq] using card_filter_val_ge N k hk
  have hinputSplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun q : Wire => highThreshold k q = true)
  have hinputFalse :
      (Finset.univ.filter fun q : Wire => highThreshold k q = false).card = k := by
    have hcard :
        (Finset.univ.filter fun q : Wire => highThreshold k q = true).card +
          (Finset.univ.filter fun q : Wire => highThreshold k q = false).card = N := by
      simpa using hinputSplit
    rw [hinputTrue] at hcard
    omega
  have hnetworkFalse :=
    Chvatal.D2BandRepair4096Network.comparatorNetwork_falseCount_preserved
      stageNet (highThreshold k)
  have hnetworkSplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun q : Wire => stageNet.exec (highThreshold k) q = true)
  have hnetworkTrue :
      (Finset.univ.filter fun q : Wire => stageNet.exec (highThreshold k) q = true).card =
        N-k := by
    have hcard :
        (Finset.univ.filter fun q : Wire => stageNet.exec (highThreshold k) q = true).card +
          (Finset.univ.filter fun q : Wire => stageNet.exec (highThreshold k) q = false).card = N := by
      simpa using hnetworkSplit
    rw [hnetworkFalse, hinputFalse] at hcard
    omega
  have houtput := ComparatorNetwork.exec_comp_monotone stageNet
    (f := highThreshold k)
    (by
      intro x y hxy
      have hval := Fin.le_iff_val_le_val.mp hxy
      by_cases hx : k <= x.val <;> by_cases hy : k <= y.val
      · simp [highThreshold, hx, hy]
      · have : False := by omega
        exact this.elim
      · simp [highThreshold, hx, hy]
      · simp [highThreshold, hx, hy])
    (fun w : Wire => w)
  have hcomm : stageNet.exec (highThreshold k) = Function.comp (highThreshold k) rankMap := by
    simpa [rankMap, Function.comp] using houtput.symm
  calc
    _ = (Finset.univ.filter fun q : Wire => stageNet.exec (highThreshold k) q = true).card := by
      apply congrArg Finset.card
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hp := congrFun hcomm q
      exact Iff.of_eq (congrArg (fun b : Bool => b = true) hp.symm)
    _ = N-k := hnetworkTrue

end Chvatal.D2BandCountProbe
