import D2ReflectedPhysicalPack
import D2CrossingToDisplacement
import AKS.Sort.Monotone
import AKS.Misc.Fin

open Chvatal.D2ReflectedPhysicalPack

set_option maxRecDepth 4096

namespace Chvatal.D2ReflectedStageDisplacement

abbrev Wire := Fin (4096 * 64)
abbrev N := 4096 * 64

noncomputable def stageNet : ComparatorNetwork N :=
  Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
    reflectedSigma35 reflectedSigma25

noncomputable def rankMap : Wire -> Wire := stageNet.exec fun w => w

def highThreshold (k : Nat) (w : Wire) : Bool := decide (k <= w.val)

def thresholdHeight (k : Nat) (c : Col) : Nat :=
  matrixColumnTrueCount c (highThreshold k)

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
  have houtput := threshold_output_eq_rankMap k
  have htotal :
      (Finset.univ.filter fun q : Wire => highThreshold k (rankMap q) = true).card = N - k := by
    have hinputTrue :
        (Finset.univ.filter fun q : Wire => highThreshold k q = true).card = N - k := by
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
          N - k := by
      have hcard :
          (Finset.univ.filter fun q : Wire => stageNet.exec (highThreshold k) q = true).card +
            (Finset.univ.filter fun q : Wire => stageNet.exec (highThreshold k) q = false).card =
              N := by
        simpa using hnetworkSplit
      rw [hnetworkFalse, hinputFalse] at hcard
      omega
    calc
      _ = (Finset.univ.filter fun q : Wire => stageNet.exec v q = true).card := by
        apply congrArg Finset.card
        ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hp := congrFun houtput q
        exact Iff.of_eq (congrArg (fun b : Bool => b = true) hp.symm)
      _ = N - k := hnetworkTrue
  have hupper :
      (Finset.univ.filter fun q : Wire => highThreshold k (rankMap q) = true).card <=
        N - 64 * a := by
    calc
      _ <= (Finset.univ.filter fun q : Wire => 64 * a <= q.val).card := by
        apply Finset.card_le_card
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        by_contra hqa
        have hout := hfalse q (by omega)
        change stageNet.exec (highThreshold k) q = false at hout
        have hp := congrFun houtput q
        have hp' : stageNet.exec (highThreshold k) q = highThreshold k (rankMap q) := by
          simpa only [Function.comp_apply] using hp
        rw [hp'] at hout
        simp [hq] at hout
      _ = N - 64 * a := card_filter_val_ge N (64 * a) haN
  have hlower : N - 64 * b <=
      (Finset.univ.filter fun q : Wire => highThreshold k (rankMap q) = true).card := by
    calc
      N - 64 * b = (Finset.univ.filter fun q : Wire => 64 * b <= q.val).card :=
        (card_filter_val_ge N (64 * b) hbN).symm
      _ <= _ := by
        apply Finset.card_le_card
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        have hout := htrue q hq
        have hp := congrFun houtput q
        change stageNet.exec (highThreshold k) q = true at hout
        have hp' : stageNet.exec (highThreshold k) q = highThreshold k (rankMap q) := by
          simpa only [Function.comp_apply] using hp
        rw [hp'] at hout
        exact hout
  refine ⟨a, b, hwidth, hab, haN, hbN, ?_, ?_, hfalse, htrue⟩
  · rw [htotal] at hupper
    omega
  · rw [htotal] at hlower
    omega

theorem rankMap_displacement_le_832 (q : Wire) :
    (rankMap q).val <= q.val + 832 /\ q.val <= (rankMap q).val + 832 := by
  constructor
  · by_contra hbad
    have hlt : q.val + 832 < (rankMap q).val := by omega
    let k := q.val + 832 + 1
    have hk : k <= N := by
      have hr := (rankMap q).isLt
      dsimp [k]
      omega
    obtain ⟨a, b, hwidth, hab, haN, hbN, haK, hkB, hfalse, htrue⟩ :=
      threshold_band_brackets k hk
    have hgap : 64 * b - 64 * a <= 832 := by omega
    have hboundA : k <= 64 * a + 832 := by omega
    have hqA : q.val < 64 * a := by dsimp [k] at hboundA; omega
    have hout := hfalse q hqA
    change stageNet.exec (highThreshold k) q = false at hout
    have hp := congrFun (threshold_output_eq_rankMap k) q
    have hp' : stageNet.exec (highThreshold k) q = highThreshold k (rankMap q) := by
      simpa only [Function.comp_apply] using hp
    rw [hp'] at hout
    have hkR : k <= (rankMap q).val := by dsimp [k]; omega
    simp [highThreshold, hkR] at hout
  · by_contra hbad
    have hlt : (rankMap q).val + 832 < q.val := by omega
    let k := (rankMap q).val + 1
    have hk : k <= N := by dsimp [k]; omega
    obtain ⟨a, b, hwidth, hab, haN, hbN, haK, hkB, hfalse, htrue⟩ :=
      threshold_band_brackets k hk
    have hgap : 64 * b - 64 * a <= 832 := by omega
    have hboundB : 64 * b <= k + 832 := by omega
    have hqB : 64 * b <= q.val := by dsimp [k] at hboundB; omega
    have hout := htrue q hqB
    change stageNet.exec (highThreshold k) q = true at hout
    have hp := congrFun (threshold_output_eq_rankMap k) q
    have hp' : stageNet.exec (highThreshold k) q = highThreshold k (rankMap q) := by
      simpa only [Function.comp_apply] using hp
    rw [hp'] at hout
    have hnotk : ¬ k <= (rankMap q).val := by dsimp [k]; omega
    simp [highThreshold, hnotk] at hout

end Chvatal.D2ReflectedStageDisplacement
