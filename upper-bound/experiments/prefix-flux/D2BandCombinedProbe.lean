import D2ReflectedPhysicalPack
import AKS.Sort.Monotone
import AKS.Misc.Fin

open Chvatal.D2ReflectedPhysicalPack

namespace Chvatal.D2BandCombinedProbe

abbrev Wire := Fin (4096 * 64)
abbrev Col := Fin 64
abbrev N := 4096 * 64
noncomputable def stageNet : ComparatorNetwork N :=
  Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet reflectedSigma35 reflectedSigma25
noncomputable def rankMap : Wire -> Wire := stageNet.exec fun w => w
def highThreshold (k : Nat) (w : Wire) : Bool := decide (k <= w.val)
def thresholdHeight (k : Nat) (c : Col) : Nat := matrixColumnTrueCount c (highThreshold k)

theorem highThreshold_monotone (k : Nat) : Monotone (highThreshold k) := by
  intro x y hxy
  have hval : x.val <= y.val := Fin.le_iff_val_le_val.mp hxy
  by_cases hx : k <= x.val <;> by_cases hy : k <= y.val
  · simp [highThreshold, hx, hy]
  · have hbad : False := by omega
    exact hbad.elim
  · simp [highThreshold, hx, hy]
  · simp [highThreshold, hx, hy]

theorem threshold_output_eq_rankMap (k : Nat) :
    stageNet.exec (highThreshold k) = Function.comp (highThreshold k) rankMap := by
  have h := ComparatorNetwork.exec_comp_monotone stageNet (highThreshold_monotone k)
    (fun w : Wire => w)
  simpa [rankMap, Function.comp] using h.symm

theorem threshold_band_brackets (k : Nat) (hk : k <= N) :
    exists a b, 64 * (b-a) <= 832 /\ a <= b /\ 64*a <= N /\ 64*b <= N /\
      64*a <= k /\ k <=64*b /\
      (forall q : Wire, q.val <64*a -> stageNet.exec (highThreshold k) q=false) /\
      (forall q : Wire, 64*b<=q.val -> stageNet.exec (highThreshold k) q=true) := by
  let v : Wire -> Bool := highThreshold k
  let h : Col -> Nat := thresholdHeight k
  have hcount : forall c, matrixColumnTrueCount c v=h c := by intro c; rfl
  have hbound : forall c, h c <=4096 := by intro c; exact matrixColumnTrueCount_le c v
  obtain ⟨a,b,hwidth,hab,haN,hbN,hfalse,htrue⟩ :=
    reflectedPhysicalPackTwoGrid_common_band v h hcount hbound
  have hinputTrue : (Finset.univ.filter fun q : Wire => highThreshold k q=true).card=N-k := by
    simpa only [highThreshold, decide_eq_true_eq] using card_filter_val_ge N k hk
  have hinputSplit := Finset.card_filter_add_card_filter_not (s:=Finset.univ)
    (fun q : Wire => highThreshold k q=true)
  have hinputFalse : (Finset.univ.filter fun q : Wire => highThreshold k q=false).card=k := by
    have hcard : (Finset.univ.filter fun q : Wire => highThreshold k q=true).card+
        (Finset.univ.filter fun q : Wire => highThreshold k q=false).card=N := by
      simpa using hinputSplit
    rw [hinputTrue] at hcard
    omega
  have hnetworkFalse := Chvatal.D2BandRepair4096Network.comparatorNetwork_falseCount_preserved
    stageNet (highThreshold k)
  have hnetworkSplit := Finset.card_filter_add_card_filter_not (s:=Finset.univ)
    (fun q : Wire => stageNet.exec (highThreshold k) q=true)
  have hnetworkTrue : (Finset.univ.filter fun q : Wire => stageNet.exec (highThreshold k) q=true).card=N-k := by
    have hcard : (Finset.univ.filter fun q : Wire => stageNet.exec (highThreshold k) q=true).card+
        (Finset.univ.filter fun q : Wire => stageNet.exec (highThreshold k) q=false).card=N := by
      simpa using hnetworkSplit
    rw [hnetworkFalse,hinputFalse] at hcard
    omega
  have houtput := threshold_output_eq_rankMap k
  have htotal : (Finset.univ.filter fun q : Wire => highThreshold k (rankMap q)=true).card=N-k := by
    calc
      _ = (Finset.univ.filter fun q : Wire => stageNet.exec (highThreshold k) q=true).card := by
        apply congrArg Finset.card
        ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hp := congrFun houtput q
        exact Iff.of_eq (congrArg (fun b : Bool => b=true) hp.symm)
      _ = N-k := hnetworkTrue
  have hupper : (Finset.univ.filter fun q : Wire => highThreshold k (rankMap q)=true).card <= N-64*a := by
    calc
      _ <= (Finset.univ.filter fun q : Wire => 64*a<=q.val).card := by
        apply Finset.card_le_card
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        by_contra hqa
        have hout := hfalse q (by omega)
        change stageNet.exec (highThreshold k) q=false at hout
        have hp := congrFun houtput q
        have hp' : stageNet.exec (highThreshold k) q = highThreshold k (rankMap q) := by
          simpa only [Function.comp_apply] using hp
        rw [hp'] at hout
        simp [hq] at hout
      _ = N-64*a := card_filter_val_ge N (64*a) haN
  have hlower : N-64*b <= (Finset.univ.filter fun q : Wire => highThreshold k (rankMap q)=true).card := by
    calc
      N-64*b = (Finset.univ.filter fun q : Wire => 64*b<=q.val).card :=
        (card_filter_val_ge N (64*b) hbN).symm
      _ <= _ := by
        apply Finset.card_le_card
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        have hout := htrue q hq
        change stageNet.exec (highThreshold k) q=true at hout
        have hp := congrFun houtput q
        have hp' : stageNet.exec (highThreshold k) q = highThreshold k (rankMap q) := by
          simpa only [Function.comp_apply] using hp
        rw [hp'] at hout
        exact hout
  refine ⟨a,b,hwidth,hab,haN,hbN,?_,?_,hfalse,htrue⟩
  · rw [htotal] at hupper
    have hsum : N <= (N - 64 * a) + k := (Nat.sub_le_iff_le_add).mp hupper
    have hcancel : (N - 64 * a) + 64 * a = N := Nat.sub_add_cancel haN
    omega
  · rw [htotal] at hlower
    have hsum : N <= (N - k) + 64 * b := (Nat.sub_le_iff_le_add).mp hlower
    have hcancel : (N - k) + k = N := Nat.sub_add_cancel hk
    omega

end Chvatal.D2BandCombinedProbe
