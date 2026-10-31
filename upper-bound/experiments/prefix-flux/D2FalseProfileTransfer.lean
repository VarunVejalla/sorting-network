import D2ReflectedPhysicalPack
import D2Range13PortError
import D2LiftedShuffleBridge

open scoped BigOperators

namespace Chvatal.D2FalseProfileTransfer

open Chvatal.D2BandRepair4096Network
open Chvatal.D2ColumnRebatchBridge
open Chvatal.D2LiftedShuffleBridge
open Chvatal.D2ReflectedPhysicalPack
open Chvatal.D2RankAlignment
open Chvatal.D2Range13PortError

abbrev Col := Fin 64
abbrev Row := Fin 4096
abbrev Wire := Fin (4096 * 64)

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The reflected physical core's false-count profile has the same range-13
port bound as its true-count profile. False wires occupy the top prefix of
each sorted column, matching the prefix orientation used by rank-port flow. -/
theorem reflected_core_false_exact_rank_port_error_le_448
    (v : Wire -> Bool) (h : Col -> Nat)
    (hcount : forall c, Chvatal.matrixColumnTrueCount c v = h c)
    (hbound : forall c, h c <= 4096)
    (H ports : Nat) (cuts : Col -> Nat -> Nat)
    (hH : H = Finset.univ.sum fun c : Col =>
      matrixColumnFalseCount c
        ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
          Chvatal.D2ReflectedPhysicalPack.reflectedSigma35
          Chvatal.D2ReflectedPhysicalPack.reflectedSigma25).exec v))
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = 4096)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1)) :
    (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
      abs ((prefixIntervalMass
          (matrixColumnFalseCount cell.1
            ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
              Chvatal.D2ReflectedPhysicalPack.reflectedSigma35
              Chvatal.D2ReflectedPhysicalPack.reflectedSigma25).exec v))
          (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat) -
        (prefixIntervalMass (exactRankColumnHeight H cell.1)
          (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat))) <= 448 := by
  let net := Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
    Chvatal.D2ReflectedPhysicalPack.reflectedSigma35
    Chvatal.D2ReflectedPhysicalPack.reflectedSigma25
  let out := net.exec v
  let actual : Col -> Nat := fun c => matrixColumnFalseCount c out
  obtain ⟨a, b, hwidth, hab, ha, hb, hbelow, habove⟩ :=
    reflectedPhysicalPackTwoGrid_common_band v h hcount hbound
  have hba : b - a <= 13 := by omega
  have hactual (c : Col) : actual c <= 4096 := by
    dsimp [actual]
    unfold matrixColumnFalseCount
    calc
      _ <= (Finset.univ : Finset Row).card := Finset.card_filter_le _ _
      _ = 4096 := by simp
  have htrueUpper (c : Col) : Chvatal.matrixColumnTrueCount c out <= 4096 - a := by
    change (Finset.univ.filter fun r : Row =>
      out (Chvatal.matrixWire 4096 64 r c) = true).card <= 4096 - a
    have hsubset : (Finset.univ.filter fun r : Row =>
        out (Chvatal.matrixWire 4096 64 r c) = true) ⊆
      Finset.univ.filter fun r : Row => a <= r.val := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra hnot
      have hfalse := hbelow (Chvatal.matrixWire 4096 64 r c) (by
        rw [Chvatal.matrixWire_row]
        have hc := c.isLt
        omega)
      have hfalse' : out (Chvatal.matrixWire 4096 64 r c) = false := by
        simpa [out, net] using hfalse
      rw [hfalse'] at hr
      cases hr
    have hcard := Finset.card_le_card hsubset
    rw [card_filter_val_ge 4096 a (by omega)] at hcard
    exact hcard
  have htrueLower (c : Col) : 4096 - b <= Chvatal.matrixColumnTrueCount c out := by
    change 4096 - b <= (Finset.univ.filter fun r : Row =>
      out (Chvatal.matrixWire 4096 64 r c) = true).card
    have hsubset : Finset.univ.filter (fun r : Row => b <= r.val) ⊆
      Finset.univ.filter fun r : Row =>
        out (Chvatal.matrixWire 4096 64 r c) = true := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have htrue := habove (Chvatal.matrixWire 4096 64 r c) (by
        rw [Chvatal.matrixWire_row]
        have hc := c.isLt
        omega)
      simpa [out, net] using htrue
    have hcard := Finset.card_le_card hsubset
    rw [card_filter_val_ge 4096 b (by omega)] at hcard
    exact hcard
  have hlo (c : Col) : a <= actual c := by
    have hfalse := matrixColumnFalseCount_eq_sub_trueCount c out
    have hsum : actual c + Chvatal.matrixColumnTrueCount c out = 4096 := by
      simpa [actual] using hfalse
    have hcombine : Chvatal.matrixColumnTrueCount c out + a <= 4096 := by
      calc
        _ <= (4096 - a) + a := Nat.add_le_add_right (htrueUpper c) a
        _ = 4096 := Nat.sub_add_cancel (by omega)
    omega
  have hhi (c : Col) : actual c <= b := by
    have hfalse := matrixColumnFalseCount_eq_sub_trueCount c out
    have hsum : actual c + Chvatal.matrixColumnTrueCount c out = 4096 := by
      simpa [actual] using hfalse
    have hcombine : 4096 <= Chvatal.matrixColumnTrueCount c out + b := by
      calc
        _ = (4096 - b) + b := (Nat.sub_add_cancel (by omega)).symm
        _ <= _ := Nat.add_le_add_right (htrueLower c) b
    omega
  simpa [actual, out, net] using
    exact_rank_port_error_le_448 actual cuts ports H hzero hend hmono
      hactual hH a b hlo hhi hba

end Chvatal.D2FalseProfileTransfer
