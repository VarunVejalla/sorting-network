import D2Slope35Physical4096
import D2RankAlignment

namespace Chvatal.D2ProfileOrientationGate

open Chvatal.D2Slope35Physical4096
open Chvatal.D2RankAlignment

abbrev Col := Fin 64
abbrev Row := Fin 4096

theorem bottomUnaryProfile_true_iff
    (height : Col → Nat) (c : Col) (r : Row) :
    bottomUnaryProfile height (Chvatal.matrixWire 4096 64 r c) = true ↔
      4096 - height c ≤ r.val := by
  simp [bottomUnaryProfile, Chvatal.matrixWire_row_col]

/-- True wires in a physical row interval of one unary column. -/
def bottomUnaryIntervalTrueCount (height : Col → Nat) (c : Col)
    (lo hi : Nat) : Nat :=
  (Finset.range 4096 |>.filter fun r =>
    lo ≤ r ∧ r < hi ∧ 4096 - height c ≤ r).card

/-- A physical row interval counts the bottom-unary height after reflecting
its endpoints. The profile transport must use this reflected cut convention. -/
theorem bottomUnaryIntervalTrueCount_eq_reflected_prefixMass
    (height : Col → Nat) (c : Col) (lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ 4096) :
    bottomUnaryIntervalTrueCount height c lo hi =
      prefixIntervalMass (height c) (4096 - hi) (4096 - lo) := by
  have hset :
      (Finset.range 4096 |>.filter fun r =>
        lo ≤ r ∧ r < hi ∧ 4096 - height c ≤ r) =
        Finset.Ico (max lo (4096 - height c)) hi := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  unfold bottomUnaryIntervalTrueCount
  rw [hset, Nat.card_Ico]
  unfold prefixIntervalMass
  omega

theorem bottomUnaryProfile_false_on_top_rows
    (height : Col → Nat) (c : Col) (r : Row)
    (hheight : height c ≤ 4032) (hr : r.val < 64) :
    bottomUnaryProfile height (Chvatal.matrixWire 4096 64 r c) = false := by
  simp [bottomUnaryProfile, Chvatal.matrixWire_row_col]
  omega

/-- The low 64 physical rows contain no true wires when the column has one
true bit; the profile's prefix-mass convention counts that bit there. This
isolates the required row-reversal conversion for any stage/profile bridge. -/
theorem one_true_orientation_mismatch
    (height : Col → Nat) (c : Col) (hheight : height c = 1) :
    bottomUnaryIntervalTrueCount height c 0 64 = 0 ∧
      prefixIntervalMass (height c) 0 64 = 1 := by
  constructor
  · have hcount := bottomUnaryIntervalTrueCount_eq_reflected_prefixMass
      height c 0 64 (by omega) (by omega)
    rw [hcount, hheight]
    norm_num [prefixIntervalMass]
  · rw [hheight]
    norm_num [prefixIntervalMass]

end Chvatal.D2ProfileOrientationGate
