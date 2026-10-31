import D2Slope25LiftArea

open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Chvatal.D2Range13Area

open Chvatal.D2Slope25LiftArea
open Chvatal.D2RankAlignment

abbrev Col := Fin 64

/-- Any 64-column profile whose range is at most 13 has the same 416 area
allowance used by the two-shuffle provider. -/
theorem area_le_169_over_eight
    (actual : Col -> Nat) (lo hi : Nat)
    (hlo : forall c, lo <= actual c)
    (hhi : forall c, actual c <= hi)
    (hrange : hi - lo <= 13) :
    (1 / 2 : Rat) *
      (Finset.univ.sum fun c : Col =>
        ((actual c : Rat) -
          (Finset.univ.sum fun j : Col => (actual j : Rat)) / 64) ^ 2) / 64
        <= 169 / 8 := by
  let theta : Rat :=
    (Finset.univ.sum fun j : Col => (actual j : Rat)) / 64
  have hmean : (Finset.univ.sum fun c : Col =>
      ((actual c : Rat) - theta)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hconst : (Finset.univ.sum fun _ : Col => theta) = 64 * theta := by
      simp [Fintype.card_fin]
    rw [hconst]
    dsimp [theta]
    field_simp
    ring
  have hlo' (c : Col) : (lo : Rat) <= (actual c : Rat) := by
    exact_mod_cast hlo c
  have hhi' (c : Col) : (actual c : Rat) <= (hi : Rat) := by
    exact_mod_cast hhi c
  have hlohi : lo <= hi := le_trans (hlo ⟨0, by decide⟩) (hhi ⟨0, by decide⟩)
  have hwidth : (hi : Rat) - lo <= 13 := by
    rw [← Nat.cast_sub hlohi]
    exact_mod_cast hrange
  have hwidthsq : ((hi : Rat) - lo) ^ 2 <= (13 : Rat) ^ 2 := by
    have hn : 0 <= (hi : Rat) - lo := by
      rw [← Nat.cast_sub hlohi]
      exact_mod_cast (Nat.zero_le (hi - lo))
    nlinarith
  have hbase := half_variance_le_range_sq_div_eight
    (n := 64) (by norm_num) (fun c : Col => (actual c : Rat)) theta
    (lo : Rat) (hi : Rat) hmean hlo' hhi'
  have hwidthsq : ((hi : Rat) - lo) ^ 2 <= (13 : Rat) ^ 2 := by
    nlinarith [sq_nonneg ((hi : Rat) - lo)]
  have hscaled :
      (1 / 2 : Rat) *
        (Finset.univ.sum fun c : Col => ((actual c : Rat) - theta) ^ 2) / 64
        <= 169 / 8 := by
    calc
      _ <= ((64 : Rat) * ((hi : Rat) - lo) ^ 2 / 8) / 64 := by
        exact div_le_div_of_nonneg_right hbase (by norm_num)
      _ <= 169 / 8 := by
        norm_num
        nlinarith [hwidthsq]
  simpa [theta] using hscaled

end Chvatal.D2Range13Area
