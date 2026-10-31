import D2PhysicalProfilePortError
import D2LiftedShuffleBridge
import AKS.Sub800.Round2Det

open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Chvatal.D2PhysicalProfileMass

open Chvatal.D2BandRepair4096Network
open Chvatal.D2Slope35Physical4096
open Chvatal.D2LiftedShuffleBridge
open Chvatal.D2TwoGridPhysicalBand
open Chvatal.D2TwoGridBandInterface
open Chvatal.D2RankAlignment

abbrev Col := Fin 64
abbrev Row := Fin 4096

/-- A row-preserving column scramble redistributes a tile's keys but preserves
its total marked mass. -/
theorem physical_profile_sum_eq_semantic_sum
    (h : Col -> Nat) (hbound : forall c, h c <= 4096)
    (perm : Row -> Equiv.Perm Col) :
    (Finset.univ.sum fun c : Col => physicalTwoGridRepairHeight h perm c) =
      Finset.univ.sum fun c : Col => fullHeightTwoShuffle h c := by
  let sums := heightColumnSums (fullHeightTwoShuffle h)
    (fullHeightTwoShuffle_le_4096 h hbound)
  let sigma : Row -> Equiv.Perm Col := fun r => (perm r).symm
  have hscramble (c : Col) :
      physicalTwoGridRepairHeight h perm c = Chvatal.scrambledColSum sums sigma c := by
    simpa [sums, sigma] using
      physical_twoGridRepairHeight_eq_scrambledColSum h hbound perm c
  calc
    (Finset.univ.sum fun c : Col => physicalTwoGridRepairHeight h perm c) =
        Finset.univ.sum fun c : Col => Chvatal.scrambledColSum sums sigma c := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hscramble c
    _ = Finset.univ.sum fun j : Col => Round2.walkN sigma Finset.univ j (sums j).val := by
      simpa using Round2.sum_scrambledColSum_eq sums sigma (Finset.univ : Finset Col)
    _ = Finset.univ.sum fun j : Col => (sums j).val := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Round2.walkN]
      simp only [Finset.mem_univ, and_true]
      rw [card_filter_val_ge 4096 (4096 - (sums j).val) (by omega)]
      omega
    _ = Finset.univ.sum fun j : Col => fullHeightTwoShuffle h j := by
      simp [sums, heightColumnSums]

theorem physical_profile_le_m
    (h : Col -> Nat) (perm : Row -> Equiv.Perm Col) (m : Nat)
    (hm : m <= 4096) (hinput : forall c, h c <= m) (c : Col) :
    physicalTwoGridRepairHeight h perm c <= m := by
  change (Finset.univ.filter fun r : Row =>
    fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r c) = true).card <= m
  have hsubset :
      (Finset.univ.filter fun r : Row =>
        fullHeightAfterRowPermutation h perm (matrixWire 4096 64 r c) = true) ⊆
      Finset.univ.filter (fun r : Row => 4096 - m <= r.val) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    rw [fullHeightAfterRowPermutation_matrixWire] at hr
    have hrow : fullHeightTwoShuffle h (perm r c) <= m :=
      fullHeightTwoShuffle_le_of_height_le h m hm hinput (perm r c)
    unfold rowScrambledUnary bottomUnary threshold outputHeight at hr
    simp only [decide_eq_true_eq] at hr
    omega
  calc
    _ <= (Finset.univ.filter fun r : Row => 4096 - m <= r.val).card :=
      Finset.card_le_card hsubset
    _ = m := by rw [card_filter_val_ge 4096 (4096 - m) (by omega)]; omega

theorem prefixIntervalMass_extend_end
    (H u m N : Nat) (hH : H <= m) (hu : u <= m) (hmN : m <= N) :
    prefixIntervalMass H u m = prefixIntervalMass H u N := by
  unfold prefixIntervalMass
  have h1 : H - u <= m - u := Nat.sub_le_sub_right hH u
  have h2 : H - u <= N - u := le_trans h1 (Nat.sub_le_sub_right hmN u)
  rw [Nat.min_eq_left h1, Nat.min_eq_left h2]

/-- The physical 448 exact-rank bound extends to clipped partial-row cuts:
padding only the final port through the all-zero rows changes neither the
actual nor exact-rank mass. -/
theorem physical_profile_partial_rows_rebinned_l1_le_448
    (h : Col -> Nat) (perm : Row -> Equiv.Perm Col)
    (m ports H : Nat) (cuts : Col -> Nat -> Nat)
    (hm : m <= 4096) (hports : 0 < ports)
    (hinput : forall c, h c <= m)
    (hH : H = Finset.univ.sum fun c : Col => physicalTwoGridRepairHeight h perm c)
    (hzero : forall c, cuts c 0 = 0)
    (hend : forall c, cuts c ports = m)
    (hmono : forall c i, i < ports -> cuts c i <= cuts c (i + 1))
    (hcutBound : forall c i, i <= ports -> cuts c i <= m) :
    (Finset.univ.sum fun cell : Prod Col (Fin ports) =>
      abs ((prefixIntervalMass (physicalTwoGridRepairHeight h perm cell.1)
          (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat) -
        (prefixIntervalMass
          (Chvatal.D2ColumnRebatchBridge.exactRankColumnHeight H cell.1)
          (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat))) <= 448 := by
  let padded : Col -> Nat -> Nat := fun c i => if i = ports then 4096 else cuts c i
  have hpzero (c : Col) : padded c 0 = 0 := by
    have hp : 0 ≠ ports := by omega
    simp [padded, hp, hzero c]
  have hpend (c : Col) : padded c ports = 4096 := by simp [padded]
  have hpmono (c : Col) (i : Nat) (hi : i < ports) :
      padded c i <= padded c (i + 1) := by
    by_cases hlast : i + 1 = ports
    · have hci : i <= ports := by omega
      have hnot : i ≠ ports := by omega
      simp [padded, hlast, hnot]
      exact le_trans (hcutBound c i hci) (by omega)
    · have hnext : i + 1 < ports := by omega
      simp [padded, Nat.ne_of_lt hi, Nat.ne_of_lt hnext]
      exact hmono c i hi
  have hsumSemantic := physical_profile_sum_eq_semantic_sum h
    (fun c => le_trans (hinput c) hm) perm
  have hHsemantic : H = Finset.univ.sum fun c : Col => fullHeightTwoShuffle h c := by
    calc
      H = Finset.univ.sum fun c : Col => physicalTwoGridRepairHeight h perm c := hH
      _ = Finset.univ.sum fun c : Col => fullHeightTwoShuffle h c := hsumSemantic
  have hresult := Chvatal.D2PhysicalProfilePortError.physical_profile_exact_rank_port_error_le_448
    h perm (fun c => le_trans (hinput c) hm) H ports hH padded hpzero hpend
    (by intro c i hi; exact hpmono c i hi)
  have hsame (cell : Prod Col (Fin ports)) :
      abs ((prefixIntervalMass (physicalTwoGridRepairHeight h perm cell.1)
          (padded cell.1 cell.2.val) (padded cell.1 (cell.2.val + 1)) : Rat) -
        (prefixIntervalMass
          (Chvatal.D2ColumnRebatchBridge.exactRankColumnHeight H cell.1)
          (padded cell.1 cell.2.val) (padded cell.1 (cell.2.val + 1)) : Rat)) =
      abs ((prefixIntervalMass (physicalTwoGridRepairHeight h perm cell.1)
          (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat) -
        (prefixIntervalMass
          (Chvatal.D2ColumnRebatchBridge.exactRankColumnHeight H cell.1)
          (cuts cell.1 cell.2.val) (cuts cell.1 (cell.2.val + 1)) : Rat)) := by
    rcases cell with ⟨c, p⟩
    by_cases hlast : p.val + 1 = ports
    · have hprev : p.val ≠ ports := by omega
      have hu : cuts c p.val <= m := hcutBound c p.val (by omega)
      have hactualBound := physical_profile_le_m h perm m hm hinput c
      have hHboundSem :
          (Finset.univ.sum fun c : Col => fullHeightTwoShuffle h c) <= 64 * m := by
        calc
          (Finset.univ.sum fun c : Col => fullHeightTwoShuffle h c) <=
              Finset.univ.sum fun _ : Col => m :=
            Finset.sum_le_sum fun c hc =>
              fullHeightTwoShuffle_le_of_height_le h m hm hinput c
          _ = 64 * m := by simp
      have hHbound : H <= 64 * m := by rw [hHsemantic]; exact hHboundSem
      have hrankBound :
          Chvatal.D2ColumnRebatchBridge.exactRankColumnHeight H c <= m := by
        unfold Chvatal.D2ColumnRebatchBridge.exactRankColumnHeight
        have hmod := Nat.mod_lt H (by decide : 0 < 64)
        have hq : H / 64 <= m := by omega
        split_ifs <;> omega
      simp [padded, hprev, hlast]
      have ha := prefixIntervalMass_extend_end
        (physicalTwoGridRepairHeight h perm c) (cuts c p.val) m 4096
        hactualBound hu hm
      have hr := prefixIntervalMass_extend_end
        (Chvatal.D2ColumnRebatchBridge.exactRankColumnHeight H c)
        (cuts c p.val) m 4096 hrankBound hu hm
      rw [hend c]
      rw [← congrArg (fun n : Nat => (n : Rat)) ha,
        ← congrArg (fun n : Nat => (n : Rat)) hr]
    · have hprev : p.val ≠ ports := by omega
      simp [padded, hprev, hlast]
  calc
    _ = Finset.univ.sum fun cell : Prod Col (Fin ports) =>
        abs ((prefixIntervalMass (physicalTwoGridRepairHeight h perm cell.1)
            (padded cell.1 cell.2.val) (padded cell.1 (cell.2.val + 1)) : Rat) -
          (prefixIntervalMass
            (Chvatal.D2ColumnRebatchBridge.exactRankColumnHeight H cell.1)
            (padded cell.1 cell.2.val) (padded cell.1 (cell.2.val + 1)) : Rat)) := by
      apply Finset.sum_congr rfl
      intro cell hc
      exact (hsame cell).symm
    _ <= 448 := hresult

end Chvatal.D2PhysicalProfileMass
