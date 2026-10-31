import D2ReflectedPhysicalPack
import D2ClippedFlowProfileTransfer

open scoped BigOperators

namespace Chvatal.D2PhysicalProfileRangeTransfer

open Chvatal.D2ReflectedPhysicalPack
open Chvatal.D2ClippedFlowProfileTransfer
open Chvatal.D2ColumnRebatchBridge
open Chvatal.D2RankAlignment

abbrev Col := Fin 64
abbrev Wire := Fin (4096 * 64)

private theorem output_column_mass_eq_input_mass (v : Wire → Bool) :
    (Finset.univ.sum fun c : Col =>
      matrixColumnTrueCount c
        ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
          reflectedSigma35 reflectedSigma25).exec v)) =
      (Finset.univ.filter fun w : Wire => v w = true).card := by
  let net := Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
    reflectedSigma35 reflectedSigma25
  let out := net.exec v
  have hcolumn (c : Col) : matrixColumnTrueCount c out =
      Finset.univ.sum fun r : Fin 4096 =>
        if out (Chvatal.matrixWire 4096 64 r c) then 1 else 0 := by
    unfold matrixColumnTrueCount
    rw [Finset.card_filter]
  have htotal : (Finset.univ.filter fun w : Wire => out w = true).card =
      (Finset.univ.filter fun w : Wire => v w = true).card := by
    obtain ⟨ρ, hρ⟩ := Chvatal.ComparatorNetwork.exec_eq_comp_perm net v
    change (Finset.univ.filter fun w : Wire => net.exec v w = true).card = _
    rw [hρ]
    exact Chvatal.card_true_comp_equiv v ρ
  calc
    _ = Finset.univ.sum fun c : Col =>
          Finset.univ.sum fun r : Fin 4096 =>
            if out (Chvatal.matrixWire 4096 64 r c) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          exact hcolumn c
    _ = Finset.univ.sum fun w : Wire => if out w then 1 else 0 :=
          (Chvatal.sum_matrixWire (by omega)
            (fun w : Wire => if out w then 1 else 0)).symm
    _ = (Finset.univ.filter fun w : Wire => out w = true).card := by
          rw [Finset.card_filter]
    _ = (Finset.univ.filter fun w : Wire => v w = true).card := htotal

/-- The physical four-sort output's 64 column counts differ from its exact
row-major rank profile by at most 448 in l1. This instantiates the zero-sum
range lemma with the physical 13-row band, including the row-dependent
permutation and final two-grid repair. -/
theorem physical_output_exact_rank_l1_le_448 (v : Wire → Bool) :
    (Finset.univ.sum fun c : Col => countDistance
      (matrixColumnTrueCount c
        ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
          reflectedSigma35 reflectedSigma25).exec v))
      (exactRankColumnHeight
        (Finset.univ.filter fun w : Wire => v w = true).card c)) <= 448 := by
  let net := Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
    reflectedSigma35 reflectedSigma25
  let out := net.exec v
  let H := (Finset.univ.filter fun w : Wire => v w = true).card
  let actual : Col → Nat := fun c => matrixColumnTrueCount c out
  let ideal : Col → Nat := fun c => exactRankColumnHeight H c
  have hH : H <= 64 * 4096 := by
    dsimp [H]
    calc
      _ <= (Finset.univ : Finset Wire).card := Finset.card_filter_le _ _
      _ = 64 * 4096 := by simp [Wire]
  have hactual : (Finset.univ.sum fun c : Col => actual c) = H := by
    simpa [H, actual, out, net] using output_column_mass_eq_input_mass v
  have hideal : (Finset.univ.sum fun c : Col => ideal c) = H := by
    simpa [ideal, H] using exactRankColumnHeight_sum H hH
  have hidealRange (c d : Col) : ideal c <= ideal d + 1 := by
    dsimp [ideal, exactRankColumnHeight]
    by_cases hc : c.val < H % 64 <;>
      by_cases hd : d.val < H % 64 <;> simp [hc, hd] <;> omega
  have hactualRange (c d : Col) : actual c <= actual d + 13 := by
    change matrixColumnTrueCount c (net.exec v) <=
      matrixColumnTrueCount d (net.exec v) + 13
    exact reflectedPhysicalPackTwoGrid_columnCount_range_le_13
      v (fun c => matrixColumnTrueCount c v)
      (fun _ => rfl) (fun c => matrixColumnTrueCount_le c v) c d
  let defect : Col → Int := fun c => (actual c : Int) - (ideal c : Int)
  have hzero : (Finset.univ.sum fun c : Col => defect c) = 0 := by
    have ha : (Finset.univ.sum fun c : Col => (actual c : Int)) = (H : Int) := by
      exact_mod_cast hactual
    have hi : (Finset.univ.sum fun c : Col => (ideal c : Int)) = (H : Int) := by
      exact_mod_cast hideal
    simp only [defect, Finset.sum_sub_distrib, ha, hi]
    ring
  have hdefectRange (c d : Col) : defect c <= defect d + 14 := by
    have h1 := hactualRange c d
    have h2 := hidealRange d c
    dsimp [defect]
    omega
  have hint := sum_abs_int_le_448_of_zero_sum_range14 defect hzero hdefectRange
  have hconvert : (Finset.univ.sum fun c : Col =>
      (countDistance (actual c) (ideal c) : Int)) =
      Finset.univ.sum fun c : Col => |defect c| := by
    apply Finset.sum_congr rfl
    intro c hc
    change (countDistance (actual c) (ideal c) : Int) =
      |(actual c : Int) - (ideal c : Int)|
    by_cases h : actual c <= ideal c
    · have hcast : (actual c : Int) <= (ideal c : Int) := by exact_mod_cast h
      simp only [countDistance, Nat.sub_eq_zero_of_le h, zero_add]
      rw [Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr hcast)]
      omega
    · have h' : ideal c <= actual c := by omega
      have hcast : (ideal c : Int) <= (actual c : Int) := by exact_mod_cast h'
      simp only [countDistance, Nat.sub_eq_zero_of_le h', add_zero]
      rw [Nat.cast_sub h', abs_of_nonneg (sub_nonneg.mpr hcast)]
  have hconverted := hint
  rw [← hconvert] at hconverted
  exact_mod_cast hconverted

/-- Splitting the physical profile into arbitrary monotone row ports in each
column cannot increase its exact-rank l1 error. This is the physical 448
provider interface needed by the clipped D2 rank transfer. -/
theorem physical_output_exact_rank_port_cells_l1_le_448
    (v : Wire → Bool) (ports : Nat) (cuts : Nat → Nat → Nat)
    (hzero : ∀ c < 64, cuts c 0 = 0)
    (hend : ∀ c < 64, cuts c ports = 4096)
    (hmono : ∀ c < 64, ∀ i, i < ports → cuts c i ≤ cuts c (i + 1)) :
    (Finset.sum (Finset.range 64) fun c =>
      Finset.sum (Finset.range ports) fun p => countDistance
        (prefixIntervalMass
          (matrixColumnTrueCount ⟨c % 64, Nat.mod_lt c (by omega)⟩
            ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
              reflectedSigma35 reflectedSigma25).exec v))
          (cuts c p) (cuts c (p + 1)))
        (prefixIntervalMass
          (exactRankColumnHeight
            ((Finset.univ.filter fun w : Wire => v w = true).card)
            ⟨c % 64, Nat.mod_lt c (by omega)⟩)
          (cuts c p) (cuts c (p + 1)))) <= 448 := by
  let H := (Finset.univ.filter fun w : Wire => v w = true).card
  let actual : Col → Nat := fun c => matrixColumnTrueCount c
    ((Chvatal.D2PhysicalPackTwoGrid.physicalPackTwoGridNet
      reflectedSigma35 reflectedSigma25).exec v)
  let ideal : Col → Nat := fun c => exactRankColumnHeight H c
  let actualN : Nat → Nat := fun c => actual ⟨c % 64, Nat.mod_lt c (by omega)⟩
  let idealN : Nat → Nat := fun c => ideal ⟨c % 64, Nat.mod_lt c (by omega)⟩
  have hlocal := physical_output_exact_rank_l1_le_448 v
  have hlocalRange : (Finset.sum (Finset.range 64) fun ci =>
      countDistance (actualN ci) (idealN ci)) <= 448 := by
    have hlocal' : (Finset.univ.sum fun c : Col =>
        countDistance (actualN c.val) (idealN c.val)) <= 448 := by
      simpa [actualN, idealN, actual, ideal, H, Nat.mod_eq_of_lt] using hlocal
    rw [Fin.sum_univ_eq_sum_range
      (fun ci : Nat => countDistance (actualN ci) (idealN ci))] at hlocal'
    exact hlocal'
  have hcell (c : Nat) (hc : c ∈ Finset.range 64) :
      (Finset.sum (Finset.range ports) fun p => countDistance
        (prefixIntervalMass (actualN c) (cuts c p) (cuts c (p + 1)))
        (prefixIntervalMass (idealN c) (cuts c p) (cuts c (p + 1)))) <=
      countDistance (actualN c) (idealN c) :=
    prefixIntervalMass_partition_distance (actualN c) (idealN c) (cuts c)
      ports 4096 (hzero c (Finset.mem_range.mp hc))
      (hend c (Finset.mem_range.mp hc))
      (fun i hi => hmono c (Finset.mem_range.mp hc) i hi)
  calc
    _ <= Finset.sum (Finset.range 64) fun c => countDistance (actualN c) (idealN c) := by
      apply Finset.sum_le_sum
      intro c hc
      exact hcell c hc
    _ <= 448 := hlocalRange

/-- Partitioning two arbitrary column profiles into monotone row ports cannot
increase their l1 distance. This abstract interface lets the physical 448
provider feed clipped-flow transfers without unfolding the comparator net. -/
theorem profile_port_cells_distance_le
    (actual ideal : Col → Nat) (ports : Nat) (cuts : Col → Nat → Nat)
    (hzero : ∀ c, cuts c 0 = 0)
    (hend : ∀ c, cuts c ports = 4096)
    (hmono : ∀ c, ∀ i, i < ports → cuts c i ≤ cuts c (i + 1))
    (hlocal : (Finset.univ.sum fun c : Col => countDistance (actual c) (ideal c)) ≤ 448) :
    (Finset.univ.sum fun c : Col =>
      Finset.univ.sum fun p : Fin ports =>
        countDistance
          (prefixIntervalMass (actual c) (cuts c p.val) (cuts c (p.val + 1)))
          (prefixIntervalMass (ideal c) (cuts c p.val) (cuts c (p.val + 1)))) ≤ 448 := by
  have hcolumn (c : Col) :
      (Finset.univ.sum fun p : Fin ports =>
        countDistance
          (prefixIntervalMass (actual c) (cuts c p.val) (cuts c (p.val + 1)))
          (prefixIntervalMass (ideal c) (cuts c p.val) (cuts c (p.val + 1)))) ≤
        countDistance (actual c) (ideal c) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun p : Nat => countDistance
        (prefixIntervalMass (actual c) (cuts c p) (cuts c (p + 1)))
        (prefixIntervalMass (ideal c) (cuts c p) (cuts c (p + 1))))]
    exact prefixIntervalMass_partition_distance (actual c) (ideal c) (cuts c)
      ports 4096 (hzero c) (hend c) (fun i hi => hmono c i hi)
  calc
    _ ≤ Finset.univ.sum fun c : Col => countDistance (actual c) (ideal c) := by
      apply Finset.sum_le_sum
      intro c hc
      exact hcolumn c
    _ ≤ 448 := hlocal

end Chvatal.D2PhysicalProfileRangeTransfer
