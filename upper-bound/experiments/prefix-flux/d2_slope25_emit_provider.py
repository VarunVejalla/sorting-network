#!/usr/bin/env python3
"""Emit the Lean aggregator for the 64 exact slope-25 dual certificates."""
from pathlib import Path

here = Path(__file__).parent
imports = [f"import D2Slope25Certificate{i:02}" for i in range(64)]
imports.insert(0, "import D2RankAlignment")
imports.insert(0, "import D2Slope25Abstract")
imports.insert(0, "import D2Slope25Physical")

potential_cases = "\n".join(
    f"  | {i} => (Chvatal.D2Slope25Certificate{i}.potentials[layer.val]!)[height.val]!"
    for i in range(64)
)
budget_cases = "\n".join(
    f"  | {i} => Chvatal.D2Slope25Certificate{i}.budgets[layer.val]!"
    for i in range(64)
)
edge_cases = "\n".join(
    f'''  · simpa [certificateBudget, certificatePotential,
      Chvatal.D2Slope25Abstract.unary,
      Chvatal.D2Slope25Certificate{i}.unary] using
      Chvatal.D2Slope25Certificate{i}.delta_edge_inequality
        layer current previous htransition'''
    for i in range(64)
)

source = "\n".join(imports) + '''

set_option maxHeartbeats 0

namespace Chvatal.D2Slope25Provider

open Chvatal.D2Slope25Abstract

def certificatePotential (delta layer : Col) (height : Height) : Int :=
  match delta.val with
''' + potential_cases + '''
  | _ => 0

def certificateBudget (delta layer : Col) : Int :=
  match delta.val with
''' + budget_cases + '''
  | _ => 0

theorem certificate_edge (delta layer : Col) (current previous : Height)
    (htransition : current.val ≤ previous.val + 1) :
    unary delta layer current ≤
      certificateBudget delta layer +
        certificatePotential delta (predecessor layer) previous -
          certificatePotential delta layer current := by
  fin_cases delta
''' + edge_cases + '''

theorem certificate_budget_sum_le_77 (delta : Col) :
    (∑ layer : Col, certificateBudget delta layer) ≤ 77 := by
  fin_cases delta <;> decide

theorem shiftLayer_predecessor_commute (shift layer : Col) :
    shiftLayer shift (predecessor layer) = predecessor (shiftLayer shift layer) := by
  apply Fin.ext
  dsimp [shiftLayer, predecessor]
  omega

theorem slope25_output_pair_range_le_thirteen
    (height : Col → Height)
    (hgradient : ∀ layer,
      (height layer).val ≤ (height (predecessor layer)).val + 1) :
    ∀ origin target,
      output25Height height origin ≤ output25Height height target + 13 := by
  apply all_output_pairs_le_thirteen height
    (fun delta _origin layer h => certificatePotential delta layer h)
    (fun delta _origin layer => certificateBudget delta layer)
  · intro origin delta layer
    let shift := shiftForOrigin origin
    let current := rotateProfile height shift layer
    let previous := rotateProfile height shift (predecessor layer)
    have htransition : current.val ≤ previous.val + 1 := by
      dsimp [current, previous, rotateProfile]
      rw [shiftLayer_predecessor_commute]
      exact hgradient (shiftLayer shift layer)
    have hedge := certificate_edge delta layer current previous htransition
    simpa [current, previous] using hedge
  · intro delta origin
    simpa using certificate_budget_sum_le_77 delta

theorem slope25_popoviciu_area_per_column_le_169_over_eight
    (height : Col → Height)
    (hgradient : ∀ layer,
      (height layer).val ≤ (height (predecessor layer)).val + 1) :
    (1 / 2 : ℚ) *
      (∑ i : Col,
        ((output25Height height i : ℚ) -
          (∑ j : Col, (output25Height height j : ℚ)) / 64) ^ 2) / 64
      ≤ 169 / 8 := by
  let x : Col → ℚ := fun i => output25Height height i
  let vals : Finset ℚ := Finset.univ.image x
  have hvals : vals.Nonempty := by
    refine ⟨x ⟨0, by decide⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0, by decide⟩, Finset.mem_univ _, rfl⟩
  let lo : ℚ := vals.min' hvals
  let hi : ℚ := vals.max' hvals
  have hlo : ∀ i, lo ≤ x i := by
    intro i
    have hm : x i ∈ vals := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    simpa [lo, vals] using Finset.min'_le (s := Finset.univ.image x) (x i) hm
  have hhi : ∀ i, x i ≤ hi := by
    intro i
    have hm : x i ∈ vals := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    simpa [hi, vals] using Finset.le_max' (s := Finset.univ.image x) (x i) hm
  have hminmem := Finset.min'_mem vals hvals
  have hmaxmem := Finset.max'_mem vals hvals
  rcases Finset.mem_image.mp hminmem with ⟨imin, _, hmin⟩
  rcases Finset.mem_image.mp hmaxmem with ⟨imax, _, hmax⟩
  have hpair := slope25_output_pair_range_le_thirteen height hgradient imax imin
  have hrange : hi - lo ≤ 13 := by
    have hpair' : x imax ≤ x imin + 13 := by
      dsimp [x]
      exact_mod_cast hpair
    change vals.max' hvals - vals.min' hvals ≤ 13
    rw [← hmax, ← hmin]
    linarith
  let theta : ℚ := (∑ i : Col, x i) / 64
  have hmean : (∑ i : Col, (x i - theta)) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_fin]
    dsimp [theta]
    ring
  have hbase := Chvatal.D2RankAlignment.half_variance_le_range_sq_div_eight
    (n := 64) (by decide) x theta lo hi hmean hlo hhi
  have hwidth_nonneg : 0 ≤ hi - lo := by linarith [hlo ⟨0, by decide⟩, hhi ⟨0, by decide⟩]
  have hwidthsq : (hi - lo) ^ 2 ≤ (13 : ℚ) ^ 2 := by
    nlinarith [sq_nonneg (hi - lo)]
  have hscaled :
      (1 / 2 : ℚ) * (∑ i : Col, (x i - theta) ^ 2) ≤ 1352 := by
    nlinarith [hbase, hwidthsq]
  have hresult :
      (1 / 2 : ℚ) * (∑ i : Col, (x i - theta) ^ 2) / 64 ≤ 169 / 8 := by
    norm_num at hscaled ⊢
    nlinarith
  simpa [x, theta] using hresult

def slope35Destination (layer : Col) : Col :=
  ⟨(35 * layer.val) % 64, Nat.mod_lt _ (by omega)⟩

def slope35IndexedProfile (sourceHeight : Col → Height) : Col → Height :=
  fun layer =>
    ⟨Chvatal.D2RankAlignment.slope35PhysicalOutputHeight
        (fun c => (sourceHeight c).val) (slope35Destination layer),
      Nat.lt_succ_of_le
        (Chvatal.D2Slope25Physical.slope35PhysicalOutputHeight_le_64
          (fun c => (sourceHeight c).val)
          (by
            intro c
            have hc := (sourceHeight c).isLt
            change (sourceHeight c).val ≤ 64
            omega)
          (slope35Destination layer))⟩

theorem slope35IndexedProfile_gradient (sourceHeight : Col → Height) :
    ∀ layer,
      (slope35IndexedProfile sourceHeight layer).val ≤
        (slope35IndexedProfile sourceHeight (predecessor layer)).val + 1 := by
  intro layer
  have h := Chvatal.D2RankAlignment.slope35PhysicalOutputHeight_gradient
    (fun c => (sourceHeight c).val) (slope35Destination layer)
  have hdest : slope35Destination (predecessor layer) =
      Chvatal.D2RankAlignment.slope35PrevDestination (slope35Destination layer) := by
    apply Fin.ext
    dsimp [slope35Destination, predecessor,
      Chvatal.D2RankAlignment.slope35PrevDestination]
    omega
  simpa [slope35IndexedProfile, hdest] using h

def slope35Then25PhysicalOutputHeight
    (sourceHeight : Col → Height) (destination : Col) : Nat :=
  Chvatal.D2Slope25Physical.slope25PhysicalOutputHeight
    (fun layer => Chvatal.D2RankAlignment.slope35PhysicalOutputHeight
      (fun c => (sourceHeight c).val) (slope35Destination layer)) destination

theorem slope35Then25PhysicalOutputHeight_eq_abstract
    (sourceHeight : Col → Height) (destination : Col) :
    (slope35Then25PhysicalOutputHeight sourceHeight destination : Int) =
      output25Height (slope35IndexedProfile sourceHeight) destination := by
  let intermediate := fun layer : Col =>
    Chvatal.D2RankAlignment.slope35PhysicalOutputHeight
      (fun c => (sourceHeight c).val) (slope35Destination layer)
  have hbound : ∀ layer, intermediate layer ≤ 64 := by
    intro layer
    exact Chvatal.D2Slope25Physical.slope35PhysicalOutputHeight_le_64
      (fun c => (sourceHeight c).val)
      (by
        intro c
        have hc := (sourceHeight c).isLt
        change (sourceHeight c).val ≤ 64
        omega)
      (slope35Destination layer)
  have heq := Chvatal.D2Slope25Physical.slope25PhysicalOutputHeight_eq_abstract
    intermediate hbound destination
  simpa [slope35Then25PhysicalOutputHeight, slope35IndexedProfile,
    intermediate] using heq

theorem slope35_then_slope25_output_range_le_thirteen
    (sourceHeight : Col → Height) :
    ∀ origin target,
      slope35Then25PhysicalOutputHeight sourceHeight origin ≤
        slope35Then25PhysicalOutputHeight sourceHeight target + 13 := by
  intro origin target
  have h := slope25_output_pair_range_le_thirteen
    (slope35IndexedProfile sourceHeight)
    (slope35IndexedProfile_gradient sourceHeight) origin target
  have hInt :
      (slope35Then25PhysicalOutputHeight sourceHeight origin : Int) ≤
        (slope35Then25PhysicalOutputHeight sourceHeight target : Int) + 13 := by
    rw [slope35Then25PhysicalOutputHeight_eq_abstract,
      slope35Then25PhysicalOutputHeight_eq_abstract]
    exact h
  exact_mod_cast hInt

theorem slope35_then_slope25_area_per_column_le_169_over_eight
    (sourceHeight : Col → Height) :
    (1 / 2 : ℚ) *
      (∑ i : Col,
        ((slope35Then25PhysicalOutputHeight sourceHeight i : ℚ) -
          (∑ j : Col,
            (slope35Then25PhysicalOutputHeight sourceHeight j : ℚ)) / 64) ^ 2) / 64
      ≤ 169 / 8 := by
  have h := slope25_popoviciu_area_per_column_le_169_over_eight
    (slope35IndexedProfile sourceHeight)
    (slope35IndexedProfile_gradient sourceHeight)
  have hphysical : ∀ i : Col,
      (slope35Then25PhysicalOutputHeight sourceHeight i : ℚ) =
        (output25Height (slope35IndexedProfile sourceHeight) i : ℚ) := by
    intro i
    exact_mod_cast slope35Then25PhysicalOutputHeight_eq_abstract sourceHeight i
  simpa only [hphysical] using h

end Chvatal.D2Slope25Provider
'''

out = here / "D2Slope25Provider.lean"
out.write_text(source, encoding="utf-8")
print(f"wrote {out.name}: {len(source)} bytes")
