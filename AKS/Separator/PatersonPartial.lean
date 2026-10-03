module

public import AKS.Separator.PatersonRefinement
public import AKS.Paterson.Padding
public import AKS.Bitonic.Depth
public import AKS.Paterson.FastParams

/-! # The concrete padded separator for an even partial bag

The first halver uses the real arity. The two half refinements are padded to
the ideal half arity, with maxima on the left and minima on the right. This
module proves actual execution views, the 989-depth budget, the first good
contract, and both padded refinement contracts. Combining those into the
whole partial-bag invariant is a remaining scheduler obligation.
-/

@[expose] public section

namespace Paterson

open Finset

/-- The larger error of the partial-bag gadget fits the higher-order decay
budget when no contribution arrives from children below the partial level.
The whole-bag filtering proof is still needed to use this certificate. -/
theorem partial_tail_budget :
    patersonDelta0 + refinementTailError ≤
      Bags.fastParams.nu * Bags.fastParams.A * Bags.fastParams.delta := by
  norm_num [refinementTailError, patersonDelta0, patersonDelta2,
    patersonDelta3, patersonDelta4, patersonDelta5, Bags.fastParams]

noncomputable def partialRefinement (full real : ℕ) (hs : real ≤ full) :
    ComparatorNetwork (2 * real) :=
  let left := (refinementNetwork full).restrictWires real hs
  let right := paddedFinalNetwork (refinementNetwork full) real hs
  ⟨(left.shiftEmbed (2 * real) 0 (by omega)).comparators ++
    (right.shiftEmbed (2 * real) real (by omega)).comparators⟩

noncomputable def partialNetwork (full real : ℕ) (hs : real ≤ full) :
    ComparatorNetwork (2 * real) :=
  ⟨(firstLevelNetwork real).comparators ++ (partialRefinement full real hs).comparators⟩

theorem partialRefinement_depth_le (full real : ℕ) (hs : real ≤ full) :
    (partialRefinement full real hs).depth ≤ 726 := by
  let left := (refinementNetwork full).restrictWires real hs
  let right := paddedFinalNetwork (refinementNetwork full) real hs
  let left' := left.shiftEmbed (2 * real) 0 (by omega)
  let right' := right.shiftEmbed (2 * real) real (by omega)
  apply depth_append_wire_disjoint left' right' 726
  · exact (depth_shiftEmbed_le _ _ _ _).trans
      ((restrictWires_depth_le _ _ _).trans (refinementNetwork_depth_le _))
  · exact (depth_shiftEmbed_le _ _ _ _).trans
      ((paddedFinalNetwork_depth_le _ _ _).trans (refinementNetwork_depth_le _))
  · intro c hc d hd
    have hL := shiftEmbed_wires_range left (2 * real) 0 (by omega) c hc
    have hR := shiftEmbed_wires_range right (2 * real) real (by omega) d hd
    exact ⟨⟨by intro h; have := congrArg Fin.val h; omega,
      by intro h; have := congrArg Fin.val h; omega⟩,
      ⟨by intro h; have := congrArg Fin.val h; omega,
        by intro h; have := congrArg Fin.val h; omega⟩⟩

theorem partialNetwork_depth_le (full real : ℕ) (hs : real ≤ full) :
    (partialNetwork full real hs).depth ≤ 989 :=
  (depth_append _ _).trans (add_le_add (firstLevelNetwork_depth_le real)
    (partialRefinement_depth_le full real hs))

theorem partialNetwork_good (full real : ℕ) (hs : real ≤ full) :
    IsEpsilonAlphaHalver (partialNetwork full real hs) patersonDelta0 patersonAlpha0 :=
  IsEpsilonAlphaHalver.append (firstLevelNetwork_good real) (partialRefinement full real hs)

theorem partialRefinement_left_exec (full real : ℕ) (hs : real ≤ full)
    {ambient : ℕ} (w : Fin (2 * real) → Fin ambient) (i : Fin real) :
    (partialRefinement full real hs).exec w ⟨i.val, by have := i.isLt; omega⟩ =
      ((refinementNetwork full).restrictWires real hs).exec
        (fun j ↦ w ⟨j.val, by have := j.isLt; omega⟩) i := by
  unfold partialRefinement
  rw [ComparatorNetwork.exec_append]
  rw [ComparatorNetwork.shiftEmbed_exec_outside _ _ _ _ _ _
    (Or.inl (by show i.val < real; exact i.isLt))]
  simpa only [Nat.zero_add] using
    ComparatorNetwork.shiftEmbed_exec_inside
      ((refinementNetwork full).restrictWires real hs) (2 * real) 0 (by omega) w i

theorem partialRefinement_right_exec (full real : ℕ) (hs : real ≤ full)
    {ambient : ℕ} (w : Fin (2 * real) → Fin ambient) (i : Fin real) :
    (partialRefinement full real hs).exec w ⟨real + i.val, by have := i.isLt; omega⟩ =
      (paddedFinalNetwork (refinementNetwork full) real hs).exec
        (fun j ↦ w ⟨real + j.val, by have := j.isLt; omega⟩) i := by
  unfold partialRefinement
  rw [ComparatorNetwork.exec_append, ComparatorNetwork.shiftEmbed_exec_inside]
  congr 1
  funext j
  exact ComparatorNetwork.shiftEmbed_exec_outside _ _ _ _ _ _
    (Or.inr (by show 0 + real ≤ real + j.val; omega))

/-- The left refinement contract applies at the ideal supported size even
when only a small real prefix of the ideal block is occupied. -/
theorem partialNetwork_left_refinement {full real ambient : ℕ} (hs : real ≤ full)
    (h16 : 16 ∣ full) (u : Fin (2 * real) → Fin ambient) (hu : Function.Injective u)
    (threshold : ℕ) (ht : threshold ≤ ambient)
    (hcohort : ((univ.filter (fun i : Fin real ↦
      ((firstLevelNetwork real).exec u ⟨i.val, by have := i.isLt; omega⟩).val < threshold)).card : ℝ) ≤
        (2 * patersonMu : ℝ) * full) :
    ((univ.filter (fun i : Fin real ↦ full / 16 ≤ i.val ∧
      ((partialNetwork full real hs).exec u ⟨i.val, by have := i.isLt; omega⟩).val < threshold)).card : ℝ) ≤
      (refinementTailError : ℝ) * (univ.filter (fun i : Fin real ↦
        ((firstLevelNetwork real).exec u ⟨i.val, by have := i.isLt; omega⟩).val < threshold)).card := by
  have hview (i : Fin real) :
      (partialNetwork full real hs).exec u ⟨i.val, by have := i.isLt; omega⟩ =
      ((refinementNetwork full).restrictWires real hs).exec
        (fun j ↦ (firstLevelNetwork real).exec u ⟨j.val, by have := j.isLt; omega⟩) i := by
    rw [partialNetwork, ComparatorNetwork.exec_append, partialRefinement_left_exec]
  simp_rw [hview]
  apply padded_initial_separator (refinementNetwork_supported full h16) hs
    _ _ threshold ht hcohort
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin (2 * real) ↦ x.val)
    (ComparatorNetwork.exec_injective _ hu hij))

theorem partialNetwork_right_refinement {full real ambient : ℕ} (hs : real ≤ full)
    (h16 : 16 ∣ full) (u : Fin (2 * real) → Fin ambient) (hu : Function.Injective u)
    (threshold : ℕ) (ht : threshold ≤ ambient)
    (hcohort : ((univ.filter (fun i : Fin real ↦ threshold ≤
      ((firstLevelNetwork real).exec u ⟨real + i.val, by have := i.isLt; omega⟩).val)).card : ℝ) ≤
        (2 * patersonMu : ℝ) * full) :
    ((univ.filter (fun i : Fin real ↦ i.val < real - full / 16 ∧ threshold ≤
      ((partialNetwork full real hs).exec u ⟨real + i.val, by have := i.isLt; omega⟩).val)).card : ℝ) ≤
      (refinementTailError : ℝ) * (univ.filter (fun i : Fin real ↦ threshold ≤
        ((firstLevelNetwork real).exec u ⟨real + i.val, by have := i.isLt; omega⟩).val)).card := by
  have hview (i : Fin real) :
      (partialNetwork full real hs).exec u ⟨real + i.val, by have := i.isLt; omega⟩ =
      (paddedFinalNetwork (refinementNetwork full) real hs).exec
        (fun j ↦ (firstLevelNetwork real).exec u ⟨real + j.val, by have := j.isLt; omega⟩) i := by
    rw [partialNetwork, ComparatorNetwork.exec_append, partialRefinement_right_exec]
  simp_rw [hview]
  apply padded_final_separator (refinementNetwork_supported full h16) hs
    _ _ threshold ht hcohort
  intro i j hij
  have h := congrArg (fun x : Fin (2 * real) ↦ x.val)
    (ComparatorNetwork.exec_injective _ hu hij)
  change real + i.val = real + j.val at h
  exact Fin.ext (by omega)

end Paterson
